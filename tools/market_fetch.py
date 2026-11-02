#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
房價行情：抓取＋清理＋聚合（資料源＝內政部實價登錄批次下載）
------------------------------------------------
  下載 lvr_landcsv.zip → 只讀 f_lvr_land_a.csv（新北市買賣）與 build_time.xml
  → 篩 6 個行政區 → 剔除（車位／特殊備註／單價無效／面積過小／離群）
  → 追加進 market_samples.json（只留最近 6 期）→ 輸出 market.json

只用 Python 標準庫。輸出檔放在本檔上一層（repo 根目錄），可用 --outdir 覆寫。
任何一步失敗 → 不動舊的 market.json／market_samples.json，印出原因，結束碼 1。
無變更（同一期重跑且結果相同）→ 不改檔（避免 Actions 每次都產生 commit）。

用法：python tools/market_fetch.py [--outdir DIR] [--zip LOCAL.zip]
"""
import argparse, csv, io, json, os, pathlib, re, statistics, sys, tempfile, time
import urllib.request, zipfile
from datetime import datetime, timezone, timedelta

URL = "https://plvr.land.moi.gov.tw/Download?type=zip&fileName=lvr_landcsv.zip"
CSV_NAME = "f_lvr_land_a.csv"          # f = 新北市，_a = 買賣
XML_NAME = "build_time.xml"
DISTRICTS = ["新莊區", "板橋區", "三重區", "泰山區", "中和區", "永和區"]
KEYWORDS = ["親友", "員工", "共有人", "特殊關係", "預售屋", "法拍", "地上權",
            "急買急賣", "瑕疵", "凶宅", "毛胚", "分件登記"]
MIN_AREA_M2 = 30          # 約 9 坪
M2_TO_PING = 3.3058
MIN_SAMPLES = 20          # 行政區×型態 少於此數標 provisional（參考值）
MIN_SHOW = 10             # 少於此數不輸出
OUTLIER_MIN_N = 10
OUTLIER_K = 3
KEEP_PERIODS = 6
MAX_ZIP_BYTES = 50 * 1024 * 1024
MAX_MEMBER_BYTES = 100 * 1024 * 1024
TZ = timezone(timedelta(hours=8))
TYPE_MAP = [("住宅大樓", "住宅大樓"), ("華廈", "華廈"), ("公寓", "公寓"), ("套房", "套房")]
NOTES = "已剔除車位、親友/特殊關係交易、預售屋、法拍等；單價為建物單價（萬/坪）"
SOURCE = "內政部不動產交易實價查詢服務網（實價登錄）"
SOURCE_URL = "https://lvr.land.moi.gov.tw/"


class Fail(Exception):
    pass


# ── 下載與解析 ─────────────────────────────────────────────
def download(url):
    last = None
    for i in range(3):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (market-fetch)"})
            with urllib.request.urlopen(req, timeout=90) as r:
                data = r.read(MAX_ZIP_BYTES + 1)
            if len(data) > MAX_ZIP_BYTES:
                raise Fail("下載內容超過大小上限")
            if not data.startswith(b"PK"):
                raise Fail("下載內容不是 zip（前 4 bytes=%r）" % data[:4])
            return data
        except Fail:
            raise
        except Exception as e:           # 網路錯誤：重試
            last = e
            time.sleep(3 * (i + 1))
    raise Fail(f"下載失敗：{last!r}")


def read_member(z, name):
    try:
        info = z.getinfo(name)
    except KeyError:
        raise Fail(f"zip 內找不到 {name}")
    if info.file_size > MAX_MEMBER_BYTES:
        raise Fail(f"{name} 解壓後過大")
    return z.read(name)


def parse_period(xml_text):
    """回傳（買賣案件期間字串, start_iso, end_iso, label）"""
    m = re.search(r"登記日期\s*(\d+)年(\d+)月(\d+)日至\s*(\d+)年(\d+)月(\d+)日之買賣案件", xml_text)
    if not m:
        raise Fail("build_time.xml 找不到「登記日期…之買賣案件」期間字串")
    y1, m1, d1, y2, m2, d2 = map(int, m.groups())
    pid = m.group(0)
    start = f"{y1 + 1911:04d}-{m1:02d}-{d1:02d}"
    end = f"{y2 + 1911:04d}-{m2:02d}-{d2:02d}"
    datetime.strptime(start, "%Y-%m-%d"); datetime.strptime(end, "%Y-%m-%d")
    label = f"{y1}/{m1}/{d1}–{m2}/{d2}" if y1 == y2 else f"{y1}/{m1}/{d1}–{y2}/{m2}/{d2}"
    return pid, start, end, label


def norm_type(s):
    s = (s or "").strip()
    for prefix, name in TYPE_MAP:
        if s.startswith(prefix):
            return name
    return s or "其他"


def roc_to_iso(s):
    s = (s or "").strip()
    if not re.fullmatch(r"\d{6,7}", s):
        return ""
    try:
        y, md = int(s[:-4]) + 1911, s[-4:]
        d = datetime(y, int(md[:2]), int(md[2:]))
        return d.strftime("%Y-%m-%d")
    except ValueError:
        return ""


def num(s):
    try:
        return float((s or "").replace(",", "").strip() or 0)
    except ValueError:
        return 0.0


def clean(csv_text, period_id):
    """回傳（samples, per_district 統計, dropped 總計, 關鍵字明細）"""
    rows = list(csv.reader(io.StringIO(csv_text)))
    if len(rows) < 3:
        raise Fail(f"{CSV_NAME} 資料列數異常（{len(rows)}）")
    head = [h.strip() for h in rows[0]]
    need = ["鄉鎮市區", "建物型態", "交易年月日", "建物移轉總面積平方公尺",
            "單價元平方公尺", "車位類別", "備註"]
    miss = [c for c in need if c not in head]
    if miss:
        raise Fail(f"{CSV_NAME} 欄位缺少：{miss}")
    ix = {c: head.index(c) for c in need}
    data = rows[2:]                       # 第 2 列是英文欄名
    stat = {d: {"raw": 0, "車位": 0, "備註關鍵字": 0, "單價無效": 0, "面積過小": 0, "離群": 0}
            for d in DISTRICTS}
    kw_count = {k: 0 for k in KEYWORDS}
    samples = []
    for r in data:
        if len(r) < len(head):
            continue
        d = r[ix["鄉鎮市區"]].strip()
        if d not in stat:
            continue
        st = stat[d]
        st["raw"] += 1
        if r[ix["車位類別"]].strip():
            st["車位"] += 1; continue
        note = r[ix["備註"]]
        hit = next((k for k in KEYWORDS if k in note), None)
        if hit:
            st["備註關鍵字"] += 1; kw_count[hit] += 1; continue
        unit = num(r[ix["單價元平方公尺"]])
        if unit <= 0:
            st["單價無效"] += 1; continue
        area = num(r[ix["建物移轉總面積平方公尺"]])
        if area < MIN_AREA_M2:
            st["面積過小"] += 1; continue
        samples.append({
            "district": d,
            "type": norm_type(r[ix["建物型態"]]),
            "unit_price_wp": round(unit * M2_TO_PING / 10000, 2),
            "area_m2": round(area, 2),
            "deal_date": roc_to_iso(r[ix["交易年月日"]]),
            "period_id": period_id,
        })
    # 離群：每個（行政區×型態）樣本 ≥10 → 剔除 median ± 3×MAD
    groups = {}
    for s in samples:
        groups.setdefault((s["district"], s["type"]), []).append(s)
    out = []
    for (d, _t), g in groups.items():
        if len(g) >= OUTLIER_MIN_N:
            vals = [x["unit_price_wp"] for x in g]
            med = statistics.median(vals)
            mad = statistics.median([abs(v - med) for v in vals])
            if mad > 0:
                keep = [x for x in g if abs(x["unit_price_wp"] - med) <= OUTLIER_K * mad]
                stat[d]["離群"] += len(g) - len(keep)
                g = keep
        out.extend(g)
    return out, stat, kw_count


# ── 聚合 ──────────────────────────────────────────────────
def quantile(sorted_vals, q):
    pos = (len(sorted_vals) - 1) * q
    lo = int(pos)
    hi = min(lo + 1, len(sorted_vals) - 1)
    return sorted_vals[lo] + (sorted_vals[hi] - sorted_vals[lo]) * (pos - lo)


def aggregate(samples):
    districts = {}
    for d in DISTRICTS:
        ds = [s for s in samples if s["district"] == d]
        by_type = {}
        for s in ds:
            by_type.setdefault(s["type"], []).append(s["unit_price_wp"])
        types = []
        for t, vals in by_type.items():
            if len(vals) < MIN_SHOW:
                continue
            v = sorted(vals)
            types.append({"type": t, "n": len(v), "median": round(statistics.median(v), 1),
                          "p25": round(quantile(v, .25), 1), "p75": round(quantile(v, .75), 1),
                          "provisional": len(v) < MIN_SAMPLES})
        types.sort(key=lambda x: -x["n"])
        districts[d] = {"samples": len(ds), "types": types}
    return districts


def window_label(periods):
    s = min(p["start"] for p in periods)
    e = max(p["end"] for p in periods)
    sy, sm, sd = (int(x) for x in s.split("-")); ey, em, ed = (int(x) for x in e.split("-"))
    span = (f"{sy - 1911}/{sm}/{sd}–{em}/{ed}" if sy == ey
            else f"{sy - 1911}/{sm}/{sd}–{ey - 1911}/{em}/{ed}")
    return f"{span}（累積 {len(periods)} 期）"


# ── 檔案 I/O ──────────────────────────────────────────────
def load_json(path):
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as e:
        raise Fail(f"既有檔案 {path.name} 無法解析（{e}）；請人工檢查，未覆寫")


def write_atomic(path, text):
    fd, tmp = tempfile.mkstemp(dir=str(path.parent), prefix=path.name + ".", suffix=".tmp")
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as f:
            f.write(text)
        os.replace(tmp, path)
    except Exception:
        if os.path.exists(tmp):
            os.remove(tmp)
        raise


def run(outdir, local_zip):
    if local_zip:
        data = pathlib.Path(local_zip).read_bytes()
    else:
        data = download(URL)
    print(f"下載 bytes：{len(data)}")
    try:
        z = zipfile.ZipFile(io.BytesIO(data))
    except zipfile.BadZipFile as e:
        raise Fail(f"zip 損毀：{e}")
    print(f"zip 內檔案數：{len(z.namelist())}")
    # 只取需要的兩個檔，解到暫存目錄（固定檔名，不信任 zip 內路徑）
    with tempfile.TemporaryDirectory(prefix="lvr_") as tmp:
        for name in (CSV_NAME, XML_NAME):
            (pathlib.Path(tmp) / name).write_bytes(read_member(z, name))
        try:
            xml_text = (pathlib.Path(tmp) / XML_NAME).read_text(encoding="utf-8-sig")
            csv_text = (pathlib.Path(tmp) / CSV_NAME).read_text(encoding="utf-8-sig")
        except UnicodeDecodeError as e:
            raise Fail(f"編碼解析失敗：{e}")
    pid, start, end, label = parse_period(xml_text)
    print(f"本期期間字串：{pid}")
    new_samples, stat, kw = clean(csv_text, pid)
    if sum(s["raw"] for s in stat.values()) == 0:
        raise Fail("6 個行政區原始筆數為 0，疑似格式變動")

    now = datetime.now(TZ).isoformat(timespec="seconds")
    sp = outdir / "market_samples.json"
    mp = outdir / "market.json"
    old = load_json(sp) or {"periods": [], "samples": []}
    old_market = load_json(mp)
    per_dropped = {k: sum(s[k] for s in stat.values())
                   for k in ("車位", "備註關鍵字", "單價無效", "面積過小", "離群")}

    prev = next((p for p in old["periods"] if p["id"] == pid), None)
    entry = {"id": pid, "label": label, "start": start, "end": end,
             "added_at": prev["added_at"] if prev else now,
             "raw": sum(s["raw"] for s in stat.values()),
             "dropped": per_dropped, "dropped_keywords": kw}
    periods = [p for p in old["periods"] if p["id"] != pid] + [entry]
    periods.sort(key=lambda p: (p["start"], p["end"]))
    periods = periods[-KEEP_PERIODS:]
    ids = {p["id"] for p in periods}
    samples = [s for s in old["samples"] if s["period_id"] != pid] + new_samples
    samples = [s for s in samples if s["period_id"] in ids]

    drop_total = {k: sum(p["dropped"].get(k, 0) for p in periods)
                  for k in ("車位", "備註關鍵字", "單價無效", "面積過小", "離群")}
    market = {
        "source": SOURCE, "source_url": SOURCE_URL, "generated_at": now,
        "periods": [{"id": p["id"], "label": p["label"], "added_at": p["added_at"]} for p in periods],
        "window_label": window_label(periods),
        "min_samples": MIN_SAMPLES,
        "min_show": MIN_SHOW,
        "districts": aggregate(samples),
        "dropped": drop_total,
        "notes": NOTES,
    }

    # 逐區稽核輸出
    print("── 本期各區（原始 / 剔除 / 最終）──")
    for d in DISTRICTS:
        s = stat[d]
        rm = s["車位"] + s["備註關鍵字"] + s["單價無效"] + s["面積過小"] + s["離群"]
        fin = s["raw"] - rm
        print(f"{d}：原始 {s['raw']}／剔除 {rm}（車位 {s['車位']}、備註 {s['備註關鍵字']}、"
              f"單價無效 {s['單價無效']}、面積過小 {s['面積過小']}、離群 {s['離群']}）／最終 {fin}")
    print("本期剔除合計：", json.dumps(per_dropped, ensure_ascii=False))
    print("備註關鍵字明細：", json.dumps({k: v for k, v in kw.items() if v}, ensure_ascii=False))
    print(f"窗口：{market['window_label']}，期數 {len(periods)}，樣本總數 {len(samples)}")

    new_sp = {"periods": periods, "samples": samples}
    same = (old_market is not None and old == new_sp and
            {k: v for k, v in old_market.items() if k != "generated_at"} ==
            {k: v for k, v in market.items() if k != "generated_at"})
    if same:
        print("無變更（同一期且結果相同），不改檔。")
        return
    # 先全部序列化好，再寫檔（任何一步失敗都不會留下半套）
    sp_text = json.dumps(new_sp, ensure_ascii=False, separators=(",", ":")) + "\n"
    mp_text = json.dumps(market, ensure_ascii=False, indent=2) + "\n"
    write_atomic(sp, sp_text)
    write_atomic(mp, mp_text)
    print(f"已寫入 {sp.name}（{len(sp_text.encode('utf-8'))} bytes）與 {mp.name}")


def main():
    for st in (sys.stdout, sys.stderr):
        try:
            st.reconfigure(encoding="utf-8")
        except Exception:
            pass
    ap = argparse.ArgumentParser()
    ap.add_argument("--outdir", default=str(pathlib.Path(__file__).resolve().parent.parent))
    ap.add_argument("--zip", default=None, help="測試用：改讀本機 zip，不下載")
    a = ap.parse_args()
    try:
        run(pathlib.Path(a.outdir), a.zip)
    except Fail as e:
        print(f"ERROR: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"ERROR: 未預期的錯誤：{e!r}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
