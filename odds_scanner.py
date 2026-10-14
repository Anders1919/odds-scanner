#!/usr/bin/env python3
"""
Odds-scanner: finner feilprisede odds (value bets) og arbitrasje på tvers av bookmakere.

Datakilde: The Odds API (https://the-odds-api.com) – dekker 40+ bookmakere og mange
markeder (h2h/1X2, handicap, over/under, BTTS, draw no bet, alternative linjer, spillermarkeder).

Hvordan "feil" odds oppdages:
  1. For hver kamp + marked + linje samles prisene fra alle bookmakere.
  2. En rettferdig sannsynlighet estimeres ved å fjerne marginen ("devig"):
       - fra en skarp bookmaker (Pinnacle / Betfair-børs) hvis tilgjengelig, ellers
       - som median av alle bookmakernes devigga sannsynligheter (konsensus).
  3. VALUE:  EV = odds * rettferdig_sannsynlighet - 1. Flagges når EV >= terskel.
     Veldig høy EV merkes "MISTENKELIG" (ofte datafeil, ulike regler, eller en
     åpenbar feilpris som bookmakeren kan annullere).
  4. ARBITRASJE: beste odds per utfall på tvers av bookmakere; hvis sum(1/odds) < 1
     gir fordelt innsats garantert gevinst.

Bruk:
  export ODDS_API_KEY=din_nøkkel
  python odds_scanner.py                          # alle aktive idretter, h2h/spreads/totals
  python odds_scanner.py --sports soccer_epl soccer_norway_eliteserien
  python odds_scanner.py --extra-markets btts,draw_no_bet,alternate_totals
  python odds_scanner.py --interval 120           # skann hvert 2. minutt
  python odds_scanner.py --demo                   # test uten API-nøkkel (syntetiske data)
"""
import argparse
import csv
import html
import json
import os
import random
import statistics
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo

TZ = ZoneInfo("Europe/Oslo")


def local(iso):
    """ISO-tid (UTC) -> norsk tid som tekst."""
    try:
        return parse_ts(iso).astimezone(TZ).strftime("%d.%m %H:%M")
    except Exception:
        return iso

API = "https://api.the-odds-api.com/v4"
DEFAULT_SHARP = ["pinnacle", "betfair_ex_eu", "betfair_ex_uk", "matchbook"]
EXCHANGES = {"betfair_ex_eu", "betfair_ex_uk", "betfair_ex_au", "matchbook", "smarkets"}

quota = {"remaining": None, "used": None}


# ----------------------------------------------------------------------------- API
def http_get(path, params):
    url = f"{API}{path}?{urllib.parse.urlencode(params)}"
    req = urllib.request.Request(url, headers={"User-Agent": "odds-scanner/1.0"})
    with urllib.request.urlopen(req, timeout=30) as r:
        quota["remaining"] = r.headers.get("x-requests-remaining", quota["remaining"])
        quota["used"] = r.headers.get("x-requests-used", quota["used"])
        return json.loads(r.read())


def safe_get(path, params, what):
    try:
        return http_get(path, params)
    except urllib.error.HTTPError as e:
        body = e.read().decode(errors="ignore")[:200]
        print(f"  ! {what}: HTTP {e.code} {body}", file=sys.stderr)
    except Exception as e:  # nettverk, timeout osv.
        print(f"  ! {what}: {e}", file=sys.stderr)
    return None


def fetch_sports(api_key, include_outrights=False):
    data = safe_get("/sports", {"apiKey": api_key}, "henter idretter") or []
    return [s["key"] for s in data
            if s.get("active") and (include_outrights or not s.get("has_outrights"))]


def fetch_odds(api_key, sport, regions, markets):
    params = {"apiKey": api_key, "regions": regions, "markets": markets,
              "oddsFormat": "decimal", "dateFormat": "iso"}
    return safe_get(f"/sports/{sport}/odds", params, f"{sport} odds") or []


def fetch_event_odds(api_key, sport, event_id, regions, markets):
    params = {"apiKey": api_key, "regions": regions, "markets": markets,
              "oddsFormat": "decimal", "dateFormat": "iso"}
    return safe_get(f"/sports/{sport}/events/{event_id}/odds", params,
                    f"{sport}/{event_id} ekstra markeder")


# ----------------------------------------------------------------------------- Matte
def parse_ts(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


def devig(prices, method="power"):
    """Fjerner bookmakerens margin. Returnerer {utfall: sannsynlighet}."""
    inv = {k: 1.0 / v for k, v in prices.items()}
    s = sum(inv.values())
    if method == "multiplicative" or s <= 1.0:
        return {k: v / s for k, v in inv.items()}
    # Power-metoden: finn k slik at sum(p_i^k) = 1. Korrigerer favoritt/longshot-skjevhet.
    lo, hi = 1.0, 10.0
    for _ in range(60):
        k = (lo + hi) / 2
        if sum(p ** k for p in inv.values()) > 1:
            lo = k
        else:
            hi = k
    k = (lo + hi) / 2
    out = {o: p ** k for o, p in inv.items()}
    t = sum(out.values())
    return {o: v / t for o, v in out.items()}


def fair_probs(book_prices, labels, sharp_books, min_books, method):
    complete = {b: p for b, p in book_prices.items() if set(p) == labels}
    for sb in sharp_books:
        if sb in complete:
            return devig(complete[sb], method), f"skarp:{sb}", sb
    if len(complete) >= min_books:
        dv = [devig(p, method) for p in complete.values()]
        fair = {l: statistics.median(d[l] for d in dv) for l in labels}
        s = sum(fair.values())
        return {l: v / s for l, v in fair.items()}, f"konsensus({len(complete)})", None
    return None, None, None


# ----------------------------------------------------------------------------- Normalisering
def group_lines(event, args):
    """(marked, beskrivelse, linje) -> bookmaker -> {utfall: odds}"""
    home = event.get("home_team")
    now = datetime.now(timezone.utc)
    lines = defaultdict(lambda: defaultdict(dict))
    for bm in event.get("bookmakers", []):
        bk = bm["key"]
        if args.exclude_books and bk in args.exclude_books:
            continue
        for m in bm.get("markets", []):
            mk = m["key"]
            if mk.endswith("_lay"):
                continue
            lu = m.get("last_update") or bm.get("last_update")
            if lu and args.max_age and (now - parse_ts(lu)).total_seconds() / 60 > args.max_age:
                continue  # utdatert odds – gir falske treff
            for o in m.get("outcomes", []):
                try:
                    price = float(o["price"])
                except (KeyError, TypeError, ValueError):
                    continue
                if price <= 1.0:
                    continue
                if bk in EXCHANGES:  # trekk fra børskommisjon på gevinst
                    price = 1 + (price - 1) * (1 - args.commission)
                pt = o.get("point")
                desc = o.get("description")
                is_spread = "spread" in mk or "handicap" in mk
                if pt is None:
                    line = None
                    label = o["name"]
                elif is_spread:
                    line = pt if o["name"] == home else -pt
                    label = f"{o['name']} {pt:+g}"
                else:
                    line = pt
                    label = f"{o['name']} {pt:g}"
                lines[(mk, desc, line)][bk][label] = price
    return lines


# ----------------------------------------------------------------------------- Analyse
def analyse_event(event, sport, args):
    value, arbs = [], []
    title = f"{event.get('home_team', '?')} – {event.get('away_team', '?')}"
    start = event.get("commence_time", "")
    for (mk, desc, line), book_prices in group_lines(event, args).items():
        labels = set().union(*[set(p) for p in book_prices.values()])
        if len(labels) < 2 or len(book_prices) < 2:
            continue
        market_name = mk + (f" [{desc}]" if desc else "")

        # --- Arbitrasje
        best = {}
        for l in labels:
            cands = [(p[l], b) for b, p in book_prices.items() if l in p]
            best[l] = max(cands)
        inv_sum = sum(1 / best[l][0] for l in labels)
        # Krev at minst én bookmaker tilbyr hele markedet (sikrer at utfallene er uttømmende)
        has_full = any(set(p) == labels for p in book_prices.values())
        if has_full and inv_sum < 1:
            profit = 1 / inv_sum - 1
            if profit >= args.min_arb:
                legs = [{"utfall": l, "odds": round(best[l][0], 3), "bookmaker": best[l][1],
                         "innsats": round(args.bankroll * (1 / best[l][0]) / inv_sum, 2)}
                        for l in sorted(labels)]
                arbs.append({"idrett": sport, "kamp": title, "start": start, "marked": market_name,
                             "gevinst_pct": round(profit * 100, 2), "ben": legs,
                             "flagg": "MISTENKELIG" if profit > args.suspicious / 2 else ""})

        # --- Value
        fair, source, source_book = fair_probs(book_prices, labels, args.sharp,
                                                args.min_books, args.devig)
        if not fair:
            continue
        for bk, prices in book_prices.items():
            if bk == source_book:
                continue
            for l, price in prices.items():
                p = fair[l]
                ev = price * p - 1
                if ev < args.min_ev:
                    continue
                fair_odds = 1 / p
                kelly = max(0.0, (p * price - 1) / (price - 1)) * args.kelly
                others = [bp[l] for b, bp in book_prices.items() if b != bk and l in bp]
                med = statistics.median(others) if others else None
                value.append({
                    "idrett": sport, "kamp": title, "start": start, "marked": market_name,
                    "utfall": l, "bookmaker": bk, "odds": round(price, 3),
                    "fair_odds": round(fair_odds, 3), "median_andre": round(med, 3) if med else "",
                    "ev_pct": round(ev * 100, 2), "kilde": source,
                    "kelly_innsats": round(kelly * args.bankroll, 2),
                    "flagg": "MISTENKELIG" if ev > args.suspicious else "",
                })
    return value, arbs


def scan_once(args):
    all_value, all_arbs = [], []
    now = datetime.now(timezone.utc)
    horizon = now + timedelta(hours=args.hours) if args.hours else None

    if args.demo:
        batches = demo_batches()
    else:
        sports = args.sports or fetch_sports(args.api_key, args.outrights)
        print(f"Skanner {len(sports)} idretter …")
        batches = []
        for sport in sports:
            events = fetch_odds(args.api_key, sport, args.regions, args.markets)
            if args.extra_markets and events:
                for ev in events:
                    if not upcoming(ev, now, horizon, args.live):
                        continue
                    extra = fetch_event_odds(args.api_key, sport, ev["id"],
                                             args.regions, args.extra_markets)
                    if extra:
                        merge_bookmakers(ev, extra)
            batches.append((sport, events))

    n_events = 0
    for sport, events in batches:
        for ev in events:
            if not upcoming(ev, now, horizon, args.live):
                continue
            n_events += 1
            v, a = analyse_event(ev, sport, args)
            all_value += v
            all_arbs += a
    all_value.sort(key=lambda r: r["ev_pct"], reverse=True)
    all_arbs.sort(key=lambda r: r["gevinst_pct"], reverse=True)
    return all_value, all_arbs, n_events


def upcoming(ev, now, horizon, live):
    ct = ev.get("commence_time")
    if not ct:
        return True
    t = parse_ts(ct)
    if t < now and not live:
        return False
    return horizon is None or t <= horizon


def merge_bookmakers(ev, extra):
    by_key = {b["key"]: b for b in ev.setdefault("bookmakers", [])}
    for b in extra.get("bookmakers", []):
        if b["key"] in by_key:
            by_key[b["key"]]["markets"].extend(b.get("markets", []))
        else:
            ev["bookmakers"].append(b)


# ----------------------------------------------------------------------------- Output
def print_report(value, arbs, n_events):
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    print(f"\n=== Skann {ts} – {n_events} kamper, {len(value)} value, {len(arbs)} arbitrasje ===")
    if quota["remaining"] is not None:
        print(f"API-kvote: {quota['remaining']} igjen ({quota['used']} brukt)")
    if arbs:
        print("\n-- ARBITRASJE --")
        for a in arbs[:20]:
            print(f"{a['gevinst_pct']:>6.2f}%  {a['kamp']} | {a['marked']} {a['flagg']}")
            for leg in a["ben"]:
                print(f"           {leg['utfall']:<28} {leg['odds']:>7} @ {leg['bookmaker']:<16} innsats {leg['innsats']}")
    if value:
        print("\n-- VALUE / FEILPRISEDE ODDS --")
        print(f"{'EV%':>7}  {'Odds':>6} {'Fair':>6}  {'Bookmaker':<16} {'Utfall':<26} Kamp | marked")
        for r in value[:40]:
            print(f"{r['ev_pct']:>6.2f}%  {r['odds']:>6} {r['fair_odds']:>6}  {r['bookmaker']:<16} "
                  f"{r['utfall'][:26]:<26} {r['kamp']} | {r['marked']} {r['flagg']}")


def write_csv(value, arbs, outdir):
    os.makedirs(outdir, exist_ok=True)
    if value:
        with open(os.path.join(outdir, "value.csv"), "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=list(value[0].keys()))
            w.writeheader()
            w.writerows(value)
    with open(os.path.join(outdir, "arbitrasje.csv"), "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["gevinst_pct", "idrett", "kamp", "start", "marked", "utfall", "odds", "bookmaker", "innsats", "flagg"])
        for a in arbs:
            for leg in a["ben"]:
                w.writerow([a["gevinst_pct"], a["idrett"], a["kamp"], a["start"], a["marked"],
                            leg["utfall"], leg["odds"], leg["bookmaker"], leg["innsats"], a["flagg"]])


def write_html(value, arbs, n_events, outdir, filename="index.html", refresh=300):
    os.makedirs(outdir, exist_ok=True)
    e = html.escape
    ts = datetime.now(TZ).strftime("%d.%m.%Y kl. %H:%M")
    arb_rows = "".join(
        f"<tr class='{'sus' if a['flagg'] else ''}'><td class='num'>{a['gevinst_pct']}%</td><td>{e(a['kamp'])}</td>"
        f"<td>{e(a['marked'])}</td><td>{'<br>'.join(e(f'{l['utfall']} @ {l['odds']} ({l['bookmaker']}) – {l['innsats']}') for l in a['ben'])}</td>"
        f"<td>{e(local(a['start']))}</td><td>{a['flagg']}</td></tr>" for a in arbs)
    val_rows = "".join(
        f"<tr class='{'sus' if r['flagg'] else ''}'><td class='num'>{r['ev_pct']}%</td><td>{e(r['kamp'])}</td>"
        f"<td>{e(r['marked'])}</td><td>{e(r['utfall'])}</td><td>{e(r['bookmaker'])}</td>"
        f"<td class='num'>{r['odds']}</td><td class='num'>{r['fair_odds']}</td><td class='num'>{r['median_andre']}</td>"
        f"<td>{e(r['kilde'])}</td><td class='num'>{r['kelly_innsats']}</td>"
        f"<td>{e(local(r['start']))}</td><td>{r['flagg']}</td></tr>" for r in value)
    doc = f"""<!doctype html><html lang="no"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><meta http-equiv="refresh" content="{refresh}"><title>Odds-scanner</title>
<style>
:root{{--bg:#fff;--fg:#1a1a1a;--mut:#666;--line:#e5e5e5;--acc:#0b7a3e;--warn:#fff4d6}}
@media (prefers-color-scheme:dark){{:root{{--bg:#151515;--fg:#eee;--mut:#999;--line:#333;--acc:#3ecf7e;--warn:#3a3000}}}}
body{{background:var(--bg);color:var(--fg);font:14px/1.45 system-ui,sans-serif;margin:0;padding:16px}}
h1{{font-size:20px;margin:0 0 4px}} h2{{font-size:16px;margin:24px 0 8px}} p{{color:var(--mut);margin:0}}
.wrap{{overflow-x:auto}} table{{border-collapse:collapse;width:100%;min-width:720px}}
th,td{{padding:6px 8px;border-bottom:1px solid var(--line);text-align:left;vertical-align:top}}
th{{font-size:12px;color:var(--mut);text-transform:uppercase}} .num{{text-align:right;font-variant-numeric:tabular-nums}}
td.num:first-child{{color:var(--acc);font-weight:600}} tr.sus{{background:var(--warn)}}
</style></head><body>
<h1>Odds-scanner</h1><p>Sist oppdatert {ts} · {n_events} kamper · {len(value)} value · {len(arbs)} arbitrasje. Gule rader = mistenkelig høy edge, sjekk manuelt.</p>
<h2>Arbitrasje</h2><div class="wrap"><table><tr><th>Gevinst</th><th>Kamp</th><th>Marked</th><th>Ben (odds, bookmaker, innsats)</th><th>Start</th><th></th></tr>{arb_rows or '<tr><td colspan=6>Ingen funnet</td></tr>'}</table></div>
<h2>Value / feilprisede odds</h2><div class="wrap"><table><tr><th>EV</th><th>Kamp</th><th>Marked</th><th>Utfall</th><th>Bookmaker</th><th>Odds</th><th>Fair</th><th>Median andre</th><th>Kilde</th><th>Kelly</th><th>Start</th><th></th></tr>{val_rows or '<tr><td colspan=12>Ingen funnet</td></tr>'}</table></div>
</body></html>"""
    with open(os.path.join(outdir, filename), "w", encoding="utf-8") as f:
        f.write(doc)


# ----------------------------------------------------------------------------- Demo-data
def demo_batches():
    """Syntetiske kamper med realistisk margin + noen innplantede feil, for testing."""
    rnd = random.Random(42)
    books = ["pinnacle", "unibet_eu", "betsson", "nordicbet", "williamhill", "betfair_ex_eu", "coolbet", "888sport"]
    teams = [("Rosenborg", "Molde"), ("Bodø/Glimt", "Brann"), ("Arsenal", "Chelsea"),
             ("Liverpool", "Everton"), ("Viking", "Lillestrøm"), ("Real Madrid", "Sevilla")]
    start = (datetime.now(timezone.utc) + timedelta(hours=20)).isoformat().replace("+00:00", "Z")
    now_s = datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")
    events = []
    for i, (h, a) in enumerate(teams):
        ph = rnd.uniform(0.3, 0.6); pd = rnd.uniform(0.22, 0.3); pa = 1 - ph - pd
        pover = rnd.uniform(0.45, 0.6)
        bms = []
        for b in books:
            margin = 1.02 if b in ("pinnacle", "betfair_ex_eu") else rnd.uniform(1.05, 1.09)
            def px(p): return round(1 / (p * margin * rnd.uniform(0.98, 1.02)), 2)
            mk = [
                {"key": "h2h", "last_update": now_s, "outcomes": [
                    {"name": h, "price": px(ph)}, {"name": "Draw", "price": px(pd)}, {"name": a, "price": px(pa)}]},
                {"key": "totals", "last_update": now_s, "outcomes": [
                    {"name": "Over", "price": px(pover), "point": 2.5}, {"name": "Under", "price": px(1 - pover), "point": 2.5}]},
            ]
            bms.append({"key": b, "title": b, "last_update": now_s, "markets": mk})
        events.append({"id": f"demo{i}", "home_team": h, "away_team": a, "commence_time": start, "bookmakers": bms})
    # Innplantet feilpris: Coolbet har byttet om hjemme/borte-odds i kamp 0
    o = events[0]["bookmakers"][6]["markets"][0]["outcomes"]
    o[0]["price"], o[2]["price"] = o[2]["price"], o[0]["price"]
    # Innplantet arbitrasje: NordicBet høy på Over, 888 høy på Under i kamp 2
    events[2]["bookmakers"][3]["markets"][1]["outcomes"][0]["price"] = 2.40
    events[2]["bookmakers"][7]["markets"][1]["outcomes"][1]["price"] = 2.10
    return [("soccer_demo", events)]


# ----------------------------------------------------------------------------- CLI
def main():
    ap = argparse.ArgumentParser(description="Finn feilprisede odds og arbitrasje på tvers av bookmakere.")
    ap.add_argument("--api-key", default=os.getenv("ODDS_API_KEY"))
    ap.add_argument("--sports", nargs="*", help="Idrettsnøkler (standard: alle aktive). F.eks. soccer_epl")
    ap.add_argument("--regions", default="eu,uk", help="eu,uk,us,us2,au (hver region koster kvote)")
    ap.add_argument("--markets", default="h2h,spreads,totals")
    ap.add_argument("--extra-markets", default="",
                    help="Hentes per kamp (dyrt i kvote): btts,draw_no_bet,alternate_totals,alternate_spreads,team_totals, spillermarkeder …")
    ap.add_argument("--outrights", action="store_true", help="Ta med langtidsmarkeder (vinner av ligaen osv.)")
    ap.add_argument("--min-ev", type=float, default=0.03, help="Min. forventet verdi (0.03 = 3%%)")
    ap.add_argument("--min-arb", type=float, default=0.0, help="Min. arbitrasjegevinst (0.01 = 1%%)")
    ap.add_argument("--suspicious", type=float, default=0.25, help="EV over dette merkes MISTENKELIG")
    ap.add_argument("--sharp", nargs="*", default=DEFAULT_SHARP, help="Skarpe bookmakere brukt som fasit, i prioritert rekkefølge")
    ap.add_argument("--min-books", type=int, default=4, help="Min. bookmakere for konsensus når skarp mangler")
    ap.add_argument("--devig", choices=["power", "multiplicative"], default="power")
    ap.add_argument("--commission", type=float, default=0.05, help="Børskommisjon (Betfair m.fl.)")
    ap.add_argument("--max-age", type=float, default=10, help="Ignorer odds eldre enn N minutter (0 = av)")
    ap.add_argument("--hours", type=float, default=72, help="Kun kamper som starter innen N timer (0 = alle)")
    ap.add_argument("--live", action="store_true", help="Ta med kamper som har startet")
    ap.add_argument("--exclude-books", nargs="*", default=[], help="Bookmakere du ikke har konto hos")
    ap.add_argument("--bankroll", type=float, default=1000)
    ap.add_argument("--kelly", type=float, default=0.25, help="Kelly-brøk for innsatsforslag")
    ap.add_argument("--interval", type=int, default=0, help="Skann på nytt hvert N sekund (0 = én gang)")
    ap.add_argument("--out", default="output")
    ap.add_argument("--demo", action="store_true")
    args = ap.parse_args()

    args.sports = [x for s in (args.sports or []) for x in s.replace(",", " ").split()] or None
    if not args.demo and not args.api_key:
        sys.exit("Mangler API-nøkkel. Sett ODDS_API_KEY eller bruk --api-key (gratis på the-odds-api.com). Eller kjør --demo.")

    while True:
        value, arbs, n = scan_once(args)
        print_report(value, arbs, n)
        write_csv(value, arbs, args.out)
        write_html(value, arbs, n, args.out)
        print(f"\nLagret: {args.out}/index.html, value.csv, arbitrasje.csv")
        if not args.interval:
            break
        time.sleep(args.interval)


if __name__ == "__main__":
    main()
