#!/usr/bin/env python3
"""TrueStars: the GitHub repos gaining stars fastest, checked for fake stars.

  python3 -I truestars.py           collect today's data, then build the site
  python3 -I truestars.py collect   only collect                  -> data/latest.json
  python3 -I truestars.py build     only build from the saved data -> data/days/<day>.json, site/

Needs GITHUB_TOKEN in the environment or a logged-in GitHub CLI (`gh`). Standard library only.
"""
import collections
import concurrent.futures as futures
import datetime as dt
import gzip
import html
import json
import math
import os
import re
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from string import Template
from zoneinfo import ZoneInfo

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
LATEST = os.path.join(DATA, "latest.json")
DAYS = os.path.join(DATA, "days")
SITE = os.path.join(HERE, "site")
SITE_URL = "https://truestars.dev"
UA = "truestars (+https://truestars.dev)"
PACIFIC = ZoneInfo("America/Los_Angeles")  # GitHub's star-history days are Pacific days
STAR_HISTORY_API_VERSION = "2026-03-10"
HISTORY_WEEKS = 13         # weeks of daily stars fetched per repo (one API call either way)
MIN_REPOS = 50             # a run with fewer repos than this has failed; the last data is kept

# Red flags: hints, not proof. Tuned on the 2026-11-02 run (253 listed repos).
NEW_OWNER_DAYS = 90        # owner account younger than this
RATIO_MIN_STARS = 300      # only judge ratios once a repo has this many stars
FORKS_PER_100 = 1.0        # fewer forks than this per 100 stars
TALK_PER_1K = 0.5          # fewer issues + pull requests than this per 1,000 stars
WATCHERS_PER_1K = 0.5      # fewer watchers than this per 1,000 stars
MIN_COMMITS = 3            # fewer commits than this
STOP_MIN_PEAK = 100        # "stars stopped dead": a day with at least this many stars, after which
STOP_SHARE = 0.01          # every complete day from two days on stayed under this share of it
HIDE_AT_FLAGS = 2          # repos with this many flags are left out of the ranking (owner, 2026-11-03)
HN_MIN_POINTS = 20         # a Hacker News post counts as a reason from this many points
HN_DAYS = 14               # ... if it was posted within this many days
RISKY_ASSET = re.compile(r"\.(exe|msi|scr|bat|cmd|apk|dmg|pkg|rar|7z)$", re.I)

_token = None


# ---------------------------------------------------------------- fetching

def gh_token():
    global _token
    if _token is None:
        _token = os.environ.get("GITHUB_TOKEN") or subprocess.run(
            ["gh", "auth", "token"], capture_output=True, text=True, check=True).stdout.strip()
    return _token


def fetch(url, headers=None, body=None, timeout=60, tries=3):
    """Return (status, bytes). Retries network and server errors."""
    hdrs = {"User-Agent": UA}
    hdrs.update(headers or {})
    for attempt in range(tries):
        try:
            req = urllib.request.Request(url, data=body, headers=hdrs)
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.status, resp.read()
        except urllib.error.HTTPError as err:
            if err.code >= 500 and attempt < tries - 1:
                time.sleep(2 * (attempt + 1))
                continue
            return err.code, err.read()
        except OSError:
            if attempt < tries - 1:
                time.sleep(2 * (attempt + 1))
                continue
            return 0, b""
    return 0, b""


def github(path, params=None, version=None):
    url = "https://api.github.com" + path
    if params:
        url += "?" + urllib.parse.urlencode(params)
    headers = {"Authorization": "Bearer " + gh_token(), "Accept": "application/vnd.github+json"}
    if version:
        headers["X-GitHub-Api-Version"] = version
    status, raw = fetch(url, headers)
    try:
        return status, (json.loads(raw) if raw else None)
    except ValueError:
        return status, None


def graphql(query):
    headers = {"Authorization": "Bearer " + gh_token(), "Content-Type": "application/json"}
    status, raw = fetch("https://api.github.com/graphql", headers, json.dumps({"query": query}).encode())
    try:
        return json.loads(raw) if raw else {}
    except ValueError:
        return {}


# --------------------------------------------------------------- discovery

def from_new_repos(days, min_stars):
    """Repos created in the last `days` days with the most stars."""
    since = (dt.datetime.now(dt.timezone.utc) - dt.timedelta(days=days)).strftime("%Y-%m-%d")
    status, data = github("/search/repositories", {
        "q": f"created:>={since} stars:>={min_stars}", "sort": "stars", "order": "desc", "per_page": 100})
    if status != 200 or not data:
        return []
    return [item["full_name"] for item in data.get("items", [])]


def _gharchive_hour(hour):
    status, raw = fetch(f"https://data.gharchive.org/{hour:%Y-%m-%d}-{hour.hour}.json.gz", timeout=180)
    if status != 200:
        return hour, None
    counts = collections.Counter()
    try:
        lines = gzip.decompress(raw).splitlines()
    except (OSError, EOFError):
        return hour, None
    for line in lines:
        if b'"WatchEvent"' not in line:
            continue
        try:
            event = json.loads(line)
        except ValueError:
            continue
        if event.get("type") == "WatchEvent":
            counts[event["repo"]["name"]] += 1
    return hour, counts


def from_gharchive(hours=24, top=80):
    """Repos with the most star events in GH Archive's latest 24 hours.

    GH Archive now records only a small share of all stars, so it is used only to
    discover candidates. Real counts come from GitHub's star-history API.
    """
    now = dt.datetime.now(dt.timezone.utc).replace(minute=0, second=0, microsecond=0)
    wanted = [now - dt.timedelta(hours=k) for k in range(1, hours + 7)]
    with futures.ThreadPoolExecutor(max_workers=4) as pool:
        results = sorted(pool.map(_gharchive_hour, wanted), key=lambda hc: hc[0], reverse=True)
    got = [counts for _, counts in results if counts is not None][:hours]
    total = collections.Counter()
    for counts in got:
        total.update(counts)
    return [name for name, n in total.most_common(top) if n >= 3], len(got)


# ------------------------------------------------------------- per-repo data

def star_history(full_name):
    """Exact stars per Pacific day for the last HISTORY_WEEKS weeks: {"YYYY-MM-DD": count}."""
    status, weeks = github(f"/repos/{full_name}/stargazers/history", {"per_page": HISTORY_WEEKS},
                           version=STAR_HISTORY_API_VERSION)
    if status != 200 or not isinstance(weeks, list):
        return None
    daily = {}
    for week in weeks:
        start = dt.datetime.fromtimestamp(week["week"], dt.timezone.utc).date()  # the Sunday
        for i, n in enumerate(week.get("days") or []):
            daily[(start + dt.timedelta(days=i)).isoformat()] = n
    return daily


REPO_FIELDS = """
  nameWithOwner url description homepageUrl createdAt pushedAt
  stargazerCount forkCount isFork isArchived hasIssuesEnabled
  primaryLanguage { name }
  watchers { totalCount }
  issues { totalCount }
  pullRequests { totalCount }
  defaultBranchRef { target { ... on Commit { history { totalCount } } } }
  releases(first: 1, orderBy: {field: CREATED_AT, direction: DESC}) {
    nodes { tagName url publishedAt releaseAssets(first: 20) { nodes { name } } }
  }
  owner { login __typename
    ... on User { createdAt followers { totalCount } }
    ... on Organization { createdAt } }
"""


def repo_details(names, batch=20):
    """Public facts about each repo and its owner, 20 repos per request."""
    out = {}
    for i in range(0, len(names), batch):
        chunk = names[i:i + batch]
        parts = []
        for j, full in enumerate(chunk):
            owner, name = full.split("/", 1)
            parts.append(f"r{j}: repository(owner: {json.dumps(owner)}, name: {json.dumps(name)}) {{ {REPO_FIELDS} }}")
        data = graphql("query { " + " ".join(parts) + " }").get("data") or {}
        for j, full in enumerate(chunk):
            if data.get(f"r{j}"):
                out[full] = data[f"r{j}"]
    return out


def hacker_news(full_name):
    """Hacker News stories that link to this repo, newest first."""
    query = urllib.parse.urlencode({"query": "github.com/" + full_name,
                                    "restrictSearchableAttributes": "url", "hitsPerPage": 30})
    status, raw = fetch("https://hn.algolia.com/api/v1/search?" + query)
    if status != 200:
        return None
    try:
        hits = json.loads(raw).get("hits", [])
    except ValueError:
        return None
    prefix = ("github.com/" + full_name).lower()
    stories = []
    for hit in hits:
        url = (hit.get("url") or "").lower().split("://", 1)[-1]
        if url.startswith("www."):
            url = url[4:]
        if url.startswith(prefix) and (url == prefix or url[len(prefix)] in "/?#"):
            stories.append({"title": hit.get("title") or "", "points": hit.get("points") or 0,
                            "date": (hit.get("created_at") or "")[:10], "id": hit.get("objectID")})
    return sorted(stories, key=lambda s: s["date"], reverse=True)


# ----------------------------------------------------------------- collect

def collect():
    started = time.time()
    print("1/4  Finding candidates: new repos with the most stars, and GH Archive's last 24 hours ...", flush=True)
    archive, hours_read = from_gharchive()
    sources = collections.OrderedDict()
    for label, names in (("new-30d", from_new_repos(30, 300)), ("new-7d", from_new_repos(7, 100)),
                         ("gharchive", archive)):
        for name in names:
            sources.setdefault(name.lower(), {"name": name, "sources": []})["sources"].append(label)
    names = [v["name"] for v in sources.values()]
    print(f"     {len(names)} candidates ({hours_read} archive hours read)")

    print("2/4  Counting exact daily stars for each candidate ...", flush=True)
    with futures.ThreadPoolExecutor(max_workers=4) as pool:
        histories = dict(zip(names, pool.map(star_history, names)))
    print("3/4  Looking up repo and owner details ...", flush=True)
    details = repo_details(names)
    print("4/4  Checking Hacker News for each candidate ...", flush=True)
    with futures.ThreadPoolExecutor(max_workers=4) as pool:
        news = dict(zip(names, pool.map(hacker_news, names)))

    repos = [{"name": e["name"], "sources": e["sources"], "daily": histories.get(e["name"]),
              "meta": details.get(e["name"]), "hn": news.get(e["name"])} for e in sources.values()]
    good = sum(1 for r in repos if r["daily"] and r["meta"])
    if good < MIN_REPOS:
        sys.exit(f"Only {good} repos came back with data (need {MIN_REPOS}); the last saved data is kept.")
    days_with_stars = [d for r in repos if r["daily"] for d, n in r["daily"].items() if n]
    data = {"generated_at": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
            "latest_day": max(days_with_stars), "repos": repos}
    os.makedirs(DATA, exist_ok=True)
    with open(LATEST + ".tmp", "w") as fh:
        json.dump(data, fh)
    os.replace(LATEST + ".tmp", LATEST)
    print(f"     {good} repos with data, saved {LATEST} in {time.time() - started:.0f}s")


# ------------------------------------------------------------------ assess

def pacific_day(iso):
    """The Pacific calendar day of an ISO date or UTC timestamp."""
    if len(iso) <= 10:
        return dt.date.fromisoformat(iso)
    return dt.datetime.fromisoformat(iso.replace("Z", "+00:00")).astimezone(PACIFIC).date()


def days_between(iso, day):
    return (day - pacific_day(iso)).days


def day_total(daily, end, n):
    return sum(daily.get((end - dt.timedelta(days=k)).isoformat(), 0) for k in range(n))


def slug_of(name):
    """URL path for a repo: lower case; a leading dot (e.g. .github) becomes _."""
    owner, repo = name.lower().split("/", 1)
    return f"{owner}/{'_' + repo[1:] if repo.startswith('.') else repo}"


def stopped_dead(daily, yday):
    """(peak, day) when stars fell from a big day to almost none and stayed there.

    Looks at the last 14 complete days. Real interest fades over days; stars that
    stop within two days of a 100+ star day are a pattern bought stars leave.
    2026-11-02: 4 repos at 0-0.3% of their peak, the next nearest at 3.0%.
    """
    days = [yday - dt.timedelta(days=k) for k in range(13, -1, -1)]
    counts = [daily.get(d.isoformat(), 0) for d in days]
    i = max(range(len(counts)), key=counts.__getitem__)
    peak = counts[i]
    if peak < STOP_MIN_PEAK:
        return None
    for start in (i + 1, i + 2):
        tail = counts[start:]
        if tail and max(tail) < STOP_SHARE * peak:
            return peak, days[i]
    return None


def assess(repo, latest):
    """Turn raw data into the numbers and plain-language notes on the pages."""
    meta, daily = repo["meta"], repo["daily"]
    yday = latest - dt.timedelta(days=1)
    stars = meta["stargazerCount"] or 0
    forks = meta["forkCount"] or 0
    watchers = meta["watchers"]["totalCount"]
    talk = meta["issues"]["totalCount"] + meta["pullRequests"]["totalCount"]
    target = (meta.get("defaultBranchRef") or {}).get("target") or {}
    commits = (target.get("history") or {}).get("totalCount")
    owner = meta["owner"]
    owner_age = days_between(owner["createdAt"], latest) if owner.get("createdAt") else None
    repo_age = days_between(meta["createdAt"], latest)
    release = (meta["releases"]["nodes"] or [None])[0]

    flags, context = [], []
    if stars >= RATIO_MIN_STARS:
        if forks * 100 < FORKS_PER_100 * stars:
            flags.append(f"Very few forks for its stars ({forks:,} fork{'s' if forks != 1 else ''})")
        if meta["hasIssuesEnabled"] and talk * 1000 < TALK_PER_1K * stars:
            flags.append(f"Almost no issues or pull requests ({talk:,})")
        if watchers * 1000 < WATCHERS_PER_1K * stars:
            flags.append(f"Very few people watching it ({watchers:,})")
        if commits is not None and commits < MIN_COMMITS:
            context.append(f"Only {commits} commit{'s' if commits != 1 else ''}")
    stop = stopped_dead(daily, yday)
    if stop:
        flags.append(f"Stars stopped dead: {stop[0]:,} on {fmt_day(stop[1].isoformat())}, then almost none")
    if owner_age is not None and owner_age < NEW_OWNER_DAYS:
        context.append(f"Owner's account is only {owner_age} days old")

    notes = []
    if flags:
        flags += context  # a new owner or a code drop only counts alongside another sign
    else:
        notes += [c + " (common for new launches)" for c in context]
    if release and any(RISKY_ASSET.search(a["name"]) for a in release["releaseAssets"]["nodes"]):
        notes.append("Offers program downloads; check before installing")

    why = []
    recent_hn = [s for s in (repo["hn"] or []) if s["date"] and s["points"] >= HN_MIN_POINTS
                 and days_between(s["date"], latest) <= HN_DAYS]
    if recent_hn:
        top = max(recent_hn, key=lambda s: s["points"])
        why.append({"text": f"Hacker News · {top['points']:,} points · {fmt_day(top['date'])}",
                    "url": f"https://news.ycombinator.com/item?id={top['id']}"})
    if release and release.get("publishedAt") and days_between(release["publishedAt"], latest) <= 7:
        why.append({"text": f"New release {release['tagName']} · {fmt_day(release['publishedAt'])}",
                    "url": release["url"]})
    if repo_age <= 14:
        why.append({"text": f"Brand new · created {fmt_day(meta['createdAt'])}", "url": None})

    first = min(dt.date.fromisoformat(k) for k in daily)
    chart_start = max(first, pacific_day(meta["createdAt"]), latest - dt.timedelta(days=89))
    week = day_total(daily, yday, 7)
    return {
        "slug": slug_of(meta["nameWithOwner"]),
        "name": meta["nameWithOwner"], "url": meta["url"],
        "description": (meta.get("description") or "")[:300],
        "language": (meta.get("primaryLanguage") or {}).get("name") or "",
        "stars": stars, "forks": forks,
        "today": daily.get(latest.isoformat(), 0),
        "yesterday": daily.get(yday.isoformat(), 0),
        "week": week,
        "growth": (week * 100.0 / max(stars - week, 1)) if repo_age > 7 else None,
        "spark": [daily.get((latest - dt.timedelta(days=k)).isoformat(), 0) for k in range(14, -1, -1)],
        "chart_start": chart_start.isoformat(),
        "chart": [daily.get((chart_start + dt.timedelta(days=k)).isoformat(), 0)
                  for k in range((latest - chart_start).days + 1)],
        "flags": flags, "notes": notes, "why": why,
    }


# ----------------------------------------------------------------- history

def save_day(day, rows, data):
    """The day's ranking as published. These files are the site's history."""
    os.makedirs(DAYS, exist_ok=True)
    snapshot = {"day": day.isoformat(), "generated_at": data["generated_at"],
                "repos_checked": len(data["repos"]),
                "rows": [{k: v for k, v in r.items() if k not in ("chart", "chart_start")} for r in rows]}
    path = os.path.join(DAYS, f"{day.isoformat()}.json")
    with open(path + ".tmp", "w") as fh:
        json.dump(snapshot, fh, separators=(",", ":"))
    os.replace(path + ".tmp", path)


def load_history():
    """{slug: {"ranks": [(day, rank), ...], "last": row, "last_day": day}} for every repo
    that was in the ranking on at least one day."""
    seen = {}
    for fname in sorted(os.listdir(DAYS)) if os.path.isdir(DAYS) else []:
        if not fname.endswith(".json"):
            continue
        with open(os.path.join(DAYS, fname)) as fh:
            snap = json.load(fh)
        for row in snap["rows"]:
            entry = seen.setdefault(row["slug"], {"ranks": []})
            entry["last"], entry["last_day"] = row, snap["day"]
            if row.get("rank"):
                entry["ranks"].append((snap["day"], row["rank"]))
    return {slug: e for slug, e in seen.items() if e["ranks"]}


def best_rank(ranks):
    """The best (lowest) rank and the first day it was reached."""
    best = min(rank for _, rank in ranks)
    return best, next(day for day, rank in ranks if rank == best)


# ------------------------------------------------------------------ render

def fmt_day(iso):
    day = pacific_day(iso)
    return f"{day:%b} {day.day}"


def fmt_count(n):
    if n >= 100_000:
        return f"{n / 1000:.0f}k"
    if n >= 10_000:
        return f"{n / 1000:.1f}k"
    return f"{n:,}"


def esc(text):
    return html.escape(str(text), quote=True)


def bars(values, first_day, width, height, gap, label_cls=""):
    """An SVG bar chart of stars per day; the last bar is the day in progress."""
    bar = (width - gap * (len(values) - 1)) / len(values)
    peak = max(values) or 1
    first = dt.date.fromisoformat(first_day)
    last = first + dt.timedelta(days=len(values) - 1)
    rects = []
    for i, v in enumerate(values):
        h = max(1.0, v / peak * (height - 2)) if v else 1.0
        cls = "bar-today" if i == len(values) - 1 else ("bar" if v else "bar-zero")
        day = first + dt.timedelta(days=i)
        rects.append(f'<rect class="{cls}" x="{i * (bar + gap):.1f}" y="{height - h:.1f}" width="{bar:.1f}" '
                     f'height="{h:.1f}" rx="1"><title>{fmt_day(day.isoformat())}: {v:,} stars</title></rect>')
    label = f"Stars per day from {fmt_day(first.isoformat())} to {fmt_day(last.isoformat())}"
    return (f'<svg class="{label_cls}" viewBox="0 0 {width} {height}" preserveAspectRatio="none" role="img" '
            f'aria-label="{esc(label)}">{"".join(rects)}</svg>')


def verdict(row):
    n = len(row["flags"])
    cls = "good" if n == 0 else ("warn" if n == 1 else "bad")
    text = "No red flags" if n == 0 else f"{n} red flag{'s' if n > 1 else ''}"
    return cls, text


def reasons_html(row):
    return "".join(f"<li>{esc(t)}</li>" for t in row["flags"] + row["notes"])


def why_chips(row):
    chips = []
    for w in row["why"]:
        if w["url"]:
            chips.append(f'<a class="chip" href="{esc(w["url"])}" target="_blank" rel="noopener">{esc(w["text"])}</a>')
        else:
            chips.append(f'<span class="chip">{esc(w["text"])}</span>')
    return "".join(chips)


def shell(title, body, root, description, updated):
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(title)}</title>
<meta name="description" content="{esc(description)}">
<link rel="stylesheet" href="{root}style.css">
<link rel="icon" href="{root}favicon.svg" type="image/svg+xml">
</head>
<body>
<header class="top"><div class="wrap">
  <a class="logo" href="{root}index.html">{STAR_ICON}TrueStars</a>
  <nav><a href="{root}index.html">Ranking</a><a href="{root}how/index.html">How it works</a></nav>
</div></header>
<main class="wrap">
{body}
</main>
<footer class="wrap foot">TrueStars · updated {esc(updated)} · data from GitHub's API, GH Archive and Hacker News ·
  not affiliated with GitHub</footer>
</body>
</html>
"""


def star_points(cx, cy, outer, inner):
    pts = []
    for k in range(10):
        r = outer if k % 2 == 0 else inner
        a = math.radians(-90 + 36 * k)
        pts.append(f"{cx + r * math.cos(a):.2f},{cy + r * math.sin(a):.2f}")
    return " ".join(pts)


STAR_ICON = (f'<svg class="star" viewBox="0 0 20 20" aria-hidden="true">'
             f'<polygon points="{star_points(10, 10.6, 9.5, 4)}"/></svg>')


def render_index(rows, day, latest, data, updated):
    root = ""
    today_label = fmt_day(latest.isoformat()) + (" so far" if latest >= dt.datetime.now(PACIFIC).date() else "")
    hidden = sum(1 for r in rows if not r["rank"])
    items = []
    for r in rows:
        cls, text = verdict(r)
        reasons = reasons_html(r)
        name_href = f"r/{r['slug']}/index.html" if r["rank"] else r["url"]
        growth = "new" if r["growth"] is None else f'+{r["growth"]:.0f}%'
        items.append(f"""
<li class="row" data-yesterday="{r['yesterday']}" data-today="{r['today']}" data-week="{r['week']}"
    data-growth="{r['growth'] if r['growth'] is not None else 1e9}" data-flags="{len(r['flags'])}">
  <span class="rank"></span>
  <div class="main">
    <div class="title">
      <a class="name" href="{esc(name_href)}">{esc(r['name'])}</a>
      <span class="lang">{esc(r['language'])}</span>
      <a class="gh" href="{esc(r['url'])}" target="_blank" rel="noopener">GitHub ↗</a>
    </div>
    <p class="desc">{esc(r['description'][:220])}</p>
    <div class="chips">{why_chips(r)}</div>
    <details class="verdict verdict-{cls}"{'' if reasons else ' data-empty'}>
      <summary>{text}</summary>{f'<ul>{reasons}</ul>' if reasons else ''}
    </details>
  </div>
  <div class="nums">
    <div><b>+{r['yesterday']:,}</b><span>{fmt_day(day.isoformat())}</span></div>
    <div><b>+{r['today']:,}</b><span>{today_label}</span></div>
    <div><b>+{fmt_count(r['week'])}</b><span>7 days · {growth}</span></div>
    <div><b>{fmt_count(r['stars'])}</b><span>total stars</span></div>
  </div>
  {bars(r['spark'], (latest - dt.timedelta(days=14)).isoformat(), 120, 30, 2, 'spark')}
</li>""")
    body = f"""
  <h1>The GitHub repos gaining stars fastest, checked for fake stars</h1>
  <div class="summary">Ranked by stars gained on <b>{fmt_day(day.isoformat())}</b> (a full day, US Pacific time),
    from {len(data['repos'])} fast-growing repos. <b>{hidden}</b> repos with two or more red flags are left out of
    the ranking; see them under “Has red flags”. Red flags are hints, not proof.
    <a href="how/index.html">How it works</a></div>
  <div class="controls">
    <span class="label">Rank by</span>
    <div class="seg" id="sort">
      <button data-key="yesterday" aria-pressed="true">Stars on {fmt_day(day.isoformat())}</button>
      <button data-key="today" aria-pressed="false">{today_label}</button>
      <button data-key="week" aria-pressed="false">Last 7 days</button>
      <button data-key="growth" aria-pressed="false">Growth %</button>
    </div>
    <span class="label">Show</span>
    <div class="seg" id="filter">
      <button data-f="ranking" aria-pressed="true">Ranking</button>
      <button data-f="clean" aria-pressed="false">No red flags</button>
      <button data-f="flagged" aria-pressed="false">Has red flags</button>
    </div>
  </div>
  <ol id="list">{''.join(items)}</ol>
  <script>{INDEX_JS}</script>"""
    write(os.path.join(SITE, "index.html"), shell(
        "TrueStars: GitHub repos gaining stars fastest, checked for fake stars", body, root,
        "Daily ranking of the GitHub repos gaining stars fastest, with every repo checked for signs of fake stars.",
        updated))


INDEX_JS = """
(function () {
  var list = document.getElementById('list');
  var rows = Array.prototype.slice.call(list.children);
  var state = { key: 'yesterday', f: 'ranking' };
  function keep(row) {
    var flags = Number(row.dataset.flags);
    if (state.f === 'clean') return flags === 0;
    if (state.f === 'flagged') return flags > 0;
    return flags < %d;  // the ranking leaves out repos with two or more red flags
  }
  function draw() {
    rows.sort(function (a, b) { return Number(b.dataset[state.key]) - Number(a.dataset[state.key]); });
    var n = 0;
    rows.forEach(function (row) {
      var show = keep(row);
      row.hidden = !show;
      if (show) row.querySelector('.rank').textContent = ++n;
      list.appendChild(row);
    });
  }
  function group(id, prop) {
    var el = document.getElementById(id);
    el.addEventListener('click', function (e) {
      var b = e.target.closest('button');
      if (!b) return;
      el.querySelectorAll('button').forEach(function (x) { x.setAttribute('aria-pressed', String(x === b)); });
      state[prop] = prop === 'key' ? b.dataset.key : b.dataset.f;
      draw();
    });
  }
  group('sort', 'key');
  group('filter', 'f');
  document.querySelectorAll('details[data-empty]').forEach(function (d) {
    d.addEventListener('click', function (e) { e.preventDefault(); });
  });
  draw();
})();
""" % HIDE_AT_FLAGS


COPY_JS = """
document.querySelectorAll('[data-copy]').forEach(function (b) {
  b.addEventListener('click', function () {
    var text = document.getElementById(b.dataset.copy).textContent;
    function done(msg) { b.textContent = msg; setTimeout(function () { b.textContent = 'Copy'; }, 2000); }
    try { navigator.clipboard.writeText(text).then(function () { done('Copied'); }, function () { done('Select and copy'); }); }
    catch (e) { done('Select and copy'); }
  });
});
"""


def render_repo(slug, entry, fresh, latest, updated):
    """One page per repo that has been in the ranking."""
    root = "../../../"
    row = fresh or entry["last"]
    best, best_day = best_rank(entry["ranks"])
    cls, text = verdict(row)
    reasons = reasons_html(row)
    if fresh:
        values, start = row["chart"], row["chart_start"]
        end_label = fmt_day(latest.isoformat()) + " so far"
        stale = ""
    else:  # last seen on an earlier day: its 14 complete days up to then
        values = row["spark"][:-1]
        start = (dt.date.fromisoformat(entry["last_day"]) - dt.timedelta(days=13)).isoformat()
        end_label = fmt_day(entry["last_day"])
        stale = (f'<p class="stale">Not among today\'s fastest-growing repos. The numbers below are from '
                 f'{fmt_day(entry["last_day"])}, the last day it was checked.</p>')
    chart = bars(values, start, 720, 140, 2 if len(values) > 30 else 6, "chart")
    first = fmt_day(start)
    recent = "".join(f"<li><span>{fmt_day(d)}</span><b>#{r}</b></li>" for d, r in reversed(entry["ranks"][-14:]))
    badge_md = f"[![TrueStars]({SITE_URL}/badge/{slug}.svg)]({SITE_URL}/r/{slug}/)"
    body = f"""
  <p class="crumbs"><a href="{root}index.html">Ranking</a> › {esc(row['name'])}</p>
  <div class="repo-head">
    <h1>{esc(row['name'])}</h1>
    <span class="lang">{esc(row['language'])}</span>
    <a class="gh" href="{esc(row['url'])}" target="_blank" rel="noopener">View on GitHub ↗</a>
  </div>
  <p class="desc">{esc(row['description'])}</p>
  {stale}
  <div class="stats">
    <div><b>#{best}</b><span>best daily rank ({fmt_day(best_day)})</span></div>
    <div><b>+{row['yesterday']:,}</b><span>stars on {fmt_day(entry['last_day'] if not fresh else (latest - dt.timedelta(days=1)).isoformat())}</span></div>
    <div><b>+{fmt_count(row['week'])}</b><span>stars in 7 days</span></div>
    <div><b>{fmt_count(row['stars'])}</b><span>total stars</span></div>
  </div>
  <section class="card">
    <h2>Stars per day</h2>
    {chart}
    <p class="axis"><span>{first}</span><span>peak {max(values):,} a day</span><span>{end_label}</span></p>
  </section>
  <section class="card">
    <h2>Fake-star check</h2>
    <details class="verdict verdict-{cls}" open{'' if reasons else ' data-empty'}>
      <summary>{text}</summary>{f'<ul>{reasons}</ul>' if reasons else ''}
    </details>
    <p class="hint">Checks forks, watchers, issues and how the stars arrived. A flag is a reason to look closer,
      not proof. <a href="{root}how/index.html">How the check works</a></p>
  </section>
  {f'<section class="card"><h2>Why it may be trending</h2><div class="chips">{why_chips(row)}</div></section>' if row['why'] else ''}
  <section class="card">
    <h2>Days in the ranking</h2>
    <ul class="ranks">{recent}</ul>
  </section>
  <section class="card">
    <h2>Badge for your README</h2>
    <p><img src="{root}badge/{slug}.svg" alt="TrueStars badge: #{best} best daily rank" height="20"></p>
    <p class="hint">It shows the best daily rank and updates itself. Paste this into your README:</p>
    <pre id="md">{esc(badge_md)}</pre>
    <button class="copy" data-copy="md">Copy</button>
  </section>
  <script>{COPY_JS}</script>"""
    write(os.path.join(SITE, "r", slug, "index.html"), shell(
        f"{row['name']} on TrueStars", body, root,
        f"{row['name']}: daily stars, best rank #{best} and a fake-star check.", updated))


def text_width(text):
    """Rough width in px of 11px Verdana, enough to size a badge."""
    w = 0.0
    for c in text:
        if c in "fijlrtI.,:;'|! ":
            w += 4.2
        elif c in "mwMW#%":
            w += 9.6
        elif c.isupper() or c.isdigit():
            w += 7.4
        else:
            w += 6.6
    return w


def render_badge(slug, best):
    left, right = "TrueStars", f"#{best} best daily rank"
    lw_text, rw_text = text_width(left), text_width(right)
    lw = round(6 + 12 + 4 + lw_text + 7)
    rw = round(7 + rw_text + 7)
    w = lw + rw
    svg = f"""<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="20" role="img" aria-label="TrueStars: {right}">
<title>TrueStars: {right}</title>
<linearGradient id="s" x2="0" y2="100%"><stop offset="0" stop-color="#bbb" stop-opacity=".1"/><stop offset="1" stop-opacity=".1"/></linearGradient>
<clipPath id="r"><rect width="{w}" height="20" rx="3" fill="#fff"/></clipPath>
<g clip-path="url(#r)"><rect width="{lw}" height="20" fill="#1d1e20"/><rect x="{lw}" width="{rw}" height="20" fill="#2c55c9"/><rect width="{w}" height="20" fill="url(#s)"/></g>
<polygon fill="#f5c242" points="{star_points(12, 10.4, 6, 2.6)}"/>
<g fill="#fff" font-family="Verdana,Geneva,DejaVu Sans,sans-serif" font-size="11">
<text x="22" y="14" textLength="{lw_text:.0f}" lengthAdjust="spacingAndGlyphs">{left}</text>
<text x="{lw + 7}" y="14" textLength="{rw_text:.0f}" lengthAdjust="spacingAndGlyphs">{right}</text>
</g></svg>
"""
    write(os.path.join(SITE, "badge", slug + ".svg"), svg)


def render_how(updated):
    root = "../"
    body = f"""
  <h1>How TrueStars works</h1>
  <section class="prose">
    <h2>What it ranks</h2>
    <p>Every day TrueStars ranks the GitHub repos that gained the most stars the day before, and checks each one
      for signs that its stars are not real. Days run midnight to midnight US Pacific time, the same days
      GitHub uses.</p>
    <h2>Where the numbers come from</h2>
    <p><b>Finding repos.</b> Each run looks at new repos with the most stars this month and this week (GitHub
      search), and at the repos starred most often in the last 24 hours of GH Archive, a public log of GitHub
      activity. GH Archive now records only a sample of stars, so it is used only to find repos, never to count.</p>
    <p><b>Counting stars.</b> Daily star counts come from GitHub's star-history API, so they are exact.</p>
    <h2>The fake-star check</h2>
    <p>GitHub no longer shows who starred a repo, so the check uses what is still public. Real projects usually
      draw forks, watchers and issues along with their stars; bought stars usually come alone. A repo gets a red
      flag when:</p>
    <ul>
      <li>it has fewer than {FORKS_PER_100:g} fork per 100 stars,</li>
      <li>fewer than {TALK_PER_1K:g} issues or pull requests per 1,000 stars (when issues are turned on),</li>
      <li>fewer than {WATCHERS_PER_1K:g} watchers per 1,000 stars, or</li>
      <li>its stars stopped dead: a day with {STOP_MIN_PEAK}+ stars, then, within two days, under
        {STOP_SHARE * 100:g}% of that a day. Real interest fades over several days.</li>
    </ul>
    <p>The first three are checked from {RATIO_MIN_STARS} stars up. An owner account younger than
      {NEW_OWNER_DAYS} days, or fewer than {MIN_COMMITS} commits, is normal for an honest launch, so those count
      only when one of the checks above also fails.</p>
    <p>Repos with {HIDE_AT_FLAGS} or more red flags are left out of the ranking but stay visible under “Has red
      flags”. <b>A flag is a reason to look closer, not proof of cheating.</b> We never call a repo fake.</p>
    <h2>Why a repo may be trending</h2>
    <p>Each repo shows the reasons we can see: a Hacker News post with {HN_MIN_POINTS}+ points in the last
      {HN_DAYS} days, a release in the last week, or a repo created in the last two weeks.</p>
    <h2>The badge</h2>
    <p>Every repo that makes the ranking gets a page and a badge showing its best daily rank. The badge updates
      itself every day. Copy it from the repo's page.</p>
    <h2>Not affiliated with GitHub</h2>
    <p>TrueStars is independent and uses GitHub's public API.</p>
  </section>"""
    write(os.path.join(SITE, "how", "index.html"), shell(
        "How TrueStars works", body, root,
        "How TrueStars counts stars, checks for fake stars and ranks GitHub repos.", updated))


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as fh:
        fh.write(text)


def build():
    with open(LATEST) as fh:
        data = json.load(fh)
    latest = dt.date.fromisoformat(data["latest_day"])
    day = latest - dt.timedelta(days=1)  # the ranking day: the last complete Pacific day

    rows = []
    for repo in data["repos"]:
        if not repo["meta"] or not repo["daily"] or repo["meta"]["isFork"]:
            continue
        row = assess(repo, latest)
        if row["week"] < 50 and row["today"] < 20:
            continue
        rows.append(row)
    rows.sort(key=lambda r: (-r["yesterday"], r["name"].lower()))
    rank = 0
    for r in rows:
        if len(r["flags"]) < HIDE_AT_FLAGS:
            rank += 1
            r["rank"] = rank
        else:
            r["rank"] = None
    save_day(day, rows, data)
    history = load_history()

    if os.path.isdir(SITE):
        shutil.rmtree(SITE)  # rebuilt from scratch every run
    generated = dt.datetime.fromisoformat(data["generated_at"]).astimezone(PACIFIC)
    updated = f"{generated:%b} {generated.day}, {generated:%-I:%M %p} Pacific"
    write(os.path.join(SITE, "style.css"), STYLE)
    write(os.path.join(SITE, "favicon.svg"),
          f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20"><polygon fill="#2c55c9" '
          f'points="{star_points(10, 10.6, 9.5, 4)}"/></svg>')
    render_index(rows, day, latest, data, updated)
    render_how(updated)
    fresh = {r["slug"]: r for r in rows}
    for slug, entry in history.items():
        render_repo(slug, entry, fresh.get(slug), latest, updated)
        render_badge(slug, best_rank(entry["ranks"])[0])
    write(os.path.join(SITE, "404.html"), shell(
        "Not found · TrueStars", '<h1>Page not found</h1><p>This repo has not been in the ranking yet. '
        '<a href="/index.html">See today\'s ranking</a>.</p>', "/", "Page not found.", updated))
    print(f"Site built: {len(rows)} repos listed, {rank} in the ranking, {len(history)} repo pages "
          f"and badges, day {day.isoformat()} saved")


STYLE = """
:root {
  --bg: #f7f6f2; --panel: #ffffff; --ink: #1d1e20; --muted: #676b72; --line: #e4e1da;
  --accent: #2c55c9; --chip: #efede7; --gold: #f5c242;
  --good: #1d6b44; --good-bg: #e3f2e9; --warn: #8a5800; --warn-bg: #fbefd5;
  --bad: #a3261b; --bad-bg: #fbe4e1; --bar: #2c55c9; --bar-today: #a8b9ea; --bar-zero: #dcd8cf;
}
@media (prefers-color-scheme: dark) {
  :root {
    --bg: #121315; --panel: #1b1c1f; --ink: #ebebea; --muted: #9b9fa6; --line: #2b2d31;
    --accent: #87a6ff; --chip: #26282c;
    --good: #79d3a0; --good-bg: #15301f; --warn: #f0c46c; --warn-bg: #33270e;
    --bad: #ff9187; --bad-bg: #3b1714; --bar: #87a6ff; --bar-today: #3d4c78; --bar-zero: #303236;
  }
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--bg); color: var(--ink);
  font: 15px/1.5 -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; }
a { color: var(--accent); }
.wrap { max-width: 1040px; margin: 0 auto; padding: 0 16px; }
.top { border-bottom: 1px solid var(--line); background: var(--panel); }
.top .wrap { display: flex; align-items: center; justify-content: space-between; height: 56px; }
.logo { display: inline-flex; align-items: center; gap: 8px; font-weight: 750; font-size: 18px;
  color: var(--ink); text-decoration: none; letter-spacing: -0.01em; }
.star { width: 20px; height: 20px; fill: var(--gold); }
.top nav a { margin-left: 18px; color: var(--muted); text-decoration: none; font-size: 14px; }
.top nav a:hover { color: var(--ink); }
main.wrap { padding-top: 28px; padding-bottom: 48px; }
h1 { font-size: 26px; margin: 0 0 14px; letter-spacing: -0.02em; line-height: 1.25; }
h2 { font-size: 16px; margin: 0 0 10px; }
.summary { background: var(--panel); border: 1px solid var(--line); border-radius: 12px;
  padding: 14px 16px; margin-bottom: 20px; }
.controls { display: flex; flex-wrap: wrap; gap: 8px 16px; align-items: center; margin-bottom: 12px; }
.seg { display: inline-flex; border: 1px solid var(--line); border-radius: 999px; overflow: hidden;
  background: var(--panel); }
.seg button { border: 0; background: none; color: var(--ink); padding: 6px 12px; font: inherit;
  font-size: 13px; cursor: pointer; }
.seg button[aria-pressed="true"] { background: var(--ink); color: var(--bg); }
.label { font-size: 13px; color: var(--muted); }
ol { list-style: none; margin: 0; padding: 0; }
.row { display: grid; grid-template-columns: 34px 1fr auto 120px; gap: 16px; align-items: start;
  background: var(--panel); border: 1px solid var(--line); border-radius: 12px;
  padding: 14px 16px; margin-bottom: 8px; }
.row[hidden] { display: none; }
.rank { font-weight: 700; color: var(--muted); font-variant-numeric: tabular-nums; padding-top: 2px; }
.title { display: flex; gap: 8px; align-items: baseline; flex-wrap: wrap; }
.name { font-weight: 650; text-decoration: none; word-break: break-word; }
.name:hover { text-decoration: underline; }
.lang, .gh { font-size: 12px; color: var(--muted); }
.gh { text-decoration: none; }
.gh:hover { color: var(--accent); }
.desc { margin: 2px 0 8px; color: var(--muted); font-size: 14px; }
.chips { display: flex; flex-wrap: wrap; gap: 6px; margin-bottom: 8px; }
.chip { font-size: 12px; padding: 2px 8px; border-radius: 999px; background: var(--chip);
  color: var(--ink); text-decoration: none; white-space: nowrap; }
a.chip:hover { text-decoration: underline; }
.verdict summary { display: inline-block; font-size: 12px; font-weight: 600; padding: 2px 8px;
  border-radius: 6px; cursor: pointer; list-style: none; }
.verdict summary::-webkit-details-marker { display: none; }
.verdict[data-empty] summary { cursor: default; }
.verdict ul { margin: 6px 0 0; padding-left: 18px; font-size: 13px; color: var(--muted); }
.verdict-good summary { background: var(--good-bg); color: var(--good); }
.verdict-warn summary { background: var(--warn-bg); color: var(--warn); }
.verdict-bad summary { background: var(--bad-bg); color: var(--bad); }
.nums { display: grid; grid-template-columns: repeat(2, minmax(84px, auto)); gap: 4px 14px;
  font-variant-numeric: tabular-nums; }
.nums div, .stats div { display: flex; flex-direction: column; }
.nums b { font-size: 15px; }
.nums span, .stats span { font-size: 11px; color: var(--muted); }
.spark { width: 120px; height: 30px; margin-top: 6px; }
.bar { fill: var(--bar); } .bar-today { fill: var(--bar-today); } .bar-zero { fill: var(--bar-zero); }
.crumbs { font-size: 13px; color: var(--muted); margin: 0 0 8px; }
.crumbs a { text-decoration: none; }
.repo-head { display: flex; gap: 10px; align-items: baseline; flex-wrap: wrap; }
.repo-head h1 { margin: 0; word-break: break-word; }
.stale { background: var(--warn-bg); color: var(--warn); border-radius: 8px; padding: 8px 12px; font-size: 14px; }
.stats { display: grid; grid-template-columns: repeat(4, 1fr); gap: 12px; margin: 16px 0;
  font-variant-numeric: tabular-nums; }
.stats div { background: var(--panel); border: 1px solid var(--line); border-radius: 12px; padding: 12px 14px; }
.stats b { font-size: 22px; }
.card { background: var(--panel); border: 1px solid var(--line); border-radius: 12px;
  padding: 16px; margin-bottom: 12px; }
.chart { width: 100%; height: 140px; display: block; }
.axis { display: flex; justify-content: space-between; font-size: 12px; color: var(--muted); margin: 6px 0 0; }
.hint { font-size: 13px; color: var(--muted); margin: 8px 0; }
.ranks { list-style: none; padding: 0; margin: 0; display: flex; flex-wrap: wrap; gap: 8px; }
.ranks li { background: var(--chip); border-radius: 8px; padding: 4px 10px; font-size: 13px;
  display: flex; gap: 8px; font-variant-numeric: tabular-nums; }
.ranks span { color: var(--muted); }
pre { background: var(--chip); border-radius: 8px; padding: 10px 12px; font-size: 12px; overflow-x: auto;
  white-space: pre-wrap; word-break: break-all; margin: 0 0 8px; }
.copy { border: 1px solid var(--line); background: var(--panel); color: var(--ink); border-radius: 8px;
  padding: 6px 14px; font: inherit; font-size: 13px; cursor: pointer; }
.prose { max-width: 720px; }
.prose h2 { margin-top: 24px; }
.prose li { margin-bottom: 4px; }
.foot { color: var(--muted); font-size: 12px; padding-bottom: 32px; }
@media (max-width: 760px) {
  .row { grid-template-columns: 28px 1fr; }
  .nums, .spark { grid-column: 2; }
  .stats { grid-template-columns: repeat(2, 1fr); }
  h1 { font-size: 22px; }
}
"""


if __name__ == "__main__":
    step = sys.argv[1] if len(sys.argv) > 1 else "all"
    if step not in ("all", "collect", "build"):
        sys.exit(__doc__)
    if step in ("all", "collect"):
        collect()
    if step in ("all", "build"):
        build()
