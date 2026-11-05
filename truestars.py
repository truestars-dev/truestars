#!/usr/bin/env python3
"""TrueStars: the GitHub repos gaining stars fastest, where each one stands, why, and a fake-star check.

  python3 -I truestars.py           collect today's data, look up YouTube and X, then build the site
  python3 -I truestars.py collect   only collect                  -> data/latest.json
  python3 -I truestars.py social    only YouTube and X, for the top repos -> data/social.json
  python3 -I truestars.py build     only build from the saved data -> data/days/<day>.json, site/

Needs GITHUB_TOKEN in the environment or a logged-in GitHub CLI (`gh`). Standard library only.
GOOGLE_API_KEY (YouTube) and X_BEARER_TOKEN (X) are optional: without them that source is skipped.
"""
import collections
import colorsys
import concurrent.futures as futures
import datetime as dt
import gzip
import hashlib
import html
import json
import math
import os
import re
import shutil
import subprocess
import sys
import time
import traceback
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
RATIO_MIN_STARS = 300      # judge the issues ratio once a repo has this many stars
SMALL_MIN_STARS = 50       # forks, watchers and commits from this many: the search for repos 1-3 days old
                           # reaches 50 stars, and on 2026-11-04 it found ~45 new "full working installer"
                           # repos at 200-300 stars with no forks, no watchers and one commit
FORKS_PER_100 = 1.0        # fewer forks than this per 100 stars
TALK_PER_1K = 0.5          # fewer issues + pull requests than this per 1,000 stars
WATCHERS_PER_1K = 0.5      # fewer watchers than this per 1,000 stars
MIN_COMMITS = 3            # fewer commits than this
STOP_MIN_PEAK = 100        # "stars stopped dead": a day with at least this many stars, after which
STOP_SHARE = 0.01          # every complete day from two days on stayed under this share of it
HIDE_AT_FLAGS = 2          # repos with this many flags are left out of the ranking (owner, 2026-11-03)
HN_MIN_POINTS = 20         # a Hacker News post counts as a reason from this many points
HN_DAYS = 14               # ... if it was posted within this many days

# Direction: where a repo stands against its own best day (complete days only)
RUN_SHARE = 0.10           # a run: the days in a row with at least this share of the repo's best day
RISING_X = 1.5             # "Rising": this many times its mean over the 3 days before, and 20+ stars more
COOLING_SHARE = 0.8        # "Cooling": under this share of its best day in the 7 days before
# "Rising now" (research rule R2: it fired for 23 of the 11-03 top 30, a median 2 days before their peak)
RISE_X = 3.0               # this many times its mean over the 7 days before (that mean counted as at
RISE_FLOOR = 5             # least RISE_FLOOR), with at least RISE_MIN stars: on the last complete day,
RISE_MIN = 50              # or at today's pace once RISE_FRAC of today has passed
RISE_FRAC = 0.2
RISE_LIST = 10             # repos in the "Rising now" list
# More reasons a repo may be trending
LAUNCHED_DAYS = 30         # "Launched N days ago" after the 14-day "Brand new" chip, up to this age
FOLLOWERS_MIN = 1000       # an owner with this many followers gets a reach chip
JUMP_X = 2.0               # a release or HN post counts when a day after it had this many times the
                           # mean of the 7 days before it
WAVE_MIN = 3               # a wave chip needs this many repos in the ranking that share it
WAVES = [                  # (name, GitHub topics); the first wave that matches wins
    ("DeepSeek Harness", {"deepseek-harness", "dsh", "dsh-plugin", "dsh-plugins"}),
    ("agent skills", {"agent-skills", "agent-skill", "claude-skills", "claude-code-skills", "codex-skills"}),
    ("Claude Code", {"claude-code", "claude-code-plugin", "claude-code-plugins"}),
    ("Codex", {"codex", "codex-cli", "openai-codex"}),
    ("MCP", {"mcp", "mcp-server", "mcp-servers", "model-context-protocol"}),
    ("OpenClaw", {"openclaw"}),
]
BIG_ORGS = {               # well-known companies and AI labs (GitHub logins, lower case): "From <org>"
    "google", "google-research", "google-deepmind", "microsoft", "github", "nvidia", "nvidia-omniverse",
    "openai", "anthropics", "deepseek-ai", "meta-llama", "facebookresearch", "apple", "aws", "awslabs",
    "alibaba", "qwenlm", "tencent", "tencent-hunyuan", "bytedance", "minimax-ai", "moonshotai", "mistralai",
    "huggingface", "cloudflare", "vercel", "vercel-labs", "stripe", "spotify", "netflix", "shopify", "ibm",
    "intel",
}
WHY_ORDER = ["hn", "youtube", "x", "release", "wave", "new", "org", "reach"]
# YouTube and X: looked up once a day for the top repos (social()). The data lives only in the published
# site/social.json, which the next run reads back: never in data/days, because YouTube's rules let us keep
# its data for 30 days at most (we keep it SOCIAL_KEEP_DAYS) and git keeps history forever.
SOCIAL = os.path.join(DATA, "social.json")
SOCIAL_URL = "https://truestars.dev/social.json"
SOCIAL_KINDS = ("youtube", "x")  # reason chips left out of data/days
SOCIAL_FRESH_HOURS = 20    # data younger than this is reused, so each repo is looked up once a day
SOCIAL_KEEP_DAYS = 3       # data older than this is deleted
YT_TOP = 60                # YouTube: the top repos searched each day (YouTube allows 100 searches a day)
YT_SEARCH_DAYS = 90        # videos posted in this many days whose description links the repo
YT_DAYS = 30               # a YouTube reason: a linking video posted in the last this many days ...
YT_MIN_VIEWS = 1000        # ... with this many views
X_TOP = 50                 # X: the top repos counted each day (one prepaid count each, $0.005)
X_MIN_POSTS = 20           # an X reason: this many posts linked the repo in the last 7 days (reposts not counted)
REDDIT_APP = ""            # the Reddit test: "<Google Cloud project id>/<site search app id>", once the owner makes it
# The Explore page (a preview: not linked from the other pages, hidden from search engines) orders
# repos by TrueStars Heat, see heat()
HEAT_FULL = 3000           # stars a day that earn all 60 "stars now" points
HEAT_CLIMB = {"peak": 15, "rising": 12, "steady": 6, "cooling": 0}
SHELF_MAX = 15             # repos shown on one Explore shelf ("See all" shows the rest)
SMALL_REPO = 2000          # "Small and rising": under this many stars
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

def search_repos(query, limit=100):
    """Repos matching a GitHub search, most stars first."""
    status, data = github("/search/repositories", {
        "q": query, "sort": "stars", "order": "desc", "per_page": min(limit, 100)})
    if status != 200 or not data:
        return []
    return [item["full_name"] for item in data.get("items", [])][:limit]


def from_new_repos(days, min_stars):
    """Repos created in the last `days` days with the most stars."""
    since = (dt.datetime.now(dt.timezone.utc) - dt.timedelta(days=days)).strftime("%Y-%m-%d")
    return search_repos(f"created:>={since} stars:>={min_stars}")


def from_last_days(days=3, min_stars=50, per_day=50):
    """The most-starred repos created on each of the last few days (UTC dates).

    The searches above stop at 100 results, which cut new repos off at about 300 stars: 73 of
    the 100 biggest repos created on Nov 1-3, 2026 were missed. These find new risers early.
    """
    today = dt.datetime.now(dt.timezone.utc).date()
    names = []
    for k in range(days):
        names += search_repos(f"created:{today - dt.timedelta(days=k)} stars:>={min_stars}", per_day)
    return names


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
  openGraphImageUrl usesCustomOpenGraphImage
  primaryLanguage { name color }
  repositoryTopics(first: 10) { nodes { topic { name } } }
  watchers { totalCount }
  issues { totalCount }
  pullRequests { totalCount }
  defaultBranchRef { target { ... on Commit { history { totalCount } } } }
  releases(first: 1, orderBy: {field: CREATED_AT, direction: DESC}) {
    nodes { tagName url publishedAt releaseAssets(first: 20) { nodes { name } } }
  }
  owner { login __typename avatarUrl(size: 160)
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


def links_repo(text, full_name):
    """True when the text links github.com/<full_name> itself, not a repo with a longer name."""
    for owner, name in re.findall(r"github\.com/([\w.-]+)/([\w.-]+)", text or "", re.I):
        name = name.rstrip(".")  # a sentence's full stop
        if name.lower().endswith(".git"):
            name = name[:-4]
        if f"{owner}/{name}".lower() == full_name.lower():
            return True
    return False


def api_reason(raw):
    """A short reason code from an API's error answer, safe for the public log (never the request)."""
    try:
        body = json.loads(raw)
    except (ValueError, TypeError):
        return ""
    if not isinstance(body, dict):
        return ""
    err = body.get("error") if isinstance(body.get("error"), dict) else {}
    codes = [e.get("reason") for e in (err.get("details") or []) + (err.get("errors") or [])
             if isinstance(e, dict) and e.get("reason")]
    return " ".join(dict.fromkeys(str(c) for c in codes))[:60] or str(err.get("status") or body.get("title") or "")[:60]


def youtube(full_name, since, key):
    """(200, videos posted since `since` whose description links the repo, most viewed first), or
    (status, reason). One search (YouTube allows 100 a day) and one cheap call for the videos' details."""
    owner, name = full_name.split("/", 1)
    query = urllib.parse.urlencode({"part": "snippet", "type": "video", "q": f"{name} {owner}", "maxResults": 25,
                                    "publishedAfter": f"{since.isoformat()}T00:00:00Z", "key": key})
    status, raw = fetch("https://www.googleapis.com/youtube/v3/search?" + query, tries=2)
    if status != 200:
        return status, api_reason(raw)
    try:
        ids = [i["id"]["videoId"] for i in json.loads(raw).get("items") or [] if (i.get("id") or {}).get("videoId")]
    except (ValueError, TypeError, AttributeError):
        return 0, "unreadable answer"
    if not ids:
        return 200, []
    query = urllib.parse.urlencode({"part": "snippet,statistics", "id": ",".join(ids), "key": key})
    status, raw = fetch("https://www.googleapis.com/youtube/v3/videos?" + query, tries=2)
    if status != 200:
        return status, api_reason(raw)
    videos = []
    try:
        for v in json.loads(raw).get("items") or []:
            snip, stats = v.get("snippet") or {}, v.get("statistics") or {}
            if links_repo(snip.get("description"), full_name) and snip.get("publishedAt"):
                videos.append({"id": v["id"], "title": (snip.get("title") or "")[:150],
                               "channel": (snip.get("channelTitle") or "")[:80],
                               "published": snip["publishedAt"], "views": int(stats.get("viewCount") or 0)})
    except (ValueError, TypeError, AttributeError, KeyError):
        return 0, "unreadable answer"
    return 200, sorted(videos, key=lambda v: -v["views"])[:5]


def x_posts(full_name, token):
    """(200, {"week": posts, "days": [[UTC day, posts], ...]}): posts on X that linked the repo in the last
    7 days, reposts not counted; or (status, reason). One prepaid count."""
    query = urllib.parse.urlencode({"query": f'url:"github.com/{full_name}" -is:retweet', "granularity": "day"})
    status, raw = fetch("https://api.x.com/2/tweets/counts/recent?" + query,
                        {"Authorization": "Bearer " + token}, tries=2)
    if status != 200:
        return status, api_reason(raw)
    try:
        body = json.loads(raw)
        days = [[d["start"][:10], int(d.get("tweet_count") or 0)] for d in body.get("data") or []]
        week = int((body.get("meta") or {}).get("total_tweet_count") or sum(n for _, n in days))
    except (ValueError, TypeError, AttributeError, KeyError):
        return 0, "unreadable answer"
    return 200, {"week": week, "days": days}


def reddit_threads(full_name, key):
    """The Reddit test: (200, threads that link the repo) from Google's index of reddit.com, through the
    owner's site search app (REDDIT_APP; $4 per 1,000 searches), or (status, reason)."""
    project, app = REDDIT_APP.split("/", 1)
    config = (f"projects/{project}/locations/global/collections/default_collection/engines/{app}"
              "/servingConfigs/default_search")
    body = json.dumps({"servingConfig": config, "query": f'"github.com/{full_name}"', "pageSize": 10,
                       "userPseudoId": "truestars"}).encode()
    status, raw = fetch(f"https://discoveryengine.googleapis.com/v1/{config}:searchLite?"
                        + urllib.parse.urlencode({"key": key}), {"Content-Type": "application/json"}, body, tries=2)
    if status != 200:
        return status, api_reason(raw)
    threads = []
    try:
        for result in json.loads(raw).get("results") or []:
            found = (result.get("document") or {}).get("derivedStructData") or {}
            sub = re.match(r"https://(?:www\.|old\.)?reddit\.com/r/(\w+)/comments/", found.get("link") or "")
            if sub:
                threads.append({"url": found["link"], "sub": sub.group(1), "title": (found.get("title") or "")[:150]})
    except (ValueError, TypeError, AttributeError):
        return 0, "unreadable answer"
    return 200, threads


# ----------------------------------------------------------------- collect

def collect():
    started = time.time()
    print("1/4  Finding candidates: new repos with the most stars, and GH Archive's last 24 hours ...", flush=True)
    archive, hours_read = from_gharchive()
    sources = collections.OrderedDict()
    for label, names in (("new-30d", from_new_repos(30, 300)), ("new-7d", from_new_repos(7, 100)),
                         ("new-3d", from_last_days()), ("gharchive", archive)):
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


def mean_before(daily, day, n=7):
    """Mean stars a day over the n days before `day`, counted as at least RISE_FLOOR."""
    return max(RISE_FLOOR, sum(daily.get((day - dt.timedelta(days=k)).isoformat(), 0) for k in range(1, n + 1)) / n)


def jump(daily, day, yday, created, span):
    """The best of `span` complete days from `day` against the mean of the 7 days before it.

    None when that is under JUMP_X, or the repo had no full week before `day` (its launch
    explains the stars then, and the "Brand new" chip says so).
    """
    if (day - created).days < 7 or day > yday:
        return None
    before = mean_before(daily, day)
    after = max(daily.get((day + dt.timedelta(days=k)).isoformat(), 0) for k in range(min(span, (yday - day).days + 1)))
    return after / before if after >= JUMP_X * before else None


def direction(counts, start, full):
    """Where a repo stands against its own best day, from complete days only.

    counts: stars per day from `start` (its creation, or the first day fetched) to the ranking day.
    full: True when `start` is the creation day, so the best day is the best day ever.
    """
    if not counts or not max(counts):
        return None
    y, prev = counts[-1], counts[:-1]
    best = max(counts)
    best_i = counts.index(best)
    run = 0  # the days in a row, up to the ranking day, with at least RUN_SHARE of the best day
    for c in reversed(counts):
        if c < max(1, RUN_SHARE * best):
            break
        run += 1
    if run == len(counts) and not full:
        run = None  # it began before the first day fetched
    hot, waves = False, 0  # waves: runs of days at half the best day or more, each ending below a quarter
    for c in counts:
        if not hot and c >= best / 2:
            hot, waves = True, waves + 1
        elif hot and c < best / 4:
            hot = False
    wave = waves if best >= 100 and hot and waves >= 2 else 0  # 2 = its second wave, and so on
    avg3 = sum(prev[-3:]) / len(prev[-3:]) if prev else 0
    if not prev or y >= max(prev):
        state = "peak"
    elif y >= RISING_X * avg3 and y - avg3 >= 20:
        state = "rising"
    elif y < COOLING_SHARE * max(prev[-7:]):
        state = "cooling"
    else:
        state = "steady"
    half = next((k for k in range(1, len(counts) - best_i) if counts[best_i + k] < best / 2), None)
    return {"state": state, "best": best, "best_day": (start + dt.timedelta(days=best_i)).isoformat(),
            "share": round(100 * y / best), "run": run, "full": full, "half": half, "wave": wave}


def rising_now(daily, latest, frac, created):
    """Acceleration against the repo's own 7 days before, or None when it is not rising now.

    Checks the last complete day, and today's pace once RISE_FRAC of today has passed
    (today wins: it is fresher). "x" is how many times its usual daily stars.
    """
    yday = latest - dt.timedelta(days=1)
    found = None
    y = daily.get(yday.isoformat(), 0)
    if y >= RISE_MIN and y >= RISE_X * mean_before(daily, yday):
        found = {"when": "day", "stars": y, "rate": y, "base": mean_before(daily, yday)}
    t = daily.get(latest.isoformat(), 0)
    if frac >= RISE_FRAC and t / frac >= RISE_MIN and t / frac >= RISE_X * mean_before(daily, latest):
        found = {"when": "today", "stars": t, "rate": round(t / frac), "base": mean_before(daily, latest)}
    if found:
        found["x"] = round(found["rate"] / found["base"], 1)
        found["base"] = round(found["base"], 1)
        found["new"] = (latest - created).days <= 7  # no full week before it: the times figure means little
    return found


def assess(repo, latest, frac):
    """Turn raw data into the numbers and plain-language notes on the pages.

    frac: the share of today (Pacific) that had passed when the data was collected.
    """
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
    if stars >= SMALL_MIN_STARS:
        if forks * 100 < FORKS_PER_100 * stars:
            flags.append(f"Very few forks for its stars ({forks:,} fork{'s' if forks != 1 else ''})")
        if stars >= RATIO_MIN_STARS and meta["hasIssuesEnabled"] and talk * 1000 < TALK_PER_1K * stars:
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
    if owner.get("__typename") == "User" and not (owner.get("followers") or {}).get("totalCount"):
        context.append("Owner has no followers")

    notes = []
    if flags:
        flags += context  # a new owner or a code drop only counts alongside another sign
    else:
        notes += [c + " (common for new launches)" for c in context]
    if release and any(RISKY_ASSET.search(a["name"]) for a in release["releaseAssets"]["nodes"]):
        notes.append("Offers program downloads; check before installing")

    created = pacific_day(meta["createdAt"])
    first = min(dt.date.fromisoformat(k) for k in daily)
    start = max(first, created)  # the first day that counts: its creation, or the first day fetched
    counts = [daily.get((start + dt.timedelta(days=k)).isoformat(), 0) for k in range((yday - start).days + 1)]
    topics = [n["topic"]["name"] for n in ((meta.get("repositoryTopics") or {}).get("nodes") or [])
              if n and n.get("topic")]

    why = []  # kinds in WHY_ORDER; build() adds the wave chips, which need the whole list
    recent_hn = [s for s in (repo["hn"] or []) if s["date"] and s["points"] >= HN_MIN_POINTS
                 and days_between(s["date"], latest) <= HN_DAYS]
    if recent_hn:
        top = max(recent_hn, key=lambda s: s["points"])
        lift = jump(daily, pacific_day(top["date"]), yday, created, 3)
        why.append({"kind": "hn", "url": f"https://news.ycombinator.com/item?id={top['id']}",
                    "text": f"Hacker News · {top['points']:,} points · {fmt_day(top['date'])}"
                            + (f" · stars {fmt_x(lift)}" if lift else "")})
    if release and release.get("publishedAt") and days_between(release["publishedAt"], latest) <= 7:
        lift = jump(daily, pacific_day(release["publishedAt"]), yday, created, 2)
        if lift:  # active repos release all the time; a release explains stars only when they jumped
            why.append({"kind": "release", "url": release["url"],
                        "text": f"New release {release['tagName']} · {fmt_day(release['publishedAt'])}"
                                f" · stars {fmt_x(lift)}"})
    if repo_age <= 14:
        why.append({"kind": "new", "text": f"Brand new · created {fmt_day(meta['createdAt'])}", "url": None})
    elif repo_age <= LAUNCHED_DAYS:
        why.append({"kind": "new", "text": f"Launched {repo_age} days ago", "url": None})
    if owner.get("__typename") == "Organization" and (owner.get("login") or "").lower() in BIG_ORGS:
        why.append({"kind": "org", "text": f"From {owner['login']}", "url": None})
    followers = (owner.get("followers") or {}).get("totalCount") or 0
    if followers >= FOLLOWERS_MIN:
        shown = f"{followers:,}" if followers < 10_000 else f"{followers // 1000:,}k"
        why.append({"kind": "reach", "text": f"Owner has {shown} followers", "url": None})

    chart_start = max(start, latest - dt.timedelta(days=89))
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
        "age": repo_age, "topics": topics,
        "waves": [name for name, tags in WAVES if tags.intersection(topics)],
        "direction": direction(counts, start, created >= first),
        "rising": rising_now(daily, latest, frac, created),
        # for the Explore page only (save_day leaves them out): owner picture, the repo's own social
        # image when it set one (GitHub's generated card otherwise, which we do not show), language color
        "avatar": https_only(owner.get("avatarUrl")),
        "image": https_only(meta.get("openGraphImageUrl")) if meta.get("usesCustomOpenGraphImage") else None,
        "color": (meta.get("primaryLanguage") or {}).get("color") or "",
    }


def https_only(url):
    return url if isinstance(url, str) and url.startswith("https://") else None


def heat(row, frac):
    """TrueStars Heat, 0-100: how hot a repo is right now. Three parts, each rounded:

    stars now (60): stars on the last full day, or today's pace once RISE_FRAC of today has passed;
      10 a day scores 0, HEAT_FULL a day or more 60, on a log scale (each tenfold step adds the same)
    speeding up (25): that pace against its mean over the 7 days before; x1 or less 0, x10 or more 25
    still climbing (15): from its direction, HEAT_CLIMB
    Returns (heat, [the three parts], pace, times its usual pace).
    """
    s = row["spark"]  # 15 days: 14 complete days, then today so far
    pace, base = s[-2], sum(s[-9:-2]) / 7
    if frac >= RISE_FRAC and s[-1] / frac > pace:
        pace, base = s[-1] / frac, sum(s[-8:-1]) / 7
    stars_now = 60 * min(1.0, max(0.0, (math.log10(max(pace, 1)) - 1) / (math.log10(HEAT_FULL) - 1)))
    x = pace / max(base, RISE_FLOOR)
    speeding = 25 * min(1.0, math.log10(x)) if x > 1 else 0
    d = row["direction"]
    climbing = HEAT_CLIMB[d["state"]] if d else (HEAT_CLIMB["peak"] if pace else 0)
    parts = [round(stars_now), round(speeding), climbing]
    return sum(parts), parts, round(pace), round(x, 1)


# ----------------------------------------------------------------- history

PAGE_ONLY = ("chart", "chart_start", "avatar", "image", "color", "heat_parts", "pace", "speedup", "social")


def save_day(day, rows, data):
    """The day's ranking as published. These files are the site's history: no YouTube or X data."""
    os.makedirs(DAYS, exist_ok=True)
    snapshot = {"day": day.isoformat(), "generated_at": data["generated_at"],
                "repos_checked": len(data["repos"]),
                "rows": [{k: ([w for w in v if w["kind"] not in SOCIAL_KINDS] if k == "why" else v)
                          for k, v in r.items() if k not in PAGE_ONLY} for r in rows]}
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


def fmt_x(x):
    """3.0 -> ×3, 2.45 -> ×2.5, 14.2 -> ×14"""
    return "×" + (f"{x:.1f}".rstrip("0").rstrip(".") if x < 10 else f"{x:.0f}")


def esc(text):
    return html.escape(str(text), quote=True)


DIR_LABEL = {"peak": "At its peak", "rising": "Rising", "steady": "Steady", "cooling": "Cooling"}
WAVE_WORD = {2: "second wave", 3: "third wave"}


def dir_parts(d):
    """The direction label and its short detail, e.g. ("Cooling", "46% of its Oct 30 peak")."""
    label = "At a 3-month high" if d["state"] == "peak" and not d["full"] else DIR_LABEL[d["state"]]
    if d["state"] == "cooling":
        return label, f"{d['share']}% of its {fmt_day(d['best_day'])} {'peak' if d['full'] else 'high'}"
    detail = [WAVE_WORD.get(d["wave"], "another wave")] if d["wave"] else []
    if d["run"] and d["run"] <= 60:
        detail.append(f"day {d['run']} of its run")
    return label, " · ".join(detail)


def dir_html(row):
    d = row.get("direction")
    if not d:
        return ""
    label, detail = dir_parts(d)
    return f'<span class="dir dir-{d["state"]}">{esc(label)}{" · " + esc(detail) if detail else ""}</span>'


def where_it_stands(row, latest):
    """The repo page's card on direction: its best day, how far it is from it, its run."""
    d = row.get("direction")
    if not d:
        return ""
    yday = fmt_day((latest - dt.timedelta(days=1)).isoformat())
    facts = [f"Best day{'' if d['full'] else ' in the last 13 weeks'}: +{d['best']:,} stars on "
             f"{fmt_day(d['best_day'])}."]
    if d["state"] != "peak":
        facts.append(f"{yday}: {d['share']}% of that.")
    if d["half"] is not None:
        facts.append(f"It fell below half of its best day {d['half']} day{'s' if d['half'] != 1 else ''} later.")
    if d["run"]:
        facts.append(f"Day {d['run']} of its run (the days in a row with at least a tenth of its best day).")
    if d["wave"]:
        facts.append("Back above half its best day after dropping below a quarter of it: "
                     f"its {WAVE_WORD.get(d['wave'], 'latest wave')}.")
    x = row.get("rising")
    if x:
        when = "so far today" if x["when"] == "today" else f"on {yday}"
        facts.append(("Brand new and rising fast" if x["new"] else
                      f"Rising now: {fmt_x(x['x'])} its usual daily stars") + f" (+{x['stars']:,} {when}).")
    items = "".join(f"<li>{esc(f)}</li>" for f in facts)
    return (f'<section class="card"><h2>Where it stands</h2><p>{dir_html(row)}</p>'
            f'<ul class="facts">{items}</ul></section>')


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


def talk_html(row):
    """Repo page: YouTube videos and posts on X that link the repo (the top repos, looked up daily)."""
    found, parts = row.get("social") or {}, []
    posts = (found.get("x") or {}).get("week") or 0
    if posts:
        parts.append(f'<p>X: <b>{posts:,} post{"s" if posts != 1 else ""}</b> linked it in the last 7 days, '
                     f'reposts not counted. <a href="{esc(x_search(row["name"]))}" target="_blank" '
                     f'rel="noopener">See them on X ↗</a></p>')
    videos = (found.get("youtube") or {}).get("videos") or []
    if videos:
        items = "".join(
            f'<li><a href="https://www.youtube.com/watch?v={esc(v["id"])}" target="_blank" rel="noopener">'
            f'{esc(v["title"])}</a><span>{esc(v["channel"])} · {fmt_count(v["views"])} views · '
            f'{fmt_day(v["published"])}</span></li>' for v in videos[:3])
        parts.append(f'<h3>On YouTube</h3><ul class="vids">{items}</ul><p class="hint">Videos on YouTube whose '
                     f'description links this repo. <a href="https://www.youtube.com/t/terms" target="_blank" '
                     f'rel="noopener">YouTube Terms of Service</a></p>')
    return f'<section class="card"><h2>Where people talk</h2>{"".join(parts)}</section>' if parts else ""


def why_chips(row):
    chips = []
    for w in row["why"]:
        if w["url"]:
            chips.append(f'<a class="chip" href="{esc(w["url"])}" target="_blank" rel="noopener">{esc(w["text"])}</a>')
        else:
            chips.append(f'<span class="chip">{esc(w["text"])}</span>')
    return "".join(chips)


def shell(title, body, root, description, updated, path=None, head=""):
    # path: the page's address under SITE_URL ("" = home); None = no canonical link (404, Explore)
    # head: extra tags for <head>
    share = ""
    if path is not None:
        url = esc(f"{SITE_URL}/{path}")
        share = (f'<link rel="canonical" href="{url}">\n'
                 f'<meta property="og:type" content="website">\n'
                 f'<meta property="og:site_name" content="TrueStars">\n'
                 f'<meta property="og:title" content="{esc(title)}">\n'
                 f'<meta property="og:description" content="{esc(description)}">\n'
                 f'<meta property="og:url" content="{url}">\n')
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(title)}</title>
<meta name="description" content="{esc(description)}">
{share}<link rel="stylesheet" href="{root}style.css">
<link rel="icon" href="{root}favicon.svg" type="image/svg+xml">
{head}</head>
<body>
<header class="top"><div class="wrap">
  <a class="logo" href="{root}index.html">{STAR_ICON}TrueStars</a>
  <nav><a href="{root}index.html">Ranking</a><a href="{root}how/index.html">How it works</a></nav>
</div></header>
<main class="wrap">
{body}
</main>
<footer class="wrap foot">TrueStars · updated {esc(updated)} · data from GitHub's API, GH Archive, Hacker News, YouTube
  and X · not affiliated with GitHub · <a href="{root}privacy/index.html">Privacy and terms</a></footer>
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


def render_rising(rising, day):
    """The "Rising now" list at the top of the ranking."""
    items = []
    for r in rising:
        x = r["rising"]
        how = "brand new" if x["new"] else f"accelerating {fmt_x(x['x'])}"
        when = (f"+{x['stars']:,} so far today" if x["when"] == "today"
                else f"+{x['stars']:,} on {fmt_day(day.isoformat())}")
        link = (f'href="r/{esc(r["slug"])}/index.html"' if r["rank"]  # no page yet: not ranked on a full day
                else f'href="{esc(r["url"])}" target="_blank" rel="noopener"')
        items.append(f'<li><a class="name" {link}>{esc(r["name"])}</a>'
                     f'<span class="accel">{how}</span><span class="when">{when}</span></li>')
    found = f'<ol>{"".join(items)}</ol>' if items else '<p class="hint">Nothing in the ranking is speeding up right now.</p>'
    return f"""<section class="rising" aria-labelledby="rising-h">
    <h2 id="rising-h">Rising now</h2>
    <p class="hint">Getting at least {RISE_X:g}× their usual daily stars, on {fmt_day(day.isoformat())} or at
      today's pace so far. Updated twice a day. <a href="how/index.html#rising-now">How it's measured</a></p>
    {found}
  </section>"""


def render_index(rows, rising, day, latest, data, updated):
    root = ""
    today_label = fmt_day(latest.isoformat()) + (" so far" if latest >= dt.datetime.now(PACIFIC).date() else "")
    hidden = sum(1 for r in rows if len(r["flags"]) >= HIDE_AT_FLAGS)
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
    <div class="chips">{dir_html(r)}{why_chips(r)}</div>
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
  <h1>The GitHub repos gaining stars fastest, and why</h1>
  <div class="summary">Ranked by stars gained on <b>{fmt_day(day.isoformat())}</b> (a full day, US Pacific time),
    from {len(data['repos'])} fast-growing repos. Each shows whether it is rising, at its peak or cooling, and the
    reasons we can see. <b>{hidden}</b> repos with two or more red flags for fake stars are left out of the
    ranking; see them under “Has red flags”. Red flags are hints, not proof.
    <a href="how/index.html">How it works</a></div>
  {render_rising(rising, day)}
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
        "TrueStars: the GitHub repos gaining stars fastest, and why", body, root,
        "Daily ranking of the GitHub repos gaining stars fastest: whether each is rising or cooling, why it may be "
        "trending, and a check for fake stars.", updated, path=""))


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
  {where_it_stands(row, latest) if fresh else ''}
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
  {talk_html(row) if fresh else ''}
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
        f"{row['name']}: daily stars, whether it is rising or cooling, best rank #{best} and a fake-star check.",
        updated,
        path=f"r/{slug}/"))


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
    <p>Every day TrueStars ranks the GitHub repos that gained the most stars the day before. It shows whether
      each one is rising, at its peak or cooling, the reasons it may be trending that we can see, and a check for
      signs that its stars are not real. Days run midnight to midnight US Pacific time, the same days GitHub
      uses.</p>
    <h2>Where the numbers come from</h2>
    <p><b>Finding repos.</b> Each run looks at new repos with the most stars this month and this week, and at
      the most-starred repos created on each of the last three days, so new risers show up early (GitHub
      search). It also looks at the repos starred most often in the last 24 hours of GH Archive, a public log of
      GitHub activity. GH Archive now records only a sample of stars, so it is used only to find repos, never to
      count.</p>
    <p><b>Counting stars.</b> Daily star counts come from GitHub's star-history API, so they are exact.</p>
    <h2 id="direction">Rising, at its peak, steady or cooling</h2>
    <p>Each repo is compared with its own best day, using full days only:</p>
    <ul>
      <li><b>At its peak</b>: the ranking day was its best day so far. We keep 13 weeks of daily counts, so for an
        older repo it says <b>At a 3-month high</b>.</li>
      <li><b>Rising</b>: below its best day, but at least {RISING_X:g} times its average over the 3 days before,
        and at least 20 stars more.</li>
      <li><b>Cooling</b>: under {COOLING_SHARE:.0%} of its best day in the 7 days before.</li>
      <li><b>Steady</b>: none of these.</li>
    </ul>
    <p>A <b>run</b> is the days in a row with at least {RUN_SHARE:.0%} of the repo's best day: “day 4 of its run”
      counts them. A <b>second wave</b> means it is back above half its best day after dropping below a quarter of
      it. Most runs are short: in our data a new repo's best day comes a median of 2 days after it is created, and
      half of that is gone 2 days later.</p>
    <h2 id="rising-now">Rising now</h2>
    <p>The list at the top of the ranking shows repos getting at least {RISE_X:g} times their usual daily stars
      (their average over the 7 days before, counted as at least {RISE_FLOOR}), and at least {RISE_MIN} stars: on
      the last full day, or at today's pace once a fifth of the day has passed. It is refreshed on both daily
      updates. Tested on our own history, this rule picked out 23 of Nov 3's top 30 a median of two days before
      their best day. It says a repo is speeding up, not that it will trend.</p>
    <h2>Why a repo may be trending</h2>
    <p>Each repo shows the reasons we can see:</p>
    <ul>
      <li>a Hacker News post with {HN_MIN_POINTS}+ points in the last {HN_DAYS} days, with how much its stars
        jumped after it;</li>
      <li>a YouTube video from the last {YT_DAYS} days with {YT_MIN_VIEWS:,}+ views whose description links the
        repo, with how much its stars jumped after it;</li>
      <li>{X_MIN_POSTS}+ posts on X that linked the repo in the last 7 days, reposts not counted;</li>
      <li>a release in the last week, shown only when a day after it brought at least {JUMP_X:g} times the repo's
        usual daily stars;</li>
      <li>a <b>wave</b>: {WAVE_MIN} or more repos in the ranking that share a GitHub topic, such as DeepSeek
        Harness, agent skills or Claude Code;</li>
      <li>a repo created in the last two weeks (“Brand new”) or the last {LAUNCHED_DAYS} days (“Launched N days
        ago”);</li>
      <li>an owner that is a well-known company or AI lab, or a person with {FOLLOWERS_MIN:,}+ followers.</li>
    </ul>
    <p>YouTube and X are checked once a day for the top {YT_TOP} and top {X_TOP} repos, through their official
      APIs. Stars also come from places we can't see, such as Reddit, Discord and newsletters, so a repo with no
      reason shown may still have a good one.</p>
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
    <p>Forks and watchers are checked from {SMALL_MIN_STARS} stars up, issues and pull requests from
      {RATIO_MIN_STARS}. An owner account younger than {NEW_OWNER_DAYS} days, an owner with no followers, or fewer
      than {MIN_COMMITS} commits is normal for an honest launch, so those count only when one of the checks above
      also fails.</p>
    <p>Repos with {HIDE_AT_FLAGS} or more red flags are left out of the ranking. Those with {RATIO_MIN_STARS} stars
      or more stay visible under “Has red flags”. <b>A flag is a reason to look closer, not proof of
      cheating.</b> We never call a repo fake.</p>
    <h2>The badge</h2>
    <p>Every repo that makes the ranking gets a page and a badge showing its best daily rank. The badge updates
      itself every day. Copy it from the repo's page.</p>
    <h2>Not affiliated with GitHub</h2>
    <p>TrueStars is independent and uses GitHub's public API.</p>
  </section>"""
    write(os.path.join(SITE, "how", "index.html"), shell(
        "How TrueStars works", body, root,
        "How TrueStars ranks GitHub repos, tells rising from cooling, finds reasons and checks for fake stars.",
        updated, path="how/"))


def render_privacy(updated):
    """Privacy and terms. YouTube's API rules ask for a privacy policy and a link to YouTube's terms."""
    root = "../"
    body = f"""
  <h1>Privacy and terms</h1>
  <section class="prose">
    <p>TrueStars has no accounts, sets no cookies and runs no ads or analytics. It collects nothing about you.
      The site is hosted on GitHub Pages, and the Explore page loads repo and owner pictures from GitHub. GitHub
      may log those visits, as
      <a href="https://docs.github.com/site-policy/privacy-policies/github-general-privacy-statement">GitHub's
      privacy statement</a> describes.</p>
    <h2>YouTube and X</h2>
    <p>Repo pages list YouTube videos that link a repo, found through the YouTube API Services, and count the
      posts on X that link it, through X's API. By using TrueStars you agree to be bound by
      <a href="https://www.youtube.com/t/terms">YouTube's Terms of Service</a>. Google's handling of YouTube data
      is covered by the <a href="https://www.google.com/policies/privacy">Google Privacy Policy</a>. TrueStars
      keeps YouTube and X data for at most {SOCIAL_KEEP_DAYS} days; repos near the top are looked up again every
      day.</p>
    <h2>Contact</h2>
    <p>For questions, or to have something removed, open an issue at
      <a href="https://github.com/truestars-dev/truestars/issues">github.com/truestars-dev/truestars</a>.</p>
  </section>"""
    write(os.path.join(SITE, "privacy", "index.html"), shell(
        "Privacy and terms · TrueStars", body, root,
        "TrueStars collects nothing about you. How it uses YouTube and X data.", updated, path="privacy/"))


# ----------------------------------------------------------------- explore

def art_color(h, l, s):
    """An HLS color at hue h, darkened until white lines and text on it have 4.5:1 contrast."""
    while True:
        rgb = colorsys.hls_to_rgb(h, l, s)
        lin = [c / 12.92 if c <= 0.04045 else ((c + 0.055) / 1.055) ** 2.4 for c in rgb]
        if 1.05 / (0.2126 * lin[0] + 0.7152 * lin[1] + 0.0722 * lin[2] + 0.05) >= 4.5 or l <= 0.12:
            return "#%02x%02x%02x" % tuple(round(c * 255) for c in rgb)
        l -= 0.02


def art_of(name, color=""):
    """Card art for a repo without its own social image: two colors around the hue of its language's
    GitHub color (a hue from its name when it has none), and where the light falls, in percent."""
    seed = hashlib.sha256(name.lower().encode()).digest()
    hue = seed[0] / 256
    if re.fullmatch(r"#[0-9a-fA-F]{6}", color or ""):
        h, l, s = colorsys.rgb_to_hls(*(int(color[i:i + 2], 16) / 255 for i in (1, 3, 5)))
        if s >= 0.15 and 0.08 <= l <= 0.95:  # a gray language color (C, for one) carries no hue
            hue = h
    lean = (seed[1] / 255 - 0.5) * 0.12  # each repo leans a little its own way
    return ([art_color(hue, 0.42, 0.62), art_color((hue + 0.09 + lean) % 1, 0.3, 0.58)],
            [55 + seed[2] % 36, 6 + seed[3] % 26])


def render_explore(rows, day, latest, generated, updated):
    """Explore: an App Store-style page for browsing the repos with no red flags, by TrueStars Heat.
    The page is drawn in the browser from the JSON below (EXPLORE_JS)."""
    pool = sorted((r for r in rows if not r["flags"] and r["heat"] > 0),
                  key=lambda r: (-r["heat"], -r["pace"], r["name"].lower()))
    if not pool:
        return
    day_label = fmt_day(day.isoformat())
    repos = []
    for r in pool:
        colors, orb = art_of(r["name"], r["color"])
        d = r["direction"]
        label, detail = dir_parts(d) if d else (None, "")
        repos.append({
            "slug": r["slug"], "name": r["name"], "desc": r["description"][:200], "lang": r["language"],
            "url": r["url"], "page": os.path.exists(os.path.join(SITE, "r", r["slug"], "index.html")),
            "avatar": r["avatar"], "image": r["image"], "colors": colors, "orb": orb,
            "stars": r["stars"], "yday": r["yesterday"], "today": r["today"], "age": r["age"],
            "spark": r["spark"][:-1], "heat": r["heat"], "parts": r["heat_parts"], "pace": r["pace"],
            "speedup": r["speedup"], "state": d["state"] if d else None, "dir": label, "dir_detail": detail,
            # the wave chip's count is the ranking's; here the wave card counts the repos on this page
            "why": [[w["text"].split(" · ")[0] if w["kind"] == "wave" else w["text"], w["url"]] for w in r["why"]],
            "topics": r["topics"],
        })

    def state(r):
        return (r["direction"] or {}).get("state")

    def has(kind):
        return lambda r: any(w["kind"] == kind for w in r["why"])

    filters = [{"id": "hot", "chip": "Hottest", "title": "Hottest by TrueStars Heat",
                "sub": "Every repo on this page, hottest first", "items": list(range(len(pool)))}]
    shelves = [  # id, chip, title, subtitle, which repos
        ("speeding", "Speeding up", "Speeding up", f"At least {RISE_X:g} times their usual daily stars",
         lambda r: r["rising"] and r["age"] > 7),
        ("new", "Just launched", "Just launched", "Created in the last 7 days", lambda r: r["age"] <= 7),
        ("best", "Best day yet", "Best day yet", f"No day in the last 3 months beat {day_label}",
         lambda r: state(r) == "peak"),
        ("hn", "Hacker News", "On Hacker News", f"Posted there in the last {HN_DAYS} days", has("hn")),
        ("small", "Small and rising", "Small and rising", f"Under {SMALL_REPO:,} stars and climbing",
         lambda r: r["stars"] < SMALL_REPO and state(r) in ("peak", "rising")),
        ("again", "Another wave", "Back for another wave", "Took off, cooled down, and are climbing again",
         lambda r: (r["direction"] or {}).get("wave", 0) >= 2),
        ("labs", "Big names", "From the big names", "New work from big companies and AI labs", has("org")),
        ("releases", "Releases", "Fresh releases", "A release this week, and the stars jumped after it",
         has("release")),
        ("runs", "Long runs", "On a long run", "Two weeks or more of steady stars",
         lambda r: ((r["direction"] or {}).get("run") or 0) >= 14),
    ]
    for sid, chip, title, sub, test in shelves:
        items = [i for i, r in enumerate(pool) if test(r)]
        if len(items) >= 3:
            filters.append({"id": sid, "chip": chip, "title": title, "sub": sub, "items": items})
    waves = collections.defaultdict(list)
    for i, r in enumerate(pool):
        if r["waves"]:
            waves[r["waves"][0]].append(i)
    for name, items in sorted(waves.items(), key=lambda w: (-len(w[1]), w[0])):
        if len(items) >= WAVE_MIN:
            filters.append({"id": "wave:" + name, "chip": f"{name} wave", "title": f"The {name} wave",
                            "sub": "Repos that share its GitHub topics", "items": items,
                            "colors": art_of("wave " + name)[0]})
    langs = collections.Counter(r["language"] for r in pool if r["language"]).most_common(3)
    for name, n in langs:
        if n >= 4:
            filters.append({"id": "lang:" + name, "chip": name, "title": f"Top in {name}", "sub": "",
                            "kind": "list", "items": [i for i, r in enumerate(pool) if r["language"] == name]})
    lang_ids = [f["id"] for f in filters if f.get("kind") == "list"] + ["", "", ""]
    blocks = ["speeding", "new", "@top", "@waves", lang_ids[0], "best", "hn", "small", lang_ids[1], "again",
              "labs", "releases", lang_ids[2], "runs"]
    fresh = next((i for i, r in enumerate(pool) if i and r["age"] <= 14), None)
    fast = next((i for i in next((f["items"] for f in filters if f["id"] == "speeding"), [])
                 if i and i != fresh), None)
    data = {"day": day_label, "today": fmt_day(latest.isoformat()) + " so far",
            "spark_days": [fmt_day((day - dt.timedelta(days=k)).isoformat()) for k in range(13, -1, -1)],
            "shelf_max": SHELF_MAX, "fresh": fresh, "fast": fast, "filters": filters,
            "blocks": [b for b in blocks if b], "repos": repos}
    blob = json.dumps(data, separators=(",", ":")).replace("<", "\\u003c")  # ASCII; no "</script>" inside
    when = f"{generated:%A, %B} {generated.day}"
    body = f"""
<div class="ex">
  <header class="ex-head">
    <p class="eyebrow">{esc(when)} · Preview</p>
    <h1>Explore</h1>
    <p class="ex-lede">{len(pool)} fast-growing GitHub repos with no red flags, picked and ordered by TrueStars
      Heat: our own score of how hot a repo is right now. <a href="#heat">What is Heat?</a></p>
  </header>
  <div class="ex-bar" id="bar">
    <input id="q" type="search" placeholder="Search repos, topics, languages" aria-label="Search repos"
      autocomplete="off" spellcheck="false">
    <div class="ex-chips" id="chips" role="group" aria-label="Show"></div>
  </div>
  <div id="home"><div class="ex-today" id="today"></div><div id="blocks"></div></div>
  <section id="grid" hidden></section>
  <noscript><p>Explore needs JavaScript. <a href="../index.html">See the ranking</a>.</p></noscript>
  <section class="ex-about" id="heat" aria-labelledby="heat-h">
    <h2 id="heat-h">What is TrueStars Heat?</h2>
    <p>Our own score, from 0 to 100, of how hot a repo is right now. It adds three parts:</p>
    <ul>
      <li><b>Stars now, up to 60.</b> Its stars on {day_label}, or today's pace once a fifth of the day has
        passed. 10 stars a day scores 0 and {HEAT_FULL:,} or more scores 60; each tenfold step adds the same.</li>
      <li><b>Speeding up, up to 25.</b> That pace against its usual: its average over the 7 days before. Its
        usual pace or slower scores 0, ten times or more scores 25.</li>
      <li><b>Still climbing, up to 15.</b> At its peak {HEAT_CLIMB['peak']}, rising {HEAT_CLIMB['rising']},
        steady {HEAT_CLIMB['steady']}, cooling {HEAT_CLIMB['cooling']}.</li>
    </ul>
    <p>Only repos with no red flags for fake stars are on this page. Days are US Pacific time.
      <a href="../how/index.html">How TrueStars works</a></p>
  </section>
</div>
<button class="ex-surprise" id="surprise" type="button" hidden><svg viewBox="0 0 16 16" aria-hidden="true">
  <rect x="1.5" y="1.5" width="13" height="13" rx="3.5" fill="none" stroke="currentColor" stroke-width="1.6"/>
  <circle cx="5.2" cy="5.2" r="1.3"/><circle cx="8" cy="8" r="1.3"/><circle cx="10.8" cy="10.8" r="1.3"/>
  </svg>Surprise me</button>
<dialog class="ex-sheet" id="sheet" aria-labelledby="sheet-name"></dialog>
<script type="application/json" id="explore-data">{blob}</script>
<script>{EXPLORE_JS}</script>"""
    write(os.path.join(SITE, "explore", "index.html"), shell(
        "Explore · TrueStars", body, "../",
        "Browse today's fast-growing GitHub repos by TrueStars Heat: shelves, waves and surprises.", updated,
        head=f'<meta name="robots" content="noindex">\n<style>{EXPLORE_CSS}</style>\n'))


EXPLORE_JS = r"""
(function () {
  'use strict';
  var D = JSON.parse(document.getElementById('explore-data').textContent);
  var R = D.repos, NS = 'http://www.w3.org/2000/svg', byId = {};
  D.filters.forEach(function (f) { byId[f.id] = f; });
  var hay = R.map(function (r) { return [r.name, r.desc, r.lang].concat(r.topics).join(' ').toLowerCase(); });
  var sheet = document.getElementById('sheet');
  var FLAME = 'M8 .9c.5 2.2 2 3.4 3.2 4.8 1.2 1.4 1.9 2.8 1.9 4.3a5.1 5.1 0 0 1-10.2 0c0-1.7.8-3.1 1.8-4.1' +
              '.2 1.3.8 2.1 1.6 2.5C6 6.1 6.5 3.2 8 .9z';

  function el(tag, cls, text) {
    var e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text !== undefined && text !== null) e.textContent = text;
    return e;
  }
  function sv(tag, attrs) {
    var e = document.createElementNS(NS, tag);
    Object.keys(attrs || {}).forEach(function (k) { e.setAttribute(k, attrs[k]); });
    return e;
  }
  function fmt(n) {
    if (n >= 100000) return Math.round(n / 1000) + 'k';
    if (n >= 10000) return (n / 1000).toFixed(1) + 'k';
    return n.toLocaleString('en-US');
  }
  function plus(n) { return '+' + fmt(n); }
  function owner(r) { return r.name.slice(0, r.name.indexOf('/')); }
  function short(r) { return r.name.slice(r.name.indexOf('/') + 1); }
  function gained(r) { return r.yday ? plus(r.yday) + ' on ' + D.day : plus(r.today) + ' so far today'; }
  function paint(node, colors) {
    node.style.setProperty('--c1', colors[0]);
    node.style.setProperty('--c2', colors[1]);
  }
  function picture(src, cls, onfail) {
    var i = el('img', cls);
    i.alt = ''; i.loading = 'lazy'; i.decoding = 'async'; i.referrerPolicy = 'no-referrer';
    i.addEventListener('error', onfail);
    i.src = src;
    return i;
  }
  function flame() {
    var s = sv('svg', { viewBox: '0 0 16 16', 'class': 'flame', 'aria-hidden': 'true' });
    s.appendChild(sv('path', { d: FLAME }));
    return s;
  }
  function heatTag(r) {
    var t = el('span', 'heat-tag');
    t.title = 'TrueStars Heat: ' + r.heat + ' of 100';
    t.appendChild(flame());
    t.appendChild(el('span', 'vh', 'Heat '));
    t.appendChild(document.createTextNode(String(r.heat)));
    return t;
  }
  function meter(value, max, label) {
    var m = el('span', 'meter'), f = el('span', 'meter-fill');
    m.setAttribute('role', 'img');
    m.setAttribute('aria-label', label);
    f.style.width = (100 * Math.max(0, Math.min(value, max)) / max) + '%';
    m.appendChild(f);
    return m;
  }
  function icon(r, cls) {
    var box = el('span', 'icon ' + cls);
    paint(box, r.colors);
    box.appendChild(el('span', 'icon-letter', owner(r).charAt(0).toUpperCase()));
    if (r.avatar) box.appendChild(picture(r.avatar, 'icon-img', function () { this.remove(); }));
    return box;
  }

  // Card art: the repo's own social image, or a gradient in its language's color with the owner's
  // picture and a white line of its stars per day over the last 14 full days
  function sparkArt(r) {
    var v = r.spark, n = v.length, W = 300, H = 70, P = 12, max = Math.max.apply(null, v) || 1;
    var pts = v.map(function (y, i) { return [P + i * (W - 2 * P) / (n - 1), H - 8 - y / max * (H - 24)]; });
    var line = pts.map(function (p, i) { return (i ? 'L' : 'M') + p[0].toFixed(1) + ' ' + p[1].toFixed(1); }).join('');
    var s = sv('svg', { viewBox: '0 0 ' + W + ' ' + H, 'class': 'art-spark', 'aria-hidden': 'true' });
    s.appendChild(sv('path', { d: line + 'L' + (W - P) + ' ' + H + 'L' + P + ' ' + H + 'Z', 'class': 'area' }));
    s.appendChild(sv('path', { d: line, 'class': 'line' }));
    var end = pts[n - 1];
    s.appendChild(sv('circle', { cx: end[0].toFixed(1), cy: end[1].toFixed(1), r: 4, 'class': 'dot' }));
    return s;
  }
  function art(r) {
    var box = el('span', 'art');
    function made() {
      box.classList.add('art-made');
      paint(box, r.colors);
      box.style.setProperty('--ox', r.orb[0] + '%');
      box.style.setProperty('--oy', r.orb[1] + '%');
      box.appendChild(icon(r, 'icon-art'));
      box.appendChild(sparkArt(r));
    }
    if (r.image) box.appendChild(picture(r.image, 'art-img', function () { this.remove(); made(); }));
    else made();
    box.appendChild(heatTag(r));
    return box;
  }

  // A link to the repo's TrueStars page (GitHub when it has none); a plain click opens the quick look
  function opens(a, r) {
    a.href = r.page ? '../r/' + r.slug + '/index.html' : r.url;
    if (!r.page) { a.target = '_blank'; a.rel = 'noopener'; }
    a.addEventListener('click', function (e) {
      if (e.button || e.metaKey || e.ctrlKey || e.shiftKey || e.altKey || !sheet.showModal) return;
      e.preventDefault();
      show(r, false);
    });
    return a;
  }
  function card(r, eyebrow) {
    var a = opens(el('a', 'tile' + (eyebrow ? ' tile-big' : '')), r);
    a.appendChild(art(r));
    var b = el('span', 'tile-body');
    if (eyebrow) b.appendChild(el('span', 'eyebrow', eyebrow));
    b.appendChild(el('span', 'tile-name', short(r)));
    b.appendChild(el('span', 'tile-sub', owner(r) + (r.lang ? ' · ' + r.lang : '')));
    b.appendChild(el('span', 'tile-desc', r.desc));
    var m = el('span', 'tile-meta');
    m.appendChild(el('span', 'tile-stars', gained(r)));
    if (r.dir) m.appendChild(el('span', 'dir dir-' + r.state, r.dir));
    b.appendChild(m);
    a.appendChild(b);
    return a;
  }
  function lockup(r, n) {
    var a = opens(el('a', 'lockup'), r);
    a.appendChild(el('span', 'lockup-n', String(n)));
    a.appendChild(icon(r, 'icon-md'));
    var t = el('span', 'lockup-text');
    t.appendChild(el('span', 'lockup-name', short(r)));
    t.appendChild(el('span', 'lockup-desc', r.desc || owner(r)));
    t.appendChild(el('span', 'lockup-stars', gained(r)));
    a.appendChild(t);
    a.appendChild(heatTag(r));
    return a;
  }
  function chips(r) {
    var c = el('div', 'chips');
    if (r.dir) c.appendChild(el('span', 'dir dir-' + r.state, r.dir + (r.dir_detail ? ' · ' + r.dir_detail : '')));
    r.why.forEach(function (w) {
      var chip = el(w[1] ? 'a' : 'span', 'chip', w[0]);
      if (w[1]) { chip.href = w[1]; chip.target = '_blank'; chip.rel = 'noopener'; }
      c.appendChild(chip);
    });
    return c;
  }
  function heatParts(r) {
    var box = el('div', 'parts'), head = el('div', 'parts-head'), big = el('span', 'parts-heat');
    head.appendChild(el('span', 'parts-title', 'TrueStars Heat'));
    big.appendChild(flame());
    big.appendChild(document.createTextNode(String(r.heat)));
    big.appendChild(el('span', 'parts-of', '/100'));
    head.appendChild(big);
    box.appendChild(head);
    var x = r.speedup >= 10 ? Math.round(r.speedup) : r.speedup;
    [['Stars now', r.parts[0], 60, fmt(r.pace) + ' a day'],
     ['Speeding up', r.parts[1], 25, r.age <= 7 ? 'new this week' : x >= 1.1 ? '×' + x + ' its usual' :
       x <= 0.9 ? 'slower than its usual' : 'its usual pace'],
     ['Still climbing', r.parts[2], 15, r.dir || 'new today']].forEach(function (p) {
      var row = el('div', 'part');
      row.appendChild(el('span', 'part-name', p[0]));
      row.appendChild(meter(p[1], p[2], p[0] + ': ' + p[1] + ' of ' + p[2]));
      row.appendChild(el('span', 'part-pts', p[1] + '/' + p[2]));
      row.appendChild(el('span', 'part-why', p[3]));
      box.appendChild(row);
    });
    return box;
  }

  // Stars per day in the quick look: 14 full days and today so far, a tooltip on hover or touch,
  // and the same numbers in a table
  function chart(r) {
    var v = r.spark.concat([r.today]), days = D.spark_days.concat([D.today]);
    var n = v.length, W = 600, H = 120, gap = 4, bw = (W - gap * (n - 1)) / n;
    var max = Math.max.apply(null, v) || 1;
    var box = el('div', 'sheet-chart'), plot = el('div', 'plot'), tip = el('span', 'tip');
    box.appendChild(el('h3', null, 'Stars per day'));
    var s = sv('svg', { viewBox: '0 0 ' + W + ' ' + H, role: 'img',
                        'aria-label': 'Stars per day from ' + days[0] + ' to ' + days[n - 1] + ', in the table below' });
    tip.hidden = true;
    v.forEach(function (y, i) {
      var x = i * (bw + gap), h = y ? Math.max(3, y / max * (H - 2)) : 2, k = Math.min(4, bw / 2, h), top = H - h;
      var g = sv('g', { 'class': 'col' });
      g.appendChild(sv('rect', { x: x - gap / 2, y: 0, width: bw + gap, height: H, 'class': 'hit' }));
      g.appendChild(sv('path', { 'class': i === n - 1 ? 'b-today' : y ? 'b' : 'b-zero',
        d: 'M' + x + ' ' + H + 'V' + (top + k) + 'Q' + x + ' ' + top + ' ' + (x + k) + ' ' + top + 'H' + (x + bw - k) +
           'Q' + (x + bw) + ' ' + top + ' ' + (x + bw) + ' ' + (top + k) + 'V' + H + 'Z' }));
      g.addEventListener('pointerenter', function () {
        tip.textContent = days[i] + ': ' + plus(y) + ' star' + (y === 1 ? '' : 's');
        tip.hidden = false;
        var pw = plot.clientWidth, tw = tip.offsetWidth, px = pw * (x + bw / 2) / W;
        tip.style.left = Math.max(tw / 2, Math.min(pw - tw / 2, px)) + 'px';
        s.classList.add('hovering');
        g.classList.add('on');
      });
      g.addEventListener('pointerleave', function () {
        tip.hidden = true;
        s.classList.remove('hovering');
        g.classList.remove('on');
      });
      s.appendChild(g);
    });
    plot.appendChild(s);
    plot.appendChild(tip);
    box.appendChild(plot);
    var axis = el('div', 'axis');
    axis.appendChild(el('span', null, days[0]));
    axis.appendChild(el('span', null, days[n - 1]));
    box.appendChild(axis);
    var det = el('details', 'numbers'), table = el('table');
    det.appendChild(el('summary', null, 'Day by day'));
    v.forEach(function (y, i) {
      var tr = el('tr');
      tr.appendChild(el('td', null, days[i]));
      tr.appendChild(el('td', null, plus(y)));
      table.appendChild(tr);
    });
    det.appendChild(table);
    box.appendChild(det);
    return box;
  }

  // The quick look, also used by "Surprise me"
  var seen = {};
  function surprise(prev) {
    var pool = R.filter(function (r) { return !seen[r.slug] && r !== prev; });
    if (!pool.length) { seen = {}; pool = R.filter(function (r) { return r !== prev; }); }
    if (!pool.length) pool = R.slice();
    var total = pool.reduce(function (t, r) { return t + r.heat; }, 0), t = Math.random() * total;
    for (var i = 0; i < pool.length; i++) { t -= pool[i].heat; if (t <= 0) break; }
    var r = pool[Math.min(i, pool.length - 1)];
    seen[r.slug] = true;
    return r;
  }
  function show(r, lucky) {
    sheet.textContent = '';
    var bar = el('div', 'sheet-bar'), close = el('button', 'sheet-close', '×');
    bar.appendChild(el('span', 'eyebrow', lucky ? 'Surprise pick' : 'Quick look'));
    close.type = 'button';
    close.setAttribute('aria-label', 'Close');
    close.addEventListener('click', function () { sheet.close(); });
    bar.appendChild(close);
    sheet.appendChild(bar);
    var body = el('div', 'sheet-body');
    if (r.image) body.appendChild(art(r));
    var head = el('div', 'sheet-head'), t = el('div', 'sheet-titles'), h = el('h2', 'sheet-name', short(r));
    h.id = 'sheet-name';
    head.appendChild(icon(r, 'icon-lg'));
    t.appendChild(h);
    t.appendChild(el('p', 'tile-sub', [owner(r), r.lang, fmt(r.stars) + ' stars',
      r.age <= 30 ? 'created ' + (r.age ? r.age + ' day' + (r.age === 1 ? '' : 's') + ' ago' : 'today') : '']
      .filter(Boolean).join(' · ')));
    head.appendChild(t);
    body.appendChild(head);
    if (r.desc) body.appendChild(el('p', 'sheet-desc', r.desc));
    body.appendChild(chips(r));
    body.appendChild(heatParts(r));
    body.appendChild(chart(r));
    var acts = el('div', 'sheet-actions'), gh = el('a', 'btn btn-main', 'Open on GitHub ↗');
    gh.href = r.url; gh.target = '_blank'; gh.rel = 'noopener';
    acts.appendChild(gh);
    if (r.page) {
      var p = el('a', 'btn', 'TrueStars page');
      p.href = '../r/' + r.slug + '/index.html';
      acts.appendChild(p);
    }
    if (lucky) {
      var again = el('button', 'btn', 'Another one');
      again.type = 'button';
      again.addEventListener('click', function () { show(surprise(r), true); });
      acts.appendChild(again);
    }
    body.appendChild(acts);
    sheet.appendChild(body);
    if (!sheet.open) sheet.showModal();
    sheet.scrollTop = 0;
    close.focus();
    try { history.replaceState(null, '', '#' + r.slug); } catch (e) { /* file:// */ }
  }
  sheet.addEventListener('click', function (e) { if (e.target === sheet) sheet.close(); });
  sheet.addEventListener('close', function () {
    try { history.replaceState(null, '', location.pathname + location.search); } catch (e) { /* file:// */ }
  });

  // Shelves
  function head(title, sub, rail, f, shown) {
    var h = el('div', 'shelf-head'), t = el('div', 'shelf-titles'), tools = el('div', 'shelf-tools');
    t.appendChild(el('h2', null, title));
    if (sub) t.appendChild(el('p', 'shelf-sub', sub));
    h.appendChild(t);
    if (f && f.items.length > shown) {
      var all = el('button', 'see-all', 'See all ' + f.items.length);
      all.type = 'button';
      all.addEventListener('click', function () { choose(f.id); });
      tools.appendChild(all);
    }
    if (rail) {
      ['‹', '›'].forEach(function (g, k) {
        var b = el('button', 'nav-btn', g);
        b.type = 'button';
        b.setAttribute('aria-label', k ? 'Scroll right' : 'Scroll left');
        b.addEventListener('click', function () {
          rail.scrollBy({ left: (k ? 1 : -1) * rail.clientWidth * 0.9, behavior: 'smooth' });
        });
        tools.appendChild(b);
      });
    }
    h.appendChild(tools);
    return h;
  }
  function shelf(f) {
    var sec = el('section', 'shelf'), rail = el('div', 'rail' + (f.kind === 'list' ? ' rail-list' : ''));
    var items = f.items.slice(0, D.shelf_max);
    if (f.kind === 'list') {
      for (var i = 0; i < items.length; i += 3) {
        var col = el('div', 'col');
        for (var j = i; j < Math.min(i + 3, items.length); j++) col.appendChild(lockup(R[items[j]], j + 1));
        rail.appendChild(col);
      }
    } else {
      items.forEach(function (k) { rail.appendChild(card(R[k])); });
    }
    sec.appendChild(head(f.title, f.sub, rail, f, items.length));
    sec.appendChild(rail);
    return sec;
  }
  function waveCard(f, eyebrow) {
    var b = el('button', 'wave' + (eyebrow ? ' wave-big' : '')), stack = el('span', 'stack');
    b.type = 'button';
    paint(b, f.colors);
    b.style.setProperty('--ring', f.colors[0]);
    b.appendChild(el('span', 'eyebrow', eyebrow || 'Wave'));
    b.appendChild(el('span', 'wave-name', f.title));
    b.appendChild(el('span', 'wave-count', f.items.length + ' repos riding it today'));
    f.items.slice(0, 5).forEach(function (i) { stack.appendChild(icon(R[i], 'icon-stack')); });
    b.appendChild(stack);
    b.appendChild(el('span', 'wave-names', f.items.slice(0, 3).map(function (i) { return short(R[i]); }).join(' · ')));
    b.addEventListener('click', function () { choose(f.id); });
    return b;
  }
  var waves = D.filters.filter(function (f) { return f.id.indexOf('wave:') === 0; });
  function waveShelf() {
    if (!waves.length) return null;
    var sec = el('section', 'shelf'), rail = el('div', 'rail rail-waves');
    waves.forEach(function (f) { rail.appendChild(waveCard(f)); });
    sec.appendChild(head('Waves', 'Topics many repos are riding at once', rail));
    sec.appendChild(rail);
    return sec;
  }
  function topChart() {
    var f = byId.hot, sec = el('section', 'shelf'), ol = el('ol', 'top-list');
    var items = f.items.slice(0, 20);
    sec.appendChild(head('Hottest by TrueStars Heat', 'Stars now, speeding up and still climbing, in one score',
                         null, f, items.length));
    items.forEach(function (i, k) {
      var r = R[i], li = el('li'), a = opens(el('a', 'top-item'), r), t = el('span', 'top-text');
      var h = el('span', 'top-heat');
      a.appendChild(el('span', 'top-n', String(k + 1)));
      a.appendChild(icon(r, 'icon-md'));
      t.appendChild(el('span', 'top-name', short(r)));
      t.appendChild(el('span', 'top-sub', owner(r) + (r.lang ? ' · ' + r.lang : '')));
      a.appendChild(t);
      h.appendChild(meter(r.heat, 100, 'Heat ' + r.heat + ' of 100'));
      h.appendChild(el('span', 'top-num', String(r.heat)));
      a.appendChild(h);
      li.appendChild(a);
      ol.appendChild(li);
    });
    sec.appendChild(ol);
    return sec;
  }

  // The top of the page: the repo of the day, the newest riser and the biggest wave
  var today = document.getElementById('today'), top = R[0];
  var feat = el('article', 'feature'), fa = opens(el('a', 'feature-art'), top), ft = el('div', 'feature-text');
  var fh = el('h2', 'feature-name');
  fa.setAttribute('aria-label', short(top));
  fa.appendChild(art(top));
  feat.appendChild(fa);
  ft.appendChild(el('p', 'eyebrow', 'Repo of the day'));
  fh.appendChild(opens(el('a', null, short(top)), top));
  ft.appendChild(fh);
  ft.appendChild(el('p', 'tile-sub', [owner(top), top.lang, fmt(top.stars) + ' stars'].filter(Boolean).join(' · ')));
  if (top.desc) ft.appendChild(el('p', 'feature-desc', top.desc));
  ft.appendChild(chips(top));
  ft.appendChild(heatParts(top));
  feat.appendChild(ft);
  today.appendChild(feat);
  var duo = el('div', 'duo');
  if (D.fresh !== null) duo.appendChild(card(R[D.fresh], 'Brand new and taking off'));
  if (waves.length) duo.appendChild(waveCard(waves[0], 'The biggest wave'));
  else if (D.fast !== null) duo.appendChild(card(R[D.fast], 'Speeding up the most'));
  if (duo.children.length) today.appendChild(duo);
  var blocks = document.getElementById('blocks');
  D.blocks.forEach(function (id) {
    var node = id === '@top' ? topChart() : id === '@waves' ? waveShelf() : byId[id] ? shelf(byId[id]) : null;
    if (node) blocks.appendChild(node);
  });

  // Filters and search: anything but "Highlights" shows a grid, hottest first
  var chipBox = document.getElementById('chips'), q = document.getElementById('q');
  var home = document.getElementById('home'), grid = document.getElementById('grid'), current = '';
  [{ id: '', chip: 'Highlights' }].concat(D.filters).forEach(function (f) {
    var b = el('button', 'fchip', f.chip);
    b.type = 'button';
    b.dataset.id = f.id;
    b.setAttribute('aria-pressed', String(!f.id));
    b.addEventListener('click', function () { q.value = ''; choose(f.id); });
    chipBox.appendChild(b);
  });
  function choose(id) {
    current = id;
    chipBox.querySelectorAll('button').forEach(function (b) {
      var on = b.dataset.id === id;
      b.setAttribute('aria-pressed', String(on));
      if (on) chipBox.scrollTo({ left: b.offsetLeft - chipBox.offsetLeft - 24, behavior: 'smooth' });
    });
    draw();
  }
  function draw() {
    var text = q.value.trim().toLowerCase();
    var y = document.querySelector('.ex-head').getBoundingClientRect().bottom + window.scrollY;
    if (!current && !text) {
      home.hidden = false;
      grid.hidden = true;
      if (window.scrollY > y) window.scrollTo(0, y);
      return;
    }
    var f = byId[current] || byId.hot;
    var items = f.items.filter(function (i) { return !text || hay[i].indexOf(text) >= 0; });
    grid.textContent = '';
    var gh = el('div', 'grid-head'), titles = el('div');
    titles.appendChild(el('h2', null, text ? 'Results for “' + q.value.trim() + '”' + (current ? ' in ' + f.chip : '')
                                           : f.title));
    titles.appendChild(el('p', 'shelf-sub', items.length + (items.length === 1 ? ' repo' : ' repos') +
                                           (!text && f.sub ? ' · ' + f.sub : '')));
    gh.appendChild(titles);
    var back = el('button', 'see-all', 'Back to highlights');
    back.type = 'button';
    back.addEventListener('click', function () { q.value = ''; choose(''); });
    gh.appendChild(back);
    grid.appendChild(gh);
    var g = el('div', 'grid');
    items.forEach(function (i) { g.appendChild(card(R[i])); });
    grid.appendChild(g);
    if (!items.length) grid.appendChild(el('p', 'empty', 'Nothing matches. Try a language, a topic or part of a name.'));
    home.hidden = true;
    grid.hidden = false;
    if (window.scrollY > y) window.scrollTo(0, y);
  }
  var typing;
  q.addEventListener('input', function () { clearTimeout(typing); typing = setTimeout(draw, 150); });

  var lucky = document.getElementById('surprise');
  lucky.hidden = !sheet.showModal;
  lucky.addEventListener('click', function () { show(surprise(null), true); });
  var start = decodeURIComponent(location.hash.slice(1));
  R.forEach(function (r) { if (r.slug === start && sheet.showModal) show(r, false); });
})();
"""


EXPLORE_CSS = """
:root { --heat: #e8590c; --heat-track: #fbe3d4; --bar-bg: rgba(247, 246, 242, 0.9);
  --lift: 0 1px 2px rgba(29, 30, 32, 0.06), 0 6px 18px rgba(29, 30, 32, 0.08); }
@media (prefers-color-scheme: dark) {
  :root { --heat: #e9682a; --heat-track: #45291c; --bar-bg: rgba(18, 19, 21, 0.9);
    --lift: 0 1px 2px rgba(0, 0, 0, 0.5), 0 8px 22px rgba(0, 0, 0, 0.4); }
}
main.wrap { padding-bottom: 96px; }
.vh { position: absolute; width: 1px; height: 1px; overflow: hidden; clip: rect(0 0 0 0); white-space: nowrap; }
.eyebrow { display: block; font-size: 12px; font-weight: 650; letter-spacing: 0.06em; text-transform: uppercase;
  color: var(--muted); margin: 0 0 4px; }
.ex-head h1 { font-size: 34px; margin: 0 0 6px; }
.ex-lede { margin: 0; color: var(--muted); max-width: 680px; }
.ex-bar { position: sticky; top: 0; z-index: 5; display: flex; gap: 10px; align-items: center;
  margin: 10px -16px 14px; padding: 10px 16px; background: var(--bar-bg);
  -webkit-backdrop-filter: saturate(1.4) blur(10px); backdrop-filter: saturate(1.4) blur(10px); }
.ex-bar input { order: 2; flex: 0 0 250px; min-width: 0; font: inherit; font-size: 14px; padding: 7px 14px;
  border: 1px solid var(--line); border-radius: 999px; background: var(--panel); color: var(--ink); }
.ex-chips { flex: 1 1 auto; min-width: 0; display: flex; gap: 6px; overflow-x: auto; scrollbar-width: none;
  -webkit-mask-image: linear-gradient(to right, #000 92%, transparent);
  mask-image: linear-gradient(to right, #000 92%, transparent); }
.ex-chips::-webkit-scrollbar { display: none; }
.fchip { flex: none; border: 1px solid var(--line); background: var(--panel); color: var(--ink);
  border-radius: 999px; padding: 6px 12px; font: inherit; font-size: 13px; cursor: pointer; white-space: nowrap; }
.fchip[aria-pressed="true"] { background: var(--ink); border-color: var(--ink); color: var(--bg); }
.ex-today { display: grid; gap: 16px; margin-bottom: 34px; }
.feature { display: grid; grid-template-columns: minmax(0, 1.1fr) minmax(0, 1fr); background: var(--panel);
  border: 1px solid var(--line); border-radius: 20px; overflow: hidden; box-shadow: var(--lift); }
.feature-art { display: block; }
.feature .art { height: 100%; min-height: 300px; aspect-ratio: auto; border-radius: 0; box-shadow: none; }
.feature .icon-art { width: 76px; height: 76px; left: 20px; top: 20px; font-size: 30px; }
.feature-text { padding: 22px 24px; min-width: 0; }
.feature-name { font-size: 30px; margin: 0; letter-spacing: -0.02em; line-height: 1.15; word-break: break-word; }
.feature-name a { color: var(--ink); text-decoration: none; }
.feature-name a:hover { text-decoration: underline; }
.feature-desc { margin: 10px 0 12px; }
.duo { display: grid; grid-template-columns: repeat(auto-fit, minmax(280px, 1fr)); gap: 16px; }
.art { position: relative; display: block; aspect-ratio: 2 / 1; border-radius: 14px; overflow: hidden;
  background: var(--chip); }
.art-img { position: absolute; inset: 0; width: 100%; height: 100%; object-fit: cover; }
.art-made { background: radial-gradient(circle at var(--ox) var(--oy), rgba(255, 255, 255, 0.26),
  rgba(255, 255, 255, 0) 46%), linear-gradient(135deg, var(--c1), var(--c2)); }
.art-spark { position: absolute; left: 0; bottom: 0; width: 100%; height: auto; }
.art-spark .line { fill: none; stroke: #fff; stroke-width: 2; stroke-linecap: round; stroke-linejoin: round;
  vector-effect: non-scaling-stroke; }
.art-spark .area { fill: rgba(255, 255, 255, 0.16); }
.art-spark .dot { fill: #fff; }
.heat-tag { display: inline-flex; align-items: center; gap: 3px; flex: none; padding: 3px 8px 3px 6px;
  border-radius: 999px; background: var(--panel); color: var(--ink); font-size: 12px; font-weight: 700; }
.art .heat-tag { position: absolute; top: 10px; right: 10px; box-shadow: 0 2px 8px rgba(0, 0, 0, 0.18); }
.flame { width: 12px; height: 12px; fill: var(--heat); }
.icon { position: relative; display: inline-grid; place-items: center; flex: none; overflow: hidden;
  border-radius: 22%; background: linear-gradient(135deg, var(--c1), var(--c2)); color: #fff; font-weight: 700; }
.icon-img { position: absolute; inset: 0; width: 100%; height: 100%; object-fit: cover; background: #fff; }
.icon-art { position: absolute; left: 14px; top: 14px; width: 52px; height: 52px; font-size: 22px;
  box-shadow: 0 0 0 2px rgba(255, 255, 255, 0.9), 0 4px 14px rgba(0, 0, 0, 0.25); }
.icon-md { width: 44px; height: 44px; font-size: 18px; }
.icon-lg { width: 64px; height: 64px; font-size: 26px; }
.icon-stack { width: 34px; height: 34px; margin-right: -8px; border-radius: 50%; font-size: 14px;
  box-shadow: 0 0 0 2px var(--ring); }
.shelf { margin: 0 0 34px; }
.shelf-head { display: flex; align-items: flex-end; justify-content: space-between; gap: 12px; margin-bottom: 10px; }
.shelf-titles { min-width: 0; }
.shelf-head h2, .grid-head h2 { font-size: 21px; margin: 0; letter-spacing: -0.01em; }
.shelf-sub { margin: 2px 0 0; font-size: 13px; color: var(--muted); }
.shelf-tools { display: flex; gap: 6px; align-items: center; flex: none; }
.see-all { border: 0; background: none; color: var(--accent); font: inherit; font-size: 14px; font-weight: 600;
  cursor: pointer; padding: 4px 6px; white-space: nowrap; }
.see-all:hover { text-decoration: underline; }
.nav-btn { width: 30px; height: 30px; border-radius: 50%; border: 1px solid var(--line); background: var(--panel);
  color: var(--ink); font-size: 18px; line-height: 1; cursor: pointer; }
.nav-btn:hover { border-color: var(--muted); }
.rail { position: relative; display: grid; grid-auto-flow: column; grid-auto-columns: calc((100% - 3 * 16px) / 3.4); gap: 16px;
  overflow-x: auto; scroll-snap-type: x mandatory; padding: 4px 2px 14px; scrollbar-width: thin; }
.rail > * { scroll-snap-align: start; }
.rail-list { grid-auto-columns: calc((100% - 2 * 16px) / 2.4); }
.rail-waves { grid-auto-columns: calc((100% - 2 * 16px) / 2.6); }
.tile { display: flex; flex-direction: column; gap: 10px; min-width: 0; padding: 10px 10px 12px;
  background: var(--panel); border: 1px solid var(--line); border-radius: 16px; color: var(--ink);
  text-decoration: none; }
.tile .art { box-shadow: var(--lift); transition: transform 0.15s ease; }
.tile:hover .art { transform: translateY(-2px); }
.tile:hover .tile-name { text-decoration: underline; }
.tile-body { display: flex; flex-direction: column; gap: 2px; min-width: 0; padding: 0 2px; }
.tile-name { font-weight: 700; font-size: 15px; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.tile-sub { margin: 0; font-size: 12px; color: var(--muted); overflow: hidden; text-overflow: ellipsis;
  white-space: nowrap; }
.tile-desc { font-size: 13px; color: var(--muted); min-height: 2.9em; overflow: hidden; display: -webkit-box;
  -webkit-line-clamp: 2; -webkit-box-orient: vertical; }
.tile-meta { display: flex; flex-wrap: wrap; gap: 4px 8px; align-items: center; margin-top: 4px; font-size: 12px; }
.tile-stars { font-weight: 650; }
.tile-big { background: var(--panel); border: 1px solid var(--line); border-radius: 18px; padding: 12px;
  box-shadow: var(--lift); }
.tile-big .art { box-shadow: none; }
.tile-big .tile-name { font-size: 19px; }
.col { display: grid; align-content: start; }
.lockup { display: grid; grid-template-columns: 18px 44px minmax(0, 1fr) auto; gap: 10px; align-items: center;
  padding: 9px 2px; border-bottom: 1px solid var(--line); color: var(--ink); text-decoration: none; }
.col .lockup:last-child { border-bottom: 0; }
.lockup:hover .lockup-name { text-decoration: underline; }
.lockup-n { font-weight: 700; color: var(--muted); text-align: center; }
.lockup-text { min-width: 0; }
.lockup-name, .lockup-desc, .lockup-stars, .top-name, .top-sub { display: block; overflow: hidden;
  text-overflow: ellipsis; white-space: nowrap; }
.lockup-name, .top-name { font-weight: 650; }
.lockup-desc, .top-sub { font-size: 12px; color: var(--muted); }
.lockup-stars { font-size: 12px; font-weight: 600; }
.lockup .heat-tag { background: var(--chip); }
.wave { display: flex; flex-direction: column; align-items: flex-start; gap: 4px; min-height: 196px; padding: 18px;
  border: 0; border-radius: 18px; color: #fff; font: inherit; text-align: left; cursor: pointer; box-shadow: var(--lift);
  background: radial-gradient(circle at 86% 8%, rgba(255, 255, 255, 0.22), rgba(255, 255, 255, 0) 46%),
    linear-gradient(135deg, var(--c1), var(--c2)); }
.wave .eyebrow { color: #fff; }
.wave-name { font-size: 22px; font-weight: 750; letter-spacing: -0.01em; line-height: 1.2; }
.wave-count, .wave-names { font-size: 13px; }
.wave .stack { display: flex; margin: auto 0 4px; padding-right: 8px; }
.wave:hover .wave-name { text-decoration: underline; }
.top-list { display: grid; grid-template-columns: 1fr 1fr; grid-template-rows: repeat(10, auto);
  grid-auto-flow: column; column-gap: 32px; padding: 4px 18px; background: var(--panel);
  border: 1px solid var(--line); border-radius: 18px; }
.top-item { display: grid; grid-template-columns: 24px 44px minmax(0, 1fr) 104px; gap: 10px; align-items: center;
  padding: 9px 0; border-bottom: 1px solid var(--line); color: var(--ink); text-decoration: none; }
.top-list li:nth-child(10) .top-item, .top-list li:last-child .top-item { border-bottom: 0; }
.top-item:hover .top-name { text-decoration: underline; }
.top-n { font-weight: 750; font-size: 17px; color: var(--muted); text-align: center; }
.top-text { min-width: 0; }
.top-heat { display: grid; grid-template-columns: minmax(0, 1fr) 2.2em; gap: 8px; align-items: center; }
.top-num { font-weight: 700; text-align: right; }
.meter { display: block; height: 6px; border-radius: 3px; background: var(--heat-track); overflow: hidden; }
.meter-fill { display: block; height: 100%; border-radius: 3px; background: var(--heat); }
.grid-head { display: flex; align-items: flex-end; justify-content: space-between; gap: 12px; margin-bottom: 14px; }
.grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(230px, 1fr)); gap: 24px 16px; }
.empty { color: var(--muted); }
.ex-about { max-width: 760px; margin-top: 8px; padding: 18px 20px; background: var(--panel);
  border: 1px solid var(--line); border-radius: 16px; scroll-margin-top: 80px; }
.ex-about h2 { font-size: 18px; }
.ex-about ul { padding-left: 18px; }
.ex-about li { margin-bottom: 6px; }
.ex-surprise { position: fixed; z-index: 6; right: max(16px, env(safe-area-inset-right));
  bottom: max(16px, env(safe-area-inset-bottom)); display: inline-flex; align-items: center; gap: 8px;
  padding: 12px 18px; border: 0; border-radius: 999px; background: var(--ink); color: var(--bg); font: inherit;
  font-size: 15px; font-weight: 700; cursor: pointer; box-shadow: 0 6px 20px rgba(0, 0, 0, 0.28); }
.ex-surprise[hidden] { display: none; }
.ex-surprise svg { width: 18px; height: 18px; fill: currentColor; }
.ex-surprise:hover { transform: translateY(-1px); }
.ex-sheet { width: min(640px, calc(100vw - 24px)); max-height: calc(100dvh - 32px); padding: 0; border: 0;
  border-radius: 20px; background: var(--panel); color: var(--ink); overflow: auto; overscroll-behavior: contain;
  box-shadow: 0 20px 60px rgba(0, 0, 0, 0.35); }
.ex-sheet::backdrop { background: rgba(10, 10, 12, 0.55); }
.sheet-bar { position: sticky; top: 0; z-index: 3; display: flex; align-items: center; justify-content: space-between;
  padding: 10px 14px 10px 18px; background: var(--panel); border-bottom: 1px solid var(--line); }
.sheet-bar .eyebrow { margin: 0; }
.sheet-close { width: 32px; height: 32px; border: 0; border-radius: 50%; background: var(--chip); color: var(--ink);
  font-size: 20px; line-height: 1; cursor: pointer; }
.sheet-body { padding: 16px 18px 20px; }
.sheet-head { display: flex; gap: 14px; align-items: center; margin: 14px 0 8px; }
.sheet-titles { min-width: 0; }
.sheet-name { font-size: 24px; margin: 0; letter-spacing: -0.01em; word-break: break-word; }
.sheet-desc { margin: 4px 0 10px; }
.parts { display: grid; gap: 8px; margin: 12px 0; padding: 12px 14px; border: 1px solid var(--line);
  border-radius: 14px; }
.parts-head { display: flex; justify-content: space-between; align-items: center; }
.parts-title { font-weight: 700; font-size: 14px; }
.parts-heat { display: inline-flex; align-items: baseline; gap: 4px; font-size: 26px; font-weight: 800; line-height: 1; }
.parts-heat .flame { width: 20px; height: 20px; align-self: center; }
.parts-of { font-size: 13px; font-weight: 600; color: var(--muted); }
.part { display: grid; grid-template-columns: 7.2em minmax(50px, 1fr) 3em minmax(0, 1.25fr); gap: 10px;
  align-items: center; font-size: 13px; }
.part-pts { font-weight: 650; text-align: right; font-variant-numeric: tabular-nums; }
.part-why { color: var(--muted); overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.sheet-chart { margin-top: 16px; }
.sheet-chart h3 { font-size: 14px; margin: 0 0 8px; }
.plot { position: relative; }
.plot svg { display: block; width: 100%; height: auto; }
.plot .hit { fill: transparent; }
.plot .b { fill: var(--bar); } .plot .b-today { fill: var(--bar-today); } .plot .b-zero { fill: var(--bar-zero); }
.plot svg.hovering .col:not(.on) path { opacity: 0.45; }
.tip { position: absolute; top: -4px; transform: translate(-50%, -100%); padding: 4px 8px; border-radius: 6px;
  background: var(--ink); color: var(--bg); font-size: 12px; font-weight: 600; white-space: nowrap; pointer-events: none; }
.tip[hidden] { display: none; }
.numbers { margin-top: 10px; font-size: 13px; }
.numbers summary { cursor: pointer; color: var(--accent); }
.numbers table { margin-top: 6px; border-collapse: collapse; font-variant-numeric: tabular-nums; }
.numbers td { padding: 2px 18px 2px 0; }
.numbers td + td { text-align: right; }
.sheet-actions { display: flex; flex-wrap: wrap; gap: 8px; margin-top: 18px; }
.btn { display: inline-flex; align-items: center; padding: 9px 16px; border: 1px solid var(--line); border-radius: 999px;
  background: var(--panel); color: var(--ink); font: inherit; font-size: 14px; font-weight: 650; text-decoration: none;
  cursor: pointer; }
.btn:hover { border-color: var(--muted); }
.btn-main { background: var(--ink); border-color: var(--ink); color: var(--bg); }
@media (hover: none) { .nav-btn { display: none; } }
@media (max-width: 760px) {
  .ex-head h1 { font-size: 28px; }
  .ex-bar { flex-wrap: wrap; }
  .ex-bar input { order: 0; flex: 1 1 100%; }
  .feature { grid-template-columns: 1fr; border-radius: 16px; }
  .feature .art { min-height: 0; aspect-ratio: 2 / 1; }
  .feature .icon-art { width: 60px; height: 60px; left: 14px; top: 14px; }
  .feature-text { padding: 16px; }
  .feature-name { font-size: 25px; }
  .rail { grid-auto-columns: 74%; margin: 0 -16px; padding: 4px 16px 14px; scroll-padding: 0 16px; }
  .rail-list { grid-auto-columns: 88%; }
  .rail-waves { grid-auto-columns: 78%; }
  .top-list { grid-template-columns: 1fr; grid-template-rows: none; grid-auto-flow: row; padding: 2px 12px; }
  .top-list li:nth-child(10) .top-item { border-bottom: 1px solid var(--line); }
  .top-list li:last-child .top-item { border-bottom: 0; }
  .top-item { grid-template-columns: 22px 40px minmax(0, 1fr) 76px; gap: 8px; }
  .icon-md { width: 40px; height: 40px; }
  .grid-head { flex-wrap: wrap; }
}
@media (max-width: 520px) {
  .grid { grid-template-columns: 1fr; }
  .part { grid-template-columns: 7em minmax(0, 1fr) 3em; row-gap: 2px; }
  .part-why { grid-column: 2 / 4; }
  .sheet-body { padding: 14px 14px 18px; }
}
"""


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as fh:
        fh.write(text)


def ranked(data):
    """The listed repos, sorted and ranked as published. Also returns today (Pacific), when the data was
    collected (Pacific time) and the share of today that had passed by then."""
    latest = dt.date.fromisoformat(data["latest_day"])
    generated = dt.datetime.fromisoformat(data["generated_at"]).astimezone(PACIFIC)
    midnight = generated.replace(hour=0, minute=0, second=0, microsecond=0)
    frac = (generated - midnight).total_seconds() / 86400 if generated.date() == latest else 0.0
    rows = []
    for repo in data["repos"]:
        if not repo["meta"] or not repo["daily"] or repo["meta"]["isFork"]:
            continue
        row = assess(repo, latest, frac)
        if row["week"] < 50 and row["today"] < 20:
            continue
        if len(row["flags"]) >= HIDE_AT_FLAGS and row["stars"] < RATIO_MIN_STARS:
            continue  # small and flagged, mostly installer spam: not even listed under "Has red flags"
        rows.append(row)
    rows.sort(key=lambda r: (-r["yesterday"], r["name"].lower()))
    rank = 0
    for r in rows:  # ranked: fewer than HIDE_AT_FLAGS flags and stars on the ranking day (not just today)
        if len(r["flags"]) < HIDE_AT_FLAGS and r["yesterday"] > 0:
            rank += 1
            r["rank"] = rank
        else:
            r["rank"] = None
    return rows, latest, generated, frac


def load_social():
    """{slug: {"youtube": ..., "x": ...}}: this machine's copy, else the copy published with the site."""
    try:
        with open(SOCIAL) as fh:
            return json.load(fh)["repos"]
    except (OSError, ValueError, KeyError, TypeError):
        pass
    status, raw = fetch(SOCIAL_URL, timeout=20, tries=2)
    try:
        return json.loads(raw)["repos"] if status == 200 else {}
    except (ValueError, KeyError, TypeError):
        return {}


def social():
    """YouTube videos and posts on X that link the top repos, looked up once a day per repo. Any refusal
    (a wrong key, no credit left, a used-up quota) only stops that source for this run."""
    with open(LATEST) as fh:
        data = json.load(fh)
    rows, latest, _, _ = ranked(data)
    top = [r for r in rows if r["rank"]]
    now = dt.datetime.now(dt.timezone.utc)
    stamp = now.isoformat(timespec="seconds")
    state = load_social()

    def stale(slug, source):
        at = ((state.get(slug) or {}).get(source) or {}).get("at")
        return not at or (now - dt.datetime.fromisoformat(at)).total_seconds() > SOCIAL_FRESH_HOURS * 3600

    def since(r):  # YouTube: videos posted after the repo was made, within YT_SEARCH_DAYS
        return max(latest - dt.timedelta(days=r["age"] + 1), latest - dt.timedelta(days=YT_SEARCH_DAYS))

    key, token = os.environ.get("GOOGLE_API_KEY", ""), os.environ.get("X_BEARER_TOKEN", "")
    print("     YouTube and X for the top repos ...", flush=True)
    for source, label, secret, limit, look in (
            ("youtube", "YouTube", key, YT_TOP, lambda r: youtube(r["name"], since(r), key)),
            ("x", "X", token, X_TOP, lambda r: x_posts(r["name"], token))):
        if not secret:
            print(f"     {label}: no key, skipped")
            continue
        todo = [r for r in top[:limit] if stale(r["slug"], source)]
        done = found = 0
        for r in todo:
            status, result = look(r)
            if status != 200:
                print(f"     {label}: stopped after {done} of {len(todo)} lookups: HTTP {status} {result}".rstrip())
                break
            state.setdefault(r["slug"], {})[source] = dict(
                {"at": stamp}, **({"videos": result} if source == "youtube" else result))
            done += 1
            found += bool(result if source == "youtube" else result["week"])
        print(f"     {label}: {done} looked up, {found} with videos or posts that link the repo, "
              f"{len(top[:limit]) - len(todo)} still fresh")
    if key and REDDIT_APP:  # the Reddit test: the log shows whether Google's site search finds threads
        for r in top[:5]:
            status, result = reddit_threads(r["name"], key)
            print(f"     Reddit test {r['name']}: HTTP {status} "
                  + (f"{len(result)} threads" + (f", e.g. r/{result[0]['sub']}" if result else "")
                     if status == 200 else str(result)))
            if status != 200:
                break
    cutoff = now - dt.timedelta(days=SOCIAL_KEEP_DAYS)
    kept = {}
    for slug, entry in state.items():
        entry = {s: v for s, v in entry.items() if s in SOCIAL_KINDS
                 and dt.datetime.fromisoformat(v["at"]) > cutoff}
        if entry:
            kept[slug] = entry
    write(SOCIAL, json.dumps({"generated_at": stamp, "about": (
        f"YouTube and X data shown on TrueStars, looked up daily for the top repos and deleted after "
        f"{SOCIAL_KEEP_DAYS} days. YouTube data comes from the YouTube API Services."), "repos": kept},
        separators=(",", ":")))


def social_chips(row, repo, latest):
    """Reasons from YouTube and X, for the repos looked up in social()."""
    chips, found = [], row["social"]
    videos = [v for v in (found.get("youtube") or {}).get("videos") or []
              if v["views"] >= YT_MIN_VIEWS and days_between(v["published"], latest) <= YT_DAYS]
    if videos:
        top = videos[0]
        lift = jump(repo["daily"], pacific_day(top["published"]), latest - dt.timedelta(days=1),
                    pacific_day(repo["meta"]["createdAt"]), 3) if repo else None
        channel = top["channel"] if len(top["channel"]) <= 24 else top["channel"][:23] + "…"
        chips.append({"kind": "youtube", "url": f"https://www.youtube.com/watch?v={top['id']}",
                      "text": f"YouTube · {fmt_count(top['views'])} views · {channel} · {fmt_day(top['published'])}"
                              + (f" · stars {fmt_x(lift)}" if lift else "")})
    posts = (found.get("x") or {}).get("week") or 0
    if posts >= X_MIN_POSTS:
        chips.append({"kind": "x", "url": x_search(row["name"]), "text": f"X · {posts:,} posts in 7 days"})
    return chips


def x_search(full_name):
    return "https://x.com/search?" + urllib.parse.urlencode({"q": f'url:"github.com/{full_name}"', "f": "live"})


def build():
    with open(LATEST) as fh:
        data = json.load(fh)
    rows, latest, generated, frac = ranked(data)
    day = latest - dt.timedelta(days=1)  # the ranking day: the last complete Pacific day
    rank = sum(1 for r in rows if r["rank"])
    found = {}
    if os.path.exists(SOCIAL):  # written by social() in this run
        with open(SOCIAL) as fh:
            found = json.load(fh)["repos"]
    by_name = {r["meta"]["nameWithOwner"]: r for r in data["repos"] if r["meta"]}
    # Waves: GitHub topics shared by WAVE_MIN+ repos in the ranking; a repo shows the first one in WAVES
    listed = collections.Counter(w for r in rows if r["rank"] for w in r["waves"])
    for r in rows:
        wave = next((w for w in r["waves"] if listed[w] >= WAVE_MIN), None)
        if wave:
            r["why"].append({"kind": "wave", "text": f"Part of the {wave} wave · {listed[wave]} on the list",
                             "url": None})
        r["social"] = found.get(r["slug"]) or {}
        r["why"] += social_chips(r, by_name.get(r["name"]), latest)
        r["why"].sort(key=lambda w: WHY_ORDER.index(w["kind"]))
        r["heat"], r["heat_parts"], r["pace"], r["speedup"] = heat(r, frac)
    rising = sorted((r for r in rows if not r["flags"] and r["rising"]),  # no red flags; biggest gain first
                    key=lambda r: (r["rising"]["base"] - r["rising"]["rate"], r["name"].lower()))[:RISE_LIST]
    save_day(day, rows, data)
    history = load_history()

    if os.path.isdir(SITE):
        shutil.rmtree(SITE)  # rebuilt from scratch every run
    updated = f"{generated:%b} {generated.day}, {generated:%-I:%M %p} Pacific"
    write(os.path.join(SITE, "style.css"), STYLE)
    write(os.path.join(SITE, "favicon.svg"),
          f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20"><polygon fill="#2c55c9" '
          f'points="{star_points(10, 10.6, 9.5, 4)}"/></svg>')
    render_index(rows, rising, day, latest, data, updated)
    render_how(updated)
    render_privacy(updated)
    if os.path.exists(SOCIAL):  # published so the next run can read it back (social())
        shutil.copyfile(SOCIAL, os.path.join(SITE, "social.json"))
    fresh = {r["slug"]: r for r in rows}
    for slug, entry in history.items():
        render_repo(slug, entry, fresh.get(slug), latest, updated)
        render_badge(slug, best_rank(entry["ranks"])[0])
    try:
        render_explore(rows, day, latest, generated, updated)
    except Exception:  # a preview page must never keep the ranking from publishing
        print("Explore page failed; the rest of the site is built:", file=sys.stderr)
        traceback.print_exc()
    write(os.path.join(SITE, "404.html"), shell(
        "Not found · TrueStars", '<h1>Page not found</h1><p>This repo has not been in the ranking yet. '
        '<a href="/index.html">See today\'s ranking</a>.</p>', "/", "Page not found.", updated))
    # Search engines: every page that rendered above, home and How first
    pages = ["", "how/", "privacy/"] + [f"r/{slug}/" for slug in sorted(history)
                            if os.path.exists(os.path.join(SITE, "r", slug, "index.html"))]
    write(os.path.join(SITE, "sitemap.xml"),
          '<?xml version="1.0" encoding="UTF-8"?>\n'
          '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'
          + "".join(f"<url><loc>{esc(SITE_URL + '/' + p)}</loc></url>\n" for p in pages)
          + "</urlset>\n")
    write(os.path.join(SITE, "robots.txt"), f"User-agent: *\nAllow: /\nSitemap: {SITE_URL}/sitemap.xml\n")
    print(f"Site built: {len(rows)} repos listed, {rank} in the ranking, {len(history)} repo pages "
          f"and badges, day {day.isoformat()} saved")


STYLE = """
:root {
  --bg: #f7f6f2; --panel: #ffffff; --ink: #1d1e20; --muted: #676b72; --line: #e4e1da;
  --accent: #2c55c9; --chip: #efede7; --gold: #f5c242;
  --good: #1d6b44; --good-bg: #e3f2e9; --warn: #8a5800; --warn-bg: #fbefd5;
  --bad: #a3261b; --bad-bg: #fbe4e1; --bar: #2c55c9; --bar-today: #a8b9ea; --bar-zero: #dcd8cf;
  --accent-bg: #e6ecfa; --cool: #4f5f7a; --cool-bg: #e8ecf2;
}
@media (prefers-color-scheme: dark) {
  :root {
    --bg: #121315; --panel: #1b1c1f; --ink: #ebebea; --muted: #9b9fa6; --line: #2b2d31;
    --accent: #87a6ff; --chip: #26282c;
    --good: #79d3a0; --good-bg: #15301f; --warn: #f0c46c; --warn-bg: #33270e;
    --bad: #ff9187; --bad-bg: #3b1714; --bar: #87a6ff; --bar-today: #3d4c78; --bar-zero: #303236;
    --accent-bg: #1f2945; --cool: #a9b7d0; --cool-bg: #242a35;
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
.dir { font-size: 12px; font-weight: 600; padding: 2px 8px; border-radius: 999px; white-space: nowrap; }
.dir-peak { background: var(--accent-bg); color: var(--accent); }
.dir-rising { background: var(--good-bg); color: var(--good); }
.dir-steady { background: var(--chip); color: var(--muted); }
.dir-cooling { background: var(--cool-bg); color: var(--cool); }
.dir-peak::before { content: "▲ "; } .dir-rising::before { content: "↑ "; }
.dir-steady::before { content: "→ "; } .dir-cooling::before { content: "↓ "; }
.rising { background: var(--panel); border: 1px solid var(--line); border-radius: 12px;
  padding: 14px 16px; margin-bottom: 20px; }
.rising h2 { margin-bottom: 2px; }
.rising .hint { margin: 0 0 10px; }
.rising ol { display: grid; gap: 6px; }
.rising li { display: flex; flex-wrap: wrap; gap: 2px 10px; align-items: baseline; }
.accel { font-size: 12px; font-weight: 600; color: var(--good); }
.when { font-size: 12px; color: var(--muted); }
.facts { margin: 10px 0 0; padding-left: 18px; font-size: 14px; }
.facts li { margin-bottom: 4px; }
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
.card h3 { font-size: 14px; margin: 14px 0 6px; }
.vids { list-style: none; padding: 0; margin: 0; display: grid; gap: 8px; }
.vids a { font-weight: 600; overflow-wrap: anywhere; }
.vids span { display: block; color: var(--muted); font-size: 13px; }
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
.foot a { color: inherit; }
@media (max-width: 760px) {
  .row { grid-template-columns: 28px 1fr; }
  .nums, .spark { grid-column: 2; }
  .chip, .dir { white-space: normal; }
  .stats { grid-template-columns: repeat(2, 1fr); }
  h1 { font-size: 22px; }
}
"""


if __name__ == "__main__":
    step = sys.argv[1] if len(sys.argv) > 1 else "all"
    if step not in ("all", "collect", "social", "build"):
        sys.exit(__doc__)
    if step in ("all", "collect"):
        collect()
    if step in ("all", "social"):
        try:
            social()
        except Exception:  # YouTube and X must never keep the ranking from publishing
            report = traceback.format_exc()
            for secret in (os.environ.get("GOOGLE_API_KEY"), os.environ.get("X_BEARER_TOKEN")):
                if secret:
                    report = report.replace(secret, "***")
            print("YouTube and X lookups failed; the site is built without new ones:\n" + report, file=sys.stderr)
    if step in ("all", "build"):
        build()
