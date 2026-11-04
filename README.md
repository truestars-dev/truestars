# TrueStars

The GitHub repos gaining stars fastest, checked for fake stars. Live at https://truestars.dev

- **Exact daily stars** from GitHub's star-history API.
- **A fake-star check** on every repo: forks, watchers and issues that keep up with the stars, and stars that
  fade instead of stopping dead. Repos with two or more red flags are left out of the ranking.
  A flag is a reason to look closer, not proof.
- **Why it may be trending:** Hacker News posts, new releases, brand-new repos.
- **A badge** for every repo that makes the ranking, showing its best daily rank.

How the ranking and the check work: https://truestars.dev/how/

## Run it yourself

Python 3.12 and a GitHub token (`GITHUB_TOKEN`, or a logged-in `gh`). No other installs.

    python3 -I truestars.py           # collect today's data, then build the site into site/
    python3 -I truestars.py build     # rebuild the site from the saved data

`data/days/` holds each day's published ranking; that is the site's history. A GitHub Action
(`.github/workflows/daily.yml`) runs this every day and publishes `site/` with GitHub Pages.

TrueStars is independent and not affiliated with GitHub.
