# TrueStars

The GitHub repos gaining stars fastest, and why. Live at https://truestars.dev

- **Explore**, the home page: an App Store-style page of the repos with no red flags, on shelves (speeding up,
  just launched, waves, top in each language), ordered by **TrueStars Heat**, our 0-100 score of how hot a repo
  is right now and whether it keeps going. The daily ranking is at https://truestars.dev/ranking/

- **Exact daily stars** from GitHub's star-history API.
- **A fake-star check** on every repo: forks, watchers and issues that keep up with the stars, and stars that
  fade instead of stopping dead. Repos with two or more red flags are left out of the ranking.
  A flag is a reason to look closer, not proof.
- **Where each repo stands:** rising, at its peak, steady or cooling against its own best day, and a
  "Rising now" list of repos getting at least 3 times their usual daily stars.
- **Why it may be trending:** Hacker News posts, YouTube videos and releases that moved the stars, posts on X
  and Bluesky that link the repo, waves of repos that share a GitHub topic, brand-new and recent launches,
  well-known owners. Star charts mark them on the day they happened.
- **A badge** for every repo that makes the ranking, showing its best daily rank.

How Explore, Heat, the ranking and the check work: https://truestars.dev/how/

## Run it yourself

Python 3.12 and a GitHub token (`GITHUB_TOKEN`, or a logged-in `gh`). No other installs. YouTube needs
`GOOGLE_API_KEY` and X needs `X_BEARER_TOKEN`; without them those lookups are skipped. Bluesky needs no key.

    python3 -I truestars.py           # collect today's data, then build the site into site/
    python3 -I truestars.py build     # rebuild the site from the saved data

`data/days/` holds each day's published ranking; that is the site's history. A GitHub Action
(`.github/workflows/daily.yml`) runs this every day and publishes `site/` with GitHub Pages.

TrueStars is independent and not affiliated with GitHub.
