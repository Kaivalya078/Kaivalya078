#!/usr/bin/env python3
"""Render the animated SVG cards for the GitHub profile README.

    python scripts/render_readme_cards.py            # render every card into cards/
    STATIC=1 python scripts/render_readme_cards.py   # render the final frame only
    python scripts/render_readme_cards.py fetch      # refresh data/contributions.json
    python scripts/render_readme_cards.py preview    # also write build/preview.html

The cards are shown through <img>, which sandboxes them: no scripts, no
external requests. So everything here is inline: one <style> block with CSS
keyframes, SMIL for motion along a path, and fonts subset to the characters
each card uses and embedded as base64 WOFF. Under prefers-reduced-motion every
animation is switched off and each card shows its final frame.

Content lives in cards.toml. Contribution data lives in data/contributions.json,
which `fetch` refreshes (the GitHub Action runs it daily).
"""

from __future__ import annotations

import base64
import datetime as dt
import html
import io
import json
import math
import os
import random
import re
import sys
import tomllib
import urllib.request
from collections import defaultdict
from pathlib import Path

from fontTools import subset
from fontTools.ttLib import TTFont

ROOT = Path(__file__).resolve().parent.parent
CONFIG = ROOT / "cards.toml"
DATA = ROOT / "data" / "contributions.json"
OUT = ROOT / "cards"
FONTS = ROOT / "assets" / "fonts"

STATIC = os.environ.get("STATIC", "") not in ("", "0", "false")
W = 900  # every full-width card is 900 units wide; the README scales it to fit

# Each card starts a little later than the one above it, so the page plays top
# to bottom. Every image runs its own clock from the moment it loads.
BASE_DELAY = {
    "hero": 0.0,
    "tile": 0.35,  # +0.12 per tile
    "repo": 0.55,  # +0.12 per repo
    "timeline": 0.9,
    "stack": 1.0,
    "activity": 1.1,
    "graph": 1.2,
}


# ---------------------------------------------------------------------------
# Fonts: measure text, then subset and embed only the glyphs a card uses
# ---------------------------------------------------------------------------


class Face:
    def __init__(self, family: str, weight: int, file: str):
        self.family, self.weight, self.path = family, weight, FONTS / file
        font = TTFont(self.path)
        self.upm = font["head"].unitsPerEm
        self.cmap = font.getBestCmap()
        self.hmtx = font["hmtx"].metrics
        self.space = self.hmtx[self.cmap[ord(" ")]][0]

    def width(self, text: str, size: float, tracking: float = 0.0) -> float:
        units = sum(self.hmtx[self.cmap[ord(c)]][0] if ord(c) in self.cmap else self.space for c in text)
        return units / self.upm * size + tracking * size * len(text)

    def woff(self, chars: set[str]) -> str:
        opts = subset.Options()
        opts.flavor = "woff"
        opts.layout_features = ["kern", "liga", "calt", "tnum"]
        opts.name_IDs = []
        opts.notdef_outline = True
        font = TTFont(self.path)
        sub = subset.Subsetter(opts)
        sub.populate(text="".join(sorted(chars | {" "})))
        sub.subset(font)
        buf = io.BytesIO()
        font.flavor = "woff"
        font.save(buf)
        return base64.b64encode(buf.getvalue()).decode()


SANS, SANS_B = "KP Sans", "KP Sans"
MONO = "KP Mono"
FACES = {
    ("sans", 400): Face(SANS, 400, "Inter-Regular.ttf"),
    ("sans", 600): Face(SANS, 600, "Inter-SemiBold.ttf"),
    ("mono", 400): Face(MONO, 400, "JetBrainsMono-Regular.ttf"),
    ("mono", 500): Face(MONO, 500, "JetBrainsMono-Medium.ttf"),
}


def esc(s: str) -> str:
    return html.escape(str(s), quote=True)


def wrap(text: str, face: Face, size: float, width: float) -> list[str]:
    lines, line = [], ""
    for word in text.split():
        trial = f"{line} {word}".strip()
        if line and face.width(trial, size) > width:
            lines.append(line)
            line = word
        else:
            line = trial
    if line:
        lines.append(line)
    return lines


def mix(a: str, b: str, t: float) -> str:
    """Blend hex colour a toward hex colour b by t."""
    pa = [int(a[i : i + 2], 16) for i in (1, 3, 5)]
    pb = [int(b[i : i + 2], 16) for i in (1, 3, 5)]
    return "#" + "".join(f"{round(x + (y - x) * t):02x}" for x, y in zip(pa, pb))


# ---------------------------------------------------------------------------
# Card: collects elements, tracks glyphs per face, writes the SVG
# ---------------------------------------------------------------------------

CSS_MOTION = """
.a{animation-duration:.6s;animation-timing-function:cubic-bezier(.22,.61,.36,1);animation-fill-mode:both}
.fade{animation-name:fade}.rise{animation-name:rise}.draw{animation-name:draw;animation-duration:1s}
.pop{animation-name:pop;animation-duration:.35s;transform-box:fill-box;transform-origin:center}
.grow{animation-name:grow;animation-duration:.8s;transform-box:fill-box;transform-origin:50% 100%}
.wipe{animation-name:wipe;animation-duration:.9s;transform-box:fill-box;transform-origin:0 50%}
.frame{opacity:0;animation-name:on;animation-timing-function:step-end;animation-fill-mode:none}
.hold{animation-name:off;animation-timing-function:step-end;animation-fill-mode:none}
.bob{animation:bob 7s ease-in-out 2.4s infinite}
@keyframes fade{from{opacity:0}}
@keyframes rise{from{opacity:0;transform:translateY(6px)}}
@keyframes draw{from{stroke-dashoffset:1}}
@keyframes pop{from{opacity:0;transform:scale(.3)}}
@keyframes grow{from{transform:scaleY(0)}}
@keyframes wipe{from{transform:scaleX(0)}}
@keyframes on{from,to{opacity:1}}
@keyframes off{from,to{opacity:0}}
@keyframes bob{0%,100%{transform:translate(0,0)}50%{transform:translate(-3px,2px)}}
@media (prefers-reduced-motion:reduce){*{animation:none!important}.motion{display:none!important}}
"""


class Card:
    def __init__(self, name: str, width: float, height: float, theme: dict, base: float, title: str):
        self.name, self.w, self.h, self.t, self.base, self.title = name, width, height, theme, base, title
        self.parts: list[str] = []
        self.defs: list[str] = []
        self.chars: dict[tuple, set[str]] = defaultdict(set)

    # -- animation helpers ----------------------------------------------------
    def anim(self, kind: str, delay: float, dur: float | None = None) -> str:
        """class and style attributes for an element that animates in."""
        if STATIC:
            return ""
        style = f"animation-delay:{self.base + delay:.2f}s"
        if dur is not None:
            style += f";animation-duration:{dur:.2f}s"
        return f' class="a {kind}" style="{style}"'

    # -- drawing --------------------------------------------------------------
    def add(self, svg: str):
        self.parts.append(svg)

    def text(self, x, y, s, *, font="sans", weight=400, size=14, fill=None, anchor="start",
             tracking=0.0, upper=False, attrs="", raw_class=""):
        s = s.upper() if upper else s
        self.chars[(font, weight)].update(s)
        fam = MONO if font == "mono" else SANS
        ls = f' letter-spacing="{tracking:.2f}em"' if tracking else ""
        cls = f' class="{raw_class}"' if raw_class else ""
        self.add(
            f'<text x="{x:.1f}" y="{y:.1f}" font-family="{fam}" font-weight="{weight}" font-size="{size}"'
            f' fill="{fill or self.t["ink"]}" text-anchor="{anchor}"{ls}{cls}{attrs}>{esc(s)}</text>'
        )

    def label(self, x, y, s, delay=0.0, fill=None, anchor="start"):
        """Mono, uppercase, tracked: the site's .detail__label."""
        self.text(x, y, s, font="mono", size=11.5, fill=fill or self.t["ink_3"], tracking=0.08,
                  upper=True, anchor=anchor, attrs=self.anim("fade", delay))

    def counter(self, x, y, value: str, *, delay=0.0, size=26, font="mono", weight=500, fill=None, anchor="start"):
        """Counts a number up from zero, then holds the real value.

        Built from text frames that each show for one slot (CSS step animations),
        so no script is needed. The final value is a plain <text> that is hidden
        only until the count finishes: with motion off it is simply there.
        """
        m = re.search(r"\d[\d,]*\.?\d*", value)
        steps, slot = 10, 0.07
        if m and not STATIC:
            num = m.group(0)
            decimals = len(num.split(".")[1]) if "." in num else 0
            target = float(num.replace(",", ""))
            for i in range(steps):
                v = target * (1 - (1 - (i + 1) / (steps + 1)) ** 3)
                shown = f"{v:,.{decimals}f}" if "," in num else f"{v:.{decimals}f}"
                frame = value[: m.start()] + shown + value[m.end() :]
                start = self.base + delay + i * slot
                self.text(x, y, frame, font=font, weight=weight, size=size, fill=fill, anchor=anchor,
                          raw_class="frame motion",
                          attrs=f' style="animation-delay:{start:.2f}s;animation-duration:{slot:.2f}s"')
            end = self.base + delay + steps * slot
            self.text(x, y, value, font=font, weight=weight, size=size, fill=fill, anchor=anchor,
                      raw_class="hold", attrs=f' style="animation-duration:{end:.2f}s"')
        else:
            self.text(x, y, value, font=font, weight=weight, size=size, fill=fill, anchor=anchor)

    # -- output ---------------------------------------------------------------
    def fonts_css(self) -> str:
        rules = []
        for (font, weight), chars in sorted(self.chars.items()):
            face = FACES[(font, weight)]
            rules.append(
                f"@font-face{{font-family:'{face.family}';font-weight:{weight};"
                f"src:url(data:font/woff;base64,{face.woff(chars)}) format('woff')}}"
            )
        return "".join(rules)

    def background(self) -> str:
        t = self.t
        return (
            f'<defs><pattern id="g" width="12" height="12" patternUnits="userSpaceOnUse">'
            f'<path d="M12 0H0V12" fill="none" stroke="{t["grid"]}" stroke-width="1"/></pattern>{"".join(self.defs)}</defs>'
            f'<rect x=".5" y=".5" width="{self.w - 1}" height="{self.h - 1}" rx="6" fill="{t["paper"]}"/>'
            f'<rect x=".5" y=".5" width="{self.w - 1}" height="{self.h - 1}" rx="6" fill="url(#g)"/>'
            f'<rect x=".5" y=".5" width="{self.w - 1}" height="{self.h - 1}" rx="6" fill="none" stroke="{t["rule"]}"/>'
        )

    def svg(self) -> str:
        style = self.fonts_css() + ("" if STATIC else CSS_MOTION)
        style += "text{font-variant-numeric:tabular-nums}"
        return (
            f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.w}" height="{self.h}" '
            f'viewBox="0 0 {self.w} {self.h}" role="img" aria-label="{esc(self.title)}">'
            f"<title>{esc(self.title)}</title><style>{style}</style>"
            f"{self.background()}{''.join(self.parts)}</svg>"
        )

    def save(self):
        OUT.mkdir(exist_ok=True)
        (OUT / f"{self.name}.svg").write_text(self.svg(), encoding="utf-8")
        return self.name


# ---------------------------------------------------------------------------
# Contribution data
# ---------------------------------------------------------------------------


def load_data() -> dict:
    if not DATA.exists():
        sys.exit(f"{DATA} not found. Run `python {Path(__file__).name} fetch` first.")
    return json.loads(DATA.read_text())


def daily_counts(data: dict) -> tuple[dict[dt.date, int], dt.date]:
    counts = {dt.date.fromisoformat(d["date"]): d["count"] for d in data["days"]}
    today = dt.date.fromisoformat(data["fetched_at"][:10])
    return {d: c for d, c in counts.items() if d <= today}, today


def stats(counts: dict[dt.date, int], today: dt.date) -> dict:
    year_ago = today - dt.timedelta(days=364)
    last_year = {d: c for d, c in counts.items() if d >= year_ago}

    # Current streak: consecutive active days ending today, or yesterday if
    # today has nothing yet (the day is not over).
    day = today if counts.get(today, 0) else today - dt.timedelta(days=1)
    current = 0
    while counts.get(day, 0) > 0:
        current += 1
        day -= dt.timedelta(days=1)

    longest = run = 0
    for d in sorted(counts):
        run = run + 1 if counts[d] > 0 and counts.get(d - dt.timedelta(days=1), 0) > 0 else (1 if counts[d] else 0)
        longest = max(longest, run)

    busiest = max(last_year.items(), key=lambda kv: (kv[1], kv[0]), default=(today, 0))
    months = []
    y, m = today.year, today.month
    for _ in range(12):
        total = sum(c for d, c in counts.items() if d.year == y and d.month == m)
        months.append((dt.date(y, m, 1), total))
        y, m = (y, m - 1) if m > 1 else (y - 1, 12)
    months.reverse()
    return {
        "current": current,
        "longest": longest,
        "active": sum(1 for c in last_year.values() if c > 0),
        "total": sum(last_year.values()),
        "busiest": busiest,
        "months": months,
    }


GRAPHQL = """
query($login:String!,$from:DateTime!,$to:DateTime!){
  user(login:$login){
    createdAt
    contributionsCollection(from:$from,to:$to){
      contributionCalendar{weeks{contributionDays{date contributionCount}}}
    }
  }
}"""


def graphql(token: str, query: str, variables: dict) -> dict:
    req = urllib.request.Request(
        "https://api.github.com/graphql",
        data=json.dumps({"query": query, "variables": variables}).encode(),
        headers={"Authorization": f"bearer {token}", "User-Agent": "readme-cards"},
    )
    with urllib.request.urlopen(req, timeout=30) as r:
        body = json.loads(r.read())
    if body.get("errors"):
        raise RuntimeError(body["errors"])
    return body["data"]


def scrape_year(user: str, year: int, today: dt.date) -> dict[str, int]:
    """Fallback without a token: the public contribution calendar HTML."""
    url = f"https://github.com/users/{user}/contributions?from={year}-01-01&to={year}-12-31"
    req = urllib.request.Request(url, headers={"User-Agent": "readme-cards"})
    with urllib.request.urlopen(req, timeout=30) as r:
        page = r.read().decode()
    ids = dict(re.findall(r'data-date="(\d{4}-\d\d-\d\d)"[^>]*id="([^"]+)"', page))
    ids.update({d: i for i, d in re.findall(r'id="([^"]+)"[^>]*data-date="(\d{4}-\d\d-\d\d)"', page)})
    tips = {i: t for i, t in re.findall(r'<tool-tip[^>]*for="([^"]+)"[^>]*>([^<]*)</tool-tip>', page)}
    out = {}
    for date, cid in ids.items():
        m = re.match(r"\s*(\d+) contribution", tips.get(cid, ""))
        out[date] = int(m.group(1)) if m else 0
    return out


def fetch(cfg: dict):
    user = cfg["user"]
    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    now = dt.datetime.now(dt.timezone.utc)
    days: dict[str, int] = {}
    repos: dict[str, dict] = {}

    if token:
        first = graphql(token, GRAPHQL, {"login": user, "from": now.replace(month=1, day=1).isoformat(), "to": now.isoformat()})
        start_year = int(first["user"]["createdAt"][:4])
        for year in range(start_year, now.year + 1):
            frm = dt.datetime(year, 1, 1, tzinfo=dt.timezone.utc)
            to = min(dt.datetime(year, 12, 31, 23, 59, 59, tzinfo=dt.timezone.utc), now)
            d = graphql(token, GRAPHQL, {"login": user, "from": frm.isoformat(), "to": to.isoformat()})
            for week in d["user"]["contributionsCollection"]["contributionCalendar"]["weeks"]:
                for day in week["contributionDays"]:
                    days[day["date"]] = day["contributionCount"]
        fields = " ".join(
            f'r{i}:repository(owner:"{r["slug"].split("/")[0]}",name:"{r["slug"].split("/")[1]}")'
            "{stargazerCount forkCount primaryLanguage{name color}}"
            for i, r in enumerate(cfg.get("repos", []))
        )
        if fields:
            data = graphql(token, "query{" + fields + "}", {})
            for i, r in enumerate(cfg["repos"]):
                info = data.get(f"r{i}")
                if info:
                    lang = info["primaryLanguage"] or {}
                    repos[r["slug"]] = {"stars": info["stargazerCount"], "forks": info["forkCount"],
                                        "language": lang.get("name"), "color": lang.get("color")}
    else:
        print("No GH_TOKEN/GITHUB_TOKEN set: scraping the public calendar (last 3 years, no repo stats).")
        for year in range(now.year - 2, now.year + 1):
            days.update(scrape_year(user, year, now.date()))

    DATA.parent.mkdir(exist_ok=True)
    DATA.write_text(json.dumps({
        "user": user,
        "fetched_at": now.isoformat(timespec="seconds"),
        "days": [{"date": d, "count": c} for d, c in sorted(days.items())],
        "repos": repos,
    }, indent=1) + "\n")
    print(f"Wrote {DATA.relative_to(ROOT)}: {len(days)} days, {sum(days.values())} contributions.")


# ---------------------------------------------------------------------------
# Hero
# ---------------------------------------------------------------------------


def koi_cells(t: dict, cols: int, rows: int, cw: float, ch: float):
    """Sample a koi on a cell grid, in the style of the site's ascii-animals pond.

    Returns (row, col, kind, colour, glyph): kind "solid" is a block of colour
    with a glyph on it; "glyph" is a bare glyph for soft edges and fins.
    """
    rnd = random.Random(7)
    wpx, hpx = cols * cw, rows * ch
    # Spine from head (up right, like the site's fish) to tail, with an S-bend.
    def spine(s):
        x = wpx * (0.88 - 0.74 * s)
        y = hpx * (0.30 + 0.42 * s) + math.sin(s * math.pi * 1.3) * hpx * 0.07
        return x, y

    pts = [spine(i / 240) for i in range(241)]
    half = 33.0

    def body_w(s):
        if s > 0.76:
            return 0
        head = math.sqrt(min(s / 0.11, 1))
        taper = math.cos(min(max(s - 0.26, 0) / 0.5, 1) * math.pi / 2) * 0.72 + 0.28
        return half * head * taper

    # Red patches: a few soft blobs along the back plus a head cap.
    blobs = [(0.12, 0.0, 0.07), (0.33, 0.3, 0.09), (0.5, -0.25, 0.07), (0.64, 0.2, 0.05)]
    pal = {k: t[k] for k in ("koi_red", "koi_cream", "koi_orange", "koi_slate")}
    ramp = ".:-=+*"
    out = []
    for r in range(rows):
        for c in range(cols):
            px, py = (c + 0.5) * cw, (r + 0.5) * ch
            best = min(range(len(pts)), key=lambda i: (pts[i][0] - px) ** 2 + (pts[i][1] - py) ** 2)
            s = best / 240
            sx, sy = pts[best]
            d = math.hypot(px - sx, py - sy)
            # signed side of the spine (for fins and patches)
            nx, ny = pts[min(best + 1, 240)][0] - pts[max(best - 1, 0)][0], pts[min(best + 1, 240)][1] - pts[max(best - 1, 0)][1]
            side = 1 if (px - sx) * ny - (py - sy) * nx > 0 else -1
            w = body_w(s)
            if w and d <= w:
                v = d / w * side  # -1..1 across the body
                colour = pal["koi_cream"]
                for bs, bv, br in blobs:
                    if ((s - bs) / br) ** 2 + ((v - bv) / 0.75) ** 2 < 1 + rnd.uniform(-0.25, 0.15):
                        colour = pal["koi_red"]
                if colour == pal["koi_cream"] and rnd.random() < 0.06:
                    colour = pal["koi_orange"]
                if s < 0.07 and abs(v) > 0.35 and abs(v) < 0.75 and r % 2 == 0 and abs(s - 0.045) < 0.02:
                    out.append((r, c, "solid", "#1b1c22", "o"))
                    continue
                shade = abs(v) ** 2
                glyph = ramp[min(int(shade * len(ramp) + rnd.random() * 1.4), len(ramp) - 1)]
                out.append((r, c, "solid", colour, glyph))
            elif s >= 0.74:
                # forked tail fin, see-through like the site's INK_GLASS
                f = (s - 0.74) / 0.26
                spread = half * (0.32 + 0.95 * f)
                if best < 238 and d <= spread and not (f > 0.7 and d < spread * (f - 0.7) / 0.3 * 0.6):
                    out.append((r, c, "glass", pal["koi_slate"], rnd.choice("~-=")))
            elif 0.17 < s < 0.33 and w < d < w + half * 0.85 * math.sin((s - 0.17) / 0.16 * math.pi):
                out.append((r, c, "glass", pal["koi_slate"], rnd.choice("~-")))
            elif 0.52 < s < 0.62 and side < 0 and w < d < w + half * 0.45 * math.sin((s - 0.52) / 0.1 * math.pi):
                out.append((r, c, "glass", pal["koi_slate"], "~"))
            elif w and d <= w + cw * 0.8:
                out.append((r, c, "glyph", pal["koi_cream"], rnd.choice("·.'")))
    return out


def portrait_cells(t: dict, path: Path, cols: int, rows: int):
    from PIL import Image, ImageOps

    img = ImageOps.grayscale(Image.open(path))
    img = ImageOps.autocontrast(img).resize((cols, rows))
    ramp = " .:-=+*#%@"
    out = []
    for r in range(rows):
        for c in range(cols):
            lum = img.getpixel((c, r)) / 255
            g = ramp[min(int(lum * len(ramp)), len(ramp) - 1)]
            if g != " ":
                out.append((r, c, "glyph", mix(t["paper"], t["ink"], 0.25 + 0.75 * lum), g))
    return out


def render_hero(cfg: dict) -> str:
    t, h = cfg["theme"], cfg["hero"]
    card = Card("hero", W, 250, t, BASE_DELAY["hero"], f'{h["name"]}: {h["meta"]}')
    x = 40

    card.label(x, 58, h["meta"], delay=0.05)

    # Name: decrypts in, like the site's sidebar name (DecryptedText).
    name, size, y = h["name"], 44, 116
    if not STATIC:
        rnd = random.Random(3)
        noise = "░▒▓█#*+=-:"
        frames, slot = 9, 0.075
        for i in range(frames):
            revealed = int(len(name) * (i + 1) / (frames + 1))
            s = "".join(ch if (j < revealed or ch == " ") else rnd.choice(noise) for j, ch in enumerate(name))
            card.text(x, y, s, font="mono", size=size, raw_class="frame motion",
                      attrs=f' style="animation-delay:{0.1 + i * slot:.2f}s;animation-duration:{slot:.3f}s"')
        card.text(x, y, name, font="mono", size=size, tracking=-0.01, raw_class="hold",
                  attrs=f' style="animation-duration:{0.1 + frames * slot:.2f}s"')
    else:
        card.text(x, y, name, font="mono", size=size, tracking=-0.01)

    face = FACES[("sans", 400)]
    for i, line in enumerate(wrap(h["line"], face, 16, 430)):
        card.text(x, 154 + i * 24, line, size=16, fill=t["ink_2"], attrs=card.anim("rise", 0.85 + i * 0.08))

    # The site's nav marker: an accent disc, then the link in mono.
    card.add(f'<circle cx="{x + 5}" cy="210" r="5" fill="{t["accent"]}"{card.anim("pop", 1.15)}/>')
    card.text(x + 18, 214, h["link"], font="mono", size=13, fill=t["ink_2"], attrs=card.anim("fade", 1.2))

    # Portrait on the right, printed in row by row.
    portrait = h.get("portrait", "koi")
    if portrait:
        cols, rows, cw, ch = 46, 22, 8.0, 10.0
        ox, oy = W - 40 - cols * cw, (card.h - rows * ch) / 2
        cells = koi_cells(t, cols, rows, cw, ch) if portrait == "koi" else portrait_cells(t, ROOT / portrait, cols, rows)
        by_row = defaultdict(list)
        for cell in cells:
            by_row[cell[0]].append(cell)
        g = [f'<g class="{"" if STATIC else "bob"}"><g transform="translate({ox:.1f},{oy:.1f})">']
        for r in sorted(by_row):
            row = sorted(by_row[r], key=lambda c: c[1])
            parts = []
            # merge runs of same-coloured solid cells into one rect
            run = None
            for _, c, kind, colour, _g in row + [(r, 10**6, "end", "", "")]:
                if kind in ("solid", "glass") and run and run[1] == colour and run[3] == kind and run[0] + run[2] == c:
                    run[2] += 1
                    continue
                if run:
                    op = ' fill-opacity=".22"' if run[3] == "glass" else ""
                    parts.append(f'<rect x="{run[0] * cw:.1f}" y="{r * ch:.1f}" width="{run[2] * cw:.1f}" height="{ch:.1f}" fill="{run[1]}"{op}/>')
                run = [c, colour, 1, kind] if kind in ("solid", "glass") else None
            glyphs = defaultdict(list)
            for _, c, kind, colour, gl in row:
                ink = {"solid": mix(colour, t["paper"], 0.38), "glass": mix(colour, t["ink"], 0.25)}.get(kind, colour)
                glyphs[ink].append((c, gl))
            for ink, items in glyphs.items():
                xs = " ".join(f"{c * cw + cw / 2:.1f}" for c, _ in items)
                s = "".join(gl for _, gl in items)
                card.chars[("mono", 400)].update(s)
                parts.append(f'<text x="{xs}" y="{r * ch + ch * 0.78:.1f}" font-family="{MONO}" font-size="10" '
                             f'text-anchor="middle" fill="{ink}">{esc(s)}</text>')
            g.append(f'<g{card.anim("fade", 0.3 + r * 0.045, 0.25)}>{"".join(parts)}</g>')
        g.append("</g></g>")
        card.add("".join(g))
    return card.save()


# ---------------------------------------------------------------------------
# Tiles
# ---------------------------------------------------------------------------


def render_tiles(cfg: dict) -> list[str]:
    t = cfg["theme"]
    names = []
    for i, tile in enumerate(cfg.get("tiles", [])[:3]):
        card = Card(f"tile-{i + 1}", 292, 150, t, BASE_DELAY["tile"] + i * 0.12, f'{tile["label"]}: {tile["title"]}')
        card.label(24, 38, f'{i + 1:02d} · {tile["label"]}', delay=0.0)
        card.text(24, 76, tile["title"], weight=600, size=20, attrs=card.anim("rise", 0.1))
        for j, line in enumerate(wrap(tile["text"], FACES[("sans", 400)], 13, 232)[:2]):
            card.text(24, 102 + j * 19, line, size=13, fill=t["ink_2"], attrs=card.anim("rise", 0.18 + j * 0.05))
        card.add(f'<line x1="24" y1="134" x2="72" y2="134" stroke="{t["accent"]}" stroke-width="1.5"{card.anim("wipe", 0.3)}/>')
        card.text(268, 40, "↗", size=15, fill=t["ink_3"], anchor="end", attrs=card.anim("fade", 0.35))
        names.append(card.save())
    return names


# ---------------------------------------------------------------------------
# Repo cards and their drawings
# ---------------------------------------------------------------------------


DEFAULT_PIPELINE = [["query"], ["retrieve"], ["rerank"], ["answer"]]


def draw_pipeline(card: Card, x0: float, y0: float, w: float, h: float, rows=None):
    t = card.t
    face = FACES[("mono", 400)]
    rows = rows or DEFAULT_PIPELINE
    n = len(rows)
    bh, gap = 24, (h - n * 24) / max(n - 1, 1)
    cx = x0 + w / 2
    boxes = []
    for r, names in enumerate(rows):
        y = y0 + r * (bh + gap)
        widths = [max(100 if len(names) > 1 else 130, face.width(nm, 11.5) + 28) for nm in names]
        span = sum(widths) + (len(names) - 1) * 18
        row_boxes = []
        bx = cx - span / 2 - 18
        for k, label in enumerate(names):
            bw = widths[k]
            bx += (widths[k - 1] if k else 0) + 18
            final = r == len(rows) - 1
            stroke = t["accent"] if final else t["rule_strong"]
            card.add(f'<rect x="{bx:.1f}" y="{y:.1f}" width="{bw:.1f}" height="{bh}" rx="5" fill="{t["raised"]}" '
                     f'stroke="{stroke}"{card.anim("fade", 0.25 + r * 0.12)}/>')
            card.text(bx + bw / 2, y + 16, label, font="mono", size=11.5, fill=t["ink"] if final else t["ink_2"],
                      anchor="middle", attrs=card.anim("fade", 0.3 + r * 0.12))
            row_boxes.append((bx + bw / 2, y))
        boxes.append(row_boxes)
    # connectors, drawn in after the boxes
    for r in range(len(rows) - 1):
        for (ax, ay) in boxes[r]:
            for (bx, by) in boxes[r + 1]:
                card.add(f'<path d="M{ax:.1f} {ay + bh:.1f} C{ax:.1f} {ay + bh + gap / 2:.1f} {bx:.1f} {by - gap / 2:.1f} {bx:.1f} {by:.1f}" '
                         f'fill="none" stroke="{t["rule_strong"]}" pathLength="1" stroke-dasharray="1"{card.anim("draw", 0.45 + r * 0.12, 0.4)}/>')
    # a query travelling through the pipeline, looping quietly
    if not STATIC:
        # route through the last box of each row (the main retrieval path)
        pts = [(row[-1][0], row[-1][1]) for row in boxes]
        path = f"M{pts[0][0]:.1f} {pts[0][1] + bh:.1f}"
        for (ax, ay), (bx, by) in zip(pts, pts[1:]):
            mid = ay + bh + gap / 2
            path += f" V{mid:.1f} H{bx:.1f} V{by:.1f}"
        begin = card.base + 1.3
        card.add(f'<circle r="3" fill="{t["accent"]}" class="motion" opacity="0">'
                 f'<set attributeName="opacity" to="1" begin="{begin:.2f}s"/>'
                 f'<animateMotion path="{path}" dur="3.2s" begin="{begin:.2f}s" repeatCount="indefinite" '
                 f'keyPoints="0;1;1" keyTimes="0;0.6;1" calcMode="linear"/></circle>')


def draw_laps(card: Card, x0: float, y0: float, w: float, h: float):
    """An illustrative pace trace: actual lap times against the model's prediction."""
    t = card.t
    rnd = random.Random(11)
    n, pit = 44, 19
    actual, pred = [], []
    for i in range(n):
        stint = i if i < pit else i - pit
        base = 0.62 - stint * 0.006 + (0.0 if i < pit else -0.05) - i * 0.0035
        p = base + stint * stint * 0.00055
        pred.append(p)
        actual.append(p + rnd.gauss(0, 0.022) + (0.28 if i == pit else 0))
    lo, hi = min(pred + actual) - 0.04, max(pred + actual) + 0.04
    top = y0 + 22
    ph = h - 40

    def pt(i, v):
        return x0 + i / (n - 1) * w, top + (1 - (v - lo) / (hi - lo)) * ph

    card.label(x0, y0 + 8, "Lap time · actual vs model", delay=0.2)
    card.text(x0 + w, y0 + 8, "illustrative", font="mono", size=10.5, fill=t["ink_3"], anchor="end",
              attrs=card.anim("fade", 0.2))
    for k in range(4):
        gy = top + k * ph / 3
        card.add(f'<line x1="{x0}" y1="{gy:.1f}" x2="{x0 + w}" y2="{gy:.1f}" stroke="{t["rule"]}"{card.anim("fade", 0.25)}/>')
    px, _ = pt(pit, 0)
    card.add(f'<line x1="{px:.1f}" y1="{top:.1f}" x2="{px:.1f}" y2="{top + ph:.1f}" stroke="{t["rule_strong"]}" stroke-dasharray="3 3"{card.anim("fade", 0.9)}/>')
    card.text(px + 6, top + 12, "PIT", font="mono", size=10.5, fill=t["ink_3"], tracking=0.08, attrs=card.anim("fade", 0.95))
    a = " ".join(f"{x:.1f},{y:.1f}" for x, y in (pt(i, v) for i, v in enumerate(actual)))
    p = " ".join(f"{x:.1f},{y:.1f}" for x, y in (pt(i, v) for i, v in enumerate(pred)))
    card.add(f'<polyline points="{a}" fill="none" stroke="{t["ink_2"]}" stroke-width="1.3" stroke-linejoin="round" '
             f'pathLength="1" stroke-dasharray="1"{card.anim("draw", 0.35, 1.3)}/>')
    card.add(f'<polyline points="{p}" fill="none" stroke="{t["accent"]}" stroke-width="1.6" stroke-linejoin="round" '
             f'pathLength="1" stroke-dasharray="1"{card.anim("draw", 0.7, 1.3)}/>')
    ly = top + ph + 16
    card.add(f'<line x1="{x0}" y1="{ly - 4}" x2="{x0 + 14}" y2="{ly - 4}" stroke="{t["ink_2"]}" stroke-width="1.3"{card.anim("fade", 1.2)}/>')
    card.text(x0 + 20, ly, "actual", font="mono", size=10.5, fill=t["ink_3"], attrs=card.anim("fade", 1.2))
    card.add(f'<line x1="{x0 + 84}" y1="{ly - 4}" x2="{x0 + 98}" y2="{ly - 4}" stroke="{t["accent"]}" stroke-width="1.6"{card.anim("fade", 1.25)}/>')
    card.text(x0 + 104, ly, "XGBoost prediction", font="mono", size=10.5, fill=t["ink_3"], attrs=card.anim("fade", 1.25))


# MediaPipe's 21 hand landmarks for the ASL letter B: four fingers up and
# together, thumb folded across the palm. Units are arbitrary; scaled below.
HAND_B = [(0, 100), (-18, 88), (-24, 72), (-14, 62), (0, 60),
          (-20, 52), (-21, 30), (-22, 16), (-23, 4),
          (-6, 50), (-6, 26), (-6, 10), (-6, -4),
          (8, 51), (9, 29), (9, 14), (9, 2),
          (21, 55), (23, 38), (24, 27), (24, 17)]
HAND_EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (0, 5), (5, 6), (6, 7), (7, 8), (5, 9), (9, 10), (10, 11),
              (11, 12), (9, 13), (13, 14), (14, 15), (15, 16), (13, 17), (0, 17), (17, 18), (18, 19), (19, 20)]


def draw_hand(card: Card, x0: float, y0: float, w: float, h: float):
    t = card.t
    scale = (h - 10) / 108
    hx = x0 + 70
    pts = [(hx + px * scale * 1.15, y0 + 8 + (py + 6) * scale) for px, py in HAND_B]
    for k, (a, b) in enumerate(HAND_EDGES):
        (ax, ay), (bx, by) = pts[a], pts[b]
        card.add(f'<line x1="{ax:.1f}" y1="{ay:.1f}" x2="{bx:.1f}" y2="{by:.1f}" stroke="{t["ink_3"]}" stroke-width="1.4" '
                 f'stroke-linecap="round" pathLength="1" stroke-dasharray="1"{card.anim("draw", 0.3 + k * 0.03, 0.3)}/>')
    tips = {4, 8, 12, 16, 20}
    for k, (px, py) in enumerate(pts):
        fill = t["accent"] if k in tips else t["koi_cream"]
        card.add(f'<circle cx="{px:.1f}" cy="{py:.1f}" r="{3.2 if k in tips else 2.6}" fill="{fill}"{card.anim("pop", 0.35 + k * 0.03)}/>')

    # what the model sees: the predicted letter and its confidence
    rx = x0 + 168
    card.label(rx, y0 + 30, "Prediction", delay=0.8)
    card.text(rx, y0 + 96, "B", font="mono", weight=500, size=58, attrs=card.anim("rise", 1.0))
    by = y0 + 128
    card.add(f'<rect x="{rx}" y="{by}" width="150" height="4" rx="2" fill="{t["rule"]}"{card.anim("fade", 1.0)}/>')
    card.add(f'<rect x="{rx}" y="{by}" width="{150 * 0.96:.1f}" height="4" rx="2" fill="{t["accent"]}"{card.anim("wipe", 1.1)}/>')
    card.text(rx, by + 22, "conf 0.96 · 3 frames held", font="mono", size=10.5, fill=t["ink_3"], attrs=card.anim("fade", 1.3))


VISUALS = {"pipeline": draw_pipeline, "laps": draw_laps, "hand": draw_hand}


def render_repos(cfg: dict, data: dict) -> list[str]:
    t = cfg["theme"]
    names = []
    sans = FACES[("sans", 400)]
    for i, repo in enumerate(cfg.get("repos", [])):
        slug_name = repo["slug"].split("/")[1].lower().replace("_", "-")
        card = Card(f"repo-{slug_name}", W, 252, t, BASE_DELAY["repo"] + i * 0.12, f'{repo["title"]}: {repo["kicker"]}')
        x = 40
        card.label(x, 46, f'{i + 1:02d} · {repo["kicker"]}', delay=0.0)
        card.text(x, 82, repo["title"], weight=600, size=24, attrs=card.anim("rise", 0.08))
        for j, line in enumerate(wrap(repo["description"], sans, 14, 440)[:3]):
            card.text(x, 110 + j * 21, line, size=14, fill=t["ink_2"], attrs=card.anim("rise", 0.14 + j * 0.05))

        # headline numbers
        sx = x
        for k, (value, label) in enumerate(repo.get("stats", [])[:3]):
            need = max(FACES[("mono", 500)].width(value, 22), FACES[("mono", 400)].width(label, 11))
            if sx + need > x + 460:
                break
            card.counter(sx, 186, value, delay=0.35 + k * 0.1, size=22)
            card.text(sx, 204, label, font="mono", size=11, fill=t["ink_3"], attrs=card.anim("fade", 0.4 + k * 0.1))
            sx += max(FACES[("mono", 500)].width(value, 22), FACES[("mono", 400)].width(label, 11)) + 36

        # stack and live repo stats along the bottom
        meta = " · ".join(repo.get("stack", []))
        info = data.get("repos", {}).get(repo["slug"])
        if repo.get("live"):
            host = re.sub(r"^https?://|/$", "", repo["live"])
            tw = FACES[("mono", 400)].width(host, 11)
            card.text(W - 40, 236, host, font="mono", size=11, fill=t["ink_2"], anchor="end", attrs=card.anim("fade", 0.6))
            card.text(W - 52 - tw, 236, "LIVE", font="mono", size=10.5, fill=t["accent"], anchor="end", tracking=0.08,
                      attrs=card.anim("fade", 0.6))
            pulse = "" if STATIC else ' class="motion"'
            card.add(f'<circle cx="{W - 52 - tw - FACES[("mono", 400)].width("LIVE", 10.5, 0.08) - 9:.1f}" cy="232.5" r="3" fill="{t["accent"]}"{card.anim("pop", 0.6)}/>')
            if not STATIC:
                card.add(f'<circle cx="{W - 52 - tw - FACES[("mono", 400)].width("LIVE", 10.5, 0.08) - 9:.1f}" cy="232.5" r="3" fill="none" '
                         f'stroke="{t["accent"]}" class="motion"><animate attributeName="r" values="3;8" dur="2.4s" begin="{card.base + 1.5:.2f}s" repeatCount="indefinite"/>'
                         f'<animate attributeName="opacity" values=".7;0" dur="2.4s" begin="{card.base + 1.5:.2f}s" repeatCount="indefinite"/></circle>')
        elif info:
            bits = [f'★ {info["stars"]}'] + ([info["language"]] if info.get("language") else [])
            right = "  ".join(bits)
            card.text(W - 40, 236, right, font="mono", size=11, fill=t["ink_3"], anchor="end", attrs=card.anim("fade", 0.6))
        card.text(x, 236, meta, font="mono", size=11, fill=t["ink_3"], attrs=card.anim("fade", 0.55))
        card.add(f'<line x1="{x}" y1="218.5" x2="{W - 40}" y2="218.5" stroke="{t["rule"]}"{card.anim("fade", 0.5)}/>')
        draw = VISUALS[repo.get("visual", "pipeline")]
        if draw is draw_pipeline:
            draw(card, 540, 24, 320, 176, repo.get("pipeline"))
        else:
            draw(card, 540, 24, 320, 176)
        names.append(card.save())
    return names


# ---------------------------------------------------------------------------
# Experience timeline and stack
# ---------------------------------------------------------------------------


def render_timeline(cfg: dict) -> str:
    t = cfg["theme"]
    roles = cfg.get("experience", [])
    card = Card("timeline", W, 170, t, BASE_DELAY["timeline"], "Experience: " + ", ".join(r["company"] for r in roles))
    card.label(40, 42, "Experience")
    ly, x0, step = 104, 46, 330
    end = x0 + step * len(roles)
    card.defs.append(f'<linearGradient id="fadeline" x1="0" x2="1"><stop offset="0" stop-color="{t["ink_3"]}"/>'
                     f'<stop offset="{(end - 40) / (W - 80):.2f}" stop-color="{t["ink_3"]}"/>'
                     f'<stop offset="1" stop-color="{t["ink_3"]}" stop-opacity="0"/></linearGradient>')
    card.add(f'<rect x="40" y="{ly - 0.5}" width="{W - 80}" height="1" fill="url(#fadeline)" opacity=".55"{card.anim("wipe", 0.1, 1.1)}/>')
    for i, role in enumerate(roles):
        nx = x0 + i * step
        latest = i == len(roles) - 1
        d = 0.3 + i * 0.25
        if latest:
            card.add(f'<circle cx="{nx}" cy="{ly}" r="5" fill="{t["accent"]}"{card.anim("pop", d)}/>')
        else:
            card.add(f'<circle cx="{nx}" cy="{ly}" r="4.5" fill="{t["paper"]}" stroke="{t["ink_2"]}" stroke-width="1.3"{card.anim("pop", d)}/>')
        card.text(nx - 6, ly - 20, role["period"], font="mono", size=11.5, fill=t["ink_3"], tracking=0.04, attrs=card.anim("fade", d + 0.05))
        card.text(nx - 6, ly + 32, role["company"], weight=600, size=16, attrs=card.anim("rise", d + 0.1))
        card.text(nx - 6, ly + 52, role["title"], size=13, fill=t["ink_2"], attrs=card.anim("rise", d + 0.15))
    return card.save()


def render_stack(cfg: dict) -> str:
    t = cfg["theme"]
    groups = cfg.get("stack", [])
    mono = FACES[("mono", 400)]
    colw, x0, chip_h, gapx, gapy = (W - 80 - 3 * 24) / 4, 40, 24, 6, 8
    layout, tallest = [], 0
    for gi, g in enumerate(groups):
        gx, cx, cy = x0 + gi * (colw + 24), 0.0, 0.0
        chips = []
        for item in g["items"]:
            cw = mono.width(item, 11.5) + 18
            if cx and cx + cw > colw:
                cx, cy = 0.0, cy + chip_h + gapy
            chips.append((gx + cx, cy, cw, item))
            cx += cw + gapx
        tallest = max(tallest, cy + chip_h)
        layout.append((gx, g["group"], chips))
    top = 76
    card = Card("stack", W, int(top + tallest + 36), t, BASE_DELAY["stack"], "Stack")
    card.label(40, 42, "Stack")
    for gi, (gx, name, chips) in enumerate(layout):
        d = 0.1 + gi * 0.12
        card.text(gx, top - 14, name, size=13, weight=600, fill=t["ink"], attrs=card.anim("fade", d))
        for k, (cx, cy, cw, item) in enumerate(chips):
            dd = d + 0.06 + k * 0.035
            card.add(f'<rect x="{cx:.1f}" y="{top + cy:.1f}" width="{cw:.1f}" height="{chip_h}" rx="5" fill="{t["raised"]}" '
                     f'stroke="{t["rule"]}"{card.anim("fade", dd)}/>')
            card.text(cx + cw / 2, top + cy + 16, item, font="mono", size=11.5, fill=t["ink_2"], anchor="middle",
                      attrs=card.anim("fade", dd))
    return card.save()


# ---------------------------------------------------------------------------
# Activity: contributions per month, streaks, active days, busiest day
# ---------------------------------------------------------------------------


def render_activity(cfg: dict, data: dict) -> str:
    t = cfg["theme"]
    counts, today = daily_counts(data)
    s = stats(counts, today)
    card = Card("activity", W, 270, t, BASE_DELAY["activity"],
                f'Activity: {s["total"]} contributions in the last year, current streak {s["current"]} days')
    card.label(40, 42, "Contributions per month")
    card.text(500, 42, f'{s["total"]:,} in the last year', font="mono", size=11.5, fill=t["ink_3"], anchor="end",
              attrs=card.anim("fade", 0.05))

    months = s["months"]
    peak = max((c for _, c in months), default=0) or 1
    best = max(range(len(months)), key=lambda i: (months[i][1], i))
    cx0, cw, base_y, ch = 40, 460 / 12, 220, 140
    for i, (month, total) in enumerate(months):
        bh = max(total / peak * ch, 2 if total else 1)
        bx = cx0 + i * cw + 6
        is_best = i == best and total > 0
        fill = t["accent"] if is_best else t["rule_strong"]
        card.add(f'<rect x="{bx:.1f}" y="{base_y - bh:.1f}" width="{cw - 12:.1f}" height="{bh:.1f}" rx="2" fill="{fill}"'
                 f'{card.anim("grow", 0.15 + i * 0.05)}/>')
        card.text(bx + (cw - 12) / 2, base_y + 18, month.strftime("%b")[:3], font="mono", size=10.5, fill=t["ink_3"],
                  anchor="middle", attrs=card.anim("fade", 0.1 + i * 0.03))
        if is_best:
            card.text(bx + (cw - 12) / 2, base_y - bh - 8, str(total), font="mono", size=11, fill=t["ink"], anchor="middle",
                      attrs=card.anim("fade", 0.85))
    card.add(f'<line x1="40" y1="{base_y + 0.5}" x2="500" y2="{base_y + 0.5}" stroke="{t["rule"]}"/>')

    # stat grid on the right, divided from the chart by a hairline
    card.add(f'<line x1="540" y1="28" x2="540" y2="242" stroke="{t["rule"]}"/>')
    bday, bcount = s["busiest"]
    cells = [
        ("Current streak", f'{s["current"]}', "days" if s["current"] != 1 else "day"),
        ("Longest streak", f'{s["longest"]}', "days" if s["longest"] != 1 else "day"),
        ("Active days", f'{s["active"]}', "of the last 365"),
        ("Busiest day", f"{bcount}", bday.strftime("%-d %b %Y") if bcount else "none yet"),
    ]
    for k, (label, value, unit) in enumerate(cells):
        gx = 572 + (k % 2) * 150
        gy = 60 + (k // 2) * 104
        card.label(gx, gy, label, delay=0.2 + k * 0.08)
        card.counter(gx, gy + 40, value, delay=0.3 + k * 0.08, size=30)
        card.text(gx, gy + 62, unit, font="mono", size=11, fill=t["ink_3"], attrs=card.anim("fade", 0.4 + k * 0.08))
    return card.save()


# ---------------------------------------------------------------------------
# Contribution graph
# ---------------------------------------------------------------------------


def render_graph(cfg: dict, data: dict) -> str:
    t = cfg["theme"]
    counts, today = daily_counts(data)
    end = today
    start = end - dt.timedelta(days=364)
    start -= dt.timedelta(days=(start.weekday() + 1) % 7)  # weeks start on Sunday, like GitHub
    weeks = ((end - start).days // 7) + 1
    year = [c for d, c in counts.items() if d >= today - dt.timedelta(days=364)]
    total = sum(year)

    # Levels: quartiles of the active days, like GitHub, in the accent colour.
    active = sorted(c for c in year if c > 0)
    q = [active[int(len(active) * f)] for f in (0.25, 0.5, 0.75)] if active else [1, 2, 3]

    def level(c):
        return 0 if c <= 0 else 1 + sum(c > x for x in q)

    colours = [t["rule"]] + [mix(t["paper"], t["accent"], f) for f in (0.3, 0.52, 0.76, 1.0)]

    size, gap = 11, 3
    step = size + gap
    gx0 = 40 + 30
    gy0 = 74
    card = Card("contributions", W, gy0 + 7 * step + 46, t, BASE_DELAY["graph"],
                f"Contribution graph: {total} contributions in the last year")
    card.label(40, 42, "Contributions")
    card.text(W - 40, 42, f"{total:,} in the last year", font="mono", size=11.5, fill=t["ink_3"], anchor="end",
              attrs=card.anim("fade", 0.05))
    for r, name in ((1, "Mon"), (3, "Wed"), (5, "Fri")):
        card.text(40, gy0 + r * step + 9, name, font="mono", size=10, fill=t["ink_3"], attrs=card.anim("fade", 0.1))
    last_month = None
    for w in range(weeks):
        wk = start + dt.timedelta(days=7 * w)
        if wk.month != last_month and wk.day <= 7 and w < weeks - 1:
            card.text(gx0 + w * step, gy0 - 10, wk.strftime("%b"), font="mono", size=10, fill=t["ink_3"],
                      attrs=card.anim("fade", 0.1 + w * 0.012))
            last_month = wk.month
        cells = []
        for r in range(7):
            day = wk + dt.timedelta(days=r)
            if day > end:
                break
            c = counts.get(day, 0)
            cells.append(f'<rect x="{gx0 + w * step}" y="{gy0 + r * step}" width="{size}" height="{size}" rx="2" '
                         f'fill="{colours[level(c)]}"><title>{c} on {day.isoformat()}</title></rect>')
        card.add(f'<g{card.anim("pop", 0.15 + w * 0.018, 0.3)}>{"".join(cells)}</g>')

    ly = gy0 + 7 * step + 22
    lx = W - 40 - 5 * step - 36
    card.text(lx - 8, ly + 9, "Less", font="mono", size=10, fill=t["ink_3"], anchor="end", attrs=card.anim("fade", 1.2))
    for k, colour in enumerate(colours):
        card.add(f'<rect x="{lx + k * step}" y="{ly}" width="{size}" height="{size}" rx="2" fill="{colour}"{card.anim("fade", 1.2)}/>')
    card.text(lx + 5 * step + 4, ly + 9, "More", font="mono", size=10, fill=t["ink_3"], attrs=card.anim("fade", 1.2))
    if data.get("sample"):
        card.text(40, ly + 9, "sample data: run the Action to load real contributions", font="mono", size=10,
                  fill=t["accent"])
    return card.save()


# ---------------------------------------------------------------------------
# Preview page (what the README will look like) and entry point
# ---------------------------------------------------------------------------


def write_readme(cfg: dict, data: dict):
    """README.md is generated too, so every link matches the card it wraps."""
    h = cfg["hero"]

    def img(name, alt, width="100%"):
        # The ?v= tag is a hash of the card, so the URL changes whenever the card
        # does and GitHub's image cache can never serve a stale version.
        import hashlib
        v = hashlib.sha1((OUT / f"{name}.svg").read_bytes()).hexdigest()[:8]
        return f'<img src="cards/{name}.svg?v={v}" width="{width}" alt="{esc(alt)}">'

    repo_names = {r["slug"]: "repo-" + r["slug"].split("/")[1].lower().replace("_", "-") for r in cfg.get("repos", [])}
    site = h.get("href") or "https://" + h["link"]
    out = [
        "<!-- Generated by scripts/render_readme_cards.py from cards.toml. Edit those, not this file. -->",
        "",
        f'<a href="{site}">{img("hero", h["name"] + ": " + h["meta"])}</a>',
        "",
        "<p>",
    ]
    for i, tile in enumerate(cfg.get("tiles", [])[:3]):
        out.append(f'  <a href="{esc(tile["href"])}">{img(f"tile-{i + 1}", tile["label"] + ": " + tile["title"], "32.5%")}</a>')
    out += ["</p>", ""]
    for r in cfg.get("repos", []):
        out += [f'<a href="{r.get("live") or "https://github.com/" + r["slug"]}">{img(repo_names[r["slug"]], r["title"] + ": " + r["description"])}</a>', ""]
    out += [
        img("timeline", "Experience: " + ", ".join(f'{e["title"]}, {e["company"]} ({e["period"]})' for e in cfg.get("experience", []))),
        "",
        img("stack", "Stack: " + "; ".join(f'{g["group"]}: {", ".join(g["items"])}' for g in cfg.get("stack", []))),
        "",
        img("activity", "Contributions per month, streaks, active days and busiest day"),
        "",
        img("contributions", "Contribution graph for the last year"),
        "",
    ]
    links = cfg.get("links", [])
    if links:
        out += ['<p align="center">', "  " + " &nbsp;·&nbsp; ".join(f'<a href="{esc(l["href"])}">{esc(l["label"])}</a>' for l in links), "</p>", ""]
    (ROOT / "README.md").write_text("\n".join(out))


def write_preview():
    readme = (ROOT / "README.md").read_text()
    body = re.sub(r'src="cards/', 'src="../cards/', readme)
    page = f"""<!doctype html><meta charset="utf-8"><title>README preview</title>
<style>body{{background:#0d1117;margin:0;padding:32px 0;font:14px system-ui;color:#c9d1d9}}
main{{max-width:896px;margin:0 auto;padding:0 32px}}img{{max-width:100%}}a{{color:#58a6ff}}p{{margin:0 0 12px}}</style>
<main>{body}</main>"""
    (ROOT / "build").mkdir(exist_ok=True)
    (ROOT / "build" / "preview.html").write_text(page)
    print("Wrote build/preview.html")


def write_sample(cfg: dict):
    """Made-up data so the cards can be previewed before the first fetch."""
    rnd = random.Random(1)
    today = dt.date.today()
    days = []
    for i in range(500, -1, -1):
        d = today - dt.timedelta(days=i)
        busy = 0.55 + 0.35 * math.sin(i / 40)
        c = 0 if rnd.random() > busy else int(rnd.expovariate(0.25)) + 1
        days.append({"date": d.isoformat(), "count": c})
    DATA.parent.mkdir(exist_ok=True)
    DATA.write_text(json.dumps({"user": cfg["user"], "sample": True,
                                "fetched_at": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
                                "days": days, "repos": {}}, indent=1) + "\n")
    print(f"Wrote sample data to {DATA.relative_to(ROOT)}")


def main():
    cfg = tomllib.loads(CONFIG.read_text())
    cmd = sys.argv[1] if len(sys.argv) > 1 else "render"
    if cmd == "fetch":
        fetch(cfg)
        return
    if cmd == "sample":
        write_sample(cfg)
        return
    data = load_data()
    rendered = [render_hero(cfg), *render_tiles(cfg), *render_repos(cfg, data), render_timeline(cfg),
                render_stack(cfg), render_activity(cfg, data), render_graph(cfg, data)]
    write_readme(cfg, data)
    for name in rendered:
        size = (OUT / f"{name}.svg").stat().st_size
        print(f"cards/{name}.svg  {size / 1024:6.1f} KB{'  (static)' if STATIC else ''}")
    if cmd == "preview":
        write_preview()


if __name__ == "__main__":
    main()
