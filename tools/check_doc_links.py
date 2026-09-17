#!/usr/bin/env python3
"""Check the local inline Markdown links and heading anchors used in our docs."""

from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]


def prose(path):
    return re.sub(r"^```.*?^```[^\n]*", "", path.read_text(), flags=re.M | re.S)


def anchors(path):
    found = set()
    for heading in re.findall(r"^#{1,6}\s+(.+)", prose(path), flags=re.M):
        slug = re.sub(r"[^\w\- ]", "", heading.lower()).replace(" ", "-")
        anchor = slug
        suffix = 0
        while anchor in found:
            suffix += 1
            anchor = f"{slug}-{suffix}"
        found.add(anchor)
    return found


errors = []
count = 0
for source in sorted(ROOT.rglob("*.md")):
    if any(part.startswith((".", "_")) for part in source.relative_to(ROOT).parts):
        continue
    for link in re.findall(r"\]\(([^\s)]+)\)", prose(source)):
        url = urlsplit(link)
        if url.scheme or url.netloc:
            continue
        count += 1
        target = (source.parent / unquote(url.path)).resolve() if url.path else source
        problem = None
        if not target.exists():
            problem = "missing path"
        elif url.fragment and target.suffix == ".md":
            if unquote(url.fragment) not in anchors(target):
                problem = "missing heading"
        if problem:
            errors.append(f"{source.relative_to(ROOT)}: {link}: {problem}")

if errors:
    print("\n".join(errors), file=sys.stderr)
    sys.exit(1)
print(f"Checked {count} local documentation links.")
