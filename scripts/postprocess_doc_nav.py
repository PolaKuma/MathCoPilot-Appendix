#!/usr/bin/env python3
"""Make leaf modules directly clickable in doc-gen4's navigation tree.

doc-gen4 renders a top-level module with no children as an empty ``details``
element whose module page is reachable only through a small ``(file)`` link.
For a documentation site this is needlessly indirect.  This post-processing
step rewrites only those empty leaf nodes as the same direct links doc-gen4
already uses for nested leaf modules.

The generated module pages, URLs, declarations, and Lean sources are unchanged.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path


EMPTY_LEAF = re.compile(
    r'<details class="nav_sect" data-path="(?P<path>[^"]+)">'
    r"<summary>(?P<label>[^<]+) "
    r'\(<a href="(?P=path)">file</a>\)</summary></details>'
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("navbar", type=Path)
    args = parser.parse_args()

    original = args.navbar.read_text(encoding="utf-8")
    rewritten, count = EMPTY_LEAF.subn(
        lambda match: (
            '<div class="nav_link">'
            f'<a href="{match.group("path")}">{match.group("label")}</a>'
            "</div>"
        ),
        original,
    )

    args.navbar.write_text(rewritten, encoding="utf-8")
    print(f"Rewrote {count} empty module nodes as direct links.")


if __name__ == "__main__":
    main()
