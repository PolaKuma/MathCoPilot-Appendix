#!/usr/bin/env python3
"""Curate doc-gen4's generated navigation and declaration colors.

doc-gen4 renders a top-level module with no children as an empty ``details``
element whose module page is reachable only through a small ``(file)`` link.
For a documentation site this is needlessly indirect.  This post-processing
step rewrites only those empty leaf nodes as the same direct links doc-gen4
already uses for nested leaf modules.

The DG modules are then grouped under one navigation folder.  It presents
curated links to the two public results, ``Exp1.main_theorem`` and
``Exp2.main_theorem``, followed by a collapsed ``Components`` folder containing
all implementation and audit modules.

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

DG_MODULE_LINK = re.compile(
    r'<div class="nav_link"><a href="\./'
    r"(?P<module>AuditExp1Exp2|Exp[12][A-Za-z0-9_]*)"
    r'\.html">(?P<label>[^<]+)</a></div>'
)

DG_HEADER = (
    '<details class="nav_sect" open>'
    "<summary>DG</summary>"
    '<div class="nav_link">'
    '<a href="./Exp1.html#Exp1.main_theorem">'
    "DG-1 — Upwind DG error analysis"
    "</a></div>"
    '<div class="nav_link">'
    '<a href="./Exp2.html#Exp2.main_theorem">'
    "DG-2 — Gauss–Radau approximation"
    "</a></div>"
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("navbar", type=Path)
    parser.add_argument("--style", type=Path)
    args = parser.parse_args()

    original = args.navbar.read_text(encoding="utf-8")
    rewritten, leaf_count = EMPTY_LEAF.subn(
        lambda match: (
            '<div class="nav_link">'
            f'<a href="{match.group("path")}">{match.group("label")}</a>'
            "</div>"
        ),
        original,
    )

    dg_matches = list(DG_MODULE_LINK.finditer(rewritten))
    components = [
        (match.group("module"), match.group("label"))
        for match in dg_matches
        if match.group("module") not in {"Exp1", "Exp2"}
    ]
    component_html = "".join(
        '<div class="nav_link">'
        f'<a href="./{module}.html">{label}</a>'
        "</div>"
        for module, label in components
    )
    dg_navigation = (
        DG_HEADER
        + '<details class="nav_sect"><summary>Components</summary>'
        + component_html
        + "</details></details>"
    )
    dg_count = 0

    def replace_dg_module(_: re.Match[str]) -> str:
        nonlocal dg_count
        dg_count += 1
        return dg_navigation if dg_count == 1 else ""

    rewritten = DG_MODULE_LINK.sub(replace_dg_module, rewritten)
    args.navbar.write_text(rewritten, encoding="utf-8")
    print(f"Rewrote {leaf_count} empty module nodes as direct links.")
    print(
        f"Grouped {dg_count} DG module links under two public theorems "
        f"and a {len(components)}-module Components folder."
    )

    if args.style is not None:
        style = args.style.read_text(encoding="utf-8")
        style = re.sub(
            r"--structure-and-inductive-color:\s*#[0-9A-Fa-f]{6};",
            "--structure-and-inductive-color: var(--def-color);",
            style,
        )
        style = re.sub(
            r"--structure-and-inductive-color-hsl-angle:\s*\d+;",
            "--structure-and-inductive-color-hsl-angle: "
            "var(--def-color-hsl-angle);",
            style,
        )
        args.style.write_text(style, encoding="utf-8")
        print("Mapped structure and inductive styling to the definition palette.")


if __name__ == "__main__":
    main()
