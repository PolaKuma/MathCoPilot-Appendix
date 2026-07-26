# Lean organization and verification manifest

Updated: 2026-07-26

## Stable public entries

- `Chapter00` through `Chapter09`: one repository-level entry per chapter.
- `ChapterXX.AllSections`: all textbook-facing sections in that chapter.
- `ChapterXX.Core`: reusable common/support surface.
- `ChapterXX.<Area>.All`: every helper module in a named support area.
- `Textbook`: end-to-end repository entry.

The only Lean files at the source root are these public entries. Compile
probes and statement audits live under `Tests/`; checker output lives under
`.mathcopilot/checks/` and is not proof source.

## Checked entries

| Target | Source hash | Files | Errors | Ordinary warnings | Direct `sorry` | Imported risks |
|---|---|---:|---:|---:|---:|---:|
| `Chapter00.lean` | `fdec3347c7a01ac9` | 52 | 0 | 0 | 0 | 0 |
| `Chapter01.lean` | `ac68c2e1e768ad88` | 12 | 0 | 0 | 0 | 0 |
| `Chapter02.lean` | `c530c5efb46b1234` | 272 | 0 | 0 | 0 | 1 |
| `Chapter03.lean` | `2ec6d3d1b308cdb2` | 119 | 0 | 0 | 0 | 0 |
| `Chapter04.lean` | `03368201f8f71eb5` | 157 | 0 | 0 | 0 | 1 |
| `Chapter05.lean` | `b5d9a734fdb0b9f4` | 158 | 0 | 0 | 63 | 64 |
| `Chapter06.lean` | `e62f525172caf6c7` | 164 | 0 | 0 | 44 | 108 |
| `Chapter07.lean` | `1b282f9caf29fcae` | 178 | 0 | 0 | 132 | 240 |
| `Chapter08.lean` | `945f8fc3d3f2f4b1` | 185 | 0 | 0 | 29 | 269 |
| `Chapter09.lean` | `2ac225b3feb01e40` | 196 | 0 | 0 | 56 | 325 |
| `Textbook.lean` | `d35dde8434348131` | 214 | 0 | 0 | — | 325 |

The `sorry` column is a direct static count in each chapter directory.
Imported-risk counts describe the complete dependency closure and therefore
accumulate in later chapters. Lean reports `sorry` declarations as warnings;
“ordinary warnings” above excludes those explicit proof-incompleteness
warnings so that linter cleanliness and proof completeness remain separate.

## External axiom boundaries

There are exactly two explicit shared axiom declarations reached by chapter
entries:

1. `share/Lean/BHKMultipleKhintchine.lean:27`, reached once from
   `Chapter02/Section02.lean:215`.
2. `share/Lean/NLFirst_Pfd28c3cf0fb145e58f2b0f19d4e83368.lean:95`,
   reached by the Chapter04 development.

Chapter02's `Core` and `HostKraStage` entries are axiom-free. The original
Chapter02 BHK elimination goal is therefore still open at one precisely
identified boundary; the reorganization did not hide or duplicate it.

## Code volume

Counts include `.lean` files inside each chapter directory and exclude tests,
checker JSON, README files, and top-level entry wrappers.

| Chapter | Lean files | Lines |
|---|---:|---:|
| Chapter00 | 32 | 13,395 |
| Chapter01 | 10 | 5,538 |
| Chapter02 | 265 | 92,024 |
| Chapter03 | 15 | 6,261 |
| Chapter04 | 54 | 15,070 |
| Chapter05 | 12 | 2,394 |
| Chapter06 | 8 | 1,194 |
| Chapter07 | 16 | 3,444 |
| Chapter08 | 9 | 1,262 |
| Chapter09 | 13 | 1,932 |

The complete `Lean/` tree contains 487 Lean files and 154,796 lines, including
23 test/probe files (2,556 lines), shared MCMC support, and entry wrappers.

## Structural audit

- Local import references checked: 1,377.
- Missing local modules: 0.
- Chapter02 support leaves covered by area aggregates: 248/248.
- All other support leaves covered by area aggregates: 85/85.
- Root-level stray checker/probe files: 0.

## GitHub upload

Preserve the relative layout of:

```text
Lean/
share/Lean/
share/Documents/
Documents/
README.md
.gitignore
```

Keep the `Lean/share -> ../share` symlink if the destination build uses the
current source root. Alternatively, configure the destination Lake project so
that the same `share.Lean.*` modules are visible without changing import names.

This workspace does not currently contain `lakefile.lean`,
`lake-manifest.json`, or `lean-toolchain`; a standalone GitHub build needs the
destination repository's Mathlib/Lake configuration in addition to the source
tree.
