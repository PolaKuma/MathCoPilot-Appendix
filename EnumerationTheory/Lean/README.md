# Lean source layout

The repository uses one stable entry point per textbook chapter. The source
root is deliberately limited to chapter entries, the textbook entry, and
documentation:

```text
Lean/
├── Chapter00.lean … Chapter09.lean
├── Textbook.lean
├── Chapter00/ … Chapter09/
├── Tests/
└── share -> ../share
```

Inside every `ChapterXX/` directory:

- `Common.lean` contains shared definitions.
- `SectionNN.lean` contains textbook-facing statements and proofs.
- `AllSections.lean` imports every section in that chapter.
- `Core.lean` imports reusable chapter support.
- support modules, when numerous, live in named mathematical subdirectories;
  each such directory has an `All.lean` aggregate.
- `README.md` documents the exact chapter map and preferred check targets.

Files under `Tests/` are compile probes, counterexample checks, and statement
audits. Generated checker JSON is stored outside the source tree under
`.mathcopilot/checks/`.

`Textbook.lean` remains the end-to-end textbook target. The individual
`ChapterXX.lean` files are the preferred targets for chapter-local validation.

## Verification snapshot

Checked on 2026-07-26 after the directory migration:

| Entry | Dependency files | Compile | Ordinary linter | Direct `sorry` | Imported proof risks |
|---|---:|---|---:|---:|---:|
| `Chapter00.lean` | 52 | pass | 0 | 0 | 0 |
| `Chapter01.lean` | 12 | pass | 0 | 0 | 0 |
| `Chapter02.lean` | 272 | pass | 0 | 0 | 1 |
| `Chapter03.lean` | 119 | pass | 0 | 0 | 0 |
| `Chapter04.lean` | 157 | pass | 0 | 0 | 1 |
| `Chapter05.lean` | 158 | pass | 0 | 63 | 64 |
| `Chapter06.lean` | 164 | pass | 0 | 44 | 108 |
| `Chapter07.lean` | 178 | pass | 0 | 132 | 240 |
| `Chapter08.lean` | 185 | pass | 0 | 29 | 269 |
| `Chapter09.lean` | 196 | pass | 0 | 56 | 325 |
| `Textbook.lean` | 214 | pass | 0 | — | 325 |

“Compile pass” does not reclassify `sorry` as a completed proof. Chapters
00, 01, 03 are fully clean at their entries. Chapter02 and Chapter04 each
have one documented external axiom risk. Chapters05–09 are organized and
compile, but remain proof-incomplete.

The migration audit resolved 1,377 local imports with zero missing modules.
Every named support directory has an `All.lean` importing every leaf module.
See [VERIFICATION.md](VERIFICATION.md) for hashes, code volume, risk boundaries,
and GitHub upload guidance.
