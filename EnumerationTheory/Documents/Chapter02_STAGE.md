# Chapter 2 Lean stage manifest

Updated: 2026-07-26

## Organized module map

```text
Lean/
├── Chapter02.lean
└── Chapter02/
    ├── Common.lean
    ├── Core.lean
    ├── AllSections.lean
    ├── HostKraStage.lean
    ├── AllModules.lean
    ├── Section01.lean … Section06.lean
    ├── Ergodic/          23 leaves + All.lean
    ├── Recurrence/       21 leaves + All.lean
    ├── Spectral/         52 leaves + All.lean
    ├── HostKra/          78 leaves + All.lean
    ├── HallPetresco/     59 leaves + All.lean
    ├── Dynamics/         15 leaves + All.lean
    └── README.md
```

All 248 helper modules are now under mathematical support directories. Every
support directory has an `All.lean` importing all of its leaves. The migration
rewrote downstream imports and the repository audit found no missing modules.

## Entry points

| Module | Purpose | Proof boundary |
|---|---|---|
| `Chapter02` | Release entry: all sections plus curated core | One imported BHK axiom risk |
| `Chapter02.AllSections` | Sections 1–6 | One imported BHK axiom risk |
| `Chapter02.Core` | Reusable completed core | No `sorry` or imported risk |
| `Chapter02.HostKraStage` | Host–Kra/Hall–Petresco construction stage | No `sorry` or imported risk |
| `Chapter02.AllModules` | Administrative aggregate of every Chapter02 module | Check by its six area aggregates |

`AllModules` has a 307-file dependency closure, above the checker's 300-file
single-target limit. Its complete content was therefore checked through the
six disjoint area aggregates together with `AllSections` and `Core`.

## Exact remaining theorem boundary

The original multiple-Khintchine axiom elimination is not yet complete. There
is exactly one declaration and one Chapter02 call:

```text
share/Lean/BHKMultipleKhintchine.lean:27
  axiom MathCopilotPrior.bergelsonHostKra_multipleKhintchine

Lean/Chapter02/Section02.lean:215
  the unique call
```

No replacement axiom, weakened statement, duplicate call, or hidden import
was introduced. `Chapter02.Core` and `Chapter02.HostKraStage` do not reach the
axiom. The missing mathematics remains the general Host–Kra structure input
connecting an arbitrary ergodic system to the finite toral two-step
property-(H) models already formalized.

## Textbook sections

| Section | Lines | Main area |
|---|---:|---|
| `Section01.lean` | 1,037 | Ergodicity and elementary examples |
| `Section02.lean` | 219 | Mean ergodic theory and multiple recurrence |
| `Section03.lean` | 295 | Pointwise and Markov ergodic tools |
| `Section04.lean` | 374 | Weak mixing and statistical convergence |
| `Section05.lean` | 139 | Spectral foundations |
| `Section06.lean` | 123 | Spectral multiplicity and classification |
| **Total** | **2,187** | |

## Code volume

| Area | Lean files | Lines |
|---|---:|---:|
| Root files inside `Chapter02/` | 11 | 3,655 |
| `Ergodic/` | 24 | 11,613 |
| `Recurrence/` | 22 | 13,280 |
| `Spectral/` | 53 | 19,617 |
| `HostKra/` | 79 | 26,591 |
| `HallPetresco/` | 60 | 14,509 |
| `Dynamics/` | 16 | 2,759 |
| **`Lean/Chapter02/` total** | **265** | **92,024** |
| Top-level `Lean/Chapter02.lean` | 1 | 16 |
| **Chapter02 source total** | **266** | **92,040** |

Counts include the seven aggregate/entry files inside support areas and
exclude README, tests, checker JSON, and `.mathcopilot/` artifacts.

## Verified results

All targets below had zero errors, ordinary warnings, `sorry`, and info
diagnostics. Stdout/stderr were empty. The risk count in Sections 2–4 is the
same inherited axiom, not three distinct declarations.

| Target | Source hash | Files | Imported risks |
|---|---|---:|---:|
| `Chapter02.lean` | `c530c5efb46b1234` | 272 | 1 |
| `Chapter02.AllSections` | `3ebe0073ab102b0e` | 115 | 1 |
| `Chapter02.Core` | `c2b8be60de071f5b` | 255 | 0 |
| `Chapter02.HostKraStage` | `b1bff6787bfeb48c` | 234 | 0 |
| `Section01` | `c6c2538e5595f06a` | — | 0 |
| `Section02` | `af01db5635a2217d` | 57 | 1 |
| `Section03` | `698340efba1b3e15` | 61 | 1 |
| `Section04` | `6bd558ac7b02c41a` | 81 | 1 |
| `Section05` | `7e41aefb18895103` | 76 | 0 |
| `Section06` | `520c2df49372f540` | 100 | 0 |
| `Ergodic.All` | `234591699f97e271` | 83 | 1 |
| `Recurrence.All` | `e193f859efe1b1ba` | 105 | 0 |
| `Spectral.All` | `f1ebf5c4d6eddfcf` | 103 | 0 |
| `HostKra.All` | `27623a8c3bd1c659` | 196 | 0 |
| `HallPetresco.All` | `0587ed6eb610c308` | 236 | 0 |
| `Dynamics.All` | `f7186248e741b4b5` | 173 | 0 |

## Verification command

From `/workspace`:

```bash
python3 "/codex-home/skills/lean-proof/scripts/lean_check.py" \
  "Lean/Chapter02.lean" --project-root "." --json --timeout 180
```

Use the same command with `Lean/Chapter02/<Area>/All.lean` for each area.
Reports from this reorganization are stored under
`.mathcopilot/checks/reorganized/` and are excluded from proof-source counts.

## GitHub upload boundary

Preserve these relative paths:

```text
Lean/Chapter02.lean
Lean/Chapter02/**
Lean/Chapter00/**
Lean/Chapter01/**
Lean/MCMC/**
share/Lean/BHKMultipleKhintchine.lean
share/Lean/NLFirst_Pfd28c3cf0fb145e58f2b0f19d4e83368_Chapter02.lean
share/Documents/NLFirst_Pfd28c3cf0fb145e58f2b0f19d4e83368_Chapter02.md
Documents/Chapter02_STAGE.md
```

For the complete multi-chapter upload and current proof-status table, see
`Lean/VERIFICATION.md`.
