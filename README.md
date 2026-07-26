# MathCoPilot Lean Appendix

[![Lean CI](https://github.com/PolaKuma/MathCoPilot-Appendix/actions/workflows/lean-ci.yml/badge.svg)](https://github.com/PolaKuma/MathCoPilot-Appendix/actions/workflows/lean-ci.yml)
[![Deploy documentation](https://github.com/PolaKuma/MathCoPilot-Appendix/actions/workflows/deploy-pages.yml/badge.svg)](https://github.com/PolaKuma/MathCoPilot-Appendix/actions/workflows/deploy-pages.yml)
[![Documentation](https://img.shields.io/badge/doc--gen4-browse-0b6bcb)](https://polakuma.github.io/MathCoPilot-Appendix/docs/)
[![Lean](https://img.shields.io/badge/Lean-4.28.0-blue)](https://github.com/leanprover/lean4)

This repository releases the Lean 4 sources accompanying
[MathCoPilot: An Interactive System for Human-AI Symbiotic Paradigm of Mathematical Research](https://arxiv.org/abs/2607.14582).
It contains the formalized knowledge-base case study and the two discontinuous
Galerkin (DG) theorem developments used in the paper.

## Browse the documentation

The generated documentation uses the same
[doc-gen4](https://github.com/leanprover/doc-gen4) interface as ReasBook:

**<https://polakuma.github.io/MathCoPilot-Appendix/docs/>**

It provides a searchable module tree, rendered declarations and docstrings,
import relationships, and links back to the corresponding GitHub source.

## Source snapshot

The Lean sources are published byte-for-byte as supplied for this appendix.
Repository packaging, continuous integration, and documentation generation do
not rename, reformat, or otherwise rewrite the existing `.lean` files.

| Scope | Lean files | Physical lines | Nonblank lines |
|---|---:|---:|---:|
| `EnumerationTheory/Lean` | 487 | 154,796 | 144,599 |
| `EnumerationTheory/share/Lean` | 3 | 213 | 185 |
| `DG` | 21 | 7,873 | 7,451 |
| **Total** | **511** | **162,882** | **152,235** |

The committed integrity manifest records a SHA-256 digest for every Lean file.
Its aggregate digest is:

```text
0cc53625771977948cd03718846920f02360a9d9f674cf593191475e4149e091
```

Verify the snapshot with:

```bash
python scripts/source_integrity.py
```

## Repository layout

```text
DG/                           Two verified DG theorem developments
EnumerationTheory/Lean/       Chapter 0--9 formalization source tree
EnumerationTheory/share/Lean/ Explicit shared formalization boundaries
EnumerationTheory/Documents/  Verification and staging notes
reports/                      Machine-readable source integrity manifest
scripts/                      Reproducibility utilities
```

The directory name `EnumerationTheory` is retained as part of the frozen source
snapshot. Its `Textbook.lean` entry describes the Chapter 0--9 formalization of
*Ergodic Theory and Its Applications*.

## Reproduce the Lean build

The project is pinned to Lean 4.28.0 and matching Mathlib/doc-gen4 releases.

```bash
lake update
lake build AuditExp1Exp2 Textbook
```

On Windows, run `chcp 65001` before `lake update` if the local console still
uses a legacy code page.

The DG audit entry prints the axioms of the public theorems:

```bash
lake env lean DG/AuditExp1Exp2.lean
```

Generate the two public documentation entry closures with:

```bash
lake build Textbook:docs AuditExp1Exp2:docs
```

## Verification status

“Builds successfully” and “contains no incomplete proofs” are reported
separately.

- The public chapter entries and `Textbook.lean` are recorded as compiling
  successfully in `EnumerationTheory/Lean/VERIFICATION.md`.
- Chapters 00, 01, and 03 are clean at their public entries.
- Chapters 02 and 04 have documented external axiom boundaries.
- Chapters 05--09 compile but contain documented `sorry` declarations.
- The 21 DG files contain no `sorry` declarations and no custom `axiom`
  declarations.

See
[`EnumerationTheory/Lean/VERIFICATION.md`](EnumerationTheory/Lean/VERIFICATION.md)
for the chapter-by-chapter snapshot and exact proof-risk boundaries.

## Citation

Citation metadata is provided in [`CITATION.cff`](CITATION.cff). When
referencing a particular artifact state, cite both the release tag and its Git
commit.

## License

Released under the Apache License 2.0. See [`LICENSE`](LICENSE).
