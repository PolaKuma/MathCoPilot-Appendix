# Chapter 4

```text
Chapter04/
├── Common.lean
├── Core.lean
├── AllSections.lean
├── Section01.lean … Section06.lean
├── MeasureAlgebra/
├── Descriptive/
├── Spectral/
├── Ergodic/
└── Examples/
```

The support tree separates measure-algebra representation, descriptive and
spatial realization, spectral theory, ergodic factors, and counterexamples.
Every support directory has an `All.lean` aggregate. Use `Chapter04.Core` for
the complete reusable support surface.

Verification: `Chapter04.lean` passes with 157 dependency files and no direct
`sorry` or ordinary linter warnings. Its closure contains one documented
external axiom risk from
`share/Lean/NLFirst_Pfd28c3cf0fb145e58f2b0f19d4e83368.lean`.
See [`../VERIFICATION.md`](../VERIFICATION.md).
