# Chapter 0

```text
Chapter00/
├── Common.lean
├── Core.lean
├── AllSections.lean
├── Section01.lean … Section06.lean
├── Probability/
├── PerronFrobenius/
├── Renewal/
└── Ergodic/
```

The four support directories contain foundational probability constructions,
Perron--Frobenius theory, renewal theory, and ergodic-density arguments.
Each has an `All.lean` aggregate. Use `Chapter00.AllSections` for the chapter
text and `Chapter00.Core` for all reusable support.

Verification: `Chapter00.lean` passes with 52 dependency files, zero errors,
warnings, `sorry`, or imported proof risks. See
[`../VERIFICATION.md`](../VERIFICATION.md).
