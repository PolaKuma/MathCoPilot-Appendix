# Chapter 1

```text
Chapter01/
├── Common.lean
├── Core.lean
├── AllSections.lean
├── Section01.lean … Section03.lean
└── Coding/
```

`Coding/` contains the binary, Cauchy, and Markov coding modules together with
its `All.lean` aggregate. Use `Chapter01.AllSections` for the chapter text and
`Chapter01.Core` for reusable coding support.

Verification: `Chapter01.lean` passes with 12 dependency files, zero errors,
warnings, `sorry`, or imported proof risks. See
[`../VERIFICATION.md`](../VERIFICATION.md).
