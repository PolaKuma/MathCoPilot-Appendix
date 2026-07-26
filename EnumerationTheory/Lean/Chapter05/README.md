# Chapter 5

The chapter root contains `CommonFoundation.lean`, `CommonCore.lean`,
`Common.lean`, `Core.lean`, `AllSections.lean`, and Sections 1–7. There are no
standalone helper modules requiring a support subdirectory.

Use `Chapter05.AllSections` for the chapter text and `Chapter05.Core` for the
shared foundation chain.

Verification: `Chapter05.lean` compiles with zero errors and ordinary linter
warnings. This is an organized but proof-incomplete chapter: its directory
contains 63 direct `sorry` occurrences and its entry closure reports 64
imported proof risks. See [`../VERIFICATION.md`](../VERIFICATION.md).
