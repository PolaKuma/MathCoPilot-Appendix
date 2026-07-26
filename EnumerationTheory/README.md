# MathCopilot Lean workspace

The organized Lean source tree is under [`Lean/`](Lean/README.md). Every
textbook chapter now has the same public shape:

```text
ChapterXX/
├── Common.lean
├── Core.lean
├── AllSections.lean
├── SectionNN.lean
├── <mathematical support areas>/All.lean
└── README.md
```

Stable imports are `Chapter00` through `Chapter09`; `Textbook` is the
end-to-end entry. Root-level probes were moved to `Lean/Tests/`, and generated
check reports are outside the source tree.

See [`Lean/VERIFICATION.md`](Lean/VERIFICATION.md) for the chapter-by-chapter
compile status, direct `sorry` counts, imported-risk counts, code volume,
structural audit, and GitHub upload guidance. Chapter 2's exact remaining BHK
boundary is documented in
[`Documents/Chapter02_STAGE.md`](Documents/Chapter02_STAGE.md).
