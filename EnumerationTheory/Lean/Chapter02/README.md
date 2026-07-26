# Chapter 2 module map

The chapter root is intentionally small. Textbook sections, shared
definitions, curated entry points, and this README remain at the top level;
the 248 reusable support modules are grouped by mathematical responsibility.

```text
Chapter02/
├── Common.lean
├── Core.lean
├── Section01.lean … Section06.lean
├── AllSections.lean
├── HostKraStage.lean
├── AllModules.lean
├── Ergodic/          (23 support modules + All.lean)
├── Recurrence/       (21 support modules + All.lean)
├── Spectral/         (52 support modules + All.lean)
├── HostKra/          (78 support modules + All.lean)
├── HallPetresco/     (59 support modules + All.lean)
└── Dynamics/         (15 support modules + All.lean)
```

Entry points:

- `Chapter02.Core`: curated completed core with no imported proof risk.
- `Chapter02.AllSections`: all six textbook-facing sections.
- `Chapter02.HostKraStage`: checked support developed toward eliminating the
  remaining BHK root axiom.
- `Chapter02.AllModules`: every Chapter 2 module; use this for release checks.
- `Chapter02.lean`: checkable release entry for `AllSections + Core`.

Imports now mirror the directory structure, for example
`Chapter02.Spectral.SpectralClassification` and
`Chapter02.HostKra.HostKraDirectedInverseLimitReduction`.  Each support
directory also has an `All.lean` whole-directory compilation entry.
`AllModules.lean` is intentionally checked through its six directory
aggregates because its 307-file import closure exceeds the checker limit.

The remaining documented risk is exactly the temporary axiom declared in
`share/Lean/BHKMultipleKhintchine.lean` and called once by `Section02`.
`Chapter02.Core` and `Chapter02.HostKraStage` do not inherit it.

For exact current checks and code counts, see
[`../../Documents/Chapter02_STAGE.md`](../../Documents/Chapter02_STAGE.md)
and [`../VERIFICATION.md`](../VERIFICATION.md).
