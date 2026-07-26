import Lake

open Lake DSL

package «MathCoPilotAppendix» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.28.0"

lean_lib Shared where
  srcDir := "EnumerationTheory"
  roots := #[`share]

@[default_target]
lean_lib EnumerationTheory where
  srcDir := "EnumerationTheory/Lean"
  roots := #[
    `Chapter00,
    `Chapter01,
    `Chapter02,
    `Chapter03,
    `Chapter04,
    `Chapter05,
    `Chapter06,
    `Chapter07,
    `Chapter08,
    `Chapter09,
    `Textbook
  ]
  globs := #[.submodules `MCMC]

@[default_target]
lean_lib DG where
  srcDir := "DG"
  roots := #[
    `AuditExp1Exp2,
    `Exp1,
    `Exp1Core,
    `Exp1Differentiation,
    `Exp1Energy,
    `Exp1GlobalL2,
    `Exp1Norm,
    `Exp1Projection,
    `Exp1SobolevSpace,
    `Exp2,
    `Exp2AffineMeasure,
    `Exp2BHProbe,
    `Exp2BoundedProbe,
    `Exp2BoundedProof,
    `Exp2Core,
    `Exp2ErrorBound,
    `Exp2FiniteCoordinates,
    `Exp2NormProbe,
    `Exp2StandardSobolev,
    `Exp2Trace,
    `Exp2TraceBoundProbe
  ]
