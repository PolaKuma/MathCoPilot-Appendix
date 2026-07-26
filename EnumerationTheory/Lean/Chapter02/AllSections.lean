import Chapter02.Section01
import Chapter02.Section02
import Chapter02.Section03
import Chapter02.Section04
import Chapter02.Section05
import Chapter02.Section06

/-!
# Chapter 2 section entry point

This module is the stable import surface for all six textbook sections.
The imports are intentionally explicit: Sections 5 and 6 form a spectral
branch and do not depend on Section 4 through Lean imports.

`Section02` still uses the documented, temporary
`share.Lean.BHKMultipleKhintchine` root axiom.  Consequently this module is
an all-sections compilation target, not yet a self-contained proof target.
-/
