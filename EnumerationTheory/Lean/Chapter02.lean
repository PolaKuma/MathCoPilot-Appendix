import Chapter02.AllSections
import Chapter02.Core

/-!
# Chapter 2 staged entry point

Import this module for the six chapter sections and the curated completed core.
Use `Chapter02.AllModules` when a single whole-directory aggregate is needed.

For risk-sensitive checks:

* `Chapter02.AllSections` is the textbook-section compilation target and
  currently inherits the one documented BHK root axiom used by Section 2.
* `Chapter02.Core` and `Chapter02.HostKraStage` are the curated axiom-free
  completed targets.
-/
