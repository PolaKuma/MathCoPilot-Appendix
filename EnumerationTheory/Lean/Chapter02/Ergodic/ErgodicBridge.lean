import Chapter02.Common

noncomputable section

open Filter

namespace Chapter02.ErgodicBridge

universe u

/-- The chapter's symmetric-difference formulation gives Mathlib's ergodic
map.  This foundational bridge is isolated from the section-level import
closure so spectral arguments do not inherit unrelated literature inputs. -/
theorem isErgodic_to_mathlibErgodic (M : System.{u})
    (hM : IsErgodic M) : Ergodic M.T M.μ := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  refine Ergodic.mk hM.1.2 (PreErgodic.mk ?_)
  intro s hs hinv
  have hsymm : M.μ (Chapter00.symmDiff (M.T ⁻¹' s) s) = 0 := by
    simp [hinv, Chapter00.symmDiff]
  rcases hM.2 s hs hsymm with hzero | hone
  · unfold Filter.EventuallyConst
    refine ⟨{False}, ?_⟩
    constructor
    · change ∀ᵐ x ∂M.μ, s x ∈ ({False} : Set Prop)
      filter_upwards [MeasureTheory.ae_eq_empty.mpr hzero] with x hx
      change s x = False
      exact hx
    · simp
  · have hfin : M.μ s ≠ ⊤ := by simp [hone]
    have hcompl : M.μ sᶜ = 0 := by
      rw [MeasureTheory.measure_compl hs hfin]
      simp [hone]
    unfold Filter.EventuallyConst
    refine ⟨{True}, ?_⟩
    constructor
    · change ∀ᵐ x ∂M.μ, s x ∈ ({True} : Set Prop)
      filter_upwards [MeasureTheory.ae_eq_univ.mpr hcompl] with x hx
      change s x = True
      exact hx
    · simp

end Chapter02.ErgodicBridge
