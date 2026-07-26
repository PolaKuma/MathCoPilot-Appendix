import Chapter04.MeasureAlgebra.MeasureAlgebraPullback

noncomputable section

open Classical Filter

namespace Chapter04.ErgodicFactor

universe u v

/-- Ergodicity descends through a factor map represented on invariant conull cores. -/
theorem of_factor_map (M : System.{u}) (N : System.{v}) (π : M.X → N.X)
    (hMerg : Chapter02.IsErgodic M) (hπ : Chapter01.IsFactorMap M N π) :
    Chapter02.IsErgodic N := by
  rcases hπ with
    ⟨hM, hN, M₁, M₂, hM₁, hM₂, hMT, hNT, hfull, hintertwine⟩
  rcases hfull with ⟨hM₁m, hM₂m, -, -, hπcore, hπμ⟩
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  letI : MeasureTheory.IsProbabilityMeasure N.μ := hN.1
  have hM₁c : M.μ M₁ᶜ = 0 := by
    rw [MeasureTheory.measure_compl hM₁m (by rw [hM₁]; simp)]
    simp [hM₁]
  have hM₂c : N.μ M₂ᶜ = 0 := by
    rw [MeasureTheory.measure_compl hM₂m (by rw [hM₂]; simp)]
    simp [hM₂]
  refine ⟨hN, ?_⟩
  intro A hAm hAinv
  let C : Set M.X := M₁ ∩ π ⁻¹' (A ∩ M₂)
  have hCm : MeasurableSet C := (hπμ A hAm).1
  have hCmeasure : M.μ C = N.μ A := by
    rw [(hπμ A hAm).2]
    rw [show A ∩ M₂ = A \ M₂ᶜ by ext y; simp]
    exact MeasureTheory.measure_diff_null hM₂c
  let D : Set N.X := Chapter00.symmDiff (N.T ⁻¹' A) A
  have hDm : MeasurableSet D :=
    (hAm.preimage hN.2.measurable).diff hAm |>.union
      (hAm.diff (hAm.preimage hN.2.measurable))
  let pullD : Set M.X := M₁ ∩ π ⁻¹' (D ∩ M₂)
  have hpullDzero : M.μ pullD = 0 := by
    rw [(hπμ D hDm).2]
    exact MeasureTheory.measure_mono_null Set.inter_subset_left hAinv
  have hCinv : M.μ (Chapter00.symmDiff (M.T ⁻¹' C) C) = 0 := by
    apply MeasureTheory.measure_mono_null
      (t := M₁ᶜ ∪ pullD) ?_ (MeasureTheory.measure_union_null hM₁c hpullDzero)
    intro x hx
    by_cases hxM : x ∈ M₁
    · right
      have hπxM : π x ∈ M₂ := hπcore x hxM
      have hMTxM : M.T x ∈ M₁ := hMT x hxM
      have hπTxM : π (M.T x) ∈ M₂ := hπcore (M.T x) hMTxM
      have hCx : x ∈ C ↔ π x ∈ A := by
        exact ⟨fun h => h.2.1, fun h => ⟨hxM, h, hπxM⟩⟩
      have hCTx : M.T x ∈ C ↔ N.T (π x) ∈ A := by
        constructor
        · intro h
          rw [← hintertwine x hxM]
          exact h.2.1
        · intro h
          refine ⟨hMTxM, ?_, hπTxM⟩
          rw [hintertwine x hxM]
          exact h
      refine ⟨hxM, ?_, hπxM⟩
      simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff,
        Set.mem_preimage] at hx ⊢
      rcases hx with hx | hx
      · left
        exact ⟨hCTx.mp hx.1, fun h => hx.2 (hCx.mpr h)⟩
      · right
        exact ⟨hCx.mp hx.1, fun h => hx.2 (hCTx.mpr h)⟩
    · exact Or.inl hxM
  rcases hMerg.2 C hCm hCinv with hzero | hone
  · left
    rw [← hCmeasure]
    exact hzero
  · right
    rw [← hCmeasure]
    exact hone

end Chapter04.ErgodicFactor
