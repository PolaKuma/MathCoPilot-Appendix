import Chapter04.Section01

noncomputable section

open Classical Filter

namespace Chapter04.MeasureAlgebraPullback

universe u v

theorem hom_of_factor_map
    (M : System.{u}) (N : System.{v}) (π : M.X → N.X)
    (hπ : Chapter01.IsFactorMap M N π) :
    ∃ Φ : MeasureAlgebraHomData (inducedMeasureAlgebra N.toProbabilitySpace)
        (inducedMeasureAlgebra M.toProbabilitySpace), IsMeasureAlgebraHom Φ := by
  rcases hπ with ⟨hM, hN, M₁, M₂, hM₁, hM₂, hMT, hNT, hfull, hintertwine⟩
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  letI : MeasureTheory.IsProbabilityMeasure N.μ := hN.1
  rcases hfull with ⟨hM₁m, hM₂m, -, -, hπcore, hπμ⟩
  have hM₁c : M.μ M₁ᶜ = 0 := by
    rw [MeasureTheory.measure_compl hM₁m (by rw [hM₁]; simp)]
    simp [hM₁]
  have hM₂c : N.μ M₂ᶜ = 0 := by
    rw [MeasureTheory.measure_compl hM₂m (by rw [hM₂]; simp)]
    simp [hM₂]
  let pull : (inducedMeasureAlgebra N.toProbabilitySpace).carrier → Set M.X := fun B =>
    M₁ ∩ π ⁻¹' (B.1 ∩ M₂)
  have hpull_meas (B : (inducedMeasureAlgebra N.toProbabilitySpace).carrier) :
      MeasurableSet (pull B) := (hπμ B.1 B.2).1
  have hpull_measure (B : (inducedMeasureAlgebra N.toProbabilitySpace).carrier) :
      M.μ (pull B) = N.μ B.1 := by
    rw [(hπμ B.1 B.2).2]
    rw [show B.1 ∩ M₂ = B.1 \ M₂ᶜ by ext y; simp]
    exact MeasureTheory.measure_diff_null hM₂c
  let Φ : MeasureAlgebraHomData (inducedMeasureAlgebra N.toProbabilitySpace)
      (inducedMeasureAlgebra M.toProbabilitySpace) :=
    { map := fun B => ⟨pull B, hpull_meas B⟩ }
  refine ⟨Φ, ?_, ?_, ?_, ?_, ?_⟩
  · intro B C hBC
    change M.μ (Chapter00.symmDiff (pull B) (pull C)) = 0
    rw [show Chapter00.symmDiff (pull B) (pull C) =
        pull ⟨Chapter00.symmDiff B.1 C.1,
          B.2.diff C.2 |>.union (C.2.diff B.2)⟩ by
      ext x
      simp [pull, Chapter00.symmDiff]
      tauto]
    rw [hpull_measure]
    exact hBC
  · intro B C
    change M.μ (Chapter00.symmDiff
      (pull ⟨B.1 ∪ C.1, B.2.union C.2⟩) (pull B ∪ pull C)) = 0
    have heq : pull ⟨B.1 ∪ C.1, B.2.union C.2⟩ = pull B ∪ pull C := by
      ext x
      simp [pull]
      constructor
      · rintro ⟨hx, hB | hC, h₂⟩
        · exact Or.inl ⟨hx, hB, h₂⟩
        · exact Or.inr ⟨hx, hC, h₂⟩
      · rintro (⟨hx, hB, h₂⟩ | ⟨hx, hC, h₂⟩)
        · exact ⟨hx, Or.inl hB, h₂⟩
        · exact ⟨hx, Or.inr hC, h₂⟩
    simp [heq, Chapter00.symmDiff]
  · intro B
    change M.μ (Chapter00.symmDiff (pull ⟨B.1ᶜ, B.2.compl⟩) (pull B)ᶜ) = 0
    apply MeasureTheory.measure_mono_null (t := M₁ᶜ) ?_ hM₁c
    intro x hx
    simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff, Set.mem_compl_iff] at hx ⊢
    simp [pull] at hx
    tauto
  · intro f
    change M.μ (Chapter00.symmDiff
      (pull ⟨⋃ n, (f n).1, MeasurableSet.iUnion fun n => (f n).2⟩)
      (⋃ n, pull (f n))) = 0
    have heq : pull ⟨⋃ n, (f n).1, MeasurableSet.iUnion fun n => (f n).2⟩ =
        ⋃ n, pull (f n) := by
      ext x
      simp [pull]
    simp [heq, Chapter00.symmDiff]
  · intro B
    change (M.μ (pull B)).toReal = (N.μ B.1).toReal
    rw [hpull_measure]

theorem isomorphism_of_system_isomorphism
    (M : System.{u}) (N : System.{v})
    (hIso : Chapter01.IsIsomorphicSystems M N) : IsSystemConjugate M N := by
  rcases hIso with
    ⟨hM, hN, M₁, M₂, φ, ψ, hM₁, hM₂, hMT, hNT,
      hφfull, hψfull, hφinv, hψinv⟩
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  letI : MeasureTheory.IsProbabilityMeasure N.μ := hN.1
  rcases hφfull with ⟨hM₁m, hM₂m, -, -, hφcore, hφμ⟩
  rcases hψfull with ⟨-, -, -, -, hψcore, hψμ⟩
  have hM₁c : M.μ M₁ᶜ = 0 := by
    rw [MeasureTheory.measure_compl hM₁m (by rw [hM₁]; simp)]
    simp [hM₁]
  have hM₂c : N.μ M₂ᶜ = 0 := by
    rw [MeasureTheory.measure_compl hM₂m (by rw [hM₂]; simp)]
    simp [hM₂]
  let pull : (inducedMeasureAlgebra N.toProbabilitySpace).carrier → Set M.X := fun B =>
    M₁ ∩ φ ⁻¹' (B.1 ∩ M₂)
  have hpull_meas (B : (inducedMeasureAlgebra N.toProbabilitySpace).carrier) :
      MeasurableSet (pull B) := (hφμ B.1 B.2).1
  have hpull_measure (B : (inducedMeasureAlgebra N.toProbabilitySpace).carrier) :
      M.μ (pull B) = N.μ B.1 := by
    rw [(hφμ B.1 B.2).2]
    rw [show B.1 ∩ M₂ = B.1 \ M₂ᶜ by ext y; simp]
    exact MeasureTheory.measure_diff_null hM₂c
  let Φ : MeasureAlgebraHomData (inducedMeasureAlgebra N.toProbabilitySpace)
      (inducedMeasureAlgebra M.toProbabilitySpace) :=
    { map := fun B => ⟨pull B, hpull_meas B⟩ }
  refine ⟨Φ, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro B C hBC
        change M.μ (Chapter00.symmDiff (pull B) (pull C)) = 0
        rw [show Chapter00.symmDiff (pull B) (pull C) =
            pull ⟨Chapter00.symmDiff B.1 C.1,
              B.2.diff C.2 |>.union (C.2.diff B.2)⟩ by
          ext x
          by_cases hxM : x ∈ M₁
          · have hφx : φ x ∈ M₂ := hφcore x hxM
            simp [pull, Chapter00.symmDiff, hxM, hφx]
          · simp [pull, Chapter00.symmDiff, hxM]]
        rw [hpull_measure]
        exact hBC
      · intro B C
        change M.μ (Chapter00.symmDiff
          (pull ⟨B.1 ∪ C.1, B.2.union C.2⟩) (pull B ∪ pull C)) = 0
        have heq : pull ⟨B.1 ∪ C.1, B.2.union C.2⟩ = pull B ∪ pull C := by
          ext x
          change
            (x ∈ M₁ ∧ ((φ x ∈ B.1 ∨ φ x ∈ C.1) ∧ φ x ∈ M₂)) ↔
              ((x ∈ M₁ ∧ (φ x ∈ B.1 ∧ φ x ∈ M₂)) ∨
                (x ∈ M₁ ∧ (φ x ∈ C.1 ∧ φ x ∈ M₂)))
          tauto
        simp [heq, Chapter00.symmDiff]
      · intro B
        change M.μ (Chapter00.symmDiff (pull ⟨B.1ᶜ, B.2.compl⟩) (pull B)ᶜ) = 0
        apply MeasureTheory.measure_mono_null (t := M₁ᶜ) ?_ hM₁c
        intro x hx
        simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff,
          Set.mem_compl_iff] at hx ⊢
        intro hxM
        have hφx : φ x ∈ M₂ := hφcore x hxM
        simp [pull, hxM, hφx] at hx
      · intro f
        change M.μ (Chapter00.symmDiff
          (pull ⟨⋃ n, (f n).1, MeasurableSet.iUnion fun n => (f n).2⟩)
          (⋃ n, pull (f n))) = 0
        have heq : pull ⟨⋃ n, (f n).1, MeasurableSet.iUnion fun n => (f n).2⟩ =
            ⋃ n, pull (f n) := by
          ext x
          simp only [pull, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion]
          constructor
          · rintro ⟨hxM, ⟨n, hn⟩, hφM⟩
            exact ⟨n, hxM, hn, hφM⟩
          · rintro ⟨n, hxM, hn, hφM⟩
            exact ⟨hxM, ⟨n, hn⟩, hφM⟩
        simp [heq, Chapter00.symmDiff]
      · intro B
        change (M.μ (pull B)).toReal = (N.μ B.1).toReal
        rw [hpull_measure]
    · intro B C hBC
      change N.μ (Chapter00.symmDiff B.1 C.1) = 0
      rw [← hpull_measure
        ⟨Chapter00.symmDiff B.1 C.1, B.2.diff C.2 |>.union (C.2.diff B.2)⟩]
      rw [show pull ⟨Chapter00.symmDiff B.1 C.1,
            B.2.diff C.2 |>.union (C.2.diff B.2)⟩ =
          Chapter00.symmDiff (pull B) (pull C) by
        ext x
        by_cases hxM : x ∈ M₁
        · have hφx : φ x ∈ M₂ := hφcore x hxM
          simp [pull, Chapter00.symmDiff, hxM, hφx]
        · simp [pull, Chapter00.symmDiff, hxM]]
      exact hBC
    · intro A
      let Bset : Set N.X := M₂ ∩ ψ ⁻¹' (A.1 ∩ M₁)
      have hBm : MeasurableSet Bset := (hψμ A.1 A.2).1
      refine ⟨⟨Bset, hBm⟩, ?_⟩
      change M.μ (Chapter00.symmDiff (pull ⟨Bset, hBm⟩) A.1) = 0
      apply MeasureTheory.measure_mono_null (t := M₁ᶜ) ?_ hM₁c
      intro x hx
      simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff,
        Set.mem_compl_iff] at hx ⊢
      have hcore : x ∈ M₁ → (x ∈ pull ⟨Bset, hBm⟩ ↔ x ∈ A.1) := by
        intro hxM
        have hφx := (hφinv x hxM).1
        have hψφx := (hφinv x hxM).2.1
        constructor
        · rintro ⟨-, ⟨-, hψA, -⟩, -⟩
          rw [hψφx] at hψA
          exact hψA
        · intro hxA
          have hψA : ψ (φ x) ∈ A.1 := by rw [hψφx]; exact hxA
          have hψM : ψ (φ x) ∈ M₁ := by rw [hψφx]; exact hxM
          exact ⟨hxM, ⟨hφx, hψA, hψM⟩, hφx⟩
      rcases hx with hx | hx
      · exact fun hxM => hx.2 ((hcore hxM).mp hx.1)
      · exact fun hxM => hx.2 ((hcore hxM).mpr hx.1)
  · intro B
    simp only [inducedMeasureAlgebraSystem, dif_pos hN.2.measurable,
      dif_pos hM.2.measurable]
    change M.μ (Chapter00.symmDiff
      (pull ⟨N.T ⁻¹' B.1, B.2.preimage hN.2.measurable⟩)
      (M.T ⁻¹' pull B)) = 0
    apply MeasureTheory.measure_mono_null (t := M₁ᶜ) ?_ hM₁c
    intro x hx
    simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff,
      Set.mem_compl_iff, Set.mem_preimage] at hx ⊢
    have hcore : x ∈ M₁ →
        (x ∈ pull ⟨N.T ⁻¹' B.1, B.2.preimage hN.2.measurable⟩ ↔
          M.T x ∈ pull B) := by
      intro hxM
      have hMTx := hMT x hxM
      have hφx := (hφinv x hxM).1
      have hinter := (hφinv x hxM).2.2
      simp only [pull, Set.mem_inter_iff, Set.mem_preimage]
      rw [hinter]
      exact ⟨fun h => ⟨hMTx, h.2.1, hNT _ hφx⟩,
        fun h => ⟨hxM, h.2.1, hφx⟩⟩
    rcases hx with hx | hx
    · exact fun hxM => hx.2 ((hcore hxM).mp hx.1)
    · exact fun hxM => hx.2 ((hcore hxM).mpr hx.1)

end Chapter04.MeasureAlgebraPullback
