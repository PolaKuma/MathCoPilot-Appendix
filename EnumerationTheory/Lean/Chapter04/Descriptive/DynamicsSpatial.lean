import Chapter04.Descriptive.ProbabilitySpatial

noncomputable section

open Classical Filter

namespace Chapter04.DynamicsSpatial

universe u

private theorem null_of_isNullSet {P : ProbabilitySpace.{u}} {A : Set P.X}
    (hA : IsNullSet P A) : P.μ A = 0 := by
  rcases hA with ⟨B, hB, hsub, hB0⟩
  exact MeasureTheory.measure_mono_null hsub hB0

private theorem preimage_equiv_null
    (P : ProbabilitySpace.{u}) (T : P.X → P.X)
    (hT : MeasureTheory.MeasurePreserving T P.μ P.μ)
    {A B : Set P.X}
    (hAB : quotientEquivalentByIdeal (IsNullSet P) A B) :
    quotientEquivalentByIdeal (IsNullSet P) (T ⁻¹' A) (T ⁻¹' B) := by
  rcases hAB with ⟨C, hC, hsub, hC0⟩
  refine ⟨T ⁻¹' C, hC.preimage hT.measurable, ?_, ?_⟩
  · intro x hx
    apply hsub
    simpa [Chapter00.symmDiff] using hx
  · exact hT.measure_preimage hC.nullMeasurableSet |>.trans hC0

/-- A conjugacy of the induced measure-algebra systems has global measurable
realizers which are inverse and dynamically intertwining almost everywhere. -/
theorem global_realizers_of_system_conjugacy
    (M N : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (hMLeb : IsLebesgueProbabilitySpace M.toProbabilitySpace)
    (hNLeb : IsLebesgueProbabilitySpace N.toProbabilitySpace)
    (hconj : IsSystemConjugate M N) :
    ∃ φ : M.X → N.X, ∃ ψ : N.X → M.X,
      Measurable φ ∧ Measurable ψ ∧
      MeasureTheory.MeasurePreserving φ M.μ N.μ ∧
      MeasureTheory.MeasurePreserving ψ N.μ M.μ ∧
      (fun x => ψ (φ x)) =ᵐ[M.μ] id ∧
      (fun y => φ (ψ y)) =ᵐ[N.μ] id ∧
      (fun x => φ (M.T x)) =ᵐ[M.μ] fun x => N.T (φ x) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  letI : MeasureTheory.IsProbabilityMeasure N.μ := hN.1
  rcases hconj with ⟨Φ, hΦ, hcomm⟩
  obtain ⟨Ψ, hΨiso, hΨmap⟩ :=
    MeasureAlgebraSpatial.quotient_iso_of_measureAlgebra_iso
      M.toProbabilitySpace N.toProbabilitySpace Φ hΦ
  let Md : MeasurableSpaceData.{u} :=
    { X := M.X, measurableSpace := M.measurableSpace }
  let Nd : MeasurableSpaceData.{u} :=
    { X := N.X, measurableSpace := N.measurableSpace }
  obtain ⟨φ, ψ, hφm, hψm, hXbad, hYbad, hφrep⟩ :=
    QuotientBoolean.iso_has_global_realizers Md Nd
      (IsNullSet M.toProbabilitySpace) (IsNullSet N.toProbabilitySpace) Ψ
      (MeasureAlgebraSpatial.nonempty_of_probability M.toProbabilitySpace hM.1)
      (MeasureAlgebraSpatial.nonempty_of_probability N.toProbabilitySpace hN.1)
      hMLeb.2 hNLeb.2
      (MeasureAlgebraSpatial.nullSet_sigmaIdeal M.toProbabilitySpace)
      (MeasureAlgebraSpatial.nullSet_sigmaIdeal N.toProbabilitySpace) hΨiso
  have hφm' : Measurable φ := hφm
  have hψm' : Measurable ψ := hψm
  have hφmeasure (A : Set N.X) (hA : MeasurableSet A) :
      M.μ (φ ⁻¹' A) = N.μ A := by
    have heq0 := null_of_isNullSet (hφrep A hA)
    have hae : φ ⁻¹' A =ᵐ[M.μ] Ψ.map A := by
      apply MeasureTheory.measure_symmDiff_eq_zero_iff.mp
      simpa [Set.symmDiff_def, Chapter00.symmDiff] using heq0
    calc
      M.μ (φ ⁻¹' A) = M.μ (Ψ.map A) := MeasureTheory.measure_congr hae
      _ = M.μ (Φ.map ⟨A, hA⟩).1 := by rw [hΨmap A hA]
      _ = N.μ A := by
        have hr := hΦ.1.2.2.2.2 ⟨A, hA⟩
        exact (ENNReal.toReal_eq_toReal_iff'
          (MeasureTheory.measure_ne_top M.μ _) (MeasureTheory.measure_ne_top N.μ _)).mp hr
  have hφmp : MeasureTheory.MeasurePreserving φ M.μ N.μ := by
    refine ⟨hφm', ?_⟩
    apply MeasureTheory.Measure.ext
    intro A hA
    rw [MeasureTheory.Measure.map_apply hφm' hA]
    exact hφmeasure A hA
  have hX0 : M.μ {x : M.X | ψ (φ x) ≠ x} = 0 := null_of_isNullSet hXbad
  have hY0 : N.μ {y : N.X | φ (ψ y) ≠ y} = 0 := null_of_isNullSet hYbad
  have hψmeasure (A : Set M.X) (hA : MeasurableSet A) :
      N.μ (ψ ⁻¹' A) = M.μ A := by
    have hcomp : M.μ (φ ⁻¹' (ψ ⁻¹' A)) = M.μ A := by
      apply MeasureTheory.measure_congr
      filter_upwards [show (fun x => ψ (φ x)) =ᵐ[M.μ] id from
        MeasureTheory.mem_ae_iff.mpr hX0] with x hx
      simpa using congrArg (fun z => z ∈ A) hx
    rw [← hφmeasure (ψ ⁻¹' A) (hA.preimage hψm')]
    exact hcomp
  have hψmp : MeasureTheory.MeasurePreserving ψ N.μ M.μ := by
    refine ⟨hψm', ?_⟩
    apply MeasureTheory.Measure.ext
    intro A hA
    rw [MeasureTheory.Measure.map_apply hψm' hA]
    exact hψmeasure A hA
  have hpre (A : Set N.X) (hA : MeasurableSet A) :
      quotientEquivalentByIdeal (IsNullSet M.toProbabilitySpace)
        ((fun x => N.T (φ x)) ⁻¹' A) ((fun x => φ (M.T x)) ⁻¹' A) := by
    have hApre : MeasurableSet (N.T ⁻¹' A) := hA.preimage hN.2.measurable
    have h1 := hφrep (N.T ⁻¹' A) hApre
    rw [hΨmap (N.T ⁻¹' A) hApre] at h1
    have hc0 := hcomm ⟨A, hA⟩
    simp only [inducedMeasureAlgebraSystem, dif_pos hN.2.measurable,
      dif_pos hM.2.measurable] at hc0
    have hc : quotientEquivalentByIdeal (IsNullSet M.toProbabilitySpace)
        (Φ.map ⟨N.T ⁻¹' A, hApre⟩).1
        (M.T ⁻¹' (Φ.map ⟨A, hA⟩).1) :=
      ⟨Chapter00.symmDiff (Φ.map ⟨N.T ⁻¹' A, hApre⟩).1
          (M.T ⁻¹' (Φ.map ⟨A, hA⟩).1),
        (Φ.map ⟨N.T ⁻¹' A, hApre⟩).2.diff
            ((Φ.map ⟨A, hA⟩).2.preimage hM.2.measurable) |>.union
          (((Φ.map ⟨A, hA⟩).2.preimage hM.2.measurable).diff
            (Φ.map ⟨N.T ⁻¹' A, hApre⟩).2), Set.Subset.rfl, hc0⟩
    have h3 := preimage_equiv_null M.toProbabilitySpace M.T hM.2 (hφrep A hA)
    rw [hΨmap A hA] at h3
    exact QuotientBoolean.equiv_trans
      (MeasureAlgebraSpatial.nullSet_sigmaIdeal M.toProbabilitySpace) h1
      (QuotientBoolean.equiv_trans
        (MeasureAlgebraSpatial.nullSet_sigmaIdeal M.toProbabilitySpace) hc
        (QuotientBoolean.equiv_symm h3))
  have hinter0 : M.μ {x : M.X | φ (M.T x) ≠ N.T (φ x)} = 0 := by
    have hbad := QuotientBoolean.maps_equal_mod_ideal Md Nd
      (IsNullSet M.toProbabilitySpace) hNLeb.2
      (MeasureAlgebraSpatial.nullSet_sigmaIdeal M.toProbabilitySpace)
      (fun x => φ (M.T x)) (fun x => N.T (φ x))
      (hφm'.comp hM.2.measurable) (hN.2.measurable.comp hφm')
      (fun A hA => QuotientBoolean.equiv_symm (hpre A hA))
    exact null_of_isNullSet hbad
  exact ⟨φ, ψ, hφm', hψm', hφmp, hψmp,
    MeasureTheory.mem_ae_iff.mpr hX0, MeasureTheory.mem_ae_iff.mpr hY0,
    MeasureTheory.mem_ae_iff.mpr hinter0⟩

/-- Almost-everywhere inverse intertwining maps restrict to mutually invariant
conull Borel sets, hence give the textbook spatial system isomorphism. -/
theorem system_isomorphism_of_global_realizers
    (M N : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (hMLeb : IsLebesgueProbabilitySpace M.toProbabilitySpace)
    (hNLeb : IsLebesgueProbabilitySpace N.toProbabilitySpace)
    (φ : M.X → N.X) (ψ : N.X → M.X)
    (hφm : Measurable φ) (hψm : Measurable ψ)
    (hφmp : MeasureTheory.MeasurePreserving φ M.μ N.μ)
    (hψmp : MeasureTheory.MeasurePreserving ψ N.μ M.μ)
    (hψφ : (fun x => ψ (φ x)) =ᵐ[M.μ] id)
    (hφψ : (fun y => φ (ψ y)) =ᵐ[N.μ] id)
    (hint : (fun x => φ (M.T x)) =ᵐ[M.μ] fun x => N.T (φ x)) :
    Chapter01.IsIsomorphicSystems M N := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  letI : MeasureTheory.IsProbabilityMeasure N.μ := hN.1
  letI : StandardBorelSpace M.X :=
    StandardBorel.instanceOfData
      { X := M.X, measurableSpace := M.measurableSpace } hMLeb.2
  letI : StandardBorelSpace N.X :=
    StandardBorel.instanceOfData
      { X := N.X, measurableSpace := N.measurableSpace } hNLeb.2
  letI : MeasurableEq M.X := by
    let := upgradeStandardBorel M.X
    infer_instance
  letI : MeasurableEq N.X := by
    let := upgradeStandardBorel N.X
    infer_instance
  let G : Set M.X := {x | ψ (φ x) = x ∧ φ (M.T x) = N.T (φ x)}
  have hGm : MeasurableSet G :=
    (measurableSet_eq_fun (hψm.comp hφm) measurable_id).inter
      (measurableSet_eq_fun (hφm.comp hM.2.measurable)
        (hN.2.measurable.comp hφm))
  have hGae : ∀ᵐ x ∂M.μ, x ∈ G := by
    filter_upwards [hψφ, hint] with x hx hxi
    exact ⟨hx, hxi⟩
  have hGc0 : M.μ Gᶜ = 0 := MeasureTheory.mem_ae_iff.mp hGae
  let X₀ : Set M.X := {x | ∀ n : ℕ, (M.T^[n]) x ∈ G}
  have hX₀eq : X₀ = ⋂ n : ℕ, (M.T^[n]) ⁻¹' G := by
    ext x
    simp [X₀]
  have hX₀m : MeasurableSet X₀ := by
    rw [hX₀eq]
    exact MeasurableSet.iInter fun n => hGm.preimage (hM.2.measurable.iterate n)
  have hX₀c : X₀ᶜ = ⋃ n : ℕ, (M.T^[n]) ⁻¹' Gᶜ := by
    rw [hX₀eq]
    ext x
    simp
  have hX₀c0 : M.μ X₀ᶜ = 0 := by
    rw [hX₀c]
    apply MeasureTheory.measure_iUnion_null
    intro n
    exact (hM.2.iterate n).measure_preimage hGm.compl.nullMeasurableSet |>.trans hGc0
  have hXT (x : M.X) (hx : x ∈ X₀) : M.T x ∈ X₀ := by
    intro n
    simpa [Function.iterate_succ_apply] using hx (n + 1)
  let Y₀ : Set N.X := {y | φ (ψ y) = y ∧ ψ y ∈ X₀}
  have hY₀m : MeasurableSet Y₀ :=
    (measurableSet_eq_fun (hφm.comp hψm) measurable_id).inter
      (hX₀m.preimage hψm)
  have hYbad0 : N.μ {y : N.X | φ (ψ y) ≠ y} = 0 := by
    exact MeasureTheory.mem_ae_iff.mp hφψ
  have hψXc0 : N.μ (ψ ⁻¹' X₀ᶜ) = 0 :=
    (hψmp.measure_preimage hX₀m.compl.nullMeasurableSet).trans hX₀c0
  have hY₀csub : Y₀ᶜ ⊆ {y : N.X | φ (ψ y) ≠ y} ∪ ψ ⁻¹' X₀ᶜ := by
    intro y hy
    by_cases h₁ : φ (ψ y) = y
    · right
      intro hxin
      exact hy ⟨h₁, hxin⟩
    · exact Or.inl h₁
  have hY₀c0 : N.μ Y₀ᶜ = 0 := by
    apply MeasureTheory.measure_mono_null hY₀csub
    apply MeasureTheory.measure_union_null hYbad0
    simpa only [Set.preimage_compl] using hψXc0
  have hXfull : M.μ X₀ = 1 := by
    calc
      M.μ X₀ = M.μ Set.univ :=
        MeasureTheory.measure_congr (MeasureTheory.ae_eq_univ.mpr hX₀c0)
      _ = 1 := hM.1.measure_univ
  have hYfull : N.μ Y₀ = 1 := by
    calc
      N.μ Y₀ = N.μ Set.univ :=
        MeasureTheory.measure_congr (MeasureTheory.ae_eq_univ.mpr hY₀c0)
      _ = 1 := hN.1.measure_univ
  have hφin (x : M.X) (hx : x ∈ X₀) : φ x ∈ Y₀ := by
    have hxG := hx 0
    change ψ (φ x) = x ∧ φ (M.T x) = N.T (φ x) at hxG
    change φ (ψ (φ x)) = φ x ∧ ψ (φ x) ∈ X₀
    refine ⟨congrArg φ hxG.1, ?_⟩
    rw [hxG.1]
    exact hx
  have hψin (y : N.X) (hy : y ∈ Y₀) : ψ y ∈ X₀ := hy.2
  have hYT (y : N.X) (hy : y ∈ Y₀) : N.T y ∈ Y₀ := by
    have hxG := hy.2 0
    change ψ (φ (ψ y)) = ψ y ∧
      φ (M.T (ψ y)) = N.T (φ (ψ y)) at hxG
    have htx := hXT (ψ y) hy.2
    have hNy : N.T y = φ (M.T (ψ y)) :=
      (hxG.2.trans (congrArg N.T hy.1)).symm
    rw [hNy]
    exact hφin (M.T (ψ y)) htx
  have hφinter (x : M.X) (hx : x ∈ X₀) :
      φ (M.T x) = N.T (φ x) := (hx 0).2
  have hψinter (y : N.X) (hy : y ∈ Y₀) :
      ψ (N.T y) = M.T (ψ y) := by
    have hxG := hy.2 0
    change ψ (φ (ψ y)) = ψ y ∧
      φ (M.T (ψ y)) = N.T (φ (ψ y)) at hxG
    have htx := hXT (ψ y) hy.2
    have hNy : N.T y = φ (M.T (ψ y)) :=
      (hxG.2.trans (congrArg N.T hy.1)).symm
    calc
      ψ (N.T y) = ψ (φ (M.T (ψ y))) := congrArg ψ hNy
      _ = M.T (ψ y) := by
        have h := htx 0
        change ψ (φ (M.T (ψ y))) = M.T (ψ y) ∧
          φ (M.T (M.T (ψ y))) = N.T (φ (M.T (ψ y))) at h
        exact h.1
  have hφfull : Chapter01.IsMeasurePreservingOnFullSets M N X₀ Y₀ φ := by
    refine ⟨hX₀m, hY₀m, hXfull, hYfull, hφin, ?_⟩
    intro B hB
    refine ⟨hX₀m.inter ((hB.inter hY₀m).preimage hφm), ?_⟩
    calc
      M.μ (X₀ ∩ φ ⁻¹' (B ∩ Y₀)) = M.μ (φ ⁻¹' (B ∩ Y₀)) := by
        apply MeasureTheory.measure_congr
        filter_upwards [show ∀ᵐ x ∂M.μ, x ∈ X₀ from
          MeasureTheory.mem_ae_iff.mpr hX₀c0] with x hx
        apply propext
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨hx, h⟩
      _ = N.μ (B ∩ Y₀) := hφmp.measure_preimage (hB.inter hY₀m).nullMeasurableSet
  have hψfull : Chapter01.IsMeasurePreservingOnFullSets N M Y₀ X₀ ψ := by
    refine ⟨hY₀m, hX₀m, hYfull, hXfull, hψin, ?_⟩
    intro B hB
    refine ⟨hY₀m.inter ((hB.inter hX₀m).preimage hψm), ?_⟩
    calc
      N.μ (Y₀ ∩ ψ ⁻¹' (B ∩ X₀)) = N.μ (ψ ⁻¹' (B ∩ X₀)) := by
        apply MeasureTheory.measure_congr
        filter_upwards [show ∀ᵐ y ∂N.μ, y ∈ Y₀ from
          MeasureTheory.mem_ae_iff.mpr hY₀c0] with y hy
        apply propext
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨hy, h⟩
      _ = M.μ (B ∩ X₀) := hψmp.measure_preimage (hB.inter hX₀m).nullMeasurableSet
  exact ⟨hM, hN, X₀, Y₀, φ, ψ, hXfull, hYfull, hXT, hYT,
    hφfull, hψfull,
    (fun x hx => ⟨hφin x hx, (hx 0).1, hφinter x hx⟩),
    fun y hy => ⟨hψin y hy, hy.1, hψinter y hy⟩⟩

end Chapter04.DynamicsSpatial
