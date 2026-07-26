import Chapter04.MeasureAlgebra.MeasureAlgebraSpatial

noncomputable section

open Classical

namespace Chapter04.MeasureAlgebraSpatial

universe u

theorem nonempty_of_probability (P : ProbabilitySpace.{u})
    (hP : Chapter01.IsProbabilitySpace P) : Nonempty P.X := by
  by_contra hne
  letI : IsEmpty P.X := ⟨fun x => hne ⟨x⟩⟩
  have hu : (Set.univ : Set P.X) = ∅ := by
    ext x
    exact False.elim (isEmptyElim x)
  have hone : P.μ Set.univ = 1 := hP.measure_univ
  rw [hu, MeasureTheory.measure_empty] at hone
  exact zero_ne_one hone

theorem probability_iso_of_measureAlgebra_iso
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{u})
    (hP : IsLebesgueProbabilitySpace P) (hQ : IsLebesgueProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q) (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraIsomorphism Φ) :
    IsIsomorphicProbabilitySpaces P Q := by
  letI : MeasureTheory.IsProbabilityMeasure P.μ := hP.1
  letI : MeasureTheory.IsProbabilityMeasure Q.μ := hQ.1
  obtain ⟨Ψ, hΨiso, hΨmap⟩ := quotient_iso_of_measureAlgebra_iso P Q Φ hΦ
  let PM : MeasurableSpaceData.{u} := { X := P.X, measurableSpace := P.measurableSpace }
  let QM : MeasurableSpaceData.{u} := { X := Q.X, measurableSpace := Q.measurableSpace }
  obtain ⟨X₀, Y₀, hX₀, hY₀, hXc, hYc, φ, ψ, hleft, hright,
      hφm, hψm, _hideal, hrep⟩ :=
    QuotientBoolean.iso_has_borel_core PM QM (IsNullSet P) (IsNullSet Q) Ψ
      (nonempty_of_probability P hP.1) (nonempty_of_probability Q hQ.1)
      hP.2 hQ.2 (nullSet_sigmaIdeal P) (nullSet_sigmaIdeal Q) hΨiso
  have hXc0 : P.μ X₀ᶜ = 0 := by
    rcases hXc with ⟨C, hC, hsub, hC0⟩
    exact MeasureTheory.measure_mono_null hsub hC0
  have hYc0 : Q.μ Y₀ᶜ = 0 := by
    rcases hYc with ⟨C, hC, hsub, hC0⟩
    exact MeasureTheory.measure_mono_null hsub hC0
  have hXfull : P.μ X₀ = 1 := by
    calc
      P.μ X₀ = P.μ Set.univ :=
        MeasureTheory.measure_congr (MeasureTheory.ae_eq_univ.mpr hXc0)
      _ = 1 := hP.1.measure_univ
  have hYfull : Q.μ Y₀ = 1 := by
    calc
      Q.μ Y₀ = Q.μ Set.univ :=
        MeasureTheory.measure_congr (MeasureTheory.ae_eq_univ.mpr hYc0)
      _ = 1 := hQ.1.measure_univ
  refine ⟨X₀, Y₀, hX₀, hY₀, hXfull, hYfull, φ, ψ,
    hleft, hright, hφm, hψm, ?_⟩
  intro B hB
  let A : Set Q.X := Subtype.val '' B
  have hA : MeasurableSet A := hY₀.subtype_image hB
  have hR : Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' (A ∩ Y₀))) =
      Subtype.val '' (φ ⁻¹' B) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with ⟨⟨y, hyB, hy⟩, _⟩
      have : y = φ z := Subtype.ext hy
      exact ⟨z, by simpa only [this] using hyB, rfl⟩
    · rintro ⟨z, hzB, rfl⟩
      exact ⟨z, ⟨⟨φ z, hzB, rfl⟩, (φ z).2⟩, rfl⟩
  have hqR := hrep A hA
  rw [hR] at hqR
  have hsd0 : P.μ (Chapter00.symmDiff (Ψ.map A) (Subtype.val '' (φ ⁻¹' B))) = 0 := by
    rcases hqR with ⟨C, hC, hsub, hC0⟩
    exact MeasureTheory.measure_mono_null hsub hC0
  have hae : Ψ.map A =ᵐ[P.μ] Subtype.val '' (φ ⁻¹' B) := by
    apply MeasureTheory.measure_symmDiff_eq_zero_iff.mp
    simpa [Set.symmDiff_def, Chapter00.symmDiff] using hsd0
  have hqmeasure : P.μ (Ψ.map A) = Q.μ A := by
    rw [hΨmap A hA]
    have hr := hΦ.1.2.2.2.2 ⟨A, hA⟩
    exact (ENNReal.toReal_eq_toReal_iff'
      (MeasureTheory.measure_ne_top P.μ _) (MeasureTheory.measure_ne_top Q.μ _)).mp hr
  calc
    P.μ (Subtype.val '' (φ ⁻¹' B)) = P.μ (Ψ.map A) :=
      (MeasureTheory.measure_congr hae).symm
    _ = Q.μ A := hqmeasure
    _ = Q.μ (Subtype.val '' B) := rfl

end Chapter04.MeasureAlgebraSpatial
