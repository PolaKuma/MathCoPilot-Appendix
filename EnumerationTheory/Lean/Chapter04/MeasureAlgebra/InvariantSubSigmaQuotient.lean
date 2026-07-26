import Chapter04.MeasureAlgebra.InvariantSubSigmaFactor

noncomputable section

open Classical Filter

namespace Chapter04.InvariantSubSigmaQuotient

universe u

/-- Two points are identified when the sub-sigma-algebra cannot distinguish
them. -/
def indistinguishable {X : Type u} (F : SetFamily X) (x y : X) : Prop :=
  ∀ A : Set X, A ∈ F → (x ∈ A ↔ y ∈ A)

def indistinguishableSetoid {X : Type u} (F : SetFamily X) : Setoid X where
  r := indistinguishable F
  iseqv := {
    refl := fun _ _ _ => Iff.rfl
    symm := fun h A hA => (h A hA).symm
    trans := fun hxy hyz A hA => (hxy A hA).trans (hyz A hA)
  }

abbrev QuotientSpace {X : Type u} (F : SetFamily X) :=
  Quotient (indistinguishableSetoid F)

def projection {X : Type u} (F : SetFamily X) : X → QuotientSpace F :=
  Quotient.mk (indistinguishableSetoid F)

/-- A set of equivalence classes is measurable exactly when its pullback is in
the prescribed sub-sigma-algebra. -/
def quotientMeasurableSpace {X : Type u} (F : SetFamily X)
    (hF : Chapter00.IsSigmaAlgebraFamily F) :
    MeasurableSpace (QuotientSpace F) where
  MeasurableSet' := fun B => projection F ⁻¹' B ∈ F
  measurableSet_empty := by
    change (∅ : Set X) ∈ F
    simpa using hF.2.1 Set.univ hF.1
  measurableSet_compl := by
    intro B hB
    simpa only [Set.preimage_compl] using hF.2.1 _ hB
  measurableSet_iUnion := by
    intro B hB
    simpa only [Set.preimage_iUnion] using hF.2.2 _ hB

@[simp] theorem measurableSet_quotient_iff {X : Type u}
    (F : SetFamily X) (hF : Chapter00.IsSigmaAlgebraFamily F)
    (B : Set (QuotientSpace F)) :
    @MeasurableSet (QuotientSpace F) (quotientMeasurableSpace F hF) B ↔
      projection F ⁻¹' B ∈ F :=
  Iff.rfl

theorem measurable_projection
    (M : MeasurableSpaceData.{u}) (F : SetFamily M.X)
    (hF : Chapter00.IsSigmaAlgebraFamily F) (hsub : F ⊆ M.sets) :
    @Measurable M.X (QuotientSpace F) M.measurableSpace
      (quotientMeasurableSpace F hF) (projection F) := by
  intro B hB
  exact hsub hB

/-- Forward invariance makes the original transformation descend to the
measurable quotient. -/
def quotientTransform (M : System.{u}) (F : SetFamily M.X)
    (hInv : ∀ A : Set M.X, A ∈ F → M.T ⁻¹' A ∈ F) :
  QuotientSpace F → QuotientSpace F :=
  Quotient.map M.T (by
    intro x y hxy A hA
    exact hxy (M.T ⁻¹' A) (hInv A hA))

@[simp] theorem projection_intertwines
    (M : System.{u}) (F : SetFamily M.X)
    (hInv : ∀ A : Set M.X, A ∈ F → M.T ⁻¹' A ∈ F)
    (x : M.X) :
    quotientTransform M F hInv (projection F x) =
      projection F (M.T x) :=
  rfl

theorem measurable_quotientTransform
    (M : System.{u}) (F : SetFamily M.X)
    (hF : Chapter00.IsSigmaAlgebraFamily F)
    (hInv : ∀ A : Set M.X, A ∈ F → M.T ⁻¹' A ∈ F) :
    @Measurable (QuotientSpace F) (QuotientSpace F)
      (quotientMeasurableSpace F hF) (quotientMeasurableSpace F hF)
      (quotientTransform M F hInv) := by
  intro B hB
  change projection F ⁻¹' (quotientTransform M F hInv ⁻¹' B) ∈ F
  rw [← Set.preimage_comp]
  have hinter :
      quotientTransform M F hInv ∘ projection F =
        projection F ∘ M.T := by
    funext x
    exact projection_intertwines M F hInv x
  rw [hinter, Set.preimage_comp]
  exact hInv _ hB

/-- The measurable quotient, equipped with the pushforward probability and the
descended dynamics. -/
def system
    (M : System.{u}) (F : SetFamily M.X)
    (hF : Chapter00.IsSigmaAlgebraFamily F) (_hsub : F ⊆ M.𝓧)
    (hInv : ∀ A : Set M.X, A ∈ F → M.T ⁻¹' A ∈ F) :
    System.{u} where
  X := QuotientSpace F
  measurableSpace := quotientMeasurableSpace F hF
  μ := @MeasureTheory.Measure.map M.X (QuotientSpace F)
    M.measurableSpace (quotientMeasurableSpace F hF) (projection F) M.μ
  T := quotientTransform M F hInv

theorem system_measurePreserving
    (M : System.{u}) (F : SetFamily M.X)
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hF : Chapter00.IsSigmaAlgebraFamily F) (hsub : F ⊆ M.𝓧)
    (hInv : ∀ A : Set M.X, A ∈ F → M.T ⁻¹' A ∈ F) :
    Chapter01.IsMeasurePreservingSystem (system M F hF hsub hInv) := by
  letI : MeasurableSpace (QuotientSpace F) :=
    quotientMeasurableSpace F hF
  let hπ :
      @Measurable M.X (QuotientSpace F) M.measurableSpace
        (quotientMeasurableSpace F hF) (projection F) :=
    fun _ hB => hsub hB
  let hT :
      @Measurable (QuotientSpace F) (QuotientSpace F)
        (quotientMeasurableSpace F hF) (quotientMeasurableSpace F hF)
        (quotientTransform M F hInv) :=
    measurable_quotientTransform M F hF hInv
  constructor
  · apply MeasureTheory.IsProbabilityMeasure.mk
    change
      (@MeasureTheory.Measure.map M.X (QuotientSpace F)
        M.measurableSpace (quotientMeasurableSpace F hF)
        (projection F) M.μ) Set.univ = 1
    rw [MeasureTheory.Measure.map_apply hπ MeasurableSet.univ]
    exact hM.1.measure_univ
  · refine ⟨hT, ?_⟩
    apply MeasureTheory.Measure.ext
    intro B hB
    change
      (@MeasureTheory.Measure.map (QuotientSpace F) (QuotientSpace F)
          (quotientMeasurableSpace F hF) (quotientMeasurableSpace F hF)
          (quotientTransform M F hInv)
          (@MeasureTheory.Measure.map M.X (QuotientSpace F)
            M.measurableSpace (quotientMeasurableSpace F hF)
            (projection F) M.μ)) B =
        (@MeasureTheory.Measure.map M.X (QuotientSpace F)
          M.measurableSpace (quotientMeasurableSpace F hF)
          (projection F) M.μ) B
    rw [MeasureTheory.Measure.map_apply hT hB]
    change
      (MeasureTheory.Measure.map (projection F) M.μ)
          (quotientTransform M F hInv ⁻¹' B) =
        (MeasureTheory.Measure.map (projection F) M.μ) B
    rw [MeasureTheory.Measure.map_apply hπ (hB.preimage hT),
      MeasureTheory.Measure.map_apply hπ hB]
    have hinter :
        quotientTransform M F hInv ∘ projection F =
          projection F ∘ M.T := by
      funext x
      exact projection_intertwines M F hInv x
    change M.μ ((quotientTransform M F hInv ∘ projection F) ⁻¹' B) =
      M.μ (projection F ⁻¹' B)
    rw [hinter]
    change M.μ (M.T ⁻¹' (projection F ⁻¹' B)) =
      M.μ (projection F ⁻¹' B)
    exact hM.2.measure_preimage (hsub hB).nullMeasurableSet

theorem projection_isFactorMap
    (M : System.{u}) (F : SetFamily M.X)
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hF : Chapter00.IsSigmaAlgebraFamily F) (hsub : F ⊆ M.𝓧)
    (hInv : ∀ A : Set M.X, A ∈ F → M.T ⁻¹' A ∈ F) :
    Chapter01.IsFactorMap M (system M F hF hsub hInv) (projection F) := by
  letI : MeasurableSpace (QuotientSpace F) :=
    quotientMeasurableSpace F hF
  let hπ :
      @Measurable M.X (QuotientSpace F) M.measurableSpace
        (quotientMeasurableSpace F hF) (projection F) :=
    fun _ hB => hsub hB
  have hN := system_measurePreserving M F hM hF hsub hInv
  refine ⟨hM, hN, Set.univ, Set.univ,
    hM.1.measure_univ, hN.1.measure_univ, ?_, ?_, ?_, ?_⟩
  · intro x _
    exact Set.mem_univ _
  · intro y _
    exact Set.mem_univ _
  · refine ⟨MeasurableSet.univ, ?_,
      hM.1.measure_univ, hN.1.measure_univ, ?_, ?_⟩
    · change projection F ⁻¹' (Set.univ : Set (QuotientSpace F)) ∈ F
      simpa using hF.1
    · intro x _
      exact Set.mem_univ _
    · intro B hB
      constructor
      · simpa only [Set.univ_inter, Set.inter_univ] using hπ hB
      · simp only [Set.univ_inter, Set.inter_univ]
        change M.μ (projection F ⁻¹' B) =
          (@MeasureTheory.Measure.map M.X (QuotientSpace F)
            M.measurableSpace (quotientMeasurableSpace F hF)
            (projection F) M.μ) B
        exact (MeasureTheory.Measure.map_apply hπ hB).symm
  · intro x _
    exact projection_intertwines M F hInv x

/-- The quotient projection realizes the prescribed sigma algebra exactly,
not merely modulo null sets. -/
theorem pulledBackSigma_eq
    (M : System.{u}) (F : SetFamily M.X)
    (hF : Chapter00.IsSigmaAlgebraFamily F) (hsub : F ⊆ M.𝓧)
    (hInv : ∀ A : Set M.X, A ∈ F → M.T ⁻¹' A ∈ F) :
    F =
      {A : Set M.X |
        ∃ B : Set (system M F hF hsub hInv).X,
          B ∈ (system M F hF hsub hInv).𝓧 ∧
            A = projection F ⁻¹' B} := by
  letI : MeasurableSpace (QuotientSpace F) :=
    quotientMeasurableSpace F hF
  ext A
  constructor
  · intro hA
    let B : Set (QuotientSpace F) := projection F '' A
    have hpre : projection F ⁻¹' B = A := by
      ext x
      constructor
      · rintro ⟨y, hyA, hyx⟩
        have hyx' : indistinguishable F y x :=
          Quotient.exact hyx
        exact (hyx' A hA).mp hyA
      · intro hxA
        exact ⟨x, hxA, rfl⟩
    refine ⟨B, ?_, hpre.symm⟩
    change projection F ⁻¹' B ∈ F
    rw [hpre]
    exact hA
  · rintro ⟨B, hB, rfl⟩
    exact hB

/-- Exact strict invariance makes the descended map injective on the quotient:
all distinctions visible before applying the map can be pulled back from
distinctions visible afterwards. -/
theorem quotientTransform_injective_of_strict
    (M : System.{u}) (F : SetFamily M.X)
    (hInv : ∀ A : Set M.X, A ∈ F → M.T ⁻¹' A ∈ F)
    (hStrict :
      {A : Set M.X | ∃ B ∈ F, A = M.T ⁻¹' B} = F) :
    Function.Injective (quotientTransform M F hInv) := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      intro A hA
      have hArange :
          A ∈ {C : Set M.X | ∃ B ∈ F, C = M.T ⁻¹' B} := by
        rw [hStrict]
        exact hA
      rcases hArange with ⟨B, hB, hAB⟩
      have hTxy : indistinguishable F (M.T x) (M.T y) :=
        Quotient.exact hqr
      simpa [hAB] using hTxy B hB

end Chapter04.InvariantSubSigmaQuotient
