import Chapter04.MeasureAlgebra.InducedMeasureAlgebra
import Chapter04.MeasureAlgebra.InvariantSubSigmaFactor

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter04.Counterexamples

/-- A two-point probability system whose transformation differs from the
identity only at the null point `true`. -/
def nullModifiedBoolSystem : System.{0} where
  X := Bool
  measurableSpace := ⊤
  μ := MeasureTheory.Measure.dirac false
  T := fun _ => false

theorem nullModifiedBoolSystem_measurePreserving :
    Chapter01.IsMeasurePreservingSystem nullModifiedBoolSystem := by
  constructor
  · change MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.dirac false)
    infer_instance
  · refine ⟨measurable_const, ?_⟩
    change
      MeasureTheory.Measure.map (fun _ : Bool => false)
        (MeasureTheory.Measure.dirac false) =
      MeasureTheory.Measure.dirac false
    rw [MeasureTheory.Measure.map_const]
    simp

theorem nullModifiedBoolSystem_lebesgue :
    IsLebesgueProbabilitySpace
      nullModifiedBoolSystem.toProbabilitySpace := by
  refine ⟨nullModifiedBoolSystem_measurePreserving.1, ?_⟩
  refine ⟨Bool, (⊤ : MeasurableSpace Bool), inferInstance,
    id, id, (fun _ => rfl), (fun _ => rfl), ?_, ?_⟩
  · intro A hA
    simpa using hA
  · intro A hA
    simpa using hA

theorem nullModifiedBoolSystem_invertibleModNull :
    IsInvertibleModNull nullModifiedBoolSystem := by
  refine ⟨id, measurable_id,
    MeasureTheory.MeasurePreserving.id _, ?_, ?_⟩
  · change
      (fun _ : Bool => false) =ᵐ[MeasureTheory.Measure.dirac false] id
    apply (MeasureTheory.ae_dirac_iff (by trivial)).2
    rfl
  · change
      (fun _ : Bool => false) =ᵐ[MeasureTheory.Measure.dirac false] id
    apply (MeasureTheory.ae_dirac_iff (by trivial)).2
    rfl

/-- Exact surjectivity of inverse image on measurable sets is strictly
stronger than invertibility modulo null sets: changing the identity map at one
null point destroys exact surjectivity but not mod-null invertibility. -/
theorem nullModifiedBoolSystem_not_strictlyInvariant :
    {A : Set Bool |
      ∃ B ∈ nullModifiedBoolSystem.𝓧,
        A = nullModifiedBoolSystem.T ⁻¹' B} ≠
      nullModifiedBoolSystem.𝓧 := by
  intro hEq
  have htrue :
      ({true} : Set Bool) ∈
        {A : Set Bool |
          ∃ B ∈ nullModifiedBoolSystem.𝓧,
            A = nullModifiedBoolSystem.T ⁻¹' B} := by
    rw [hEq]
    trivial
  rcases htrue with ⟨B, _hB, hB⟩
  by_cases hfalse : false ∈ B
  · have : false ∈ ({true} : Set Bool) := by
      rw [hB]
      exact hfalse
    simp at this
  · have : true ∉ ({true} : Set Bool) := by
      rw [hB]
      exact hfalse
    exact this (by simp)

/-- The one-point probability-preserving identity system. -/
def singletonSystem : System.{0} where
  X := Unit
  measurableSpace := ⊤
  μ := MeasureTheory.Measure.dirac ()
  T := id

theorem singletonSystem_probability :
    Chapter01.IsProbabilitySpace singletonSystem.toProbabilitySpace := by
  change MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.dirac ())
  infer_instance

/-- The one-point probability measure algebra equipped with Boolean
complement as its abstract dynamics. -/
def complementAlgebraSystem : MeasureAlgebraSystemData.{0} where
  toMeasureAlgebraData := inducedMeasureAlgebra singletonSystem.toProbabilitySpace
  transform := (inducedMeasureAlgebra singletonSystem.toProbabilitySpace).compl

theorem complementAlgebraSystem_isMeasureAlgebra :
    IsMeasureAlgebra complementAlgebraSystem.toMeasureAlgebraData := by
  exact isMeasureAlgebra_inducedMeasureAlgebra _ singletonSystem_probability

theorem complementAlgebraSystem_top_measure :
    complementAlgebraSystem.measure complementAlgebraSystem.top = 1 := by
  change (singletonSystem.toProbabilitySpace.μ Set.univ).toReal = 1
  rw [singletonSystem_probability.measure_univ]
  norm_num

theorem complementAlgebraSystem_separable :
    IsSeparableMeasureAlgebra complementAlgebraSystem.toMeasureAlgebraData := by
  let d : ℕ → complementAlgebraSystem.carrier := fun n =>
    if n = 0 then complementAlgebraSystem.bot else complementAlgebraSystem.top
  refine ⟨d, ?_⟩
  intro A ε hε
  by_cases hmem : () ∈ A.1
  · have hA : A = complementAlgebraSystem.top := by
      apply Subtype.ext
      ext x
      constructor
      · exact fun _ => Set.mem_univ x
      · intro _
        change Unit at x
        have hx : x = () := Subsingleton.elim _ _
        simpa only [hx] using hmem
    refine ⟨1, ?_⟩
    rw [hA]
    simpa [d, complementAlgebraSystem, inducedMeasureAlgebra, singletonSystem] using hε
  · have hA : A = complementAlgebraSystem.bot := by
      apply Subtype.ext
      ext x
      constructor
      · intro hxA
        change Unit at x
        have hx : x = () := Subsingleton.elim _ _
        exact (hmem (by simpa only [hx] using hxA)).elim
      · exact False.elim
    refine ⟨0, ?_⟩
    rw [hA]
    simpa [d, complementAlgebraSystem, inducedMeasureAlgebra, singletonSystem] using hε

def complementAlgebraSystemIdHom :
    MeasureAlgebraHomData complementAlgebraSystem.toMeasureAlgebraData
      complementAlgebraSystem.toMeasureAlgebraData where
  map := id

theorem complementAlgebraSystem_self_isomorphic :
    IsMeasureAlgebraSystemIsomorphism complementAlgebraSystem
      complementAlgebraSystem := by
  let hA := complementAlgebraSystem_isMeasureAlgebra
  refine ⟨complementAlgebraSystemIdHom, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a b hab
        exact hab
      · intro a b
        exact hA.1.refl _
      · intro a
        exact hA.1.refl _
      · intro f
        exact hA.1.refl _
      · intro a
        rfl
    · intro a b hab
      exact hab
    · intro a
      exact ⟨a, hA.1.refl _⟩
  · intro a
    exact hA.1.refl _

theorem complementAlgebraSystem_no_probability_spatial_model
    (M : System.{0}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    ¬ IsSpatialModelOfMeasureAlgebraSystem complementAlgebraSystem M := by
  intro hspatial
  rcases hspatial with ⟨Φ, hΦ, hcomm⟩
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let c := complementAlgebraSystem.transform complementAlgebraSystem.top
  have hcReal : (M.μ (Φ.map c).1).toReal = 0 := by
    have hm := hΦ.1.2.2.2.2 c
    simpa [c, complementAlgebraSystem, inducedMeasureAlgebra, singletonSystem] using hm
  have hc0 : M.μ (Φ.map c).1 = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff (M.μ (Φ.map c).1)).mp hcReal with h | h
    · exact h
    · exact (MeasureTheory.measure_ne_top M.μ _ h).elim
  have htopReal : (M.μ (Φ.map complementAlgebraSystem.top).1).toReal = 1 := by
    have hm := hΦ.1.2.2.2.2 complementAlgebraSystem.top
    rw [complementAlgebraSystem_top_measure] at hm
    exact hm
  have htop : M.μ (Φ.map complementAlgebraSystem.top).1 = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (MeasureTheory.measure_ne_top M.μ _) ENNReal.one_ne_top).mp
    simpa using htopReal
  have hcommTop := hcomm complementAlgebraSystem.top
  change (inducedMeasureAlgebraSystem M).equiv (Φ.map c)
    ((inducedMeasureAlgebraSystem M).transform
      (Φ.map complementAlgebraSystem.top)) at hcommTop
  simp only [inducedMeasureAlgebraSystem, dif_pos hM.2.measurable,
    inducedMeasureAlgebra] at hcommTop
  change M.μ (Chapter00.symmDiff (Φ.map c).1
    (M.T ⁻¹' (Φ.map complementAlgebraSystem.top).1)) = 0 at hcommTop
  have hae : (Φ.map c).1 =ᵐ[M.μ]
      M.T ⁻¹' (Φ.map complementAlgebraSystem.top).1 :=
    MeasureTheory.measure_symmDiff_eq_zero_iff.mp hcommTop
  have hpre : M.μ (M.T ⁻¹' (Φ.map complementAlgebraSystem.top).1) =
      M.μ (Φ.map complementAlgebraSystem.top).1 :=
    hM.2.measure_preimage (Φ.map complementAlgebraSystem.top).2.nullMeasurableSet
  have : (0 : ENNReal) = 1 := by
    calc
      0 = M.μ (Φ.map c).1 := hc0.symm
      _ = M.μ (M.T ⁻¹' (Φ.map complementAlgebraSystem.top).1) :=
        MeasureTheory.measure_congr hae
      _ = M.μ (Φ.map complementAlgebraSystem.top).1 := hpre
      _ = 1 := htop
  exact zero_ne_one this

/-- A checked counterexample to the current statement of Theorem 4.2.4. -/
theorem measureAlgebraSystemSpatialModel_statement_false :
    ¬ (IsMeasureAlgebra complementAlgebraSystem.toMeasureAlgebraData ->
      complementAlgebraSystem.measure complementAlgebraSystem.top = 1 ->
      IsSeparableMeasureAlgebra complementAlgebraSystem.toMeasureAlgebraData ->
      IsMeasureAlgebra complementAlgebraSystem.toMeasureAlgebraData ->
      complementAlgebraSystem.measure complementAlgebraSystem.top = 1 ->
      IsSeparableMeasureAlgebra complementAlgebraSystem.toMeasureAlgebraData ->
      IsMeasureAlgebraSystemIsomorphism complementAlgebraSystem complementAlgebraSystem ->
      ∃ M N : System.{0},
        IsSpatialModelOfMeasureAlgebraSystem complementAlgebraSystem M ∧
        IsSpatialModelOfMeasureAlgebraSystem complementAlgebraSystem N ∧
        Chapter01.IsIsomorphicSystems M N) := by
  intro h
  obtain ⟨M, N, hAM, _hAN, hMN⟩ := h
    complementAlgebraSystem_isMeasureAlgebra complementAlgebraSystem_top_measure
    complementAlgebraSystem_separable complementAlgebraSystem_isMeasureAlgebra
    complementAlgebraSystem_top_measure complementAlgebraSystem_separable
    complementAlgebraSystem_self_isomorphic
  exact complementAlgebraSystem_no_probability_spatial_model M hMN.1 hAM

/-- A one-point and a two-point space in which every nonempty set has infinite
measure. -/
def infiniteOnePoint : ProbabilitySpace.{0} where
  X := Unit
  measurableSpace := ⊤
  μ := ⊤

def infiniteTwoPoint : ProbabilitySpace.{0} where
  X := Bool
  measurableSpace := ⊤
  μ := ⊤

theorem top_measure_singleton
    {X : Type} [MeasurableSpace X] (x : X) :
    (⊤ : MeasureTheory.Measure X) {x} = ⊤ := by
  apply top_unique
  have hle : (⊤ : ENNReal) • MeasureTheory.Measure.dirac x ≤
      (⊤ : MeasureTheory.Measure X) := le_top
  simpa using hle {x}

theorem eventuallyEq_top_implies_eq
    {X E : Type} [MeasurableSpace X] (f g : X → E)
    (hfg : f =ᵐ[(⊤ : MeasureTheory.Measure X)] g) : f = g := by
  funext x
  by_contra hx
  have hzero : (⊤ : MeasureTheory.Measure X) {y | f y ≠ g y} = 0 := by
    have hmem := MeasureTheory.mem_ae_iff.mp hfg
    simpa only [Set.compl_setOf] using hmem
  have hle : (⊤ : MeasureTheory.Measure X) {x} ≤
      (⊤ : MeasureTheory.Measure X) {y | f y ≠ g y} := by
    apply MeasureTheory.measure_mono
    intro y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact hx
  rw [top_measure_singleton, hzero] at hle
  exact ENNReal.top_ne_zero (le_antisymm hle (zero_le _))

theorem memLp_two_top_measure_eq_zero
    {X : Type} [MeasurableSpace X] [MeasurableSingletonClass X]
    (f : X → ℂ) (hf : MeasureTheory.MemLp f 2 (⊤ : MeasureTheory.Measure X)) :
    f = 0 := by
  funext x
  by_contra hx
  change f x ≠ 0 at hx
  have hnorm : MeasureTheory.eLpNorm
      (Set.indicator ({x} : Set X) fun _ : X => f x) 2
        (⊤ : MeasureTheory.Measure X) = ⊤ := by
    rw [MeasureTheory.eLpNorm_indicator_const (MeasurableSet.singleton x)
      (by norm_num) (by norm_num)]
    rw [top_measure_singleton]
    simp [hx]
  have hle : MeasureTheory.eLpNorm
      (Set.indicator ({x} : Set X) fun _ : X => f x) 2
        (⊤ : MeasureTheory.Measure X) ≤
      MeasureTheory.eLpNorm f 2 (⊤ : MeasureTheory.Measure X) := by
    apply MeasureTheory.eLpNorm_mono
    intro y
    by_cases hy : y = x
    · subst y
      simp
    · simp [Set.indicator_of_notMem, hy]
  rw [hnorm] at hle
  exact (not_lt_of_ge hle) hf.2

def infiniteProjection (f : infiniteTwoPoint.X → ℂ) :
    infiniteOnePoint.X → ℂ := fun _ => f false

theorem infiniteProjection_isLtwoAlgebraUnitaryFor :
    IsLtwoAlgebraUnitaryFor infiniteOnePoint infiniteTwoPoint
      infiniteProjection := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g _hf _hg hfg
    change f =ᵐ[(⊤ : MeasureTheory.Measure Bool)] g at hfg
    have hfg' : f = g := eventuallyEq_top_implies_eq f g hfg
    subst g
    exact Filter.Eventually.of_forall fun _ => rfl
  · intro f g _hf _hg
    exact Filter.Eventually.of_forall fun _ => rfl
  · intro c f _hf
    exact Filter.Eventually.of_forall fun _ => rfl
  · intro f hf
    change MeasureTheory.MemLp f 2 (⊤ : MeasureTheory.Measure Bool) at hf
    have hf0 := memLp_two_top_measure_eq_zero f hf
    subst f
    constructor
    · exact MeasureTheory.MemLp.zero
    · change MeasureTheory.eLpNorm (fun _ : Unit => (0 : ℂ)) 2
          (⊤ : MeasureTheory.Measure Unit) =
        MeasureTheory.eLpNorm (fun _ : Bool => (0 : ℂ)) 2
          (⊤ : MeasureTheory.Measure Bool)
      simp
  · intro h hh ε hε
    change MeasureTheory.MemLp h 2 (⊤ : MeasureTheory.Measure Unit) at hh
    have hh0 := memLp_two_top_measure_eq_zero h hh
    subst h
    refine ⟨0, MeasureTheory.MemLp.zero, ?_⟩
    simpa [infiniteProjection, infiniteOnePoint, infiniteTwoPoint] using
      (ENNReal.ofReal_pos.mpr hε)
  · intro f _hf
    change MeasureTheory.MemLp (fun _ : Unit => f false) ⊤
      (⊤ : MeasureTheory.Measure Unit)
    apply MeasureTheory.memLp_top_of_bound
      MeasureTheory.aestronglyMeasurable_const ‖f false‖
    exact Filter.Eventually.of_forall fun _ => le_rfl
  · intro h _hh
    let f : Bool → ℂ := fun _ => h ()
    refine ⟨f, ?_, ?_⟩
    · change MeasureTheory.MemLp f ⊤ (⊤ : MeasureTheory.Measure Bool)
      apply MeasureTheory.memLp_top_of_bound
        MeasureTheory.aestronglyMeasurable_const ‖h ()‖
      exact Filter.Eventually.of_forall fun _ => le_rfl
    · exact Filter.Eventually.of_forall fun x => by
        change h () = h x
        congr
  · exact Filter.Eventually.of_forall fun _ => rfl
  · intro f g _hf _hg
    exact Filter.Eventually.of_forall fun _ => rfl

theorem infinite_spaces_haveLtwoAlgebraUnitary :
    HasLtwoAlgebraUnitary infiniteOnePoint infiniteTwoPoint :=
  ⟨infiniteProjection, infiniteProjection_isLtwoAlgebraUnitaryFor⟩

theorem top_measure_nonempty_ne_zero
    {X : Type} [MeasurableSpace X] {s : Set X} (hs : s.Nonempty) :
    (⊤ : MeasureTheory.Measure X) s ≠ 0 := by
  rcases hs with ⟨x, hx⟩
  intro hzero
  have hle : (⊤ : MeasureTheory.Measure X) {x} ≤
      (⊤ : MeasureTheory.Measure X) s := by
    exact MeasureTheory.measure_mono (Set.singleton_subset_iff.mpr hx)
  rw [top_measure_singleton, hzero] at hle
  exact ENNReal.top_ne_zero (le_antisymm hle (zero_le _))

theorem infiniteOnePoint_equiv_of_same_membership
    (A B : (inducedMeasureAlgebra infiniteOnePoint).carrier)
    (hmem : (() ∈ A.1 ↔ () ∈ B.1)) :
    (inducedMeasureAlgebra infiniteOnePoint).equiv A B := by
  have hsets : A.1 = B.1 := by
    ext x
    change Unit at x
    have hx : x = () := Subsingleton.elim _ _
    subst x
    exact hmem
  simp [inducedMeasureAlgebra, Chapter00.symmDiff, hsets]

theorem infiniteTwoPoint_not_equiv_of_symmDiff_nonempty
    (A B : (inducedMeasureAlgebra infiniteTwoPoint).carrier)
    (h : (Chapter00.symmDiff A.1 B.1).Nonempty) :
    ¬ (inducedMeasureAlgebra infiniteTwoPoint).equiv A B := by
  change (⊤ : MeasureTheory.Measure Bool)
    (Chapter00.symmDiff A.1 B.1) ≠ 0
  exact top_measure_nonempty_ne_zero h

theorem infinite_spaces_not_conjugate :
    ¬ AreConjugateProbabilitySpaces infiniteOnePoint infiniteTwoPoint := by
  rintro ⟨Φ, hΦ⟩
  let b₀ : (inducedMeasureAlgebra infiniteTwoPoint).carrier :=
    ⟨∅, MeasurableSet.empty⟩
  let b₁ : (inducedMeasureAlgebra infiniteTwoPoint).carrier :=
    ⟨{false}, MeasurableSet.singleton false⟩
  let b₂ : (inducedMeasureAlgebra infiniteTwoPoint).carrier :=
    ⟨Set.univ, MeasurableSet.univ⟩
  have h01 : ¬ (inducedMeasureAlgebra infiniteTwoPoint).equiv b₀ b₁ := by
    apply infiniteTwoPoint_not_equiv_of_symmDiff_nonempty
    exact ⟨false, by simp [b₀, b₁, Chapter00.symmDiff]⟩
  have h12 : ¬ (inducedMeasureAlgebra infiniteTwoPoint).equiv b₁ b₂ := by
    apply infiniteTwoPoint_not_equiv_of_symmDiff_nonempty
    exact ⟨true, by simp [b₁, b₂, Chapter00.symmDiff]⟩
  have h02 : ¬ (inducedMeasureAlgebra infiniteTwoPoint).equiv b₀ b₂ := by
    apply infiniteTwoPoint_not_equiv_of_symmDiff_nonempty
    exact ⟨false, by simp [b₀, b₂, Chapter00.symmDiff]⟩
  have hinj := hΦ.2.1
  by_cases h₀ : () ∈ (Φ.map b₀).1
  · by_cases h₁ : () ∈ (Φ.map b₁).1
    · apply h01
      apply hinj b₀ b₁
      apply infiniteOnePoint_equiv_of_same_membership
      exact ⟨fun _ => h₁, fun _ => h₀⟩
    · by_cases h₂ : () ∈ (Φ.map b₂).1
      · apply h02
        apply hinj b₀ b₂
        apply infiniteOnePoint_equiv_of_same_membership
        exact ⟨fun _ => h₂, fun _ => h₀⟩
      · apply h12
        apply hinj b₁ b₂
        apply infiniteOnePoint_equiv_of_same_membership
        exact ⟨fun h => (h₁ h).elim, fun h => (h₂ h).elim⟩
  · by_cases h₁ : () ∈ (Φ.map b₁).1
    · by_cases h₂ : () ∈ (Φ.map b₂).1
      · apply h12
        apply hinj b₁ b₂
        apply infiniteOnePoint_equiv_of_same_membership
        exact ⟨fun _ => h₂, fun _ => h₁⟩
      · apply h02
        apply hinj b₀ b₂
        apply infiniteOnePoint_equiv_of_same_membership
        exact ⟨fun h => (h₀ h).elim, fun h => (h₂ h).elim⟩
    · apply h01
      apply hinj b₀ b₁
      apply infiniteOnePoint_equiv_of_same_membership
      exact ⟨fun h => (h₀ h).elim, fun h => (h₁ h).elim⟩

/-- A checked counterexample to the current statement of Theorem 4.1.23. -/
theorem probabilitySpaceConjugacyIffLtwoAlgebraUnitary_statement_false :
    ¬ (AreConjugateProbabilitySpaces infiniteOnePoint infiniteTwoPoint ↔
      HasLtwoAlgebraUnitary infiniteOnePoint infiniteTwoPoint) := by
  intro h
  exact infinite_spaces_not_conjugate
    (h.mpr infinite_spaces_haveLtwoAlgebraUnitary)

theorem singletonSystem_bernoulli :
    LegacyIsBernoulliSystem singletonSystem := by
  let ω : ℤ → Unit := fun _ => ()
  let e : singletonSystem.X → (ℤ → Unit) := fun _ => ω
  let inv : (ℤ → Unit) → singletonSystem.X := fun _ => ()
  refine ⟨Unit, (⊤ : MeasurableSpace Unit), MeasureTheory.Measure.dirac (),
    inferInstance, MeasureTheory.Measure.dirac ω, inferInstance, e, inv,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Measurable (fun _ : Unit => ω)
    exact measurable_const
  · change Measurable (fun _ : (ℤ → Unit) => ())
    exact measurable_const
  · filter_upwards with x
    change (() : Unit) = x
    exact Subsingleton.elim _ _
  · filter_upwards with x
    exact Subsingleton.elim _ _
  · simp [e, singletonSystem]
  · filter_upwards with x n
    exact Subsingleton.elim _ _
  · intro I C hC
    by_cases hall : ∀ i ∈ I, () ∈ C i
    · have hevent : {x : ℤ → Unit | ∀ i ∈ I, x i ∈ C i} = Set.univ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro i hi
        simpa only [Subsingleton.elim (x i) ()] using hall i hi
      rw [hevent]
      simp only [MeasureTheory.measure_univ]
      symm
      apply Finset.prod_eq_one
      intro j hj
      simp [hall j hj]
    · push_neg at hall
      obtain ⟨i, hiI, hiC⟩ := hall
      have hevent : {x : ℤ → Unit | ∀ i ∈ I, x i ∈ C i} = ∅ := by
        ext x
        constructor
        · intro hx
          have hxi := hx i hiI
          exact (hiC (by simpa only [Subsingleton.elim (x i) ()] using hxi)).elim
        · exact False.elim
      rw [hevent]
      simp only [MeasureTheory.measure_empty]
      symm
      apply Finset.prod_eq_zero hiI
      simp [hiC]

theorem singletonSystem_not_kolmogorov :
    ¬ IsKolmogorovSystem singletonSystem := by
  intro hK
  rcases hK.2.2.2.1 with ⟨B, _hB, hBpos, hBlt⟩
  by_cases hmem : () ∈ B
  · have hBuniv : B = Set.univ := by
      ext x
      constructor
      · exact fun _ => Set.mem_univ x
      · intro _
        have hx : x = () := by
          change Unit at x
          exact Subsingleton.elim x ()
        simpa only [hx] using hmem
    rw [hBuniv] at hBlt
    simp [singletonSystem] at hBlt
  · have hBempty : B = ∅ := by
      ext x
      constructor
      · intro hxB
        have hx : x = () := by
          change Unit at x
          exact Subsingleton.elim x ()
        exact (hmem (by simpa only [hx] using hxB)).elim
      · exact False.elim
    rw [hBempty] at hBpos
    simp [singletonSystem] at hBpos

/-- A checked counterexample to the current statement of Theorem 4.3.4. -/
theorem exists_bernoulli_not_kolmogorov :
    ∃ M : System.{0}, LegacyIsBernoulliSystem M ∧ ¬ IsKolmogorovSystem M :=
  ⟨singletonSystem, singletonSystem_bernoulli, singletonSystem_not_kolmogorov⟩

end Chapter04.Counterexamples
