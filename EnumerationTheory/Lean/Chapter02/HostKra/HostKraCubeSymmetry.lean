import Chapter02.HostKra.HostKraDualFunction
import Chapter02.HostKra.HostKraErgodicRelativeJoining
import Chapter02.Recurrence.MultipleKhintchineProductInvariant

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraCubeSymmetry

universe u

open HostKraStandardRelativeJoining
open HostKraRelativeJoiningComplex
open HostKraCubeFactors
open HostKraDualFunction
open MultipleKhintchineProductInvariant

local instance cartesianProductSystem_standardBorel
    (M N : System) [StandardBorelSpace M.X] [StandardBorelSpace N.X] :
    StandardBorelSpace
      (MultipleKhintchineCartesian.productSystem M N).X := by
  change StandardBorelSpace (M.X × N.X)
  infer_instance

/-- The side action which applies the dynamics only on the first copy of a
relative independent joining. -/
def relativeJoiningFirstSide
    (M : System.{u}) : M.X × M.X → M.X × M.X :=
  fun p ↦ (M.T p.1, p.2)

/-- The side action which applies the dynamics only on the second copy of a
relative independent joining. -/
def relativeJoiningSecondSide
    (M : System.{u}) : M.X × M.X → M.X × M.X :=
  fun p ↦ (p.1, M.T p.2)

lemma relativeJoiningFirstSide_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasurePreserving
      (relativeJoiningFirstSide M)
      (relativeJoiningMeasure M hM)
      (relativeJoiningMeasure M hM) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let ν := relativeJoiningMeasure M hM
  have hside : Measurable (relativeJoiningFirstSide M) :=
    Measurable.prod
      (hM.2.measurable.comp measurable_fst) measurable_snd
  refine ⟨hside, ?_⟩
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply hside (hA.prod hB)]
  have hpre :
      relativeJoiningFirstSide M ⁻¹' (A ×ˢ B) =
        (M.T ⁻¹' A) ×ˢ B := by
    ext p
    rfl
  rw [hpre]
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top ν ((M.T ⁻¹' A) ×ˢ B))
    (measure_ne_top ν (A ×ˢ B))).mp
  rw [relativeJoiningMeasure_apply_prod_toReal M hM
      (M.T ⁻¹' A) B (hA.preimage hM.2.measurable) hB,
    relativeJoiningMeasure_apply_prod_toReal M hM A B hA hB,
    HostKraRelativeJoining.relativeRectangleMass_eq_integral_condExp,
    HostKraRelativeJoining.relativeRectangleMass_eq_integral_condExp]
  have hind :
      HostKraRelativeJoining.indicatorReal (M.T ⁻¹' A) =
        fun x ↦ HostKraRelativeJoining.indicatorReal A (M.T x) := by
    funext x
    rfl
  rw [hind]
  have hAint :
      Integrable (HostKraRelativeJoining.indicatorReal A) M.μ :=
    (HostKraRelativeJoining.indicatorReal_memLp M hM A hA)
      |>.integrable (by norm_num)
  have hce :=
    HostKraRelativeJoining.condExp_invariant_comp_real
      M hM (HostKraRelativeJoining.indicatorReal A) hAint
  apply integral_congr_ae
  filter_upwards [hce] with x hx
  rw [hx]

lemma relativeJoiningSecondSide_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasurePreserving
      (relativeJoiningSecondSide M)
      (relativeJoiningMeasure M hM)
      (relativeJoiningMeasure M hM) := by
  let σ : M.X × M.X → M.X × M.X := fun p ↦ (p.2, p.1)
  have hσ :
      MeasurePreserving σ
        (relativeJoiningMeasure M hM)
        (relativeJoiningMeasure M hM) := by
    simpa only [σ] using relativeJoining_swap_measurePreserving M hM
  have hconj :
      relativeJoiningSecondSide M =
        σ ∘ relativeJoiningFirstSide M ∘ σ := by
    funext p
    rfl
  rw [hconj]
  exact hσ.comp ((relativeJoiningFirstSide_measurePreserving M hM).comp hσ)

/-- Equality on measurable four-coordinate boxes determines a measure on
`(X × X) × (X × X)`.  This two-step form of `Measure.ext_prod` avoids
choosing an explicit generating semiring for the fourfold product. -/
theorem Measure.ext_fourfold
    {X : Type u} [MeasurableSpace X]
    (μ ν : Measure ((X × X) × (X × X)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hbox : ∀ A00 A01 A10 A11 : Set X,
      MeasurableSet A00 → MeasurableSet A01 →
      MeasurableSet A10 → MeasurableSet A11 →
      μ ((A00 ×ˢ A01) ×ˢ (A10 ×ˢ A11)) =
        ν ((A00 ×ˢ A01) ×ˢ (A10 ×ˢ A11))) :
    μ = ν := by
  have hrightBox (B10 B11 : Set X)
      (hB10 : MeasurableSet B10) (hB11 : MeasurableSet B11) :
      ∀ A : Set (X × X), MeasurableSet A →
        μ (A ×ˢ (B10 ×ˢ B11)) =
          ν (A ×ˢ (B10 ×ˢ B11)) := by
    let B : Set (X × X) := B10 ×ˢ B11
    let μB : Measure (X × X) :=
      Measure.map Prod.fst (μ.restrict (Set.univ ×ˢ B))
    let νB : Measure (X × X) :=
      Measure.map Prod.fst (ν.restrict (Set.univ ×ˢ B))
    have hμBνB : μB = νB := by
      apply Measure.ext_prod
      intro A00 A01 hA00 hA01
      dsimp only [μB, νB]
      rw [Measure.map_apply measurable_fst (hA00.prod hA01),
        Measure.map_apply measurable_fst (hA00.prod hA01),
        Measure.restrict_apply
          ((hA00.prod hA01).preimage measurable_fst),
        Measure.restrict_apply
          ((hA00.prod hA01).preimage measurable_fst)]
      have hset :
          Prod.fst ⁻¹' (A00 ×ˢ A01) ∩
              (Set.univ ×ˢ B) =
            (A00 ×ˢ A01) ×ˢ (B10 ×ˢ B11) := by
        ext q
        simp [B]
      rw [hset]
      exact hbox A00 A01 B10 B11 hA00 hA01 hB10 hB11
    intro A hA
    have hvalue := congrArg (fun ρ : Measure (X × X) ↦ ρ A) hμBνB
    dsimp only [μB, νB] at hvalue
    dsimp only [B] at hvalue
    rw [Measure.map_apply measurable_fst hA,
      Measure.map_apply measurable_fst hA,
      Measure.restrict_apply
        (hA.preimage measurable_fst),
      Measure.restrict_apply
        (hA.preimage measurable_fst)] at hvalue
    have hset :
        Prod.fst ⁻¹' A ∩ (Set.univ ×ˢ B) =
          A ×ˢ (B10 ×ˢ B11) := by
      ext q
      simp [B]
    rwa [hset] at hvalue
  apply Measure.ext_prod
  intro A B hA hB
  let μA : Measure (X × X) :=
    Measure.map Prod.snd (μ.restrict (A ×ˢ Set.univ))
  let νA : Measure (X × X) :=
    Measure.map Prod.snd (ν.restrict (A ×ˢ Set.univ))
  have hμAνA : μA = νA := by
    apply Measure.ext_prod
    intro B10 B11 hB10 hB11
    dsimp only [μA, νA]
    rw [Measure.map_apply measurable_snd (hB10.prod hB11),
      Measure.map_apply measurable_snd (hB10.prod hB11),
      Measure.restrict_apply
        ((hB10.prod hB11).preimage measurable_snd),
      Measure.restrict_apply
        ((hB10.prod hB11).preimage measurable_snd)]
    have hset :
        Prod.snd ⁻¹' (B10 ×ˢ B11) ∩
            (A ×ˢ Set.univ) =
          A ×ˢ (B10 ×ˢ B11) := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
        Set.mem_univ, and_true]
      tauto
    rw [hset]
    exact hrightBox B10 B11 hB10 hB11 A hA
  have hvalue := congrArg (fun ρ : Measure (X × X) ↦ ρ B) hμAνA
  dsimp only [μA, νA] at hvalue
  rw [Measure.map_apply measurable_snd hB,
    Measure.map_apply measurable_snd hB,
    Measure.restrict_apply (hB.preimage measurable_snd),
    Measure.restrict_apply (hB.preimage measurable_snd)] at hvalue
  have hset :
      Prod.snd ⁻¹' B ∩ (A ×ˢ Set.univ) = A ×ˢ B := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
      Set.mem_univ, and_true]
    tauto
  rwa [hset] at hvalue

/-- Equality on measurable eight-coordinate boxes determines a finite
measure on the three-times nested binary product.  This is the exact
extension principle needed for the remaining three-cube coordinate
permutation. -/
private theorem Measure.ext_eightfold
    {X : Type u} [MeasurableSpace X]
    (μ ν : Measure
      (((X × X) × (X × X)) × ((X × X) × (X × X))))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hbox : ∀ A000 A001 A010 A011 A100 A101 A110 A111 : Set X,
      MeasurableSet A000 → MeasurableSet A001 →
      MeasurableSet A010 → MeasurableSet A011 →
      MeasurableSet A100 → MeasurableSet A101 →
      MeasurableSet A110 → MeasurableSet A111 →
      μ (((A000 ×ˢ A001) ×ˢ (A010 ×ˢ A011)) ×ˢ
          ((A100 ×ˢ A101) ×ˢ (A110 ×ˢ A111))) =
        ν (((A000 ×ˢ A001) ×ˢ (A010 ×ˢ A011)) ×ˢ
          ((A100 ×ˢ A101) ×ˢ (A110 ×ˢ A111)))) :
    μ = ν := by
  let Q := (X × X) × (X × X)
  have hrightBox
      (B100 B101 B110 B111 : Set X)
      (hB100 : MeasurableSet B100) (hB101 : MeasurableSet B101)
      (hB110 : MeasurableSet B110) (hB111 : MeasurableSet B111) :
      ∀ A : Set Q, MeasurableSet A →
        μ (A ×ˢ ((B100 ×ˢ B101) ×ˢ (B110 ×ˢ B111))) =
          ν (A ×ˢ ((B100 ×ˢ B101) ×ˢ (B110 ×ˢ B111))) := by
    let B : Set Q :=
      (B100 ×ˢ B101) ×ˢ (B110 ×ˢ B111)
    let μB : Measure Q :=
      Measure.map Prod.fst (μ.restrict (Set.univ ×ˢ B))
    let νB : Measure Q :=
      Measure.map Prod.fst (ν.restrict (Set.univ ×ˢ B))
    have hμBνB : μB = νB := by
      apply Measure.ext_fourfold
      intro A000 A001 A010 A011 hA000 hA001 hA010 hA011
      dsimp only [μB, νB]
      rw [Measure.map_apply measurable_fst
            ((hA000.prod hA001).prod (hA010.prod hA011)),
        Measure.map_apply measurable_fst
            ((hA000.prod hA001).prod (hA010.prod hA011)),
        Measure.restrict_apply
          (((hA000.prod hA001).prod (hA010.prod hA011)).preimage
            measurable_fst),
        Measure.restrict_apply
          (((hA000.prod hA001).prod (hA010.prod hA011)).preimage
            measurable_fst)]
      have hset :
          Prod.fst ⁻¹'
                ((A000 ×ˢ A001) ×ˢ (A010 ×ˢ A011)) ∩
              (Set.univ ×ˢ B) =
            ((A000 ×ˢ A001) ×ˢ (A010 ×ˢ A011)) ×ˢ
              ((B100 ×ˢ B101) ×ˢ (B110 ×ˢ B111)) := by
        ext q
        simp [B]
      rw [hset]
      exact hbox A000 A001 A010 A011 B100 B101 B110 B111
        hA000 hA001 hA010 hA011 hB100 hB101 hB110 hB111
    intro A hA
    have hvalue := congrArg (fun ρ : Measure Q ↦ ρ A) hμBνB
    dsimp only [μB, νB] at hvalue
    dsimp only [B] at hvalue
    rw [Measure.map_apply measurable_fst hA,
      Measure.map_apply measurable_fst hA,
      Measure.restrict_apply (hA.preimage measurable_fst),
      Measure.restrict_apply (hA.preimage measurable_fst)] at hvalue
    have hset :
        Prod.fst ⁻¹' A ∩
            (Set.univ ×ˢ
              ((B100 ×ˢ B101) ×ˢ (B110 ×ˢ B111))) =
          A ×ˢ ((B100 ×ˢ B101) ×ˢ (B110 ×ˢ B111)) := by
      ext q
      simp
    rwa [hset] at hvalue
  apply Measure.ext_prod
  intro A B hA hB
  let μA : Measure Q :=
    Measure.map Prod.snd (μ.restrict (A ×ˢ Set.univ))
  let νA : Measure Q :=
    Measure.map Prod.snd (ν.restrict (A ×ˢ Set.univ))
  have hμAνA : μA = νA := by
    apply Measure.ext_fourfold
    intro B100 B101 B110 B111 hB100 hB101 hB110 hB111
    dsimp only [μA, νA]
    rw [Measure.map_apply measurable_snd
          ((hB100.prod hB101).prod (hB110.prod hB111)),
      Measure.map_apply measurable_snd
          ((hB100.prod hB101).prod (hB110.prod hB111)),
      Measure.restrict_apply
        (((hB100.prod hB101).prod (hB110.prod hB111)).preimage
          measurable_snd),
      Measure.restrict_apply
        (((hB100.prod hB101).prod (hB110.prod hB111)).preimage
          measurable_snd)]
    have hset :
        Prod.snd ⁻¹'
              ((B100 ×ˢ B101) ×ˢ (B110 ×ˢ B111)) ∩
            (A ×ˢ Set.univ) =
          A ×ˢ ((B100 ×ˢ B101) ×ˢ (B110 ×ˢ B111)) := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
        Set.mem_univ, and_true]
      tauto
    rw [hset]
    exact hrightBox B100 B101 B110 B111
      hB100 hB101 hB110 hB111 A hA
  have hvalue := congrArg (fun ρ : Measure Q ↦ ρ B) hμAνA
  dsimp only [μA, νA] at hvalue
  rw [Measure.map_apply measurable_snd hB,
    Measure.map_apply measurable_snd hB,
    Measure.restrict_apply (hB.preimage measurable_snd),
    Measure.restrict_apply (hB.preimage measurable_snd)] at hvalue
  have hset :
      Prod.snd ⁻¹' B ∩ (A ×ˢ Set.univ) = A ×ˢ B := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
      Set.mem_univ, and_true]
    tauto
  rwa [hset] at hvalue

/-- Transpose the two middle coordinates of a square. -/
def squareTranspose {X : Type u} :
    (X × X) × (X × X) → (X × X) × (X × X) :=
  fun q ↦ ((q.1.1, q.2.1), (q.1.2, q.2.2))

lemma squareTranspose_measurable
    {X : Type u} [MeasurableSpace X] :
    Measurable (squareTranspose : (X × X) × (X × X) →
      (X × X) × (X × X)) := by
  fun_prop

lemma squareTranspose_involutive {X : Type u} :
    Function.Involutive
      (squareTranspose : (X × X) × (X × X) →
        (X × X) × (X × X)) := by
  intro q
  rfl

/-- Each vertex coordinate of the second relative cube has the original
base measure as its marginal. -/
private theorem cubeTwo_coord00_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasurePreserving
      (fun q : (M.X × M.X) × (M.X × M.X) ↦ q.1.1)
      (relativeCubeSystemTwo M hM).μ M.μ := by
  exact
    (relativeJoining_fst_measurePreserving M hM).comp
      (relativeJoining_fst_measurePreserving
        (relativeCubeSystemOne M hM)
        (relativeCubeSystemOne_mps M hM))

private theorem cubeTwo_coord01_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasurePreserving
      (fun q : (M.X × M.X) × (M.X × M.X) ↦ q.1.2)
      (relativeCubeSystemTwo M hM).μ M.μ := by
  exact
    (relativeJoining_snd_measurePreserving M hM).comp
      (relativeJoining_fst_measurePreserving
        (relativeCubeSystemOne M hM)
        (relativeCubeSystemOne_mps M hM))

private theorem cubeTwo_coord10_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasurePreserving
      (fun q : (M.X × M.X) × (M.X × M.X) ↦ q.2.1)
      (relativeCubeSystemTwo M hM).μ M.μ := by
  exact
    (relativeJoining_fst_measurePreserving M hM).comp
      (relativeJoining_snd_measurePreserving
        (relativeCubeSystemOne M hM)
        (relativeCubeSystemOne_mps M hM))

private theorem cubeTwo_coord11_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasurePreserving
      (fun q : (M.X × M.X) × (M.X × M.X) ↦ q.2.2)
      (relativeCubeSystemTwo M hM).μ M.μ := by
  exact
    (relativeJoining_snd_measurePreserving M hM).comp
      (relativeJoining_snd_measurePreserving
        (relativeCubeSystemOne M hM)
        (relativeCubeSystemOne_mps M hM))

/-- Integrating four base indicator vectors on the four vertices of the
second cube recovers the measure of the corresponding fourfold box. -/
private theorem integral_fourIndicator_eq_measure
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A00 A01 A10 A11 : Set M.X)
    (hA00 : MeasurableSet A00) (hA01 : MeasurableSet A01)
    (hA10 : MeasurableSet A10) (hA11 : MeasurableSet A11) :
    ∫ q : (M.X × M.X) × (M.X × M.X),
        (MultipleKhintchineCharacteristic.indicatorLp M hM A00 hA00 q.1.1 *
          MultipleKhintchineCharacteristic.indicatorLp M hM A01 hA01 q.1.2) *
        (MultipleKhintchineCharacteristic.indicatorLp M hM A10 hA10 q.2.1 *
          MultipleKhintchineCharacteristic.indicatorLp M hM A11 hA11 q.2.2)
      ∂(relativeCubeSystemTwo M hM).μ =
      ((((relativeCubeSystemTwo M hM).μ
        ((A00 ×ˢ A01) ×ˢ (A10 ×ˢ A11))).toReal : ℝ) : ℂ) := by
  let I00 :=
    MultipleKhintchineCharacteristic.indicatorLp M hM A00 hA00
  let I01 :=
    MultipleKhintchineCharacteristic.indicatorLp M hM A01 hA01
  let I10 :=
    MultipleKhintchineCharacteristic.indicatorLp M hM A10 hA10
  let I11 :=
    MultipleKhintchineCharacteristic.indicatorLp M hM A11 hA11
  have h00 :=
    (cubeTwo_coord00_measurePreserving M hM).quasiMeasurePreserving.ae_eq
      (MultipleKhintchineCharacteristic.indicatorLp_coe
        M hM A00 hA00)
  have h01 :=
    (cubeTwo_coord01_measurePreserving M hM).quasiMeasurePreserving.ae_eq
      (MultipleKhintchineCharacteristic.indicatorLp_coe
        M hM A01 hA01)
  have h10 :=
    (cubeTwo_coord10_measurePreserving M hM).quasiMeasurePreserving.ae_eq
      (MultipleKhintchineCharacteristic.indicatorLp_coe
        M hM A10 hA10)
  have h11 :=
    (cubeTwo_coord11_measurePreserving M hM).quasiMeasurePreserving.ae_eq
      (MultipleKhintchineCharacteristic.indicatorLp_coe
        M hM A11 hA11)
  calc
    (∫ q : (M.X × M.X) × (M.X × M.X),
        (I00 q.1.1 * I01 q.1.2) *
          (I10 q.2.1 * I11 q.2.2)
        ∂(relativeCubeSystemTwo M hM).μ) =
        ∫ q, ((A00 ×ˢ A01) ×ˢ (A10 ×ˢ A11)).indicator
          (fun _ ↦ (1 : ℂ)) q
          ∂(relativeCubeSystemTwo M hM).μ := by
      apply integral_congr_ae
      filter_upwards [h00, h01, h10, h11] with q hq00 hq01 hq10 hq11
      change I00 q.1.1 = CorrelationMean.indicatorComplex A00 q.1.1 at hq00
      change I01 q.1.2 = CorrelationMean.indicatorComplex A01 q.1.2 at hq01
      change I10 q.2.1 = CorrelationMean.indicatorComplex A10 q.2.1 at hq10
      change I11 q.2.2 = CorrelationMean.indicatorComplex A11 q.2.2 at hq11
      rw [hq00, hq01, hq10, hq11]
      by_cases h00mem : q.1.1 ∈ A00 <;>
        by_cases h01mem : q.1.2 ∈ A01 <;>
        by_cases h10mem : q.2.1 ∈ A10 <;>
        by_cases h11mem : q.2.2 ∈ A11 <;>
        simp [CorrelationMean.indicatorComplex, Set.indicator,
          h00mem, h01mem, h10mem, h11mem]
    _ = ((((relativeCubeSystemTwo M hM).μ
        ((A00 ×ˢ A01) ×ˢ (A10 ×ˢ A11))).toReal : ℝ) : ℂ) := by
      change
        (∫ q : (M.X × M.X) × (M.X × M.X),
          ((A00 ×ˢ A01) ×ˢ (A10 ×ˢ A11)).indicator
            (fun _ ↦ (1 : ℂ)) q
          ∂(relativeCubeSystemTwo M hM).μ) = _
      rw [integral_indicator ((hA00.prod hA01).prod (hA10.prod hA11))]
      simp
      rfl

/-- In the ergodic case, integration of a separated four-vertex product on
the second Host--Kra cube is the row-oriented Cartesian invariant pairing. -/
theorem integral_fourVertex_eq_rowCubePairing
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ) :
    ∫ q : (M.X × M.X) × (M.X × M.X),
        (F00 q.1.1 * F01 q.1.2) *
          (F10 q.2.1 * F11 q.2.2)
      ∂relativeJoiningMeasure
        (MultipleKhintchineCartesian.productSystem M M)
        (MultipleKhintchineCartesian.productSystem_mps M M hM hM) =
      rowCubePairing M hM F00 F01 F10 F11 := by
  let P := MultipleKhintchineCartesian.productSystem M M
  let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
  letI : StandardBorelSpace P.X := by
    dsimp only [P, MultipleKhintchineCartesian.productSystem]
    infer_instance
  let A := separatedProductLp M hM F00 F01
  let B := separatedProductLp M hM F10 F11
  have hpair :=
    inner_pullback_eq_invariantProjection P hP
      (ForwardKroneckerFactor.lpStar P B) A
  rw [L2.inner_def] at hpair
  have hsnd :=
    relativeSndCLM_coe P hP
      (ForwardKroneckerFactor.lpStar P B)
  have hfst := relativeFstCLM_coe P hP A
  have hstarB := ForwardKroneckerFactor.lpStar_coe P B
  have hA := separatedProductLp_coe M hM F00 F01
  have hB := separatedProductLp_coe M hM F10 F11
  have hintegral :
      ∫ q : P.X × P.X,
          (F00 q.1.1 * F01 q.1.2) *
            (F10 q.2.1 * F11 q.2.2)
        ∂relativeJoiningMeasure P hP =
        @inner ℂ (Lp ℂ 2 P.μ) _
          (invariantProjectionCLM P hP
            (ForwardKroneckerFactor.lpStar P B))
          (invariantProjectionCLM P hP A) := by
    rw [← hpair]
    apply integral_congr_ae
    have hstarBpull :=
      (relativeJoining_snd_measurePreserving P hP)
        |>.quasiMeasurePreserving.ae_eq hstarB
    have hBpull :=
      (relativeJoining_snd_measurePreserving P hP)
        |>.quasiMeasurePreserving.ae_eq hB
    have hApull :=
      (relativeJoining_fst_measurePreserving P hP)
        |>.quasiMeasurePreserving.ae_eq hA
    filter_upwards [hsnd, hfst, hstarBpull, hBpull, hApull] with
        q hs hf hsb hb ha
    change
      ForwardKroneckerFactor.lpStar P B q.2 = star (B q.2) at hsb
    change B q.2 = F10 q.2.1 * F11 q.2.2 at hb
    change A q.1 = F00 q.1.1 * F01 q.1.2 at ha
    simp only [RCLike.inner_apply, starRingEnd_apply]
    rw [hs, hf, hsb, hb, ha]
    simp only [star_mul, star_star]
  have hproj :
      invariantProjectionCLM P hP =
        productInvariantProjectionCLM M hM := by
    rfl
  change
    (∫ q : P.X × P.X,
        (F00 q.1.1 * F01 q.1.2) *
          (F10 q.2.1 * F11 q.2.2)
      ∂relativeJoiningMeasure P hP) =
      rowCubePairing M hM F00 F01 F10 F11
  rw [hintegral, hproj]
  rw [lpStar_separatedProductLp M hM F10 F11]
  rfl

/-- The same integral after grouping vertices by columns is the
column-oriented invariant pairing. -/
theorem integral_fourVertex_transposed_eq_columnCubePairing
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ) :
    ∫ q : (M.X × M.X) × (M.X × M.X),
        (F00 q.1.1 * F10 q.1.2) *
          (F01 q.2.1 * F11 q.2.2)
      ∂relativeJoiningMeasure
        (MultipleKhintchineCartesian.productSystem M M)
        (MultipleKhintchineCartesian.productSystem_mps M M hM hM) =
      columnCubePairing M hM F00 F01 F10 F11 := by
  exact integral_fourVertex_eq_rowCubePairing
    M hM F00 F10 F01 F11

/-- The middle-coordinate transposition symmetry for four separated `L²`
weights on the second Host--Kra cube of an ergodic base system. -/
theorem integral_fourVertex_transpose
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ) :
    ∫ q : (M.X × M.X) × (M.X × M.X),
        (F00 q.1.1 * F01 q.1.2) *
          (F10 q.2.1 * F11 q.2.2)
      ∂relativeJoiningMeasure
        (MultipleKhintchineCartesian.productSystem M M)
        (MultipleKhintchineCartesian.productSystem_mps M M hM hM) =
    ∫ q : (M.X × M.X) × (M.X × M.X),
        (F00 q.1.1 * F10 q.1.2) *
          (F01 q.2.1 * F11 q.2.2)
      ∂relativeJoiningMeasure
        (MultipleKhintchineCartesian.productSystem M M)
        (MultipleKhintchineCartesian.productSystem_mps M M hM hM) := by
  rw [integral_fourVertex_eq_rowCubePairing
      M hM F00 F01 F10 F11,
    integral_fourVertex_transposed_eq_columnCubePairing
      M hM F00 F01 F10 F11]
  exact sub_eq_zero.mp
    (cubePairingDefect_eq_zero M hM hErg F00 F01 F10 F11)

/-- In an ergodic system the recursively defined second cube measure is the
relative joining built from the ordinary Cartesian-square system. -/
theorem relativeCubeSystemTwo_measure_eq_cartesianRelativeJoining
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M) :
    (relativeCubeSystemTwo M hM).μ =
      relativeJoiningMeasure
        (MultipleKhintchineCartesian.productSystem M M)
        (MultipleKhintchineCartesian.productSystem_mps M M hM hM) := by
  let C := relativeCubeSystemOne M hM
  let hC := relativeCubeSystemOne_mps M hM
  let P := MultipleKhintchineCartesian.productSystem M M
  let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
  have hCP : C = P :=
    Chapter02.HostKraErgodicRelativeJoining.relativeCubeSystemOne_eq_productSystem_of_ergodic
      M hM hErg
  change relativeJoiningMeasure C hC = relativeJoiningMeasure P hP
  apply Measure.ext_prod
  intro A B hA hB
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top (relativeJoiningMeasure C hC) (A ×ˢ B))
    (measure_ne_top (relativeJoiningMeasure P hP) (A ×ˢ B))).mp
  rw [relativeJoiningMeasure_apply_prod_toReal C hC A B hA hB,
    relativeJoiningMeasure_apply_prod_toReal P hP A B hA hB]
  rw [HostKraRelativeJoining.relativeRectangleMass_eq_integral_condExp,
    HostKraRelativeJoining.relativeRectangleMass_eq_integral_condExp]
  have hμ : C.μ = P.μ := by
    dsimp only [C, P, relativeCubeSystemOne, relativeJoiningSystem,
      MultipleKhintchineCartesian.productSystem]
    exact
      Chapter02.HostKraErgodicRelativeJoining.relativeJoiningMeasure_eq_prod_of_ergodic
        M hM hErg
  have hInv :
      HostKraRelativeJoining.invariantMeasurableSpace C =
        HostKraRelativeJoining.invariantMeasurableSpace P := by
    dsimp only [C, P, relativeCubeSystemOne, relativeJoiningSystem,
      MultipleKhintchineCartesian.productSystem]
    rw [
      Chapter02.HostKraErgodicRelativeJoining.relativeJoiningMeasure_eq_prod_of_ergodic
        M hM hErg]
    rfl
  rw [hμ, hInv]
  rfl

/-- The middle-coordinate transposition symmetry stated directly for the
recursively defined second Host--Kra cube measure. -/
theorem integral_fourVertex_transpose_relativeCube
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ) :
    ∫ q : (M.X × M.X) × (M.X × M.X),
        (F00 q.1.1 * F01 q.1.2) *
          (F10 q.2.1 * F11 q.2.2)
      ∂(relativeCubeSystemTwo M hM).μ =
    ∫ q : (M.X × M.X) × (M.X × M.X),
        (F00 q.1.1 * F10 q.1.2) *
          (F01 q.2.1 * F11 q.2.2)
      ∂(relativeCubeSystemTwo M hM).μ := by
  rw [relativeCubeSystemTwo_measure_eq_cartesianRelativeJoining
    M hM hErg]
  exact integral_fourVertex_transpose
    M hM hErg F00 F01 F10 F11

/-- In an ergodic base system, transposing the two middle vertices is a
measure-preserving automorphism of the recursively defined second cube. -/
theorem squareTranspose_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M) :
    MeasurePreserving
      (squareTranspose :
        (M.X × M.X) × (M.X × M.X) →
          (M.X × M.X) × (M.X × M.X))
      (relativeCubeSystemTwo M hM).μ
      (relativeCubeSystemTwo M hM).μ := by
  let hC := relativeCubeSystemTwo_mps M hM
  letI : IsProbabilityMeasure (relativeCubeSystemTwo M hM).μ := hC.1
  refine ⟨squareTranspose_measurable, ?_⟩
  apply Measure.ext_fourfold
  intro A00 A01 A10 A11 hA00 hA01 hA10 hA11
  rw [Measure.map_apply squareTranspose_measurable
    ((hA00.prod hA01).prod (hA10.prod hA11))]
  have hpre :
      squareTranspose ⁻¹'
          ((A00 ×ˢ A01) ×ˢ (A10 ×ˢ A11)) =
        (A00 ×ˢ A10) ×ˢ (A01 ×ˢ A11) := by
    ext q
    simp only [squareTranspose, Set.mem_preimage, Set.mem_prod]
    tauto
  rw [hpre]
  let I00 :=
    MultipleKhintchineCharacteristic.indicatorLp M hM A00 hA00
  let I01 :=
    MultipleKhintchineCharacteristic.indicatorLp M hM A01 hA01
  let I10 :=
    MultipleKhintchineCharacteristic.indicatorLp M hM A10 hA10
  let I11 :=
    MultipleKhintchineCharacteristic.indicatorLp M hM A11 hA11
  have hIntegral :=
    integral_fourVertex_transpose_relativeCube M hM hErg
      I00 I01 I10 I11
  rw [integral_fourIndicator_eq_measure
      M hM A00 A01 A10 A11 hA00 hA01 hA10 hA11,
    integral_fourIndicator_eq_measure
      M hM A00 A10 A01 A11 hA00 hA10 hA01 hA11] at hIntegral
  have hReal := congrArg Complex.re hIntegral
  simp only [Complex.ofReal_re] at hReal
  exact ((ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top (relativeCubeSystemTwo M hM).μ
      ((A00 ×ˢ A01) ×ˢ (A10 ×ˢ A11)))
    (measure_ne_top (relativeCubeSystemTwo M hM).μ
      ((A00 ×ˢ A10) ×ˢ (A01 ×ˢ A11)))).mp hReal).symm

/-- An involutive measure-preserving symmetry commuting with the dynamics
also commutes with orthogonal projection onto the invariant subspace. -/
private theorem invariantProjection_comp_involutive
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (σ : M.X → M.X)
    (hσ : MeasurePreserving σ M.μ M.μ)
    (hσinv : Function.Involutive σ)
    (hcomm : ∀ x, σ (M.T x) = M.T (σ x))
    (F : Lp ℂ 2 M.μ) :
    invariantProjectionCLM M hM
        ((Lp.compMeasurePreservingₗᵢ ℂ σ hσ) F) =
      (Lp.compMeasurePreservingₗᵢ ℂ σ hσ)
        (invariantProjectionCLM M hM F) := by
  let U : Lp ℂ 2 M.μ →ₗᵢ[ℂ] Lp ℂ 2 M.μ :=
    Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2
  let S : Submodule ℂ (Lp ℂ 2 M.μ) :=
    LinearMap.eqLocus U.toContinuousLinearMap
      (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)
  let V : Lp ℂ 2 M.μ →ₗᵢ[ℂ] Lp ℂ 2 M.μ :=
    Lp.compMeasurePreservingₗᵢ ℂ σ hσ
  have hVinvol (G : Lp ℂ 2 M.μ) : V (V G) = G := by
    apply Lp.ext
    have houter := Lp.coeFn_compMeasurePreserving (V G) hσ
    have hinner :=
      hσ.quasiMeasurePreserving.ae_eq
        (Lp.coeFn_compMeasurePreserving G hσ)
    filter_upwards [houter, hinner] with x hxOuter hxInner
    change V (V G) x = V G (σ x) at hxOuter
    change V G (σ x) = G (σ (σ x)) at hxInner
    exact hxOuter.trans (hxInner.trans (by rw [hσinv x]))
  have hVU (G : Lp ℂ 2 M.μ) : U (V G) = V (U G) := by
    apply Lp.ext
    have hleftOuter := Lp.coeFn_compMeasurePreserving (V G) hM.2
    have hleftInner :=
      hM.2.quasiMeasurePreserving.ae_eq
        (Lp.coeFn_compMeasurePreserving G hσ)
    have hrightOuter := Lp.coeFn_compMeasurePreserving (U G) hσ
    have hrightInner :=
      hσ.quasiMeasurePreserving.ae_eq
        (Lp.coeFn_compMeasurePreserving G hM.2)
    filter_upwards
      [hleftOuter, hleftInner, hrightOuter, hrightInner]
      with x hlO hlI hrO hrI
    change U (V G) x = V G (M.T x) at hlO
    change V G (M.T x) = G (σ (M.T x)) at hlI
    change V (U G) x = U G (σ x) at hrO
    change U G (σ x) = G (M.T (σ x)) at hrI
    exact hlO.trans (hlI.trans ((congrArg G (hcomm x)).trans
      (hrI.symm.trans hrO.symm)))
  have hVmapS {G : Lp ℂ 2 M.μ} (hG : G ∈ S) : V G ∈ S := by
    change U (V G) = V G
    rw [hVU]
    change U G = G at hG
    rw [hG]
  have hVmapOrth {G : Lp ℂ 2 M.μ} (hG : G ∈ Sᗮ) : V G ∈ Sᗮ := by
    rw [Submodule.mem_orthogonal] at hG ⊢
    intro Z hZ
    have hVZ : V Z ∈ S := hVmapS hZ
    have hzero := hG (V Z) hVZ
    have hisom := V.inner_map_map (V Z) G
    rw [hVinvol Z] at hisom
    exact hisom.trans hzero
  change S.starProjection (V F) = V (S.starProjection F)
  apply S.eq_starProjection_of_mem_orthogonal
  · exact hVmapS (S.starProjection_apply_mem F)
  · have horth : F - S.starProjection F ∈ Sᗮ :=
      S.sub_starProjection_mem_orthogonal F
    have hVorth := hVmapOrth horth
    simpa only [map_sub] using hVorth

/-- A measurable-set indicator pulls back to the `L²` pullback under a
measure-preserving map. -/
private theorem indicatorLp_preimage_eq_comp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (σ : M.X → M.X)
    (hσ : MeasurePreserving σ M.μ M.μ)
    (A : Set M.X) (hA : MeasurableSet A) :
    MultipleKhintchineCharacteristic.indicatorLp M hM
        (σ ⁻¹' A) (hA.preimage hσ.measurable) =
      (Lp.compMeasurePreservingₗᵢ ℂ σ hσ)
        (MultipleKhintchineCharacteristic.indicatorLp M hM A hA) := by
  let IA :=
    MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  let IApre :=
    MultipleKhintchineCharacteristic.indicatorLp M hM
      (σ ⁻¹' A) (hA.preimage hσ.measurable)
  let V : Lp ℂ 2 M.μ →ₗᵢ[ℂ] Lp ℂ 2 M.μ :=
    Lp.compMeasurePreservingₗᵢ ℂ σ hσ
  apply Lp.ext
  have hleft :=
    MultipleKhintchineCharacteristic.indicatorLp_coe M hM
      (σ ⁻¹' A) (hA.preimage hσ.measurable)
  have hrightOuter := Lp.coeFn_compMeasurePreserving IA hσ
  have hrightInner :=
    hσ.quasiMeasurePreserving.ae_eq
      (MultipleKhintchineCharacteristic.indicatorLp_coe M hM A hA)
  filter_upwards [hleft, hrightOuter, hrightInner]
    with x hl hrO hrI
  change IApre x = V IA x
  change IApre x = CorrelationMean.indicatorComplex (σ ⁻¹' A) x at hl
  change V IA x = IA (σ x) at hrO
  change IA (σ x) = CorrelationMean.indicatorComplex A (σ x) at hrI
  rw [hl, hrO, hrI]
  rfl

/-- Rectangle mass of a relative joining, expressed through the complex
invariant projection used by the cube recursion. -/
private theorem relativeJoining_prod_toReal_eq_re_innerProjection
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (relativeJoiningMeasure M hM (A ×ˢ B)).toReal =
      Complex.re
        (@inner ℂ (Lp ℂ 2 M.μ) _
          (invariantProjectionCLM M hM
            (MultipleKhintchineCharacteristic.indicatorLp M hM B hB))
          (invariantProjectionCLM M hM
            (MultipleKhintchineCharacteristic.indicatorLp M hM A hA))) := by
  rw [relativeJoiningMeasure_apply_prod_toReal M hM A B hA hB,
    invariantProjectionCLM_indicator M hM B hB,
    invariantProjectionCLM_indicator M hM A hA]
  have hAc := invariantIndicatorComplexLp_coe M hM A hA
  have hBc := invariantIndicatorComplexLp_coe M hM B hB
  have hABint : Integrable
      (fun x ↦ HostKraRelativeJoining.invariantIndicatorLp M hM A hA x *
        HostKraRelativeJoining.invariantIndicatorLp M hM B hB x) M.μ :=
    (Lp.memLp (HostKraRelativeJoining.invariantIndicatorLp M hM A hA))
      |>.integrable_mul
        (Lp.memLp
          (HostKraRelativeJoining.invariantIndicatorLp M hM B hB))
  have hinner :
      @inner ℂ (Lp ℂ 2 M.μ) _
          (invariantIndicatorComplexLp M hM B hB)
          (invariantIndicatorComplexLp M hM A hA) =
        ((HostKraRelativeJoining.relativeRectangleMass
          M hM A B hA hB : ℝ) : ℂ) := by
    rw [L2.inner_def]
    calc
      (∫ x, invariantIndicatorComplexLp M hM A hA x *
          star (invariantIndicatorComplexLp M hM B hB x) ∂M.μ) =
          ∫ x, Complex.ofReal
            (HostKraRelativeJoining.invariantIndicatorLp M hM A hA x *
              HostKraRelativeJoining.invariantIndicatorLp M hM B hB x)
              ∂M.μ := by
            apply integral_congr_ae
            filter_upwards [hAc, hBc] with x hAx hBx
            rw [hAx, hBx]
            simp
      _ = Complex.ofReal
          (∫ x, HostKraRelativeJoining.invariantIndicatorLp M hM A hA x *
            HostKraRelativeJoining.invariantIndicatorLp M hM B hB x
            ∂M.μ) := by
            exact Complex.ofRealCLM.integral_comp_comm hABint
      _ = ((HostKraRelativeJoining.relativeRectangleMass
          M hM A B hA hB : ℝ) : ℂ) := by
        rw [HostKraRelativeJoining.relativeRectangleMass, L2.inner_def]
        apply congrArg Complex.ofReal
        apply integral_congr_ae
        filter_upwards with x
        simp only [RCLike.inner_apply, conj_trivial]
        exact mul_comm _ _
  rw [hinner]
  simp

/-- Relative independent joining is functorial for an involutive
measure-preserving symmetry commuting with the base dynamics. -/
theorem relativeJoining_diagonal_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (σ : M.X → M.X)
    (hσ : MeasurePreserving σ M.μ M.μ)
    (hσinv : Function.Involutive σ)
    (hcomm : ∀ x, σ (M.T x) = M.T (σ x)) :
    MeasurePreserving
      (fun p : M.X × M.X ↦ (σ p.1, σ p.2))
      (relativeJoiningMeasure M hM)
      (relativeJoiningMeasure M hM) := by
  let ν := relativeJoiningMeasure M hM
  let σ₂ : M.X × M.X → M.X × M.X :=
    fun p ↦ (σ p.1, σ p.2)
  have hσ₂meas : Measurable σ₂ :=
    Measurable.prod
      (hσ.measurable.comp measurable_fst)
      (hσ.measurable.comp measurable_snd)
  refine ⟨hσ₂meas, ?_⟩
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply hσ₂meas (hA.prod hB)]
  have hpre : σ₂ ⁻¹' (A ×ˢ B) = (σ ⁻¹' A) ×ˢ (σ ⁻¹' B) := by
    ext p
    rfl
  rw [hpre]
  let IA := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  let IB := MultipleKhintchineCharacteristic.indicatorLp M hM B hB
  let IApre :=
    MultipleKhintchineCharacteristic.indicatorLp M hM
      (σ ⁻¹' A) (hA.preimage hσ.measurable)
  let IBpre :=
    MultipleKhintchineCharacteristic.indicatorLp M hM
      (σ ⁻¹' B) (hB.preimage hσ.measurable)
  let V : Lp ℂ 2 M.μ →ₗᵢ[ℂ] Lp ℂ 2 M.μ :=
    Lp.compMeasurePreservingₗᵢ ℂ σ hσ
  have hIA : IApre = V IA :=
    indicatorLp_preimage_eq_comp M hM σ hσ A hA
  have hIB : IBpre = V IB :=
    indicatorLp_preimage_eq_comp M hM σ hσ B hB
  have hPA :=
    invariantProjection_comp_involutive
      M hM σ hσ hσinv hcomm IA
  have hPB :=
    invariantProjection_comp_involutive
      M hM σ hσ hσinv hcomm IB
  have hinner :
      @inner ℂ (Lp ℂ 2 M.μ) _
          (invariantProjectionCLM M hM IBpre)
          (invariantProjectionCLM M hM IApre) =
        @inner ℂ (Lp ℂ 2 M.μ) _
          (invariantProjectionCLM M hM IB)
          (invariantProjectionCLM M hM IA) := by
    rw [hIA, hIB, hPA, hPB]
    exact V.inner_map_map _ _
  have hReal :
      (ν ((σ ⁻¹' A) ×ˢ (σ ⁻¹' B))).toReal =
        (ν (A ×ˢ B)).toReal := by
    rw [relativeJoining_prod_toReal_eq_re_innerProjection
        M hM (σ ⁻¹' A) (σ ⁻¹' B)
        (hA.preimage hσ.measurable) (hB.preimage hσ.measurable),
      relativeJoining_prod_toReal_eq_re_innerProjection M hM A B hA hB,
      hinner]
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top ν ((σ ⁻¹' A) ×ˢ (σ ⁻¹' B)))
    (measure_ne_top ν (A ×ˢ B))).mp hReal

/-- Apply the square transposition simultaneously on both outer faces of
the eight-vertex cube. -/
def cubeThreeMiddleTranspose {X : Type u} :
    ((X × X) × (X × X)) × ((X × X) × (X × X)) →
      ((X × X) × (X × X)) × ((X × X) × (X × X)) :=
  fun r ↦ (squareTranspose r.1, squareTranspose r.2)

lemma cubeThreeMiddleTranspose_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M) :
    MeasurePreserving
      (cubeThreeMiddleTranspose :
        ((M.X × M.X) × (M.X × M.X)) ×
            ((M.X × M.X) × (M.X × M.X)) →
          ((M.X × M.X) × (M.X × M.X)) ×
            ((M.X × M.X) × (M.X × M.X)))
      (relativeCubeSystemThree M hM).μ
      (relativeCubeSystemThree M hM).μ := by
  apply relativeJoining_diagonal_measurePreserving
    (relativeCubeSystemTwo M hM)
    (relativeCubeSystemTwo_mps M hM)
    squareTranspose
    (squareTranspose_measurePreserving M hM hErg)
    squareTranspose_involutive
  intro q
  rfl

/-- An eight-vertex separated integral is the pairing of the invariant
projections of its two outer faces.  This is the projection-level form of
the third relative-cube recursion. -/
theorem integral_eightVertex_eq_faceProjections
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F000 F001 F010 F011 F100 F101 F110 F111 : Lp ℂ 2 M.μ)
    (hF000top : MemLp (fun x ↦ F000 x) ⊤ M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ) :
    ∫ r : (relativeCubeSystemThree M hM).X,
        (((F000 r.1.1.1 * F001 r.1.1.2) *
          (F010 r.1.2.1 * F011 r.1.2.2)) *
        ((F100 r.2.1.1 * F101 r.2.1.2) *
          (F110 r.2.2.1 * F111 r.2.2.2)))
        ∂(relativeCubeSystemThree M hM).μ =
      @inner ℂ (Lp ℂ 2 (relativeCubeSystemTwo M hM).μ) _
        (invariantProjectionCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM)
          (ForwardKroneckerFactor.lpStar
            (relativeCubeSystemTwo M hM)
            (fourVertexCubeProduct M hM F100 F101 F110 F111
              hF100top hF101top hF110top)))
        (invariantProjectionCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM)
          (fourVertexCubeProduct M hM F000 F001 F010 F011
            hF000top hF001top hF010top)) := by
  let C := relativeCubeSystemTwo M hM
  let hC := relativeCubeSystemTwo_mps M hM
  let A :=
    fourVertexCubeProduct M hM F000 F001 F010 F011
      hF000top hF001top hF010top
  let B :=
    fourVertexCubeProduct M hM F100 F101 F110 F111
      hF100top hF101top hF110top
  have hpair :=
    inner_pullback_eq_invariantProjection C hC
      (ForwardKroneckerFactor.lpStar C B) A
  rw [L2.inner_def] at hpair
  rw [← hpair]
  apply integral_congr_ae
  have hsnd :=
    relativeSndCLM_coe C hC
      (ForwardKroneckerFactor.lpStar C B)
  have hfst := relativeFstCLM_coe C hC A
  have hstar :=
    (relativeJoining_snd_measurePreserving C hC)
      |>.quasiMeasurePreserving.ae_eq
        (ForwardKroneckerFactor.lpStar_coe C B)
  have hB :=
    (relativeJoining_snd_measurePreserving C hC)
      |>.quasiMeasurePreserving.ae_eq
        (fourVertexCubeProduct_coe M hM F100 F101 F110 F111
          hF100top hF101top hF110top)
  have hA :=
    (relativeJoining_fst_measurePreserving C hC)
      |>.quasiMeasurePreserving.ae_eq
        (fourVertexCubeProduct_coe M hM F000 F001 F010 F011
          hF000top hF001top hF010top)
  filter_upwards [hsnd, hfst, hstar, hB, hA] with
      r hs hf hsb hb ha
  change
    relativeSndCLM C hC
        (ForwardKroneckerFactor.lpStar C B) r =
      ForwardKroneckerFactor.lpStar C B r.2 at hs
  change relativeFstCLM C hC A r = A r.1 at hf
  change ForwardKroneckerFactor.lpStar C B r.2 =
    star (B r.2) at hsb
  change
    B r.2 =
      (F100 r.2.1.1 * F101 r.2.1.2) *
        (F110 r.2.2.1 * F111 r.2.2.2) at hb
  change
    A r.1 =
      (F000 r.1.1.1 * F001 r.1.1.2) *
        (F010 r.1.2.1 * F011 r.1.2.2) at ha
  simp only [RCLike.inner_apply, starRingEnd_apply]
  rw [hs, hf, hsb, hb, ha]
  simp only [star_star]

/-- Exchange the outermost cube direction with the first direction inside
each four-vertex face.  At the level of the eight vertices this is the
coordinate permutation `(a,b,c) ↦ (b,a,c)`. -/
def cubeThreeOuterMiddleTranspose {X : Type u} :
    ((X × X) × (X × X)) × ((X × X) × (X × X)) →
      ((X × X) × (X × X)) × ((X × X) × (X × X)) :=
  fun r ↦
    ((r.1.1, r.2.1), (r.1.2, r.2.2))

lemma cubeThreeOuterMiddleTranspose_measurable
    {X : Type u} [MeasurableSpace X] :
    Measurable
      (cubeThreeOuterMiddleTranspose :
        ((X × X) × (X × X)) × ((X × X) × (X × X)) →
          ((X × X) × (X × X)) × ((X × X) × (X × X))) := by
  fun_prop

lemma cubeThreeOuterMiddleTranspose_involutive {X : Type u} :
    Function.Involutive
      (cubeThreeOuterMiddleTranspose :
        ((X × X) × (X × X)) × ((X × X) × (X × X)) →
          ((X × X) × (X × X)) × ((X × X) × (X × X))) := by
  intro r
  rfl

lemma cubeThreeOuterMiddleTranspose_commutes
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (r : (relativeCubeSystemThree M hM).X) :
    cubeThreeOuterMiddleTranspose
        ((relativeCubeSystemThree M hM).T r) =
      (relativeCubeSystemThree M hM).T
        (cubeThreeOuterMiddleTranspose r) := by
  rfl

/-- The missing outer--middle symmetry of `C3(M)` is definitionally the
ordinary square transposition symmetry of `C2(C1(M))`.  Thus it is enough
to establish the dimension-two transposition theorem for the generally
nonergodic first cube system. -/
theorem cubeThreeOuterMiddleTranspose_measurePreserving_of_cubeOne_squareTranspose
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (htranspose :
      MeasurePreserving
        (squareTranspose :
          ((relativeCubeSystemOne M hM).X ×
              (relativeCubeSystemOne M hM).X) ×
              ((relativeCubeSystemOne M hM).X ×
                (relativeCubeSystemOne M hM).X) →
            ((relativeCubeSystemOne M hM).X ×
              (relativeCubeSystemOne M hM).X) ×
              ((relativeCubeSystemOne M hM).X ×
                (relativeCubeSystemOne M hM).X))
        (relativeCubeSystemTwo
          (relativeCubeSystemOne M hM)
          (relativeCubeSystemOne_mps M hM)).μ
        (relativeCubeSystemTwo
          (relativeCubeSystemOne M hM)
          (relativeCubeSystemOne_mps M hM)).μ) :
    MeasurePreserving
      (cubeThreeOuterMiddleTranspose :
        (relativeCubeSystemThree M hM).X →
          (relativeCubeSystemThree M hM).X)
      (relativeCubeSystemThree M hM).μ
      (relativeCubeSystemThree M hM).μ := by
  exact htranspose

/-- Equality of the eight-coordinate box masses under exchange of the
outer and middle cube directions is sufficient for the full
measure-preserving statement.  This isolates the remaining analytic
Host--Kra identity from the routine finite-measure extension step. -/
theorem cubeThreeOuterMiddleTranspose_measurePreserving_of_box_mass
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hbox :
      ∀ A000 A001 A010 A011 A100 A101 A110 A111 : Set M.X,
        MeasurableSet A000 → MeasurableSet A001 →
        MeasurableSet A010 → MeasurableSet A011 →
        MeasurableSet A100 → MeasurableSet A101 →
        MeasurableSet A110 → MeasurableSet A111 →
        (relativeCubeSystemThree M hM).μ
            (((A000 ×ˢ A001) ×ˢ (A010 ×ˢ A011)) ×ˢ
              ((A100 ×ˢ A101) ×ˢ (A110 ×ˢ A111))) =
          (relativeCubeSystemThree M hM).μ
            (((A000 ×ˢ A001) ×ˢ (A100 ×ˢ A101)) ×ˢ
              ((A010 ×ˢ A011) ×ˢ (A110 ×ˢ A111)))) :
    MeasurePreserving
      (cubeThreeOuterMiddleTranspose :
        (relativeCubeSystemThree M hM).X →
          (relativeCubeSystemThree M hM).X)
      (relativeCubeSystemThree M hM).μ
      (relativeCubeSystemThree M hM).μ := by
  let ν := (relativeCubeSystemThree M hM).μ
  let hC := relativeCubeSystemThree_mps M hM
  letI : IsProbabilityMeasure ν := hC.1
  refine ⟨cubeThreeOuterMiddleTranspose_measurable, ?_⟩
  apply Measure.ext_eightfold
  intro A000 A001 A010 A011 A100 A101 A110 A111
    hA000 hA001 hA010 hA011 hA100 hA101 hA110 hA111
  rw [Measure.map_apply cubeThreeOuterMiddleTranspose_measurable
    (((hA000.prod hA001).prod (hA010.prod hA011)).prod
      ((hA100.prod hA101).prod (hA110.prod hA111)))]
  have hpre :
      cubeThreeOuterMiddleTranspose ⁻¹'
          (((A000 ×ˢ A001) ×ˢ (A010 ×ˢ A011)) ×ˢ
            ((A100 ×ˢ A101) ×ˢ (A110 ×ˢ A111))) =
        ((A000 ×ˢ A001) ×ˢ (A100 ×ˢ A101)) ×ˢ
          ((A010 ×ˢ A011) ×ˢ (A110 ×ˢ A111)) := by
    ext r
    simp only [cubeThreeOuterMiddleTranspose, Set.mem_preimage,
      Set.mem_prod]
    tauto
  rw [hpre]
  exact (hbox A000 A001 A010 A011 A100 A101 A110 A111
    hA000 hA001 hA010 hA011 hA100 hA101 hA110 hA111).symm

/-- Products of raw complex indicators are indicators of product sets. -/
private lemma indicatorComplex_prod
    {X Y : Type*} (A : Set X) (B : Set Y) (x : X) (y : Y) :
    CorrelationMean.indicatorComplex A x *
        CorrelationMean.indicatorComplex B y =
      CorrelationMean.indicatorComplex (A ×ˢ B) (x, y) := by
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ B <;>
    simp [CorrelationMean.indicatorComplex, Set.indicator, hx, hy]

/-- The product of eight raw indicator functions integrates to the mass of
the corresponding measurable box in the third relative cube. -/
theorem integral_eightIndicator_eq_measure
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A000 A001 A010 A011 A100 A101 A110 A111 : Set M.X)
    (hA000 : MeasurableSet A000) (hA001 : MeasurableSet A001)
    (hA010 : MeasurableSet A010) (hA011 : MeasurableSet A011)
    (hA100 : MeasurableSet A100) (hA101 : MeasurableSet A101)
    (hA110 : MeasurableSet A110) (hA111 : MeasurableSet A111) :
    ∫ r : (relativeCubeSystemThree M hM).X,
        (((CorrelationMean.indicatorComplex A000 r.1.1.1 *
            CorrelationMean.indicatorComplex A001 r.1.1.2) *
          (CorrelationMean.indicatorComplex A010 r.1.2.1 *
            CorrelationMean.indicatorComplex A011 r.1.2.2)) *
        ((CorrelationMean.indicatorComplex A100 r.2.1.1 *
            CorrelationMean.indicatorComplex A101 r.2.1.2) *
          (CorrelationMean.indicatorComplex A110 r.2.2.1 *
            CorrelationMean.indicatorComplex A111 r.2.2.2)))
        ∂(relativeCubeSystemThree M hM).μ =
      (((relativeCubeSystemThree M hM).μ
        (((A000 ×ˢ A001) ×ˢ (A010 ×ˢ A011)) ×ˢ
          ((A100 ×ˢ A101) ×ˢ (A110 ×ˢ A111)))).toReal : ℂ) := by
  let box : Set (relativeCubeSystemThree M hM).X :=
    ((A000 ×ˢ A001) ×ˢ (A010 ×ˢ A011)) ×ˢ
      ((A100 ×ˢ A101) ×ˢ (A110 ×ˢ A111))
  have hbox : MeasurableSet box :=
    ((hA000.prod hA001).prod (hA010.prod hA011)).prod
      ((hA100.prod hA101).prod (hA110.prod hA111))
  calc
    (∫ r : (relativeCubeSystemThree M hM).X,
        (((CorrelationMean.indicatorComplex A000 r.1.1.1 *
            CorrelationMean.indicatorComplex A001 r.1.1.2) *
          (CorrelationMean.indicatorComplex A010 r.1.2.1 *
            CorrelationMean.indicatorComplex A011 r.1.2.2)) *
        ((CorrelationMean.indicatorComplex A100 r.2.1.1 *
            CorrelationMean.indicatorComplex A101 r.2.1.2) *
          (CorrelationMean.indicatorComplex A110 r.2.2.1 *
            CorrelationMean.indicatorComplex A111 r.2.2.2)))
        ∂(relativeCubeSystemThree M hM).μ) =
        ∫ r, box.indicator (fun _ ↦ (1 : ℂ)) r
          ∂(relativeCubeSystemThree M hM).μ := by
      apply integral_congr_ae
      filter_upwards with r
      rw [indicatorComplex_prod A000 A001 r.1.1.1 r.1.1.2,
        indicatorComplex_prod A010 A011 r.1.2.1 r.1.2.2,
        indicatorComplex_prod
          (A000 ×ˢ A001) (A010 ×ˢ A011)
          (r.1.1.1, r.1.1.2) (r.1.2.1, r.1.2.2),
        indicatorComplex_prod A100 A101 r.2.1.1 r.2.1.2,
        indicatorComplex_prod A110 A111 r.2.2.1 r.2.2.2,
        indicatorComplex_prod
          (A100 ×ˢ A101) (A110 ×ˢ A111)
          (r.2.1.1, r.2.1.2) (r.2.2.1, r.2.2.2),
        indicatorComplex_prod
          ((A000 ×ˢ A001) ×ˢ (A010 ×ˢ A011))
          ((A100 ×ˢ A101) ×ˢ (A110 ×ˢ A111))
          ((r.1.1.1, r.1.1.2), (r.1.2.1, r.1.2.2))
          ((r.2.1.1, r.2.1.2), (r.2.2.1, r.2.2.2))]
      rfl
    _ = (((relativeCubeSystemThree M hM).μ
        (((A000 ×ˢ A001) ×ˢ (A010 ×ˢ A011)) ×ˢ
          ((A100 ×ˢ A101) ×ˢ (A110 ×ˢ A111)))).toReal : ℂ) := by
      rw [integral_indicator hbox]
      simp [Measure.real_def, Measure.restrict_apply, box]

/-- Replacing the eight raw indicators by their `L²` representatives does
not change the third-cube integral.  The proof records explicitly that
every vertex marginal of the recursively defined cube is the base
measure. -/
private theorem integral_eightIndicatorLp_eq_raw
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A000 A001 A010 A011 A100 A101 A110 A111 : Set M.X)
    (hA000 : MeasurableSet A000) (hA001 : MeasurableSet A001)
    (hA010 : MeasurableSet A010) (hA011 : MeasurableSet A011)
    (hA100 : MeasurableSet A100) (hA101 : MeasurableSet A101)
    (hA110 : MeasurableSet A110) (hA111 : MeasurableSet A111) :
    let I000 :=
      MultipleKhintchineCharacteristic.indicatorLp M hM A000 hA000
    let I001 :=
      MultipleKhintchineCharacteristic.indicatorLp M hM A001 hA001
    let I010 :=
      MultipleKhintchineCharacteristic.indicatorLp M hM A010 hA010
    let I011 :=
      MultipleKhintchineCharacteristic.indicatorLp M hM A011 hA011
    let I100 :=
      MultipleKhintchineCharacteristic.indicatorLp M hM A100 hA100
    let I101 :=
      MultipleKhintchineCharacteristic.indicatorLp M hM A101 hA101
    let I110 :=
      MultipleKhintchineCharacteristic.indicatorLp M hM A110 hA110
    let I111 :=
      MultipleKhintchineCharacteristic.indicatorLp M hM A111 hA111
    (∫ r : (relativeCubeSystemThree M hM).X,
        (((I000 r.1.1.1 * I001 r.1.1.2) *
          (I010 r.1.2.1 * I011 r.1.2.2)) *
        ((I100 r.2.1.1 * I101 r.2.1.2) *
          (I110 r.2.2.1 * I111 r.2.2.2)))
        ∂(relativeCubeSystemThree M hM).μ) =
      ∫ r : (relativeCubeSystemThree M hM).X,
        (((CorrelationMean.indicatorComplex A000 r.1.1.1 *
            CorrelationMean.indicatorComplex A001 r.1.1.2) *
          (CorrelationMean.indicatorComplex A010 r.1.2.1 *
            CorrelationMean.indicatorComplex A011 r.1.2.2)) *
        ((CorrelationMean.indicatorComplex A100 r.2.1.1 *
            CorrelationMean.indicatorComplex A101 r.2.1.2) *
          (CorrelationMean.indicatorComplex A110 r.2.2.1 *
            CorrelationMean.indicatorComplex A111 r.2.2.2)))
        ∂(relativeCubeSystemThree M hM).μ := by
  dsimp only
  let C := relativeCubeSystemTwo M hM
  let hC := relativeCubeSystemTwo_mps M hM
  have h000mp :
      MeasurePreserving
        (fun r : (relativeCubeSystemThree M hM).X ↦ r.1.1.1)
        (relativeCubeSystemThree M hM).μ M.μ :=
    (cubeTwo_coord00_measurePreserving M hM).comp
      (relativeJoining_fst_measurePreserving C hC)
  have h001mp :
      MeasurePreserving
        (fun r : (relativeCubeSystemThree M hM).X ↦ r.1.1.2)
        (relativeCubeSystemThree M hM).μ M.μ :=
    (cubeTwo_coord01_measurePreserving M hM).comp
      (relativeJoining_fst_measurePreserving C hC)
  have h010mp :
      MeasurePreserving
        (fun r : (relativeCubeSystemThree M hM).X ↦ r.1.2.1)
        (relativeCubeSystemThree M hM).μ M.μ :=
    (cubeTwo_coord10_measurePreserving M hM).comp
      (relativeJoining_fst_measurePreserving C hC)
  have h011mp :
      MeasurePreserving
        (fun r : (relativeCubeSystemThree M hM).X ↦ r.1.2.2)
        (relativeCubeSystemThree M hM).μ M.μ :=
    (cubeTwo_coord11_measurePreserving M hM).comp
      (relativeJoining_fst_measurePreserving C hC)
  have h100mp :
      MeasurePreserving
        (fun r : (relativeCubeSystemThree M hM).X ↦ r.2.1.1)
        (relativeCubeSystemThree M hM).μ M.μ :=
    (cubeTwo_coord00_measurePreserving M hM).comp
      (relativeJoining_snd_measurePreserving C hC)
  have h101mp :
      MeasurePreserving
        (fun r : (relativeCubeSystemThree M hM).X ↦ r.2.1.2)
        (relativeCubeSystemThree M hM).μ M.μ :=
    (cubeTwo_coord01_measurePreserving M hM).comp
      (relativeJoining_snd_measurePreserving C hC)
  have h110mp :
      MeasurePreserving
        (fun r : (relativeCubeSystemThree M hM).X ↦ r.2.2.1)
        (relativeCubeSystemThree M hM).μ M.μ :=
    (cubeTwo_coord10_measurePreserving M hM).comp
      (relativeJoining_snd_measurePreserving C hC)
  have h111mp :
      MeasurePreserving
        (fun r : (relativeCubeSystemThree M hM).X ↦ r.2.2.2)
        (relativeCubeSystemThree M hM).μ M.μ :=
    (cubeTwo_coord11_measurePreserving M hM).comp
      (relativeJoining_snd_measurePreserving C hC)
  have h000 := h000mp.quasiMeasurePreserving.ae_eq
    (MultipleKhintchineCharacteristic.indicatorLp_coe M hM A000 hA000)
  have h001 := h001mp.quasiMeasurePreserving.ae_eq
    (MultipleKhintchineCharacteristic.indicatorLp_coe M hM A001 hA001)
  have h010 := h010mp.quasiMeasurePreserving.ae_eq
    (MultipleKhintchineCharacteristic.indicatorLp_coe M hM A010 hA010)
  have h011 := h011mp.quasiMeasurePreserving.ae_eq
    (MultipleKhintchineCharacteristic.indicatorLp_coe M hM A011 hA011)
  have h100 := h100mp.quasiMeasurePreserving.ae_eq
    (MultipleKhintchineCharacteristic.indicatorLp_coe M hM A100 hA100)
  have h101 := h101mp.quasiMeasurePreserving.ae_eq
    (MultipleKhintchineCharacteristic.indicatorLp_coe M hM A101 hA101)
  have h110 := h110mp.quasiMeasurePreserving.ae_eq
    (MultipleKhintchineCharacteristic.indicatorLp_coe M hM A110 hA110)
  have h111 := h111mp.quasiMeasurePreserving.ae_eq
    (MultipleKhintchineCharacteristic.indicatorLp_coe M hM A111 hA111)
  apply integral_congr_ae
  filter_upwards [h000, h001, h010, h011, h100, h101, h110, h111]
    with r hr000 hr001 hr010 hr011 hr100 hr101 hr110 hr111
  simp only [Function.comp_apply] at hr000 hr001 hr010 hr011 hr100 hr101 hr110 hr111
  rw [hr000, hr001, hr010, hr011, hr100, hr101, hr110, hr111]

/-- It is enough to prove the outer--middle symmetry for products of eight
measurable indicators.  This is the function-level form suited to the
finite-Cesàro and invariant-projection calculations. -/
theorem cubeThreeOuterMiddleTranspose_measurePreserving_of_indicator_integral
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hintegral :
      ∀ A000 A001 A010 A011 A100 A101 A110 A111 : Set M.X,
        MeasurableSet A000 → MeasurableSet A001 →
        MeasurableSet A010 → MeasurableSet A011 →
        MeasurableSet A100 → MeasurableSet A101 →
        MeasurableSet A110 → MeasurableSet A111 →
        (∫ r : (relativeCubeSystemThree M hM).X,
          (((CorrelationMean.indicatorComplex A000 r.1.1.1 *
              CorrelationMean.indicatorComplex A001 r.1.1.2) *
            (CorrelationMean.indicatorComplex A010 r.1.2.1 *
              CorrelationMean.indicatorComplex A011 r.1.2.2)) *
          ((CorrelationMean.indicatorComplex A100 r.2.1.1 *
              CorrelationMean.indicatorComplex A101 r.2.1.2) *
            (CorrelationMean.indicatorComplex A110 r.2.2.1 *
              CorrelationMean.indicatorComplex A111 r.2.2.2)))
          ∂(relativeCubeSystemThree M hM).μ) =
        ∫ r : (relativeCubeSystemThree M hM).X,
          (((CorrelationMean.indicatorComplex A000 r.1.1.1 *
              CorrelationMean.indicatorComplex A001 r.1.1.2) *
            (CorrelationMean.indicatorComplex A100 r.1.2.1 *
              CorrelationMean.indicatorComplex A101 r.1.2.2)) *
          ((CorrelationMean.indicatorComplex A010 r.2.1.1 *
              CorrelationMean.indicatorComplex A011 r.2.1.2) *
            (CorrelationMean.indicatorComplex A110 r.2.2.1 *
              CorrelationMean.indicatorComplex A111 r.2.2.2)))
          ∂(relativeCubeSystemThree M hM).μ) :
    MeasurePreserving
      (cubeThreeOuterMiddleTranspose :
        (relativeCubeSystemThree M hM).X →
          (relativeCubeSystemThree M hM).X)
      (relativeCubeSystemThree M hM).μ
      (relativeCubeSystemThree M hM).μ := by
  let hC := relativeCubeSystemThree_mps M hM
  letI : IsProbabilityMeasure (relativeCubeSystemThree M hM).μ := hC.1
  apply cubeThreeOuterMiddleTranspose_measurePreserving_of_box_mass M hM
  intro A000 A001 A010 A011 A100 A101 A110 A111
    hA000 hA001 hA010 hA011 hA100 hA101 hA110 hA111
  have hEq := hintegral A000 A001 A010 A011 A100 A101 A110 A111
    hA000 hA001 hA010 hA011 hA100 hA101 hA110 hA111
  rw [integral_eightIndicator_eq_measure M hM
      A000 A001 A010 A011 A100 A101 A110 A111
      hA000 hA001 hA010 hA011 hA100 hA101 hA110 hA111,
    integral_eightIndicator_eq_measure M hM
      A000 A001 A100 A101 A010 A011 A110 A111
      hA000 hA001 hA100 hA101 hA010 hA011 hA110 hA111] at hEq
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top (relativeCubeSystemThree M hM).μ
      (((A000 ×ˢ A001) ×ˢ (A010 ×ˢ A011)) ×ˢ
        ((A100 ×ˢ A101) ×ˢ (A110 ×ˢ A111))))
    (measure_ne_top (relativeCubeSystemThree M hM).μ
      (((A000 ×ˢ A001) ×ˢ (A100 ×ˢ A101)) ×ˢ
        ((A010 ×ˢ A011) ×ˢ (A110 ×ˢ A111)))))
    |>.mp (Complex.ofReal_injective hEq)

/-- It is sufficient to prove the outer--middle symmetry using the
canonical `L²` representatives of measurable indicators.  This form feeds
directly into `integral_eightVertex_eq_faceProjections`. -/
theorem cubeThreeOuterMiddleTranspose_measurePreserving_of_indicatorLp_integral
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hintegral :
      ∀ A000 A001 A010 A011 A100 A101 A110 A111 : Set M.X,
        ∀ hA000 : MeasurableSet A000, ∀ hA001 : MeasurableSet A001,
        ∀ hA010 : MeasurableSet A010, ∀ hA011 : MeasurableSet A011,
        ∀ hA100 : MeasurableSet A100, ∀ hA101 : MeasurableSet A101,
        ∀ hA110 : MeasurableSet A110, ∀ hA111 : MeasurableSet A111,
        let I000 :=
          MultipleKhintchineCharacteristic.indicatorLp M hM A000 hA000
        let I001 :=
          MultipleKhintchineCharacteristic.indicatorLp M hM A001 hA001
        let I010 :=
          MultipleKhintchineCharacteristic.indicatorLp M hM A010 hA010
        let I011 :=
          MultipleKhintchineCharacteristic.indicatorLp M hM A011 hA011
        let I100 :=
          MultipleKhintchineCharacteristic.indicatorLp M hM A100 hA100
        let I101 :=
          MultipleKhintchineCharacteristic.indicatorLp M hM A101 hA101
        let I110 :=
          MultipleKhintchineCharacteristic.indicatorLp M hM A110 hA110
        let I111 :=
          MultipleKhintchineCharacteristic.indicatorLp M hM A111 hA111
        (∫ r : (relativeCubeSystemThree M hM).X,
            (((I000 r.1.1.1 * I001 r.1.1.2) *
              (I010 r.1.2.1 * I011 r.1.2.2)) *
            ((I100 r.2.1.1 * I101 r.2.1.2) *
              (I110 r.2.2.1 * I111 r.2.2.2)))
            ∂(relativeCubeSystemThree M hM).μ) =
          ∫ r : (relativeCubeSystemThree M hM).X,
            (((I000 r.1.1.1 * I001 r.1.1.2) *
              (I100 r.1.2.1 * I101 r.1.2.2)) *
            ((I010 r.2.1.1 * I011 r.2.1.2) *
              (I110 r.2.2.1 * I111 r.2.2.2)))
            ∂(relativeCubeSystemThree M hM).μ) :
    MeasurePreserving
      (cubeThreeOuterMiddleTranspose :
        (relativeCubeSystemThree M hM).X →
          (relativeCubeSystemThree M hM).X)
      (relativeCubeSystemThree M hM).μ
      (relativeCubeSystemThree M hM).μ := by
  apply cubeThreeOuterMiddleTranspose_measurePreserving_of_indicator_integral
    M hM
  intro A000 A001 A010 A011 A100 A101 A110 A111
    hA000 hA001 hA010 hA011 hA100 hA101 hA110 hA111
  rw [← integral_eightIndicatorLp_eq_raw M hM
      A000 A001 A010 A011 A100 A101 A110 A111
      hA000 hA001 hA010 hA011 hA100 hA101 hA110 hA111,
    ← integral_eightIndicatorLp_eq_raw M hM
      A000 A001 A100 A101 A010 A011 A110 A111
      hA000 hA001 hA100 hA101 hA010 hA011 hA110 hA111]
  exact hintegral A000 A001 A010 A011 A100 A101 A110 A111
    hA000 hA001 hA010 hA011 hA100 hA101 hA110 hA111

/-- Once the outer--middle coordinate exchange is known to preserve the
third cube measure, its pullback commutes with the invariant projection on
that cube.  This isolates the exact remaining measure-symmetry obligation
from all later Hilbert-space manipulations. -/
theorem invariantProjection_cubeThreeOuterMiddleTranspose
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hσ :
      MeasurePreserving
        (cubeThreeOuterMiddleTranspose :
          (relativeCubeSystemThree M hM).X →
            (relativeCubeSystemThree M hM).X)
        (relativeCubeSystemThree M hM).μ
        (relativeCubeSystemThree M hM).μ)
    (F : Lp ℂ 2 (relativeCubeSystemThree M hM).μ) :
    invariantProjectionCLM
        (relativeCubeSystemThree M hM)
        (relativeCubeSystemThree_mps M hM)
        ((Lp.compMeasurePreservingₗᵢ ℂ
          cubeThreeOuterMiddleTranspose hσ) F) =
      (Lp.compMeasurePreservingₗᵢ ℂ
        cubeThreeOuterMiddleTranspose hσ)
        (invariantProjectionCLM
          (relativeCubeSystemThree M hM)
          (relativeCubeSystemThree_mps M hM) F) := by
  exact invariantProjection_comp_involutive
    (relativeCubeSystemThree M hM)
    (relativeCubeSystemThree_mps M hM)
    cubeThreeOuterMiddleTranspose hσ
    cubeThreeOuterMiddleTranspose_involutive
    (cubeThreeOuterMiddleTranspose_commutes M hM)
    F

end Chapter02.HostKraCubeSymmetry
