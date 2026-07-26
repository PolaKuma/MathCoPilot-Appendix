import Chapter04.MeasureAlgebra.MeasureAlgebraStone
import Chapter04.MeasureAlgebra.InducedMeasureAlgebra
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

noncomputable section

open Classical

namespace Chapter04.MeasureAlgebraStoneDynamics

universe u

open Chapter04.MeasureAlgebraRepresentation
open Chapter04.MeasureAlgebraStone

variable {A : MeasureAlgebraData.{u}} (hA : IsMeasureAlgebra A)

abbrev Q := AlgebraQuotient A hA

/-- The Boolean endomorphism induced on the quotient measure algebra. -/
def quotientMap
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ) :
    Q hA → Q hA :=
  Quotient.map Θ.map (fun _ _ hab => hΘ.1 _ _ hab)

@[simp] theorem quotientMap_mk
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ)
    (a : A.carrier) :
    quotientMap hA Θ hΘ (Quotient.mk _ a) = Quotient.mk _ (Θ.map a) :=
  rfl

theorem quotientMap_sup
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ)
    (q r : Q hA) :
    quotientMap hA Θ hΘ (q ⊔ r) =
      quotientMap hA Θ hΘ q ⊔ quotientMap hA Θ hΘ r := by
  induction q using Quotient.inductionOn with
  | _ a =>
    induction r using Quotient.inductionOn with
    | _ b =>
      exact Quotient.sound (hΘ.2.1 a b)

theorem quotientMap_compl
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ)
    (q : Q hA) :
    quotientMap hA Θ hΘ qᶜ = (quotientMap hA Θ hΘ q)ᶜ := by
  induction q using Quotient.inductionOn with
  | _ a =>
    rw [← quotientCompl_mk hA a, quotientMap_mk,
      quotientMap_mk, ← quotientCompl_mk]
    exact Quotient.sound (hΘ.2.2.1 a)

theorem quotientMap_monotone
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ) :
    Monotone (quotientMap hA Θ hΘ) := by
  intro q r hqr
  rw [← sup_eq_right] at hqr ⊢
  rw [← quotientMap_sup hA Θ hΘ, hqr]

theorem quotientMap_bot
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ) :
    quotientMap hA Θ hΘ (⊥ : Q hA) = ⊥ := by
  apply (quotientMeasure_eq_zero hA _).mp
  change A.measure (Θ.map A.bot) = 0
  rw [hΘ.2.2.2.2 A.bot]
  exact quotientMeasure_bot hA

theorem quotientMap_top
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ) :
    quotientMap hA Θ hΘ (⊤ : Q hA) = ⊤ := by
  rw [← compl_bot, quotientMap_compl, quotientMap_bot, compl_bot]

theorem quotientMap_inf
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ)
    (q r : Q hA) :
    quotientMap hA Θ hΘ (q ⊓ r) =
      quotientMap hA Θ hΘ q ⊓ quotientMap hA Θ hΘ r := by
  calc
    quotientMap hA Θ hΘ (q ⊓ r) =
        quotientMap hA Θ hΘ ((qᶜ ⊔ rᶜ)ᶜ) := by simp
    _ = (quotientMap hA Θ hΘ (qᶜ ⊔ rᶜ))ᶜ :=
      quotientMap_compl hA Θ hΘ _
    _ = (quotientMap hA Θ hΘ qᶜ ⊔
        quotientMap hA Θ hΘ rᶜ)ᶜ := by
      rw [quotientMap_sup]
    _ = quotientMap hA Θ hΘ q ⊓ quotientMap hA Θ hΘ r := by
      rw [quotientMap_compl, quotientMap_compl, compl_sup,
        compl_compl, compl_compl]

/-- The inverse image of an ideal under the quotient Boolean homomorphism. -/
def preimageIdeal
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ)
    (I : StonePoint hA) : Order.Ideal (Q hA) where
  carrier := {q | quotientMap hA Θ hΘ q ∈ I.1}
  lower' := by
    intro q r hqr hr
    exact I.1.lower (quotientMap_monotone hA Θ hΘ hqr) hr
  nonempty' := by
    refine ⟨⊥, ?_⟩
    change quotientMap hA Θ hΘ (⊥ : Q hA) ∈ I.1
    rw [quotientMap_bot]
    obtain ⟨q, hq⟩ := I.1.nonempty
    exact I.1.lower bot_le hq
  directed' := by
    intro q hq r hr
    refine ⟨q ⊔ r, ?_, le_sup_left, le_sup_right⟩
    change quotientMap hA Θ hΘ (q ⊔ r) ∈ I.1
    change quotientMap hA Θ hΘ q ∈ I.1 at hq
    change quotientMap hA Θ hΘ r ∈ I.1 at hr
    rw [quotientMap_sup]
    exact I.1.sup_mem hq hr

theorem isPrime_preimageIdeal
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ)
    (I : StonePoint hA) :
    Order.Ideal.IsPrime (preimageIdeal hA Θ hΘ I) := by
  let J := preimageIdeal hA Θ hΘ I
  letI : Order.Ideal.IsProper J :=
    Order.Ideal.isProper_of_notMem (p := (⊤ : Q hA)) (by
      change quotientMap hA Θ hΘ (⊤ : Q hA) ∉ I.1
      rw [quotientMap_top]
      exact stonePoint_top_not_mem hA I)
  apply Order.Ideal.IsPrime.of_mem_or_mem
  intro q r hqr
  change quotientMap hA Θ hΘ (q ⊓ r) ∈ I.1 at hqr
  rw [quotientMap_inf] at hqr
  exact I.2.mem_or_mem hqr

/-- Stone duality turns a measure-algebra endomorphism into a point map. -/
def stoneTransform
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ) :
    StonePoint hA → StonePoint hA :=
  fun I => ⟨preimageIdeal hA Θ hΘ I,
    isPrime_preimageIdeal hA Θ hΘ I⟩

theorem preimage_stoneSet
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ)
    (q : Q hA) :
    stoneTransform hA Θ hΘ ⁻¹' stoneSet hA q =
      stoneSet hA (quotientMap hA Θ hΘ q) :=
  rfl

theorem measurable_stoneTransform
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ) :
    @Measurable (StonePoint hA) (StonePoint hA)
      (stoneMeasurableSpace hA) (stoneMeasurableSpace hA)
      (stoneTransform hA Θ hΘ) := by
  letI : MeasurableSpace (StonePoint hA) := stoneMeasurableSpace hA
  apply measurable_generateFrom
  intro s hs
  obtain ⟨q, rfl⟩ := hs
  rw [preimage_stoneSet]
  exact measurableSet_stoneSet hA _

theorem quotientMeasure_quotientMap
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ)
    (q : Q hA) :
    quotientMeasure hA (quotientMap hA Θ hΘ q) =
      quotientMeasure hA q := by
  induction q using Quotient.inductionOn with
  | _ a =>
    exact hΘ.2.2.2.2 a

theorem isPiSystem_stoneAlgebra :
    IsPiSystem (stoneAlgebra hA) := by
  intro s hs t ht _
  obtain ⟨q, rfl⟩ := hs
  obtain ⟨r, rfl⟩ := ht
  exact ⟨q ⊓ r, stoneSet_inf hA q r⟩

theorem measurePreserving_stoneTransform
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ)
    (hTop : A.measure A.top = 1) :
    @MeasureTheory.MeasurePreserving (StonePoint hA) (StonePoint hA)
      (stoneMeasurableSpace hA) (stoneMeasurableSpace hA)
      (stoneTransform hA Θ hΘ) (stoneMeasure hA) (stoneMeasure hA) := by
  letI : MeasurableSpace (StonePoint hA) := stoneMeasurableSpace hA
  letI : MeasureTheory.IsFiniteMeasure (stoneMeasure hA) := by
    constructor
    rw [← stoneSet_top hA, stoneMeasure_stoneSet hA,
      quotientMeasure_top hA hTop]
    norm_num
  refine ⟨measurable_stoneTransform hA Θ hΘ, ?_⟩
  symm
  apply MeasureTheory.ext_of_generate_finite
    (stoneAlgebra hA) rfl (isPiSystem_stoneAlgebra hA)
  · intro s hs
    obtain ⟨q, rfl⟩ := hs
    rw [MeasureTheory.Measure.map_apply
      (measurable_stoneTransform hA Θ hΘ)
      (measurableSet_stoneSet hA q),
      preimage_stoneSet, stoneMeasure_stoneSet,
      stoneMeasure_stoneSet, quotientMeasure_quotientMap]
  · rw [MeasureTheory.Measure.map_apply
      (measurable_stoneTransform hA Θ hΘ) MeasurableSet.univ]
    simp

/-- The Stone probability space equipped with the dual transformation. -/
def stoneSystem
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ) :
    System.{u} where
  X := StonePoint hA
  measurableSpace := stoneMeasurableSpace hA
  μ := stoneMeasure hA
  T := stoneTransform hA Θ hΘ

theorem isMeasurePreservingSystem_stoneSystem
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ)
    (hTop : A.measure A.top = 1) :
    Chapter01.IsMeasurePreservingSystem (stoneSystem hA Θ hΘ) :=
  ⟨isProbabilitySpace_stoneProbabilitySpace hA hTop,
    measurePreserving_stoneTransform hA Θ hΘ hTop⟩

theorem representationHom_intertwines
    (Θ : MeasureAlgebraHomData A A) (hΘ : IsMeasureAlgebraHom Θ)
    (a : A.carrier) :
    (inducedMeasureAlgebraSystem (stoneSystem hA Θ hΘ)).equiv
      ((representationHom hA).map (Θ.map a))
      ((inducedMeasureAlgebraSystem (stoneSystem hA Θ hΘ)).transform
        ((representationHom hA).map a)) := by
  have hmeas : Measurable (stoneSystem hA Θ hΘ).T :=
    measurable_stoneTransform hA Θ hΘ
  simp only [inducedMeasureAlgebraSystem]
  rw [dif_pos hmeas]
  change stoneMeasure hA
    (Chapter00.symmDiff
      (stoneSet hA (Quotient.mk _ (Θ.map a)))
      (stoneTransform hA Θ hΘ ⁻¹'
        stoneSet hA (Quotient.mk _ a))) = 0
  rw [preimage_stoneSet, quotientMap_mk]
  simp [Chapter00.symmDiff]

theorem spatialModel_stoneSystem
    (S : MeasureAlgebraSystemData.{u})
    (hS : IsMeasureAlgebraSystem S)
    (hTop : S.measure S.top = 1) :
    ∃ Θ : MeasureAlgebraHomData S.toMeasureAlgebraData S.toMeasureAlgebraData,
      ∃ hΘ : IsMeasureAlgebraIsomorphism Θ,
        IsSpatialModelOfMeasureAlgebraSystem S
          (stoneSystem hS.1 Θ hΘ.1) := by
  obtain ⟨Θ, hΘ, htransform⟩ := hS.2
  refine ⟨Θ, hΘ, representationHom hS.1,
    isMeasureAlgebraIsomorphism_representationHom hS.1, ?_⟩
  intro a
  exact MeasureAlgebraRepresentation.equiv_trans
    (isMeasureAlgebra_inducedMeasureAlgebra
      (stoneSystem hS.1 Θ hΘ.1).toProbabilitySpace
      (isMeasurePreservingSystem_stoneSystem hS.1 Θ hΘ.1 hTop).1)
    ((isMeasureAlgebraHom_representationHom hS.1).1 _ _
      (MeasureAlgebraRepresentation.equiv_symm hS.1 (htransform a)))
    (representationHom_intertwines hS.1 Θ hΘ.1 a)

/-- Composition of measure-algebra-system isomorphisms. -/
theorem systemIsomorphism_trans
    {B : MeasureAlgebraSystemData.{u}}
    {A : MeasureAlgebraSystemData.{u}}
    {C : MeasureAlgebraSystemData.{u}}
    (_hB : IsMeasureAlgebra B.toMeasureAlgebraData)
    (_hA : IsMeasureAlgebra A.toMeasureAlgebraData)
    (hC : IsMeasureAlgebra C.toMeasureAlgebraData)
    (hBA : IsMeasureAlgebraSystemIsomorphism B A)
    (hAC : IsMeasureAlgebraSystemIsomorphism A C) :
    IsMeasureAlgebraSystemIsomorphism B C := by
  obtain ⟨Φ, hΦ, hΦT⟩ := hBA
  obtain ⟨Ψ, hΨ, hΨT⟩ := hAC
  let Ω : MeasureAlgebraHomData B.toMeasureAlgebraData C.toMeasureAlgebraData :=
    ⟨fun b => Ψ.map (Φ.map b)⟩
  refine ⟨Ω, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro b c hbc
        exact hΨ.1.1 _ _ (hΦ.1.1 _ _ hbc)
      · intro b c
        exact MeasureAlgebraRepresentation.equiv_trans hC
          (hΨ.1.1 _ _ (hΦ.1.2.1 b c))
          (hΨ.1.2.1 (Φ.map b) (Φ.map c))
      · intro b
        exact MeasureAlgebraRepresentation.equiv_trans hC
          (hΨ.1.1 _ _ (hΦ.1.2.2.1 b))
          (hΨ.1.2.2.1 (Φ.map b))
      · intro f
        exact MeasureAlgebraRepresentation.equiv_trans hC
          (hΨ.1.1 _ _ (hΦ.1.2.2.2.1 f))
          (hΨ.1.2.2.2.1 (fun n => Φ.map (f n)))
      · intro b
        exact (hΨ.1.2.2.2.2 (Φ.map b)).trans (hΦ.1.2.2.2.2 b)
    · intro b c hbc
      exact hΦ.2.1 _ _ (hΨ.2.1 _ _ hbc)
    · intro c
      obtain ⟨a, ha⟩ := hΨ.2.2 c
      obtain ⟨b, hb⟩ := hΦ.2.2 a
      refine ⟨b, MeasureAlgebraRepresentation.equiv_trans hC ?_ ha⟩
      exact hΨ.1.1 _ _ hb
  · intro b
    exact MeasureAlgebraRepresentation.equiv_trans hC
      (hΨ.1.1 _ _ (hΦT b)) (hΨT (Φ.map b))

theorem systemIsomorphism_refl
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter01.IsIsomorphicSystems M M := by
  have hfull :
      Chapter01.IsMeasurePreservingOnFullSets M M Set.univ Set.univ id := by
    refine ⟨MeasurableSet.univ, MeasurableSet.univ,
      hM.1.measure_univ, hM.1.measure_univ, by simp, ?_⟩
    intro B hB
    constructor
    · simpa using hB
    · simp
  refine ⟨hM, hM, Set.univ, Set.univ, id, id,
    hM.1.measure_univ, hM.1.measure_univ, by simp, by simp,
    hfull, hfull, ?_, ?_⟩
  · simp
  · simp

end Chapter04.MeasureAlgebraStoneDynamics
