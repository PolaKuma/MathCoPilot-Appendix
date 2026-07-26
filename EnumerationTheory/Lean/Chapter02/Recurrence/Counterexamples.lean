import Chapter02.Common
import Mathlib.NumberTheory.Zsqrtd.Basic

noncomputable section

open Set Filter

namespace Chapter02
namespace Counterexamples

universe u

private abbrev G₂ := ULift.{u} (ZMod 2)

private local instance : MetricSpace G₂ :=
  TopologicalSpace.metrizableSpaceMetric G₂

private def liftedIdentity : G₂ →+ G₂ := AddMonoidHom.id G₂

private def liftedCharacter : ContinuousCircleCharacter G₂ where
  toFun x := AddChar.zmodAddEquiv (1 : ZMod 2) x.down
  map_zero := by simp
  map_add := by
    intro x y
    exact (AddChar.zmodAddEquiv (1 : ZMod 2)).map_add_eq_mul' x.down y.down
  continuous := continuous_of_discreteTopology
  unit_norm := by intro x; exact AddChar.norm_apply _ _

private theorem liftedCharacter_nontrivial :
    ¬ ∀ x, liftedCharacter.toFun x = 1 := by
  intro h
  have heq : AddChar.zmodAddEquiv (1 : ZMod 2) = 0 := by
    ext x
    simpa using h (ULift.up x)
  have hne : AddChar.zmodAddEquiv (1 : ZMod 2) ≠ 0 :=
    (AddEquiv.map_ne_zero_iff _).2 one_ne_zero
  exact hne heq

private theorem liftedDiracIdentity_ergodic :
    IsErgodic (compactGroupEndomorphismSystem
      (MeasureTheory.Measure.dirac (0 : G₂)) liftedIdentity) := by
  let M := compactGroupEndomorphismSystem
    (MeasureTheory.Measure.dirac (0 : G₂)) liftedIdentity
  have hprob : MeasureTheory.IsProbabilityMeasure M.μ := by
    dsimp [M, compactGroupEndomorphismSystem]
    infer_instance
  have hpres : MeasureTheory.MeasurePreserving M.T M.μ M.μ := by
    simpa [M, compactGroupEndomorphismSystem, liftedIdentity] using
      (MeasureTheory.MeasurePreserving.id
        (MeasureTheory.Measure.dirac (0 : G₂)))
  refine ⟨⟨hprob, hpres⟩, ?_⟩
  intro B hB _hinv
  by_cases hzero : (0 : G₂) ∈ B
  · right
    change MeasureTheory.Measure.dirac (0 : G₂) B = 1
    simp [hzero]
  · left
    change MeasureTheory.Measure.dirac (0 : G₂) B = 0
    simp [hzero]

/-- The current formal statement of Example 2.1.15 is false without the
Haar-measure hypothesis: the identity on a two-element compact group with a
Dirac invariant probability measure is ergodic, while every character is
periodic. -/
theorem compactGroupEndomorphismErgodicityStatement_false :
    ¬ LegacyCompactGroupEndomorphismErgodicityStatement := by
  unfold LegacyCompactGroupEndomorphismErgodicityStatement
  intro h
  have hspec := h G₂ inferInstance inferInstance inferInstance
    inferInstance inferInstance (MeasureTheory.Measure.dirac (0 : G₂))
    (by infer_instance) liftedIdentity
    (by simpa [liftedIdentity] using (continuous_id : Continuous (id : G₂ → G₂)))
    (by intro x; exact ⟨x, rfl⟩)
    (by simpa [liftedIdentity] using
      (MeasureTheory.MeasurePreserving.id
        (MeasureTheory.Measure.dirac (0 : G₂))))
  have hrhs := hspec.mp liftedDiracIdentity_ergodic
  apply liftedCharacter_nontrivial
  apply hrhs liftedCharacter
  refine ⟨1, by omega, ?_⟩
  funext x
  rfl

private abbrev G₃ := ULift.{u} (ZMod 3)

private local instance : MetricSpace G₃.{u} :=
  TopologicalSpace.metrizableSpaceMetric G₃.{u}

private def liftedNegation : G₃.{u} →+ G₃.{u} where
  toFun x := ⟨-x.down⟩
  map_zero' := by apply ULift.ext; simp
  map_add' := by intro x y; apply ULift.ext; simp [add_comm]

private def orbitMeasure : MeasureTheory.Measure G₃.{u} :=
  (2 : ENNReal)⁻¹ •
    (MeasureTheory.Measure.dirac (ULift.up (1 : ZMod 3)) +
      MeasureTheory.Measure.dirac (ULift.up (-1 : ZMod 3)))

private theorem orbitMeasure_probability :
    MeasureTheory.IsProbabilityMeasure
      (orbitMeasure : MeasureTheory.Measure G₃.{u}) := by
  refine ⟨?_⟩
  simp only [orbitMeasure, MeasureTheory.Measure.smul_apply,
    MeasureTheory.Measure.add_apply]
  simp only [MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_univ _)]
  have hs : (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by simp)).mp
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]
  simpa [mul_add] using hs

private theorem liftedNegation_preserving :
    MeasureTheory.MeasurePreserving liftedNegation
      (orbitMeasure : MeasureTheory.Measure G₃.{u}) orbitMeasure := by
  apply MeasureTheory.MeasurePreserving.mk
  · exact continuous_of_discreteTopology.measurable
  · apply MeasureTheory.Measure.ext_of_singleton
    intro a
    rw [MeasureTheory.Measure.map_apply continuous_of_discreteTopology.measurable
      (measurableSet_singleton a)]
    by_cases ha : a = ULift.up (1 : ZMod 3)
    · subst a
      simp [orbitMeasure, liftedNegation, Set.indicator]
      ac_rfl
    · by_cases hb : a = ULift.up (-1 : ZMod 3)
      · subst a
        simp [orbitMeasure, liftedNegation, Set.indicator]
        ac_rfl
      · simp [orbitMeasure, liftedNegation, ha, hb, eq_comm, Set.indicator]

private theorem orbitMeasure_singleton_one :
    orbitMeasure ({ULift.up (1 : ZMod 3)} : Set G₃.{u}) = (2 : ENNReal)⁻¹ := by
  have hz : (-1 : ZMod 3) ≠ 1 := by native_decide
  have hne : (⟨(-1 : ZMod 3)⟩ : G₃.{u}) ≠ (⟨(1 : ZMod 3)⟩ : G₃.{u}) :=
    fun h ↦ hz (congrArg ULift.down h)
  simp [orbitMeasure, Set.indicator, hne]

private theorem orbitMeasure_singleton_neg_one :
    orbitMeasure ({ULift.up (-1 : ZMod 3)} : Set G₃.{u}) = (2 : ENNReal)⁻¹ := by
  have hz : (1 : ZMod 3) ≠ -1 := by native_decide
  have hne : (⟨(1 : ZMod 3)⟩ : G₃.{u}) ≠ (⟨(-1 : ZMod 3)⟩ : G₃.{u}) :=
    fun h ↦ hz (congrArg ULift.down h)
  simp [orbitMeasure, Set.indicator, hne]

private theorem liftedNegation_orbit_ergodic :
    IsErgodic (compactGroupEndomorphismSystem
      (orbitMeasure : MeasureTheory.Measure G₃.{u})
      (liftedNegation : G₃.{u} →+ G₃.{u})) := by
  refine ⟨⟨orbitMeasure_probability, liftedNegation_preserving⟩, ?_⟩
  intro B hB hInv
  change orbitMeasure (Chapter00.symmDiff (liftedNegation ⁻¹' B) B) = 0 at hInv
  have hsame : ULift.up (1 : ZMod 3) ∈ B ↔
      ULift.up (-1 : ZMod 3) ∈ B := by
    constructor
    · intro hOne
      by_contra hNeg
      have hmem : ULift.up (-1 : ZMod 3) ∈
          Chapter00.symmDiff (liftedNegation ⁻¹' B) B := by
        simp [Chapter00.symmDiff, liftedNegation, hOne, hNeg]
      have hle : orbitMeasure ({ULift.up (-1 : ZMod 3)} : Set G₃.{u}) ≤
          orbitMeasure (Chapter00.symmDiff (liftedNegation ⁻¹' B) B) :=
        MeasureTheory.measure_mono
        (show ({ULift.up (-1 : ZMod 3)} : Set G₃.{u}) ⊆
          Chapter00.symmDiff (liftedNegation ⁻¹' B) B by simpa)
      have hz : orbitMeasure ({ULift.up (-1 : ZMod 3)} : Set G₃.{u}) = 0 := by
        apply le_antisymm
        · exact hle.trans_eq hInv
        · exact bot_le
      rw [orbitMeasure_singleton_neg_one] at hz
      simp at hz
    · intro hNeg
      by_contra hOne
      have hmem : ULift.up (1 : ZMod 3) ∈
          Chapter00.symmDiff (liftedNegation ⁻¹' B) B := by
        simp [Chapter00.symmDiff, liftedNegation, hOne, hNeg]
      have hle : orbitMeasure ({ULift.up (1 : ZMod 3)} : Set G₃.{u}) ≤
          orbitMeasure (Chapter00.symmDiff (liftedNegation ⁻¹' B) B) :=
        MeasureTheory.measure_mono
        (show ({ULift.up (1 : ZMod 3)} : Set G₃.{u}) ⊆
          Chapter00.symmDiff (liftedNegation ⁻¹' B) B by simpa)
      have hz : orbitMeasure ({ULift.up (1 : ZMod 3)} : Set G₃.{u}) = 0 := by
        apply le_antisymm
        · exact hle.trans_eq hInv
        · exact bot_le
      rw [orbitMeasure_singleton_one] at hz
      simp at hz
  by_cases hOne : ULift.up (1 : ZMod 3) ∈ B
  · right
    have hNeg := hsame.mp hOne
    change orbitMeasure B = 1
    have htotal : (orbitMeasure : MeasureTheory.Measure G₃.{u}) Set.univ = 1 :=
      orbitMeasure_probability.measure_univ
    simpa [orbitMeasure, hOne, hNeg] using htotal
  · left
    have hNeg : ULift.up (-1 : ZMod 3) ∉ B := by
      exact fun h ↦ hOne (hsame.mpr h)
    change orbitMeasure B = 0
    simp [orbitMeasure, hOne, hNeg]

private theorem orbitMeasure_singleton_one_toReal :
    (orbitMeasure ({ULift.up (1 : ZMod 3)} : Set G₃.{u})).toReal = (1 : ℝ) / 2 := by
  rw [orbitMeasure_singleton_one]
  norm_num [ENNReal.toReal_inv]

private theorem liftedNegation_orbit_not_weakMixing :
    ¬ IsWeakMixing (compactGroupEndomorphismSystem
      (orbitMeasure : MeasureTheory.Measure G₃.{u})
      (liftedNegation : G₃.{u} →+ G₃.{u})) := by
  let M : System.{u} := compactGroupEndomorphismSystem
    (orbitMeasure : MeasureTheory.Measure G₃.{u})
    (liftedNegation : G₃.{u} →+ G₃.{u})
  let A : Set G₃.{u} := {ULift.up (1 : ZMod 3)}
  intro hweak
  have hterm : ∀ n : ℕ,
      |correlation M A A n - productMeasureValue M A A| = (1 : ℝ) / 4 := by
    intro n
    let E := A ∩ preimageIter M n A
    have hEA : E = A ∨ E = ∅ := by
      by_cases hp : ULift.up (1 : ZMod 3) ∈ preimageIter M n A
      · left
        ext z
        constructor
        · exact fun hz ↦ hz.1
        · intro hz
          have hzEq : z = ULift.up (1 : ZMod 3) := hz
          subst z
          exact ⟨Set.mem_singleton _, hp⟩
      · right
        ext z
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hz
        have hzEq : z = ULift.up (1 : ZMod 3) := hz.1
        subst z
        exact hp hz.2
    have hAmeasure : realMeasure M A = (1 : ℝ) / 2 := by
      exact orbitMeasure_singleton_one_toReal
    rcases hEA with hEA | hEA
    · have hcorr : correlation M A A n = (1 : ℝ) / 2 := by
        change realMeasure M E = _
        rw [hEA]
        exact hAmeasure
      rw [hcorr]
      simp [productMeasureValue, hAmeasure]
      norm_num
    · have hcorr : correlation M A A n = 0 := by
        change realMeasure M E = 0
        rw [hEA]
        simp [realMeasure]
      rw [hcorr]
      simp [productMeasureValue, hAmeasure]
      norm_num
  have hA : A ∈ M.𝓧 := by
    change MeasurableSet A
    simp [A]
  have ht := hweak.2 A A hA hA
  have hfun : (fun n : ℕ ↦
      |correlation M A A n - productMeasureValue M A A|) =
      (fun _ : ℕ ↦ (1 : ℝ) / 4) := funext hterm
  rw [hfun] at ht
  have hces : (fun N : ℕ ↦ cesaroAverage (fun _ : ℕ ↦ (1 : ℝ) / 4) N) =
      (fun _ : ℕ ↦ (1 : ℝ) / 4) := by
    funext N
    simp [cesaroAverage]
    field_simp
  change Tendsto (fun N : ℕ ↦ cesaroAverage (fun _ : ℕ ↦ (1 : ℝ) / 4) N)
    atTop (nhds 0) at ht
  rw [hces] at ht
  have ht' : Tendsto (fun _ : ℕ ↦ (1 : ℝ) / 4) atTop (nhds ((1 : ℝ) / 4)) :=
    tendsto_const_nhds
  have hz := tendsto_nhds_unique ht' ht
  norm_num at hz

/-- The current formal statement of Theorem 2.4.15 is false for arbitrary
invariant probability measures.  On `Z/3Z`, negation with the uniform measure
on its two-cycle `{1,-1}` is ergodic but not weakly mixing. -/
theorem compactGroupEndomorphismMixingEquivalence_false :
    ¬ LegacyCompactGroupEndomorphismMixingEquivalence.{u} := by
  unfold LegacyCompactGroupEndomorphismMixingEquivalence
  intro h
  have hspec := h G₃.{u} inferInstance inferInstance inferInstance
    inferInstance inferInstance
    (orbitMeasure : MeasureTheory.Measure G₃.{u}) orbitMeasure_probability
    (liftedNegation : G₃.{u} →+ G₃.{u})
    continuous_of_discreteTopology
    (by
      intro x
      refine ⟨⟨-x.down⟩, ?_⟩
      apply ULift.ext
      simp [liftedNegation])
    liftedNegation_preserving
  exact liftedNegation_orbit_not_weakMixing
    (hspec.1.mp liftedNegation_orbit_ergodic)

end Counterexamples
end Chapter02
