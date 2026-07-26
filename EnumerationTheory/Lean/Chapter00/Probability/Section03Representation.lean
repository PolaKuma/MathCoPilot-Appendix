import Chapter00.Probability.Section03Disintegration
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

noncomputable section

open Classical Filter

namespace Chapter00.Section03

universe u

theorem countablyGeneratedRepresentationAux
    (P : BasicProbabilitySpaceData) [StandardBorelSpace P.X]
    (A : SetFamily P.X) :
    IsSigmaAlgebraFamily A -> A ⊆ P.𝓧 -> CountablyGeneratedFamily A ->
      ∃ X₀ : Set P.X, X₀ ∈ A ∧ P.μ X₀ = 1 ∧
      ∃ Y : Type u, ∃ _ : MetricSpace Y, ∃ _ : MeasurableSpace Y,
        CompactSpace Y ∧ BorelSpace Y ∧
        ∃ φ : X₀ -> Y, Measurable φ ∧
          (∀ B : Set P.X, B ∈ A ->
            ∃ C : Set Y, MeasurableSet C ∧
              B ∩ X₀ = {x : P.X | ∃ hx : x ∈ X₀, φ ⟨x, hx⟩ ∈ C}) ∧
          (∀ C : Set Y, MeasurableSet C ->
            ∃ B : Set P.X, B ∈ A ∧
              B ∩ X₀ = {x : P.X | ∃ hx : x ∈ X₀, φ ⟨x, hx⟩ ∈ C}) ∧
          ∀ x : X₀,
            (⋂₀ {B : Set P.X | B ∈ A ∧ (x : P.X) ∈ B}) ∩ X₀ =
              {z : P.X | ∃ hz : z ∈ X₀, φ ⟨z, hz⟩ = φ x} := by
  rintro hA hsub ⟨G, hgen⟩
  let X₀ : Set P.X := Set.univ
  let Y₀ := ℕ → Bool
  let metricY₀ : MetricSpace Y₀ := TopologicalSpace.metrizableSpaceMetric Y₀
  let Y := ULift.{u} Y₀
  let metricY : MetricSpace Y := MetricSpace.induced ULift.down ULift.down_injective metricY₀
  let measurableY : MeasurableSpace Y := borel Y
  let compactY : CompactSpace Y := by
    letI : MetricSpace Y₀ := metricY₀
    letI : MetricSpace Y := metricY
    refine ⟨?_⟩
    have hup : Continuous (ULift.up : Y₀ → Y) :=
      (Isometry.of_dist_eq (f := (ULift.up : Y₀ → Y)) fun _ _ => rfl).continuous
    have himage : (ULift.up : Y₀ → Y) '' Set.univ = Set.univ := by
      apply Set.eq_univ_of_forall
      intro y
      exact ⟨y.down, Set.mem_univ _, ULift.up_down y⟩
    rw [← himage]
    exact isCompact_univ.image hup
  let φ : X₀ → Y := fun x =>
    ULift.up (fun n => decide ((x : P.X) ∈ G n))
  letI : MeasurableSpace Y := measurableY
  letI : BorelSpace Y := ⟨rfl⟩
  refine ⟨X₀, hA.1, MeasureTheory.measure_univ, Y, metricY, measurableY,
    compactY, inferInstance, φ, ?_, ?_, ?_, ?_⟩
  · letI : MetricSpace Y₀ := metricY₀
    letI : MetricSpace Y := metricY
    have hup : Measurable (ULift.up : Y₀ → Y) :=
      (Isometry.of_dist_eq (f := (ULift.up : Y₀ → Y)) fun _ _ => rfl).continuous.measurable
    apply hup.comp
    apply measurable_pi_lambda
    intro n
    have hGn : MeasurableSet (G n) := hsub (by
      rw [← hgen]
      exact MeasurableSpace.measurableSet_generateFrom ⟨n, rfl⟩)
    intro s hs
    by_cases ht : true ∈ s <;> by_cases hf : false ∈ s
    · have hs' : s = Set.univ := by ext b; cases b <;> simp [ht, hf]
      rw [hs']
      exact MeasurableSet.univ
    · have hs' : s = {true} := by ext b; cases b <;> simp [ht, hf]
      rw [hs']
      convert hGn.preimage
        (measurable_subtype_coe : Measurable (Subtype.val : X₀ → P.X)) using 1 <;>
        ext x <;> simp
    · have hs' : s = {false} := by ext b; cases b <;> simp [ht, hf]
      rw [hs']
      convert hGn.compl.preimage
        (measurable_subtype_coe : Measurable (Subtype.val : X₀ → P.X)) using 1 <;>
        ext x <;> simp
    · have hs' : s = ∅ := by ext b; cases b <;> simp [ht, hf]
      simp [hs']
  · intro B hBA
    have hBm : @MeasurableSet P.X
        (MeasurableSpace.generateFrom (Set.range G)) B := by
      rw [← hgen] at hBA
      exact hBA
    have hrep : ∃ C : Set Y, MeasurableSet C ∧
        B = {x : P.X | ULift.up (fun n => decide (x ∈ G n)) ∈ C} := by
      apply MeasurableSpace.generateFrom_induction (Set.range G)
          (fun B _ => ∃ C : Set Y, MeasurableSet C ∧
            B = {x : P.X | ULift.up (fun n => decide (x ∈ G n)) ∈ C})
      · rintro _ ⟨n, rfl⟩ _
        let C : Set Y := {y | y.down n = true}
        refine ⟨C, ?_, ?_⟩
        · exact (measurable_pi_apply n).comp
            ((Isometry.of_dist_eq (f := (ULift.down : Y → Y₀)) fun _ _ => rfl).continuous.measurable) |>
            fun h => h (measurableSet_singleton true)
        · ext x
          change x ∈ G n ↔ decide (x ∈ G n) = true
          simp
      · exact ⟨∅, MeasurableSet.empty, by ext; simp⟩
      · rintro B _ ⟨C, hC, hBC⟩
        refine ⟨Cᶜ, hC.compl, ?_⟩
        ext x
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
        rw [hBC]
        rfl
      · intro B _ hrepB
        choose C hCm hBC using hrepB
        refine ⟨⋃ n, C n, MeasurableSet.iUnion hCm, ?_⟩
        ext x
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, by simpa [hBC n] using hn⟩
      · exact hBm
    rcases hrep with ⟨C, hC, hBC⟩
    refine ⟨C, hC, ?_⟩
    ext x
    simp [X₀, φ, hBC]
  · intro C hC
    let ψ : P.X → Y := fun x => ULift.up (fun n => decide (x ∈ G n))
    have hψ : @Measurable P.X Y
        (MeasurableSpace.generateFrom (Set.range G)) measurableY ψ := by
      letI : MeasurableSpace P.X := MeasurableSpace.generateFrom (Set.range G)
      letI : MetricSpace Y₀ := metricY₀
      letI : MetricSpace Y := metricY
      have hup : Measurable (ULift.up : Y₀ → Y) :=
        (Isometry.of_dist_eq (f := (ULift.up : Y₀ → Y)) fun _ _ => rfl).continuous.measurable
      apply hup.comp
      apply measurable_pi_lambda
      intro n s hs
      by_cases ht : true ∈ s <;> by_cases hf : false ∈ s
      · have hs' : s = Set.univ := by ext b; cases b <;> simp [ht, hf]
        rw [hs']; exact MeasurableSet.univ
      · have hs' : s = {true} := by ext b; cases b <;> simp [ht, hf]
        rw [hs']
        convert MeasurableSpace.measurableSet_generateFrom
          (show G n ∈ Set.range G from ⟨n, rfl⟩) using 1 <;> ext x <;> simp
      · have hs' : s = {false} := by ext b; cases b <;> simp [ht, hf]
        rw [hs']
        convert (MeasurableSpace.measurableSet_generateFrom
          (show G n ∈ Set.range G from ⟨n, rfl⟩)).compl using 1 <;> ext x <;> simp
      · have hs' : s = ∅ := by ext b; cases b <;> simp [ht, hf]
        rw [hs']; exact MeasurableSet.empty
    let B : Set P.X := ψ ⁻¹' C
    have hBm : @MeasurableSet P.X
        (MeasurableSpace.generateFrom (Set.range G)) B := hC.preimage hψ
    have hBA : B ∈ A := by rw [← hgen]; exact hBm
    refine ⟨B, hBA, ?_⟩
    ext x
    simp [B, ψ, X₀, φ]
  · intro x
    ext z
    simp only [Set.mem_inter_iff, Set.mem_sInter, Set.mem_setOf_eq]
    simp only [X₀, Set.mem_univ, and_true]
    constructor
    · intro hz
      refine ⟨Set.mem_univ z, ?_⟩
      apply ULift.ext
      funext n
      change decide (z ∈ G n) = decide ((x : P.X) ∈ G n)
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hzdec
        have hzn : z ∈ G n := of_decide_eq_true hzdec
        have hxGn : (x : P.X) ∈ G n := by
          by_contra hxnot
          have := hz (G n)ᶜ
          exact (this ⟨by rw [← hgen]; exact
            (MeasurableSpace.measurableSet_generateFrom
              (show G n ∈ Set.range G from ⟨n, rfl⟩)).compl, by simpa using hxnot⟩) hzn
        exact decide_eq_true hxGn
      · intro hxdec
        have hxn : (x : P.X) ∈ G n := of_decide_eq_true hxdec
        have hGA : G n ∈ A := by
          rw [← hgen]
          exact MeasurableSpace.measurableSet_generateFrom
            (show G n ∈ Set.range G from ⟨n, rfl⟩)
        exact decide_eq_true (hz (G n) ⟨hGA, hxn⟩)
    · rintro ⟨_, heq⟩ B hB
      have hpat : ∀ n, (x : P.X) ∈ G n ↔ z ∈ G n := by
        intro n
        have hn := congrFun (congrArg ULift.down heq) n
        change decide (z ∈ G n) = decide ((x : P.X) ∈ G n) at hn
        constructor
        · intro hx
          apply of_decide_eq_true
          exact hn.trans (decide_eq_true hx)
        · intro hz
          apply of_decide_eq_true
          exact hn.symm.trans (decide_eq_true hz)
      have hBm : @MeasurableSet P.X
          (MeasurableSpace.generateFrom (Set.range G)) B := by
        change B ∈ generatedSigmaAlgebra (Set.range G)
        rw [hgen]
        exact hB.1
      have hiff : (x : P.X) ∈ B ↔ z ∈ B := by
        apply MeasurableSpace.generateFrom_induction (Set.range G)
            (fun C _ => (x : P.X) ∈ C ↔ z ∈ C)
        · rintro _ ⟨n, rfl⟩ _; exact hpat n
        · simp
        · intro C _ h; simpa only [Set.mem_compl_iff, not_iff_not] using h
        · intro C _ h
          simp only [Set.mem_iUnion]
          exact exists_congr fun n => h n
        · exact hBm
      exact hiff.mp hB.2

end Chapter00.Section03
