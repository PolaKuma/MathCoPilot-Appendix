import Chapter00.Section01
import Mathlib.Probability.UniformOn
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open Classical Filter
open scoped BigOperators

private noncomputable def probeBernoulliPMF (k : ℕ) (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : Finset.univ.sum p = 1) : PMF (Fin k) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (p i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), hsum]
    norm_num)

example (k : ℕ) (p : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : Finset.univ.sum p = 1) (a : Fin k) :
    (probeBernoulliPMF k p hp hsum).toMeasure ({a} : Set (Fin k)) =
      ENNReal.ofReal (p a) := by
  classical
  simp [probeBernoulliPMF]

example (k : ℕ) (p : Fin k → ℝ) (word : List (Fin k)) :
    (∏ i : Fin word.length, p (word.get i)) = (word.map p).prod := by
  simpa using (List.prod_ofFn (fun i : Fin word.length => p (word.get i))).symm

#check MeasureTheory.countable_generateSetAlgebra
#check MeasureTheory.isSetAlgebra_generateSetAlgebra
#check MeasureTheory.mem_generateSetAlgebra_elim
#print MeasureTheory.generateSetAlgebra
#print MeasureTheory.IsSetAlgebra
#check MeasureTheory.self_subset_generateSetAlgebra
#check MeasurableSpace.measurableSet_generateFrom
#check MeasurableSpace.generateFrom_le
#check MeasurableSpace.generateFrom_mono
#check Set.Countable.exists_surjective
#check Set.countable_range
#check TopologicalSpace.exists_countable_dense
#check Dense.exists_dist_lt
#check MeasureTheory.MemLp.toLp
#print MeasureTheory.Lp
#check MeasureTheory.Lp.norm_def
#check MeasureTheory.Lp.dist_def
#check MeasureTheory.MemLp.toLp_sub
#check MeasureTheory.Lp.memLp
#check MeasureTheory.MemLp.coeFn_toLp
#check ENNReal.toReal_lt_toReal
#check MeasureTheory.IsSeparable
#check @MeasureTheory.Lp.SecondCountableTopology
#print MeasureTheory.AddContent
#check MeasureTheory.AddContent.measureCaratheodory
#check MeasureTheory.AddContent.measureCaratheodory_eq
#check MeasureTheory.AddContent.inducedOuterMeasure_eq
#check MeasureTheory.AddContent.IsSigmaSubadditive
#check MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum
#check MeasureTheory.AddContent.measure
#check MeasureTheory.AddContent.measure_eq
#check Finset.sum_attach
#check MeasureTheory.IsSetAlgebra.isSetRing
#check MeasureTheory.IsSetRing.isSetSemiring
#check MeasureTheory.Measure.ext_of_generateFrom_of_cover
#check MeasureTheory.measure_iUnion

#check ProbabilityTheory.uniformOn
#check ProbabilityTheory.isProbabilityMeasure_uniformOn
#check MeasureTheory.Measure.count_apply
#check MeasureTheory.Measure.count_singleton
#check Continuous.measurable
#check MeasureTheory.ae_iff
#check MeasureTheory.Measure.restrict_apply_univ
#check MeasureTheory.Measure.restrict_apply

example {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (A : Set X) (hA : A.Finite) :
    MeasureTheory.Measure.count A = A.ncard := by
  rw [MeasureTheory.Measure.count_apply_finite A hA]
  norm_cast
  exact (Set.ncard_eq_toFinset_card A hA).symm

example {X : Type*} [MeasurableSpace X]
    (x : X) [MeasurableSingletonClass X] :
    MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.dirac x) := by
  infer_instance

example :
    MeasureTheory.IsProbabilityMeasure
      (@MeasureTheory.Measure.dirac PUnit ⊤ PUnit.unit) := by
  infer_instance

example {X : Type*} [TopologicalSpace X]
    (f : X -> ℝ) (hf : Continuous f) :
    @Measurable X ℝ (borel X) (borel ℝ) f := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  exact hf.measurable

example {X : Type*} [MeasurableSpace X]
    (f : X -> ℝ) :
    Measurable f ↔ ∀ B : Set ℝ, MeasurableSet B -> MeasurableSet (f ⁻¹' B) := by
  rfl

example {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (N : Set X) (hN : μ N = 0)
    (f g : X -> ℂ) :
    f =ᵐ[μ] fun x => if x ∈ N then g x else f x := by
  have h : ∀ᵐ x ∂μ, x ∉ N := by
    rw [MeasureTheory.ae_iff]
    have heq : {x | ¬ x ∉ N} = N := by
      ext x
      simp
    rwa [heq]
  filter_upwards [h] with x hx
  simp [hx]

example {X : Type*} [MeasurableSpace X]
    (A : Set X) :
    Measurable (Chapter00.Section01.characteristicFunctionDefinition A) ↔
      MeasurableSet A := by
  change Measurable (fun x => if x ∈ A then (1 : ℝ) else 0) ↔ MeasurableSet A
  constructor
  · intro h
    have hs : MeasurableSet
        ((fun x => if x ∈ A then (1 : ℝ) else 0) ⁻¹' ({1} : Set ℝ)) :=
      h (measurableSet_singleton (1 : ℝ))
    have heq :
        ((fun x => if x ∈ A then (1 : ℝ) else 0) ⁻¹' ({1} : Set ℝ)) = A := by
      ext x
      simp
    rwa [heq] at hs
  · intro hA
    exact Measurable.ite hA measurable_const measurable_const
#check MeasureTheory.Measure.count_apply_finite
#check Measurable.ite
#check PMF.toMeasure
#check PMF.toMeasure_apply_singleton
#check Set.ncard_eq_toFinset_card
#check TopologicalSpace.PositiveCompacts
#check MeasureTheory.Measure.haarMeasure
#check MeasureTheory.Measure.haarMeasure_self
#check Real.volume_Icc
#check TopologicalSpace.Compacts
#check TopologicalSpace.Compacts.mk
#check TopologicalSpace.PositiveCompacts.mk
#check MeasureTheory.tendsto_integral_of_dominated_convergence
#check MeasureTheory.hasFiniteIntegral_of_dominated_convergence
#check exists_stronglyMeasurable_limit_of_tendsto_ae
#check EReal.rec
#check MeasureTheory.IsSetSemiring.mem_supClosure_iff
#check MeasureTheory.IsSetSemiring.isSetRing_supClosure
#check Finpartition.parts
#check Fintype.equivFin
#print Finpartition
#print Finset.SupIndep
#check Finset.sup_eq_iSup
#print MeasureTheory.IsSetRing
#print MeasureTheory.JordanDecomposition
#check MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition
#check MeasureTheory.Measure.toSignedMeasure_apply
#check MeasureTheory.JordanDecomposition.toSignedMeasure_injective
#check MeasureTheory.Measure.ofMeasurable
#check MeasureTheory.Measure.ofMeasurable_apply
#check MeasureTheory.Measure.MeasureDense.approx

example (n : ℕ) (hn : 0 < n) :
    ∃ μ : MeasureTheory.Measure (Fin n),
      MeasureTheory.IsProbabilityMeasure μ ∧
        ∀ i : Fin n, μ ({i} : Set (Fin n)) = (n : ENNReal)⁻¹ := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let p : PMF (Fin n) := PMF.uniformOfFintype (Fin n)
  refine ⟨p.toMeasure, ?_, ?_⟩
  · infer_instance
  intro i
  calc
    p.toMeasure ({i} : Set (Fin n)) = p i :=
      PMF.toMeasure_apply_singleton p i (measurableSet_singleton i)
    _ = (n : ENNReal)⁻¹ := by simp [p]

example :
    ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1 ∧
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))
        (Set.Icc 0 1) = 1 := by
  constructor
  · rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num
  · rw [MeasureTheory.Measure.restrict_apply (measurableSet_Icc)]
    simp only [Set.inter_self, Real.volume_Icc]
    norm_num

example [MeasurableSpace Circle] [BorelSpace Circle] :
    ∃ m : MeasureTheory.Measure Circle,
      MeasureTheory.IsProbabilityMeasure m ∧ m.IsHaarMeasure := by
  let K : TopologicalSpace.PositiveCompacts Circle :=
    ⟨⟨Set.univ, isCompact_univ⟩, 1, by simp⟩
  let m : MeasureTheory.Measure Circle := MeasureTheory.Measure.haarMeasure K
  refine ⟨m, ?_, ?_⟩
  · apply MeasureTheory.IsProbabilityMeasure.mk
    simpa [m] using (MeasureTheory.Measure.haarMeasure_self (K₀ := K))
  · infer_instance

example {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (p q : ENNReal) : Chapter00.IsLpInclusionStatement μ p q := by
  intro hpq f hf
  exact hf.mono_exponent hpq.2.le

example (P : Chapter00.BasicProbabilitySpaceData) :
    Chapter00.DominatedConvergenceStatement P := by
  intro f g limit hf hg hbound hlim
  obtain ⟨limit', hlimit'_meas, hlimit'⟩ :=
    exists_stronglyMeasurable_limit_of_tendsto_ae hf
      (hlim.mono fun x hx ↦ ⟨limit x, hx⟩)
  have hlimit_eq : limit =ᵐ[P.μ] limit' := by
    filter_upwards [hlim, hlimit'] with x hx hx'
    exact tendsto_nhds_unique hx hx'
  have hlimit_meas : MeasureTheory.AEStronglyMeasurable limit P.μ :=
    hlimit'_meas.aestronglyMeasurable.congr hlimit_eq.symm
  have hlimit_finite : MeasureTheory.HasFiniteIntegral limit P.μ :=
    MeasureTheory.hasFiniteIntegral_of_dominated_convergence hg.2 hbound hlim
  refine ⟨⟨hlimit_meas, hlimit_finite⟩, ?_⟩
  exact MeasureTheory.tendsto_integral_of_dominated_convergence g hf hg hbound hlim

example {X : Type*} [MeasurableSpace X] (f : X → EReal) :
    Measurable f ↔
      ((∀ c : ℝ, MeasurableSet {x : X | (c : EReal) < f x}) ∧
        MeasurableSet {x : X | f x = ⊤}) := by
  constructor
  · intro hf
    refine ⟨fun c ↦ ?_, ?_⟩
    · change MeasurableSet (f ⁻¹' Set.Ioi (c : EReal))
      exact hf measurableSet_Ioi
    · change MeasurableSet (f ⁻¹' {(⊤ : EReal)})
      exact hf (measurableSet_singleton (⊤ : EReal))
  · rintro ⟨hlevel, htop⟩
    have hbot : MeasurableSet {x : X | (⊥ : EReal) < f x} := by
      have heq : {x : X | (⊥ : EReal) < f x} =
          ⋃ n : ℕ, {x : X | ((-(n : ℝ) : ℝ) : EReal) < f x} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · intro hx
          induction hfx : f x using EReal.rec with
          | bot => simp [hfx] at hx
          | coe a =>
              obtain ⟨n, hn⟩ := exists_nat_gt (-a)
              refine ⟨n, ?_⟩
              exact_mod_cast (show -(n : ℝ) < a by linarith)
          | top => exact ⟨0, by simp⟩
        · rintro ⟨n, hn⟩
          by_contra h
          have hfx : f x = ⊥ := by simpa using h
          rw [hfx] at hn
          simp at hn
      rw [heq]
      exact MeasurableSet.iUnion (fun n ↦ hlevel (-(n : ℝ)))
    apply measurable_of_Ioi
    intro a
    induction a using EReal.rec with
    | bot => simpa only [Set.preimage_setOf_eq] using hbot
    | coe a => simpa only [Set.preimage_setOf_eq] using hlevel a
    | top => simp

example {X : Type*} (Xsets : Chapter00.SetFamily X)
    (f : ℕ → X → EReal)
    (hX : Chapter00.IsSigmaAlgebraFamily Xsets)
    (hf : ∀ n : ℕ, Chapter00.MeasurableExtendedRealFunction Xsets (f n)) :
    Chapter00.MeasurableExtendedRealFunction Xsets (fun x ↦ ⨅ n : ℕ, f n x) ∧
      Chapter00.MeasurableExtendedRealFunction Xsets (fun x ↦ ⨆ n : ℕ, f n x) ∧
      Chapter00.MeasurableExtendedRealFunction Xsets
        (fun x ↦ ⨆ n : ℕ, ⨅ k : ℕ, f (n + k) x) ∧
      Chapter00.MeasurableExtendedRealFunction Xsets
        (fun x ↦ ⨅ n : ℕ, ⨆ k : ℕ, f (n + k) x) := by
  let m : MeasurableSpace X := {
    MeasurableSet' := Xsets
    measurableSet_empty := by
      have := hX.2.1 Set.univ hX.1
      simpa using this
    measurableSet_compl := hX.2.1
    measurableSet_iUnion := hX.2.2 }
  letI : MeasurableSpace X := m
  have measurable_of_levels (g : X → EReal)
      (hg : ∀ c : ℝ, MeasurableSet {x : X | (c : EReal) < g x}) :
      Measurable g := by
    have hbot : MeasurableSet {x : X | (⊥ : EReal) < g x} := by
      have heq : {x : X | (⊥ : EReal) < g x} =
          ⋃ n : ℕ, {x : X | ((-(n : ℝ) : ℝ) : EReal) < g x} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · intro hx
          induction hgx : g x using EReal.rec with
          | bot => simp [hgx] at hx
          | coe a =>
              obtain ⟨n, hn⟩ := exists_nat_gt (-a)
              exact ⟨n, by exact_mod_cast (show -(n : ℝ) < a by linarith)⟩
          | top => exact ⟨0, by simp⟩
        · rintro ⟨n, hn⟩
          by_contra h
          have hgx : g x = ⊥ := by simpa using h
          rw [hgx] at hn
          simp at hn
      rw [heq]
      exact MeasurableSet.iUnion (fun n ↦ hg (-(n : ℝ)))
    apply measurable_of_Ioi
    intro a
    induction a using EReal.rec with
    | bot => simpa only [Set.preimage_setOf_eq] using hbot
    | coe a => simpa only [Set.preimage_setOf_eq] using hg a
    | top => simp
  have hfm : ∀ n, Measurable (f n) := fun n ↦ measurable_of_levels (f n) (hf n)
  have hiInf : Measurable (fun x ↦ ⨅ n : ℕ, f n x) := Measurable.iInf hfm
  have hiSup : Measurable (fun x ↦ ⨆ n : ℕ, f n x) := Measurable.iSup hfm
  have hliminf : Measurable (fun x ↦ ⨆ n : ℕ, ⨅ k : ℕ, f (n + k) x) :=
    Measurable.iSup (fun n ↦ Measurable.iInf (fun k ↦ hfm (n + k)))
  have hlimsup : Measurable (fun x ↦ ⨅ n : ℕ, ⨆ k : ℕ, f (n + k) x) :=
    Measurable.iInf (fun n ↦ Measurable.iSup (fun k ↦ hfm (n + k)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    exact hiInf measurableSet_Ioi
  · intro c
    exact hiSup measurableSet_Ioi
  · intro c
    exact hliminf measurableSet_Ioi
  · intro c
    exact hlimsup measurableSet_Ioi

example {X : Type*} (S : Chapter00.SetFamily X) (hS : Chapter00.IsSemiAlgebra S) :
    Chapter00.generatedAlgebra S = supClosure S := by
  have hRing := hS.1.isSetRing_supClosure
  have finite_iUnion_mem :
      ∀ {n : ℕ} (B : Fin n → Set X), (∀ i, B i ∈ supClosure S) →
        (⋃ i, B i) ∈ supClosure S := by
    intro n B hB
    have hfinset : ∀ t : Finset (Fin n), (⋃ i ∈ t, B i) ∈ supClosure S := by
      intro t
      induction t using Finset.induction_on with
      | empty => simpa using hRing.empty_mem
      | @insert a t ha ih =>
          simpa [ha] using hRing.union_mem (hB a) ih
    simpa using hfinset Finset.univ
  have huniv : (Set.univ : Set X) ∈ supClosure S := by
    obtain ⟨n, B, _hdisj, hB, hcover⟩ := hS.2
    rw [← hcover]
    exact finite_iUnion_mem B (fun i ↦ subset_supClosure (hB i))
  have hAlg : Chapter00.IsAlgebra (supClosure S) := by
    refine ⟨hRing.empty_mem, (fun E hE F hF ↦ hRing.diff_mem hE hF), ?_⟩
    intro A hA
    have heq : Aᶜ = Set.univ \ A := by ext; simp
    rw [heq]
    exact hRing.diff_mem huniv hA
  apply le_antisymm
  · exact sInf_le ⟨hAlg, subset_supClosure⟩
  · intro C hC
    rw [hS.1.mem_supClosure_iff] at hC
    obtain ⟨P, hPS⟩ := hC
    rw [Chapter00.generatedAlgebra]
    intro A hA
    have hUnion : ∀ E F : Set X, E ∈ A → F ∈ A → E ∪ F ∈ A := by
      intro E F hE hF
      have hdiff := hA.1.2.1 Eᶜ (hA.1.2.2 E hE) F hF
      have hcomp := hA.1.2.2 (Eᶜ \ F) hdiff
      have heq : (Eᶜ \ F)ᶜ = E ∪ F := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_union]
        tauto
      rwa [heq] at hcomp
    have hfinite : ∀ t : Finset (Set X), (↑t : Set (Set X)) ⊆ S → t.sup id ∈ A := by
      intro t ht
      induction t using Finset.induction_on with
      | empty => simpa using hA.1.1
      | @insert E t hEt ih =>
          rw [Finset.sup_insert]
          exact hUnion E (t.sup id) (hA.2 (ht (Finset.mem_insert_self E t)))
            (ih fun F hF ↦ ht (Finset.mem_insert_of_mem hF))
    have hsup : P.parts.sup id ∈ A := hfinite P.parts hPS
    rwa [P.sup_parts] at hsup

example {X : Type*} (S : Chapter00.SetFamily X) (hS : Chapter00.IsSemiAlgebra S) :
    supClosure S =
      {C : Set X | ∃ n : ℕ, ∃ Cᵢ : Fin n → Set X,
        Chapter00.PairwiseDisjoint Cᵢ ∧ (∀ i, Cᵢ i ∈ S) ∧ C = ⋃ i, Cᵢ i} := by
  have hRing := hS.1.isSetRing_supClosure
  have finite_iUnion_mem :
      ∀ {n : ℕ} (B : Fin n → Set X), (∀ i, B i ∈ supClosure S) →
        (⋃ i, B i) ∈ supClosure S := by
    intro n B hB
    have hfinset : ∀ t : Finset (Fin n), (⋃ i ∈ t, B i) ∈ supClosure S := by
      intro t
      induction t using Finset.induction_on with
      | empty => simpa using hRing.empty_mem
      | @insert a t ha ih =>
          simpa [ha] using hRing.union_mem (hB a) ih
    simpa using hfinset Finset.univ
  ext C
  constructor
  · intro hC
    rw [hS.1.mem_supClosure_iff] at hC
    obtain ⟨P, hPS⟩ := hC
    let T := {E : Set X // E ∈ P.parts}
    let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
    let B : Fin (Fintype.card T) → Set X := fun i ↦ (e.symm i).1
    refine ⟨Fintype.card T, B, ?_, ?_, ?_⟩
    · intro i j hij
      have hi : B i ∈ P.parts := (e.symm i).2
      have hj : B j ∈ P.parts := (e.symm j).2
      have hne : B i ≠ B j := by
        intro h
        apply hij
        exact e.symm.injective (Subtype.ext h)
      have hd := P.supIndep
        (Finset.singleton_subset_iff.mpr hj) hi (by simpa using hne)
      simpa using hd
    · intro i
      exact hPS (e.symm i).2
    · have hunion_parts : (⋃ E : T, (E.1 : Set X)) = C := by
        calc
          (⋃ E : T, (E.1 : Set X)) = P.parts.sup id := by
            rw [Finset.sup_eq_iSup]
            exact iSup_subtype'' (↑P.parts : Set (Set X)) id
          _ = C := P.sup_parts
      have hreindex : (⋃ i, B i) = ⋃ E : T, (E.1 : Set X) := by
        ext x
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨i, hi⟩
          exact ⟨e.symm i, by simpa [B] using hi⟩
        · rintro ⟨E, hE⟩
          refine ⟨e E, ?_⟩
          simpa [B]
      exact hunion_parts.symm.trans hreindex.symm
  · rintro ⟨n, B, _hdisj, hB, rfl⟩
    exact finite_iUnion_mem B (fun i ↦ subset_supClosure (hB i))

example {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.SignedMeasure X) :
    ∃! p : MeasureTheory.Measure X × MeasureTheory.Measure X,
      p.1 Set.univ < ⊤ ∧ p.2 Set.univ < ⊤ ∧
        MeasureTheory.Measure.MutuallySingular p.1 p.2 ∧
        ∀ A : Set X, MeasurableSet A →
          μ A = (p.1 A).toReal - (p.2 A).toReal := by
  let j := μ.toJordanDecomposition
  refine ⟨(j.posPart, j.negPart), ?_, ?_⟩
  · refine ⟨j.posPart_finite.measure_univ_lt_top,
      j.negPart_finite.measure_univ_lt_top, j.mutuallySingular, ?_⟩
    intro A hA
    have heq := congrArg (fun s : MeasureTheory.SignedMeasure X ↦ s A)
      μ.toSignedMeasure_toJordanDecomposition
    simpa [MeasureTheory.JordanDecomposition.toSignedMeasure,
      MeasureTheory.Measure.toSignedMeasure_apply, hA, j] using heq.symm
  · intro q hq
    letI hq1 : MeasureTheory.IsFiniteMeasure q.1 :=
      ⟨by simpa using hq.1⟩
    letI hq2 : MeasureTheory.IsFiniteMeasure q.2 :=
      ⟨by simpa using hq.2.1⟩
    let jq : MeasureTheory.JordanDecomposition X :=
      ⟨q.1, q.2, hq.2.2.1⟩
    have hjq : jq.toSignedMeasure = μ := by
      ext A hA
      simpa [jq, MeasureTheory.JordanDecomposition.toSignedMeasure,
        MeasureTheory.Measure.toSignedMeasure_apply, hA] using (hq.2.2.2 A hA).symm
    have hj : jq = j :=
      MeasureTheory.JordanDecomposition.toSignedMeasure_injective
        (hjq.trans μ.toSignedMeasure_toJordanDecomposition.symm)
    exact Prod.ext (congrArg MeasureTheory.JordanDecomposition.posPart hj)
      (congrArg MeasureTheory.JordanDecomposition.negPart hj)

example (X : ℤ → Type*) (m : ∀ i, MeasurableSpace (X i))
    (μ : ∀ i, @MeasureTheory.Measure (X i) (m i))
    (hμ : ∀ i, @MeasureTheory.IsProbabilityMeasure (X i) (m i) (μ i)) :
    ∃ mprod : MeasurableSpace (∀ i, X i),
      mprod = MeasurableSpace.generateFrom
        (Chapter00.Section01.twoSidedProductCylinderFamily X m) ∧
      ∃ μprod : @MeasureTheory.Measure (∀ i, X i) mprod,
        @MeasureTheory.IsProbabilityMeasure (∀ i, X i) mprod μprod ∧
        (∀ s : Finset ℤ, ∀ A : ∀ i, Set (X i),
          (∀ i ∈ s, @MeasurableSet (X i) (m i) (A i)) →
          μprod {x | ∀ i ∈ s, x i ∈ A i} = s.prod fun i => μ i (A i)) ∧
        ∀ ν : @MeasureTheory.Measure (∀ i, X i) mprod,
          @MeasureTheory.IsProbabilityMeasure (∀ i, X i) mprod ν →
          (∀ s : Finset ℤ, ∀ A : ∀ i, Set (X i),
            (∀ i ∈ s, @MeasurableSet (X i) (m i) (A i)) →
            ν {x | ∀ i ∈ s, x i ∈ A i} = s.prod fun i => μ i (A i)) →
          ν = μprod := by
  letI (i : ℤ) : MeasurableSpace (X i) := m i
  letI (i : ℤ) : MeasureTheory.IsProbabilityMeasure (μ i) := hμ i
  let mprod : MeasurableSpace (∀ i, X i) := inferInstance
  refine ⟨mprod, ?_, MeasureTheory.Measure.infinitePi μ, ?_, ?_, ?_⟩
  · let G : Set (Set (∀ i, X i)) :=
      {C | ∃ (i : ℤ) (A : Set (X i)), MeasurableSet A ∧
        Function.eval i ⁻¹' A = C}
    have hfamily : G =
        Chapter00.Section01.twoSidedProductCylinderFamily X m := by
      dsimp [G, Chapter00.Section01.twoSidedProductCylinderFamily]
      ext C
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨i, A, hA, hEq⟩
        exact ⟨i, A, hA, hEq.symm⟩
      · rintro ⟨i, A, hA, hEq⟩
        exact ⟨i, A, hA, hEq.symm⟩
    calc
      mprod = MeasurableSpace.pi := rfl
      _ = MeasurableSpace.generateFrom G :=
        MeasurableSpace.pi_eq_generateFrom_projections
      _ = _ := congrArg MeasurableSpace.generateFrom hfamily
  · infer_instance
  · intro s A hA
    simpa [Set.pi] using MeasureTheory.Measure.infinitePi_pi μ hA
  · intro ν _hν hνcyl
    apply MeasureTheory.Measure.eq_infinitePi
    intro s A hA
    simpa [Set.pi] using hνcyl s A (fun i hi ↦ hA i)

example {X : Type*} (Xsets : Chapter00.SetFamily X) (μ : Set X → ENNReal)
    (A : Chapter00.SetFamily X) (hμ : Chapter00.IsProbabilityMeasureOn Xsets μ)
    (hA : Chapter00.IsAlgebra A) (hA_sub : A ⊆ Xsets)
    (hgen : Chapter00.generatedSigmaAlgebra A = Xsets) :
    Chapter00.almostEverywhereApproximation Xsets μ A := by
  let mX : MeasurableSpace X := {
    MeasurableSet' := Xsets
    measurableSet_empty := by
      have := hμ.1.1.2.1 Set.univ hμ.1.1.1
      simpa using this
    measurableSet_compl := hμ.1.1.2.1
    measurableSet_iUnion := hμ.1.1.2.2 }
  letI : MeasurableSpace X := mX
  let μ' : MeasureTheory.Measure X :=
    MeasureTheory.Measure.ofMeasurable
      (fun s _hs ↦ μ s)
      hμ.1.2.1
      (by
        intro f hf hd
        exact hμ.1.2.2 f hf (by simpa [Function.onFun] using hd))
  have hμ'_apply {s : Set X} (hs : MeasurableSet s) : μ' s = μ s :=
    MeasureTheory.Measure.ofMeasurable_apply s hs
  letI : MeasureTheory.IsFiniteMeasure μ' :=
    ⟨by rw [hμ'_apply MeasurableSet.univ, hμ.2]; simp⟩
  have hUnion : ∀ E F : Set X, E ∈ A → F ∈ A → E ∪ F ∈ A := by
    intro E F hE hF
    have hdiff := hA.2.1 Eᶜ (hA.2.2 E hE) F hF
    have hcomp := hA.2.2 (Eᶜ \ F) hdiff
    have heq : (Eᶜ \ F)ᶜ = E ∪ F := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_union]
      tauto
    rwa [heq] at hcomp
  have hA_math : MeasureTheory.IsSetAlgebra A := {
    empty_mem := hA.1
    compl_mem := fun _ h ↦ hA.2.2 _ h
    union_mem := fun _ _ hE hF ↦ hUnion _ _ hE hF }
  have hmgen : mX = MeasurableSpace.generateFrom A := by
    apply MeasurableSpace.ext
    intro E
    change E ∈ Xsets ↔ E ∈ Chapter00.generatedSigmaAlgebra A
    rw [hgen]
  have hdense : μ'.MeasureDense A :=
    MeasureTheory.Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
      μ' hA_math hmgen
  intro ε hε B hB
  have hBmeas : MeasurableSet B := hB
  obtain ⟨C, hCA, hdist⟩ :=
    hdense.approx B hBmeas (by simp) ε hε
  refine ⟨C, hCA, ?_⟩
  have hCmeas : MeasurableSet C := hA_sub hCA
  have heq : Chapter00.symmDiff C B = symmDiff B C := by
    change (C \ B) ∪ (B \ C) = (B \ C) ∪ (C \ B)
    exact Set.union_comm _ _
  rw [heq, ← hμ'_apply (hBmeas.symmDiff hCmeas)]
  exact hdist

example {X : Type*} (Xsets : Chapter00.SetFamily X) (μ : Set X → ENNReal)
    (hμ : Chapter00.IsProbabilityMeasureOn Xsets μ)
    (hcg : Chapter00.CountablyGeneratedFamily Xsets) :
    ∃ A : ℕ -> Set X, (∀ i, A i ∈ Xsets) ∧
      ∀ ε : ℝ, 0 < ε -> ∀ B ∈ Xsets,
        ∃ i : ℕ, μ (Chapter00.symmDiff (A i) B) < ENNReal.ofReal ε := by
  obtain ⟨G, hG⟩ := hcg
  let Alg : Chapter00.SetFamily X :=
    MeasureTheory.generateSetAlgebra (Set.range G)
  have hAlg_math : MeasureTheory.IsSetAlgebra Alg := by
    exact MeasureTheory.isSetAlgebra_generateSetAlgebra
  have hAlg : Chapter00.IsAlgebra Alg := by
    refine ⟨hAlg_math.empty_mem, ?_, hAlg_math.compl_mem⟩
    intro E hE F hF
    have h := hAlg_math.compl_mem
      (hAlg_math.union_mem (hAlg_math.compl_mem hE) hF)
    simpa [Set.diff_eq] using h
  have hAlg_meas : Alg ⊆ Chapter00.generatedSigmaAlgebra (Set.range G) := by
    intro E hE
    letI : MeasurableSpace X := MeasurableSpace.generateFrom (Set.range G)
    change MeasurableSet E
    induction hE with
    | base E hE => exact MeasurableSpace.measurableSet_generateFrom hE
    | empty => exact MeasurableSet.empty
    | compl E _ ih => exact ih.compl
    | union E F _ _ ihE ihF => exact ihE.union ihF
  have hAlg_sub : Alg ⊆ Xsets := by
    rw [← hG]
    exact hAlg_meas
  have hgenAlg : Chapter00.generatedSigmaAlgebra Alg = Xsets := by
    rw [← hG]
    have hm_forward : MeasurableSpace.generateFrom (Set.range G) ≤
        MeasurableSpace.generateFrom Alg :=
      MeasurableSpace.generateFrom_mono
        MeasureTheory.self_subset_generateSetAlgebra
    have hm_reverse : MeasurableSpace.generateFrom Alg ≤
        MeasurableSpace.generateFrom (Set.range G) :=
      MeasurableSpace.generateFrom_le hAlg_meas
    exact congrArg (fun m : MeasurableSpace X =>
      {E : Set X | @MeasurableSet X m E}) (le_antisymm hm_reverse hm_forward)
  have hAlg_count : Alg.Countable :=
    MeasureTheory.countable_generateSetAlgebra (Set.countable_range G)
  have hAlg_nonempty : Alg.Nonempty := ⟨∅, hAlg_math.empty_mem⟩
  obtain ⟨enum : ℕ → Alg, henum⟩ :=
    Set.Countable.exists_surjective hAlg_nonempty hAlg_count
  have happ := Chapter00.Section01.approximationLemma
    Xsets μ Alg hμ hAlg hAlg_sub hgenAlg
  refine ⟨fun n => (enum n).1, (fun n => hAlg_sub (enum n).2), ?_⟩
  intro ε hε B hB
  obtain ⟨C, hCAlg, hdist⟩ := happ ε hε B hB
  obtain ⟨i, hi⟩ := henum (⟨C, hCAlg⟩ : Alg)
  refine ⟨i, ?_⟩
  simpa [hi] using hdist

example {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] :
    Chapter00.IsSeparableBanachLpStatement μ := by
  intro hcg p hp hp_top
  letI : MeasurableSpace.CountablyGenerated X := hcg
  letI : Fact (1 ≤ p) := ⟨hp⟩
  letI : Fact (p ≠ ⊤) := ⟨ne_of_lt hp_top⟩
  letI : MeasureTheory.IsSeparable μ := inferInstance
  letI : SecondCountableTopology (MeasureTheory.Lp ℂ p μ) := inferInstance
  letI : TopologicalSpace.SeparableSpace (MeasureTheory.Lp ℂ p μ) := inferInstance
  obtain ⟨S, hScount, hSdense⟩ :=
    TopologicalSpace.exists_countable_dense (MeasureTheory.Lp ℂ p μ)
  let rep : MeasureTheory.Lp ℂ p μ → (X → ℂ) :=
    fun q => ⇑(q : X →ₘ[μ] ℂ)
  let D : Set (X → ℂ) := rep '' S
  refine ⟨D, hScount.image rep, ?_⟩
  intro f hf ε hε
  obtain ⟨q, hqS, hdist⟩ := hSdense.exists_dist_lt (hf.toLp f) hε
  refine ⟨rep q, ⟨q, hqS, rfl⟩, MeasureTheory.Lp.memLp q, ?_⟩
  have hae : (fun x => f x - rep q x) =ᵐ[μ]
      fun x => (hf.toLp f : X →ₘ[μ] ℂ) x - (q : X →ₘ[μ] ℂ) x := by
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  have heq : MeasureTheory.eLpNorm (fun x => f x - rep q x) p μ =
      MeasureTheory.eLpNorm
        (⇑(hf.toLp f : X →ₘ[μ] ℂ) - ⇑(q : X →ₘ[μ] ℂ)) p μ :=
    MeasureTheory.eLpNorm_congr_ae hae
  rw [heq]
  have hfinite : MeasureTheory.eLpNorm
      (⇑(hf.toLp f : X →ₘ[μ] ℂ) - ⇑(q : X →ₘ[μ] ℂ)) p μ ≠ ⊤ := by
    exact ne_of_lt ((MeasureTheory.Lp.memLp (hf.toLp f)).sub
      (MeasureTheory.Lp.memLp q)).2
  apply (ENNReal.toReal_lt_toReal hfinite (by simp)).mp
  simpa [MeasureTheory.Lp.dist_def, ENNReal.toReal_ofReal hε.le] using hdist

example (P : Chapter00.BasicProbabilitySpaceData) :
    Chapter00.NormConvergentLpSequenceHasAeSubsequence P := by
  intro p hp f limit hf hlimit htendsto
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hmeasure := MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
    hp0 (fun n => (hf n).1) hlimit.1 htendsto
  exact hmeasure.exists_seq_tendsto_ae

private noncomputable def testAddContent {X : Type*}
    (A : Chapter00.SetFamily X) (μ : Set X → ENNReal)
    (hμ : Chapter00.IsFinitelyAdditiveOn A μ) :
    MeasureTheory.AddContent ENNReal A := by
  refine
    { toFun := μ
      empty' := hμ.1
      sUnion' := ?_ }
  intro I hIA hIdis hIU
  let e := Fintype.equivFin I
  let B : Fin (Fintype.card I) → Set X := fun i => (e.symm i).1
  have hB : ∀ i, B i ∈ A := by
    intro i
    exact hIA (e.symm i).2
  have hBdis : Chapter00.PairwiseDisjoint B := by
    intro i j hij
    exact hIdis (e.symm i).2 (e.symm j).2 (by
      intro heq
      apply hij
      exact e.symm.injective (Subtype.ext heq))
  have hUnion : (⋃ i, B i) = ⋃₀ (I : Set (Set X)) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_sUnion, Finset.mem_coe, exists_prop]
    constructor
    · rintro ⟨i, hxi⟩
      exact ⟨(e.symm i).1, (e.symm i).2, hxi⟩
    · rintro ⟨U, hUI, hxU⟩
      let u : I := ⟨U, hUI⟩
      exact ⟨e u, by simpa [B, u] using hxU⟩
  have hadd := hμ.2 (Fintype.card I) B hB hBdis (hUnion.symm ▸ hIU)
  rw [hUnion] at hadd
  rw [hadd]
  classical
  simp only [B]
  calc
    (∑ i, μ (e.symm i).1) = ∑ U : I, μ U.1 :=
      Fintype.sum_equiv e.symm (fun i => μ (e.symm i).1)
        (fun U => μ U.1) (by simp)
    _ = ∑ u ∈ I, μ u := by
      change (∑ U ∈ I.attach, μ U.1) = ∑ u ∈ I, μ u
      exact Finset.sum_attach I μ

private theorem testMeasureCountablyAdditive {X : Type*}
    (A : Chapter00.SetFamily X)
    (ν : @MeasureTheory.Measure X (MeasurableSpace.generateFrom A)) :
    Chapter00.IsCountablyAdditiveOn (Chapter00.generatedSigmaAlgebra A) ν := by
  letI : MeasurableSpace X := MeasurableSpace.generateFrom A
  refine ⟨?_, ?_⟩
  · refine ⟨ν.empty, ?_⟩
    intro n F hF hdis _hUnion
    simpa [Function.onFun] using
      (MeasureTheory.measure_iUnion (μ := ν)
        (fun i j hij => hdis i j hij) (fun i => hF i))
  · intro F hF hdis _hUnion
    simpa [Function.onFun] using
      (MeasureTheory.measure_iUnion (μ := ν)
        (fun i j hij => hdis i j hij) (fun i => hF i))

example {X : Type*} (A : Chapter00.SetFamily X) (μ : Set X → ENNReal) :
    Chapter00.IsAlgebra A → Chapter00.IsCountablyAdditiveOn A μ → μ Set.univ < ⊤ →
      ∃ ν : Set X → ENNReal,
        Chapter00.IsMeasureExtension A (Chapter00.generatedSigmaAlgebra A) μ ν ∧
          Chapter00.IsCountablyAdditiveOn (Chapter00.generatedSigmaAlgebra A) ν ∧
          ∀ ν' : Set X → ENNReal,
            Chapter00.IsMeasureExtension A (Chapter00.generatedSigmaAlgebra A) μ ν' →
            Chapter00.IsCountablyAdditiveOn (Chapter00.generatedSigmaAlgebra A) ν' →
            Chapter00.EqualOnFamily (Chapter00.generatedSigmaAlgebra A) ν' ν := by
  intro hA hμ hfinite
  have hUnion : ∀ E F : Set X, E ∈ A → F ∈ A → E ∪ F ∈ A := by
    intro E F hE hF
    have hdiff := hA.2.1 Eᶜ (hA.2.2 E hE) F hF
    have hcomp := hA.2.2 (Eᶜ \ F) hdiff
    have heq : (Eᶜ \ F)ᶜ = E ∪ F := by ext; simp; tauto
    rwa [heq] at hcomp
  have hAlg : MeasureTheory.IsSetAlgebra A := {
    empty_mem := hA.1
    compl_mem := fun {_} hE => hA.2.2 _ hE
    union_mem := fun {_ _} hE hF => hUnion _ _ hE hF }
  have hRing : MeasureTheory.IsSetRing A := hAlg.isSetRing
  let content : MeasureTheory.AddContent ENNReal A := testAddContent A μ hμ.1
  have hsigma : content.IsSigmaSubadditive :=
    MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum hRing (by
      intro F hF hFU hdis
      exact hμ.2 F hF (by simpa [Function.onFun] using hdis) hFU)
  letI : MeasurableSpace X := MeasurableSpace.generateFrom A
  let νm : MeasureTheory.Measure X :=
    content.measure hRing.isSetSemiring le_rfl hsigma
  have hνeq {E : Set X} (hE : E ∈ A) : νm E = μ E := by
    exact MeasureTheory.AddContent.measure_eq content hRing.isSetSemiring rfl hsigma hE
  refine ⟨fun E => νm E, ⟨?_, (fun E hE => hνeq hE)⟩,
    testMeasureCountablyAdditive A νm, ?_⟩
  · intro E hE
    exact MeasurableSpace.measurableSet_generateFrom hE
  · intro ν' hν'ext hν'ca
    let νm' : MeasureTheory.Measure X :=
      MeasureTheory.Measure.ofMeasurable
        (fun E _hE => ν' E)
        hν'ca.1.1
        (by
          intro F hF hdis
          exact hν'ca.2 F hF (by simpa [Function.onFun] using hdis)
            (MeasurableSet.iUnion hF))
    have hνm'_apply {E : Set X} (hE : MeasurableSet E) : νm' E = ν' E :=
      MeasureTheory.Measure.ofMeasurable_apply E hE
    have heq : νm = νm' := by
      apply MeasureTheory.Measure.ext_of_generateFrom_of_cover
        (S := A) (T := {Set.univ}) rfl (Set.countable_singleton Set.univ)
        hRing.isSetSemiring.isPiSystem
      · simp
      · intro T hT
        simp only [Set.mem_singleton_iff] at hT
        subst T
        rw [hνeq hAlg.univ_mem]
        exact ne_of_lt hfinite
      · intro T hT E hE
        simp only [Set.mem_singleton_iff] at hT
        subst T
        rw [Set.inter_univ, hνeq hE, hνm'_apply
          (MeasurableSpace.measurableSet_generateFrom hE), hν'ext.2 E hE]
      · intro T hT
        simp only [Set.mem_singleton_iff] at hT
        subst T
        rw [hνeq hAlg.univ_mem, hνm'_apply MeasurableSet.univ,
          hν'ext.2 Set.univ hAlg.univ_mem]
    intro E hE
    rw [← hνm'_apply hE, ← heq]

example {X : Type*} (S : Chapter00.SetFamily X) (μ : Set X → ENNReal) :
    Chapter00.IsSemiAlgebra S → Chapter00.IsFinitelyAdditiveOn S μ →
      ∃ ν : Set X → ENNReal,
        Chapter00.IsMeasureExtension S (supClosure S) μ ν ∧
          Chapter00.IsFinitelyAdditiveOn (supClosure S) ν ∧
          ∀ ν' : Set X → ENNReal,
            Chapter00.IsMeasureExtension S (supClosure S) μ ν' →
            Chapter00.IsFinitelyAdditiveOn (supClosure S) ν' →
            Chapter00.EqualOnFamily (supClosure S) ν' ν := by
  intro hS hμ
  let content : MeasureTheory.AddContent ENNReal S := testAddContent S μ hμ
  let contentA : MeasureTheory.AddContent ENNReal (supClosure S) :=
    content.supClosure hS.1
  have hbase {E : Set X} (hE : E ∈ S) : contentA E = μ E := by
    exact MeasureTheory.AddContent.supClosure_apply_of_mem hS.1 content hE
  have hfiniteAdd : Chapter00.IsFinitelyAdditiveOn (supClosure S) contentA := by
    refine ⟨contentA.empty', ?_⟩
    intro n F hF hdis hFU
    exact MeasureTheory.addContent_iUnion hF
      (by simpa [Function.onFun] using hdis) hFU
  refine ⟨contentA, ⟨subset_supClosure, fun E hE => hbase hE⟩,
    hfiniteAdd, ?_⟩
  intro ν' hν'ext hν'add E hE
  obtain ⟨P, hPS⟩ := hS.1.mem_supClosure_iff.mp hE
  let content' : MeasureTheory.AddContent ENNReal (supClosure S) :=
    testAddContent (supClosure S) ν' hν'add
  have hPunion : (⋃ U ∈ P.parts, U) = E := by
    simpa only [Finset.sup_set_eq_biUnion] using P.sup_parts
  have hPsUnion : ⋃₀ (P.parts : Set (Set X)) = E := by
    simpa [Set.sUnion_eq_biUnion] using hPunion
  have hcontentA : contentA E = ∑ U ∈ P.parts, μ U := by
    exact MeasureTheory.AddContent.supClosure_apply_finpartition hS.1 content hPS
  have hcontent' : content' E = ∑ U ∈ P.parts, ν' U := by
    calc
      content' E = content' (⋃₀ (P.parts : Set (Set X))) :=
        congrArg content' hPsUnion.symm
      _ = ∑ U ∈ P.parts, content' U := content'.sUnion' P.parts
        (fun U hU => subset_supClosure (hPS hU)) P.disjoint
        (hPsUnion.symm ▸ hE)
      _ = ∑ U ∈ P.parts, ν' U := by rfl
  change content' E = contentA E
  rw [hcontent', hcontentA]
  apply Finset.sum_congr rfl
  intro U hU
  exact hν'ext.2 U (hPS hU)

#check isClosed_derivedSet
#check interior_maximal
#check interior_subset
#check isOpen_interior
#check closure_minimal
#check subset_closure
#check isClosed_closure
#check IsClosed.closure_eq
#check closure_eq_iff_isClosed
#check closure_eq_interior_union_frontier
