import Chapter00.Common
import Chapter00.Probability.Section01DaniellKolmogorov
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter00
namespace Section01

universe u

private theorem generatedAlgebra_eq_supClosure_of_isSemiAlgebra {X : Type u}
    (S : SetFamily X) (hS : IsSemiAlgebra S) :
    generatedAlgebra S = supClosure S := by
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
  have hAlg : IsAlgebra (supClosure S) := by
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
    rw [generatedAlgebra]
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

private theorem supClosure_eq_finiteDisjointUnions {X : Type u}
    (S : SetFamily X) (hS : IsSemiAlgebra S) :
    supClosure S =
      {C : Set X | ∃ n : ℕ, ∃ Cᵢ : Fin n → Set X,
        PairwiseDisjoint Cᵢ ∧ (∀ i, Cᵢ i ∈ S) ∧ C = ⋃ i, Cᵢ i} := by
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

/--
Source: Proposition 0.1.8, Chapter 0, Section 1.
The algebra generated by a semialgebra consists exactly of finite disjoint
unions of members of the semialgebra.
-/
theorem algebraGeneratedBySemiAlgebraFiniteDisjointUnions {X : Type u}
    (S : SetFamily X) (hS : IsSemiAlgebra S) :
    generatedAlgebra S =
      {C : Set X | ∃ n : ℕ, ∃ Cᵢ : Fin n -> Set X,
        PairwiseDisjoint Cᵢ ∧ (∀ i, Cᵢ i ∈ S) ∧ C = ⋃ i, Cᵢ i} := by
  exact (generatedAlgebra_eq_supClosure_of_isSemiAlgebra S hS).trans
    (supClosure_eq_finiteDisjointUnions S hS)

/--
Source: Proposition 0.1.15, Chapter 0, Section 1.
Approximation lemma for a probability space generated by an algebra.
-/
theorem approximationLemma {X : Type u} (𝓧 : SetFamily X) (μ : Set X -> ENNReal)
    (A : SetFamily X) (hμ : IsProbabilityMeasureOn 𝓧 μ) (hA : IsAlgebra A)
    (hA_sub : A ⊆ 𝓧) (hgen : generatedSigmaAlgebra A = 𝓧) :
    almostEverywhereApproximation 𝓧 μ A := by
  let mX : MeasurableSpace X := {
    MeasurableSet' := 𝓧
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
    change E ∈ 𝓧 ↔ E ∈ generatedSigmaAlgebra A
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
  have heq : Chapter00.symmDiff C B = _root_.symmDiff B C := by
    change (C \ B) ∪ (B \ C) = (B \ C) ∪ (C \ B)
    exact Set.union_comm _ _
  have hcustommeas : MeasurableSet (Chapter00.symmDiff C B) := by
    rw [heq]
    exact hBmeas.symmDiff hCmeas
  calc
    μ (Chapter00.symmDiff C B) = μ' (Chapter00.symmDiff C B) :=
      (hμ'_apply hcustommeas).symm
    _ = μ' (_root_.symmDiff B C) := congrArg μ' heq
    _ < ENNReal.ofReal ε := hdist

/--
Source: Proposition 0.1.17, Chapter 0, Section 1.
If a probability sigma-algebra is countably generated, then there is a
countable family which approximates every measurable set in measure.

The same source record also contains the definitions of completion, restriction
to a positive-measure set, finite product measure, two-sided countable product
measure, Bernoulli product measure, and cylinder sets.  Those are explanatory
material in this translation pass and are not encoded as independent theorems.
-/
theorem countablyGeneratedProbabilitySpaceHasCountableMetricApproximation
    {X : Type u} (Xsets : SetFamily X) (μ : Set X -> ENNReal)
    (hμ : IsProbabilityMeasureOn Xsets μ) (hcg : CountablyGeneratedFamily Xsets) :
    ∃ A : ℕ -> Set X, (∀ i, A i ∈ Xsets) ∧
      ∀ ε : ℝ, 0 < ε -> ∀ B ∈ Xsets,
        ∃ i : ℕ, μ (symmDiff (A i) B) < ENNReal.ofReal ε := by
  obtain ⟨G, hG⟩ := hcg
  let Alg : SetFamily X := MeasureTheory.generateSetAlgebra (Set.range G)
  have hAlg_math : MeasureTheory.IsSetAlgebra Alg := by
    exact MeasureTheory.isSetAlgebra_generateSetAlgebra
  have hAlg : IsAlgebra Alg := by
    refine ⟨hAlg_math.empty_mem, ?_, hAlg_math.compl_mem⟩
    intro E hE F hF
    have h := hAlg_math.compl_mem
      (hAlg_math.union_mem (hAlg_math.compl_mem hE) hF)
    simpa [Set.diff_eq] using h
  have hAlg_meas : Alg ⊆ generatedSigmaAlgebra (Set.range G) := by
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
  have hgenAlg : generatedSigmaAlgebra Alg = Xsets := by
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
  have happ := approximationLemma Xsets μ Alg hμ hAlg hAlg_sub hgenAlg
  refine ⟨fun n => (enum n).1, (fun n => hAlg_sub (enum n).2), ?_⟩
  intro ε hε B hB
  obtain ⟨C, hCAlg, hdist⟩ := happ ε hε B hB
  obtain ⟨i, hi⟩ := henum (⟨C, hCAlg⟩ : Alg)
  refine ⟨i, ?_⟩
  simpa [hi] using hdist

/--
Source: Proposition 0.1.21, Chapter 0, Section 1.
Pointwise infimum, supremum, liminf, and limsup of a sequence of measurable
extended-real-valued functions are measurable.

The source record also defines almost-everywhere truth of a predicate; that
definition is preserved here as documentation rather than encoded as a theorem.
-/
theorem measurablePointwiseInfSupLiminfLimsup {X : Type u} (𝓧 : SetFamily X)
    (f : ℕ -> X -> ExtendedReal)
    (h𝓧 : IsSigmaAlgebraFamily 𝓧)
    (hf : ∀ n : ℕ, MeasurableExtendedRealFunction 𝓧 (f n)) :
    MeasurableExtendedRealFunction 𝓧 (fun x => ⨅ n : ℕ, f n x) ∧
      MeasurableExtendedRealFunction 𝓧 (fun x => ⨆ n : ℕ, f n x) ∧
      MeasurableExtendedRealFunction 𝓧 (fun x => ⨆ n : ℕ, ⨅ m : ℕ, f (n + m) x) ∧
      MeasurableExtendedRealFunction 𝓧 (fun x => ⨅ n : ℕ, ⨆ m : ℕ, f (n + m) x) := by
  let m : MeasurableSpace X := {
    MeasurableSet' := 𝓧
    measurableSet_empty := by
      have := h𝓧.2.1 Set.univ h𝓧.1
      simpa using this
    measurableSet_compl := h𝓧.2.1
    measurableSet_iUnion := h𝓧.2.2 }
  letI : MeasurableSpace X := m
  have measurable_of_levels (g : X → ExtendedReal)
      (hg : ∀ c : ℝ, MeasurableSet {x : X | (c : ExtendedReal) < g x}) :
      Measurable g := by
    have hbot : MeasurableSet {x : X | (⊥ : ExtendedReal) < g x} := by
      have heq : {x : X | (⊥ : ExtendedReal) < g x} =
          ⋃ n : ℕ, {x : X | ((-(n : ℝ) : ℝ) : ExtendedReal) < g x} := by
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

/--
Source: Proposition 0.1.31, Chapter 0, Section 1.
On a probability space, `L^q` is included in `L^p` whenever `1 ≤ p < q ≤ ∞`.
-/
theorem probabilityLpInclusion {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (p q : ENNReal) :
    IsLpInclusionStatement μ p q := by
  intro hpq f hf
  exact hf.mono_exponent hpq.2.le

/--
Source: Proposition 0.1.33, Chapter 0, Section 1.
For a countably generated probability space, `L^p` is a separable Banach space
for `1 ≤ p < ∞`; in particular `L^2` is a separable Hilbert space with the
usual integral inner product.
-/
theorem countablyGeneratedProbabilitySpaceSeparableLp {X : Type u}
    [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] :
    IsSeparableBanachLpStatement μ := by
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

/--
Source: Theorem 0.1.4, Chapter 0, Section 1.
Jordan decomposition theorem for finite signed measures.
-/
theorem jordanDecompositionTheorem {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.SignedMeasure X) :
    ∃! p : MeasureTheory.Measure X × MeasureTheory.Measure X,
      p.1 Set.univ < ⊤ ∧ p.2 Set.univ < ⊤ ∧
        MeasureTheory.Measure.MutuallySingular p.1 p.2 ∧
        ∀ A : Set X, MeasurableSet A ->
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

/--
Source: Theorem 0.1.9, Chapter 0, Section 1.
A finitely additive measure on a semialgebra has a unique extension to the
generated algebra; countable additivity is preserved.
-/
private noncomputable def addContentOfFinitelyAdditive {X : Type u}
    (A : SetFamily X) (μ : Set X → ENNReal)
    (hμ : IsFinitelyAdditiveOn A μ) :
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
  have hBdis : PairwiseDisjoint B := by
    intro i j hij
    exact hIdis (e.symm i).2 (e.symm j).2 (by
      intro heq
      apply hij
      exact e.symm.injective (Subtype.ext heq))
  have hUnion : (⋃ i, B i) = ⋃₀ (I : Set (Set X)) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_sUnion, Finset.mem_coe]
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
    _ = ∑ U ∈ I, μ U := by
      change (∑ U ∈ I.attach, μ U.1) = ∑ U ∈ I, μ U
      exact Finset.sum_attach I μ

private theorem countablyAdditiveOn_countable {X : Type u} {ι : Type*}
    [Countable ι] (S : SetFamily X) (μ : Set X → ENNReal)
    (hEmpty : ∅ ∈ S) (hμ : IsCountablyAdditiveOn S μ) (A : ι → Set X)
    (hA : ∀ i, A i ∈ S) (hdis : Pairwise (Function.onFun Disjoint A))
    (hU : (⋃ i, A i) ∈ S) :
    μ (⋃ i, A i) = ∑' i, μ (A i) := by
  letI := Encodable.ofCountable ι
  let B : ℕ → Set X := fun n => ⋃ i ∈ Encodable.decode₂ ι n, A i
  have hB : ∀ n, B n ∈ S := by
    intro n
    exact Encodable.iUnion_decode₂_cases (C := fun E => E ∈ S) (f := A)
      hEmpty hA (n := n)
  have hBdis : Pairwise (Function.onFun Disjoint B) := by
    exact Encodable.iUnion_decode₂_disjoint_on hdis
  have hBU : (⋃ n, B n) = ⋃ i, A i := by
    exact Encodable.iUnion_decode₂ A
  calc
    μ (⋃ i, A i) = μ (⋃ n, B n) := congrArg μ hBU.symm
    _ = ∑' n, μ (B n) := hμ.2 B hB hBdis (hBU.symm ▸ hU)
    _ = ∑' i, μ (A i) := tsum_iUnion_decode₂ μ hμ.1.1 A

private theorem supClosure_countablyAdditive {X : Type u}
    (S : SetFamily X) (m : MeasureTheory.AddContent ENNReal S)
    (hS : MeasureTheory.IsSetSemiring S)
    (hm : IsCountablyAdditiveOn S m) :
    IsCountablyAdditiveOn (supClosure S) (m.supClosure hS) := by
  let mc := m.supClosure hS
  have hfa : IsFinitelyAdditiveOn (supClosure S) mc := by
    refine ⟨mc.empty', ?_⟩
    intro n F hF hdis hU
    exact MeasureTheory.addContent_iUnion hF hdis hU
  refine ⟨hfa, ?_⟩
  intro A hA hdis hU
  choose P hPS using fun n => hS.mem_supClosure_iff.mp (hA n)
  obtain ⟨Q, hQS⟩ := hS.mem_supClosure_iff.mp hU
  have hPunion (n : ℕ) : (⋃ B ∈ (P n).parts, B) = A n := by
    simpa only [Finset.sup_set_eq_biUnion] using (P n).sup_parts
  have hQunion : (⋃ q ∈ Q.parts, q) = ⋃ n, A n := by
    simpa only [Finset.sup_set_eq_biUnion] using Q.sup_parts
  have hqsum (q : Set X) (hq : q ∈ Q.parts) :
      m q = ∑' i : Σ n : ℕ, {B // B ∈ (P n).parts}, m (q ∩ i.2.1) := by
    let C : (Σ n : ℕ, {B // B ∈ (P n).parts}) → Set X :=
      fun i => q ∩ i.2.1
    have hunion : (⋃ i, C i) = q := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hxq, _⟩ := Set.mem_iUnion.mp hx
        exact hxq
      · intro hxq
        have hxU : x ∈ ⋃ n, A n := Q.le hq hxq
        obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxU
        have hxparts : x ∈ ⋃ B ∈ (P n).parts, B := by
          rw [hPunion n]
          exact hxn
        obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.mp hxparts
        exact Set.mem_iUnion.2 ⟨⟨n, B, hB⟩, hxq, hxB⟩
    have hCmem : ∀ i, C i ∈ S := by
      rintro ⟨n, B, hB⟩
      exact hS.inter_mem q (hQS hq) B (hPS n hB)
    have hCdis : Pairwise (Function.onFun Disjoint C) := by
      rintro ⟨n, B, hB⟩ ⟨n', B', hB'⟩ hij
      apply Set.disjoint_left.2
      rintro x ⟨_hxq, hxB⟩ ⟨_hxq', hxB'⟩
      by_cases hnn : n = n'
      · subst n'
        have hBB : (B : Set X) ≠ B' := by
          intro heq
          subst B'
          apply hij
          rfl
        exact Set.disjoint_left.1 ((P n).disjoint hB hB' hBB) hxB hxB'
      · exact Set.disjoint_left.1 (hdis n n' hnn)
          ((P n).le hB hxB) ((P n').le hB' hxB')
    have hadd := countablyAdditiveOn_countable S m hS.empty_mem hm
      C hCmem hCdis (hunion.symm ▸ hQS hq)
    rw [hunion] at hadd
    exact hadd
  have hBsum (n : ℕ) (B : Set X) (hB : B ∈ (P n).parts) :
      m B = ∑ q ∈ Q.parts, m (q ∩ B) := by
    have hunion : (⋃ q ∈ Q.parts, q ∩ B) = B := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨q, ⟨_hq, _hxq, hxB⟩⟩
        exact hxB
      · intro hxB
        have hxU : x ∈ ⋃ n, A n := Set.mem_iUnion.2 ⟨n, (P n).le hB hxB⟩
        have hxQ : x ∈ ⋃ q ∈ Q.parts, q := hQunion.symm ▸ hxU
        obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hxQ
        exact ⟨q, hq, hxq, hxB⟩
    nth_rewrite 1 [← hunion]
    apply MeasureTheory.addContent_biUnion
    · intro q hq
      exact hS.inter_mem q (hQS hq) B (hPS n hB)
    · exact Q.disjoint.mono fun _ => by simp
    · rw [hunion]
      exact hPS n hB
  calc
    mc (⋃ n, A n) = ∑ q ∈ Q.parts, m q :=
      MeasureTheory.AddContent.supClosure_apply_finpartition hS m hQS
    _ = ∑ q ∈ Q.parts,
          ∑' i : Σ n : ℕ, {B // B ∈ (P n).parts}, m (q ∩ i.2.1) := by
      apply Finset.sum_congr rfl
      exact fun q hq => hqsum q hq
    _ = ∑' n, ∑ B ∈ (P n).parts, m B := by
      calc
        (∑ q ∈ Q.parts,
            ∑' i : Σ n : ℕ, {B // B ∈ (P n).parts}, m (q ∩ i.2.1)) =
            ∑' i : Σ n : ℕ, {B // B ∈ (P n).parts},
              ∑ q ∈ Q.parts, m (q ∩ i.2.1) := by
          exact (Summable.tsum_finsetSum
            (f := fun q (i : Σ n : ℕ, {B // B ∈ (P n).parts}) =>
              m (q ∩ i.2.1))
            (s := Q.parts) (fun _ _ => ENNReal.summable)).symm
        _ = ∑' i : Σ n : ℕ, {B // B ∈ (P n).parts}, m i.2.1 := by
          apply tsum_congr
          rintro ⟨n, B, hB⟩
          exact (hBsum n B hB).symm
        _ = ∑' n, ∑' B : {B // B ∈ (P n).parts}, m B.1 :=
          ENNReal.tsum_sigma' _
        _ = ∑' n, ∑ B ∈ (P n).parts, m B := by
          apply tsum_congr
          intro n
          exact Finset.tsum_subtype (P n).parts m
    _ = ∑' n, mc (A n) := by
      apply tsum_congr
      intro n
      exact (MeasureTheory.AddContent.supClosure_apply_finpartition hS m (hPS n)).symm

theorem semialgebraMeasureExtendsUniquelyToGeneratedAlgebra {X : Type u}
    (S : SetFamily X) (μ : Set X -> ENNReal) :
    IsSemiAlgebra S -> IsFinitelyAdditiveOn S μ -> (∀ B ∈ S, μ B < ⊤) ->
      ∃ ν : Set X -> ENNReal,
        IsMeasureExtension S (generatedAlgebra S) μ ν ∧
          IsFinitelyAdditiveOn (generatedAlgebra S) ν ∧
          (IsCountablyAdditiveOn S μ -> IsCountablyAdditiveOn (generatedAlgebra S) ν) ∧
          ∀ ν' : Set X -> ENNReal,
            IsMeasureExtension S (generatedAlgebra S) μ ν' ->
            IsFinitelyAdditiveOn (generatedAlgebra S) ν' ->
            EqualOnFamily (generatedAlgebra S) ν' ν := by
  intro hS hμ hfinite
  let m : MeasureTheory.AddContent ENNReal S :=
    addContentOfFinitelyAdditive S μ hμ
  let νc : MeasureTheory.AddContent ENNReal (supClosure S) := m.supClosure hS.1
  have hEq : generatedAlgebra S = supClosure S :=
    generatedAlgebra_eq_supClosure_of_isSemiAlgebra S hS
  have hRing : MeasureTheory.IsSetRing (supClosure S) := hS.1.isSetRing_supClosure
  have hνext : IsMeasureExtension S (generatedAlgebra S) μ νc := by
    refine ⟨?_, ?_⟩
    · rw [hEq]
      exact subset_supClosure
    · intro E hE
      exact MeasureTheory.AddContent.supClosure_apply_of_mem hS.1 m hE
  have hνfa : IsFinitelyAdditiveOn (generatedAlgebra S) νc := by
    refine ⟨νc.empty', ?_⟩
    intro n F hF hdis hU
    apply MeasureTheory.addContent_iUnion
    · intro i
      rw [← hEq]
      exact hF i
    · exact hdis
    · rw [← hEq]
      exact hU
  refine ⟨νc, hνext, hνfa, ?_, ?_⟩
  · intro hμca
    rw [hEq]
    exact supClosure_countablyAdditive S m hS.1 hμca
  · intro ν' hν'ext hν'fa E hE
    rw [algebraGeneratedBySemiAlgebraFiniteDisjointUnions S hS] at hE
    obtain ⟨n, B, hBdis, hB, rfl⟩ := hE
    have hU : (⋃ i, B i) ∈ generatedAlgebra S := by
      rw [algebraGeneratedBySemiAlgebraFiniteDisjointUnions S hS]
      exact ⟨n, B, hBdis, hB, rfl⟩
    calc
      ν' (⋃ i, B i) = ∑ i, ν' (B i) := hν'fa.2 n B
        (fun i => hν'ext.1 (hB i)) hBdis hU
      _ = ∑ i, μ (B i) := by
        congr 1
        ext i
        exact hν'ext.2 (B i) (hB i)
      _ = ∑ i, νc (B i) := by
        congr 1
        ext i
        exact (hνext.2 (B i) (hB i)).symm
      _ = νc (⋃ i, B i) := (hνfa.2 n B
        (fun i => hνext.1 (hB i)) hBdis hU).symm

private theorem measureCountablyAdditiveOnGeneratedSigma {X : Type u}
    (A : SetFamily X)
    (ν : @MeasureTheory.Measure X (MeasurableSpace.generateFrom A)) :
    IsCountablyAdditiveOn (generatedSigmaAlgebra A) ν := by
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

private theorem generatedSigmaAlgebra_isSigmaAlgebra {X : Type u}
    (A : SetFamily X) : IsSigmaAlgebraFamily (generatedSigmaAlgebra A) := by
  letI : MeasurableSpace X := MeasurableSpace.generateFrom A
  refine ⟨?_, ?_, ?_⟩
  · change MeasurableSet (Set.univ : Set X)
    exact MeasurableSet.univ
  · intro E hE
    change MeasurableSet E at hE
    change MeasurableSet Eᶜ
    exact hE.compl
  · intro F hF
    change MeasurableSet (⋃ n, F n)
    have hF' : ∀ n, MeasurableSet (F n) := by
      intro n
      change MeasurableSet (F n)
      exact hF n
    exact MeasurableSet.iUnion hF'

/--
Source: Theorem 0.1.10, Chapter 0, Section 1.
A countably additive measure on an algebra extends uniquely to the generated
sigma-algebra.
-/
theorem algebraMeasureExtendsUniquelyToGeneratedSigmaAlgebra {X : Type u}
    (A : SetFamily X) (μ : Set X -> ENNReal) :
    IsAlgebra A -> IsCountablyAdditiveOn A μ -> μ Set.univ < ⊤ ->
      ∃ ν : Set X -> ENNReal,
        IsMeasureExtension A (generatedSigmaAlgebra A) μ ν ∧
          IsCountablyAdditiveOn (generatedSigmaAlgebra A) ν ∧
          ∀ ν' : Set X -> ENNReal,
            IsMeasureExtension A (generatedSigmaAlgebra A) μ ν' ->
            IsCountablyAdditiveOn (generatedSigmaAlgebra A) ν' ->
            EqualOnFamily (generatedSigmaAlgebra A) ν' ν := by
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
  let content : MeasureTheory.AddContent ENNReal A :=
    addContentOfFinitelyAdditive A μ hμ.1
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
    measureCountablyAdditiveOnGeneratedSigma A νm, ?_⟩
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

/--
Source: Theorem 0.1.11, Chapter 0, Section 1.
Carathéodory extension theorem from a semialgebra to the generated
sigma-algebra.
-/
theorem caratheodoryExtensionTheorem {X : Type u}
    (S : SetFamily X) (μ : Set X -> ENNReal) :
    IsSemiAlgebra S -> IsCountablyAdditiveOn S μ ->
      ∃ ν : Set X -> ENNReal,
        IsMeasureExtension S (generatedSigmaAlgebra S) μ ν ∧
          IsCountablyAdditiveOn (generatedSigmaAlgebra S) ν ∧
          ((∃ B : ℕ -> Set X, (∀ n, B n ∈ S ∧ μ (B n) < ⊤) ∧
              (⋃ n, B n) = Set.univ) ->
            ∀ ν' : Set X -> ENNReal,
              IsMeasureExtension S (generatedSigmaAlgebra S) μ ν' ->
              IsCountablyAdditiveOn (generatedSigmaAlgebra S) ν' ->
              EqualOnFamily (generatedSigmaAlgebra S) ν' ν) := by
  intro hS hμ
  let m : MeasureTheory.AddContent ENNReal S :=
    addContentOfFinitelyAdditive S μ hμ.1
  let mc : MeasureTheory.AddContent ENNReal (supClosure S) := m.supClosure hS.1
  have hmc : IsCountablyAdditiveOn (supClosure S) mc :=
    supClosure_countablyAdditive S m hS.1 hμ
  have hRing : MeasureTheory.IsSetRing (supClosure S) := hS.1.isSetRing_supClosure
  have hsigma : mc.IsSigmaSubadditive :=
    MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum hRing (by
      intro F hF hFU hdis
      exact hmc.2 F hF (by simpa [Function.onFun] using hdis) hFU)
  letI : MeasurableSpace X := MeasurableSpace.generateFrom S
  have hgen : (MeasurableSpace.generateFrom S) =
      MeasurableSpace.generateFrom (supClosure S) := by
    apply le_antisymm
    · exact MeasurableSpace.generateFrom_mono subset_supClosure
    · apply MeasurableSpace.generateFrom_le
      intro E hE
      exact measurableSet_generateFrom_of_mem_supClosure hE
  let νm : MeasureTheory.Measure X :=
    mc.measure hRing.isSetSemiring hgen.le hsigma
  have hνeq {E : Set X} (hE : E ∈ supClosure S) : νm E = mc E := by
    exact MeasureTheory.AddContent.measure_eq mc hRing.isSetSemiring hgen hsigma hE
  have hνS {E : Set X} (hE : E ∈ S) : νm E = μ E := by
    calc
      νm E = mc E := hνeq (subset_supClosure hE)
      _ = m E := MeasureTheory.AddContent.supClosure_apply_of_mem hS.1 m hE
      _ = μ E := rfl
  refine ⟨fun E => νm E, ⟨?_, fun E hE => hνS hE⟩,
    measureCountablyAdditiveOnGeneratedSigma S νm, ?_⟩
  · intro E hE
    exact MeasurableSpace.measurableSet_generateFrom hE
  · rintro ⟨B, hB, hcover⟩ ν' hν'ext hν'ca
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
        (S := S) (T := Set.range B) rfl (Set.countable_range B) hS.1.isPiSystem
      · simpa [Set.sUnion_range] using hcover
      · rintro T ⟨n, rfl⟩
        rw [hνS (hB n).1]
        exact ne_of_lt (hB n).2
      · rintro T ⟨n, rfl⟩ E hE
        have hinter : E ∩ B n ∈ S :=
          hS.1.inter_mem E hE (B n) (hB n).1
        rw [hνS hinter, hνm'_apply
          (MeasurableSpace.measurableSet_generateFrom hinter), hν'ext.2 _ hinter]
      · rintro T ⟨n, rfl⟩
        rw [hνS (hB n).1, hνm'_apply
          (MeasurableSpace.measurableSet_generateFrom (hB n).1),
          hν'ext.2 _ (hB n).1]
    intro E hE
    rw [← hνm'_apply hE, ← heq]

/--
Source: Corollary 0.1.12, Chapter 0, Section 1.
Probability version of the extension theorem for a semialgebra partitioning the
whole space.
-/
theorem probabilityMeasureExtensionFromSemialgebra {X : Type u}
    (S : SetFamily X) (μ : Set X -> ENNReal) :
    IsSemiAlgebra S -> IsCountablyAdditiveOn S μ ->
      (∃ n : ℕ, ∃ B : Fin n -> Set X,
        PairwiseDisjoint B ∧ (∀ i, B i ∈ S) ∧ (⋃ i, B i) = Set.univ ∧
          (Finset.univ.sum fun i : Fin n => μ (B i)) = 1) ->
        ∃ ν : Set X -> ENNReal,
          IsProbabilityMeasureOn (generatedSigmaAlgebra S) ν ∧
            IsMeasureExtension S (generatedSigmaAlgebra S) μ ν ∧
            ∀ ν' : Set X -> ENNReal,
              IsProbabilityMeasureOn (generatedSigmaAlgebra S) ν' ->
              IsMeasureExtension S (generatedSigmaAlgebra S) μ ν' ->
              EqualOnFamily (generatedSigmaAlgebra S) ν' ν := by
  intro hS hμ hpart
  obtain ⟨n, B, hdisj, hB, hcover, hsum⟩ := hpart
  have hfinite_fin : ∀ i : Fin n, μ (B i) < ⊤ := by
    intro i
    have hle : μ (B i) ≤ ∑ j : Fin n, μ (B j) :=
      Finset.single_le_sum (fun j _hj => zero_le (μ (B j))) (Finset.mem_univ i)
    exact lt_of_le_of_lt (by simpa [hsum] using hle) ENNReal.one_lt_top
  let C : ℕ → Set X := fun m =>
    if hm : m < n then B ⟨m, hm⟩ else ∅
  have hCmem : ∀ m, C m ∈ S := by
    intro m
    by_cases hm : m < n
    · simp [C, hm, hB ⟨m, hm⟩]
    · simp [C, hm, hS.1.empty_mem]
  have hCfinite : ∀ m, μ (C m) < ⊤ := by
    intro m
    by_cases hm : m < n
    · simpa [C, hm] using hfinite_fin ⟨m, hm⟩
    · exact lt_top_iff_ne_top.mpr (by simp [C, hm, hμ.1.1])
  have hCcover : (⋃ m, C m) = Set.univ := by
    ext x
    constructor
    · intro _hx
      exact trivial
    · intro _hx
      have hx : x ∈ ⋃ i, B i := by simp [hcover]
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      refine Set.mem_iUnion.mpr ⟨(i : ℕ), ?_⟩
      simp [C, i.isLt, hxi]
  obtain ⟨ν, hνext, hνca, huniq⟩ :=
    caratheodoryExtensionTheorem S μ hS hμ
  have hprob_univ : ν Set.univ = 1 := by
    have hUmem : (⋃ i, B i) ∈ generatedSigmaAlgebra S := by
      rw [hcover]
      exact (generatedSigmaAlgebra_isSigmaAlgebra S).1
    have hνsum := hνca.1.2 n B (fun i => hνext.1 (hB i)) hdisj hUmem
    rw [hcover] at hνsum
    calc
      ν Set.univ = ∑ i : Fin n, ν (B i) := hνsum
      _ = ∑ i : Fin n, μ (B i) := by
        congr 1
        ext i
        exact hνext.2 (B i) (hB i)
      _ = 1 := hsum
  refine ⟨ν, ⟨⟨generatedSigmaAlgebra_isSigmaAlgebra S, hνca.1.1, ?_⟩,
    hprob_univ⟩, hνext, ?_⟩
  · intro F hF hdis
    exact hνca.2 F hF hdis ((generatedSigmaAlgebra_isSigmaAlgebra S).2.2 F hF)
  intro ν' hν'prob hν'ext
  letI : MeasurableSpace X := MeasurableSpace.generateFrom S
  let νm' : MeasureTheory.Measure X :=
    MeasureTheory.Measure.ofMeasurable
      (fun E _hE => ν' E)
      hν'prob.1.2.1
      (by
        intro F hF hdis
        exact hν'prob.1.2.2 F hF (by simpa [Function.onFun] using hdis))
  have hνm'_apply {E : Set X} (hE : MeasurableSet E) : νm' E = ν' E :=
    MeasureTheory.Measure.ofMeasurable_apply E hE
  have hνm'ext : IsMeasureExtension S (generatedSigmaAlgebra S) (fun E => μ E)
      (fun E => νm' E) := by
    refine ⟨?_, ?_⟩
    · intro E hE
      exact MeasurableSpace.measurableSet_generateFrom hE
    · intro E hE
      calc
        (fun E => νm' E) E = ν' E :=
          hνm'_apply (MeasurableSpace.measurableSet_generateFrom hE)
        _ = (fun E => μ E) E := hν'ext.2 E hE
  have heq := huniq ⟨C, (by
      refine ⟨?_, hCcover⟩
      intro m
      exact ⟨hCmem m, hCfinite m⟩)⟩ (fun E => νm' E) hνm'ext
      (measureCountablyAdditiveOnGeneratedSigma S νm')
  intro E hE
  rw [← hνm'_apply hE]
  exact heq E hE

private theorem isAlgebra_union_mem {X : Type u} {A : SetFamily X}
    (hA : IsAlgebra A) {E F : Set X} (hE : E ∈ A) (hF : F ∈ A) :
    E ∪ F ∈ A := by
  have hdiff := hA.2.1 Eᶜ (hA.2.2 E hE) F hF
  have hcomp := hA.2.2 (Eᶜ \ F) hdiff
  have heq : (Eᶜ \ F)ᶜ = E ∪ F := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_union]
    tauto
  rwa [heq] at hcomp

private theorem generatedMonotoneClass_mem_of_mem {X : Type u}
    {A : SetFamily X} {E : Set X} (hE : E ∈ A) :
    E ∈ generatedMonotoneClass A := by
  rw [generatedMonotoneClass]
  intro M hM
  exact hM.2 hE

private theorem generatedMonotoneClass_isMonotoneClass {X : Type u}
    (A : SetFamily X) : IsMonotoneClass (generatedMonotoneClass A) := by
  refine ⟨?_, ?_⟩
  · intro F hF hmono
    rw [generatedMonotoneClass]
    intro M hM
    exact hM.1.1 F (fun n => by
      have hFn := hF n
      rw [generatedMonotoneClass] at hFn
      exact hFn M hM) hmono
  · intro F hF hmono
    rw [generatedMonotoneClass]
    intro M hM
    exact hM.1.2 F (fun n => by
      have hFn := hF n
      rw [generatedMonotoneClass] at hFn
      exact hFn M hM) hmono

private theorem generatedMonotoneClass_compl_mem_of_isAlgebra {X : Type u}
    {A : SetFamily X} (hA : IsAlgebra A) {E : Set X}
    (hE : E ∈ generatedMonotoneClass A) :
    Eᶜ ∈ generatedMonotoneClass A := by
  let M : SetFamily X := generatedMonotoneClass A
  let D : SetFamily X := {F | Fᶜ ∈ M}
  have hMmono : IsMonotoneClass M := generatedMonotoneClass_isMonotoneClass A
  have hDmono : IsMonotoneClass D := by
    refine ⟨?_, ?_⟩
    · intro F hF hmono
      change (⋃ n, F n)ᶜ ∈ M
      have hEq : (⋃ n, F n)ᶜ = ⋂ n, (F n)ᶜ := by
        ext x
        simp
      rw [hEq]
      exact hMmono.2 (fun n => (F n)ᶜ) hF (by
        intro n x hx hx'
        exact hx (hmono n hx'))
    · intro F hF hmono
      change (⋂ n, F n)ᶜ ∈ M
      have hEq : (⋂ n, F n)ᶜ = ⋃ n, (F n)ᶜ := by
        ext x
        simp
      rw [hEq]
      exact hMmono.1 (fun n => (F n)ᶜ) hF (by
        intro n x hx hx'
        exact hx (hmono n hx'))
  have hDsub : A ⊆ D := by
    intro F hF
    change Fᶜ ∈ M
    exact generatedMonotoneClass_mem_of_mem (hA.2.2 F hF)
  have hED : E ∈ D := by
    have h := hE
    rw [generatedMonotoneClass] at h
    exact h D ⟨hDmono, hDsub⟩
  exact hED

private theorem generatedMonotoneClass_union_left_base_mem {X : Type u}
    {A : SetFamily X} (hA : IsAlgebra A) {E F : Set X}
    (hE : E ∈ A) (hF : F ∈ generatedMonotoneClass A) :
    E ∪ F ∈ generatedMonotoneClass A := by
  let M : SetFamily X := generatedMonotoneClass A
  let D : SetFamily X := {G | E ∪ G ∈ M}
  have hMmono : IsMonotoneClass M := generatedMonotoneClass_isMonotoneClass A
  have hDmono : IsMonotoneClass D := by
    refine ⟨?_, ?_⟩
    · intro G hG hmono
      change E ∪ (⋃ n, G n) ∈ M
      have hEq : E ∪ (⋃ n, G n) = ⋃ n, E ∪ G n := by
        ext x
        by_cases hxE : x ∈ E <;> simp [hxE]
      rw [hEq]
      exact hMmono.1 (fun n => E ∪ G n) hG (by
        intro n
        exact Set.union_subset_union_right E (hmono n))
    · intro G hG hmono
      change E ∪ (⋂ n, G n) ∈ M
      have hEq : E ∪ (⋂ n, G n) = ⋂ n, E ∪ G n := by
        ext x
        by_cases hxE : x ∈ E <;> simp [hxE]
      rw [hEq]
      exact hMmono.2 (fun n => E ∪ G n) hG (by
        intro n
        exact Set.union_subset_union_right E (hmono n))
  have hDsub : A ⊆ D := by
    intro G hG
    change E ∪ G ∈ M
    exact generatedMonotoneClass_mem_of_mem (isAlgebra_union_mem hA hE hG)
  have hFD : F ∈ D := by
    have h := hF
    rw [generatedMonotoneClass] at h
    exact h D ⟨hDmono, hDsub⟩
  exact hFD

private theorem generatedMonotoneClass_union_mem_of_isAlgebra {X : Type u}
    {A : SetFamily X} (hA : IsAlgebra A) {E F : Set X}
    (hE : E ∈ generatedMonotoneClass A) (hF : F ∈ generatedMonotoneClass A) :
    E ∪ F ∈ generatedMonotoneClass A := by
  let M : SetFamily X := generatedMonotoneClass A
  let D : SetFamily X := {G | ∀ H ∈ M, G ∪ H ∈ M}
  have hMmono : IsMonotoneClass M := generatedMonotoneClass_isMonotoneClass A
  have hDmono : IsMonotoneClass D := by
    refine ⟨?_, ?_⟩
    · intro G hG hmono H hH
      change (⋃ n, G n) ∪ H ∈ M
      have hEq : (⋃ n, G n) ∪ H = ⋃ n, G n ∪ H := by
        ext x
        by_cases hxH : x ∈ H <;> simp [hxH]
      rw [hEq]
      exact hMmono.1 (fun n => G n ∪ H) (fun n => hG n H hH) (by
        intro n
        exact Set.union_subset_union_left H (hmono n))
    · intro G hG hmono H hH
      change (⋂ n, G n) ∪ H ∈ M
      have hEq : (⋂ n, G n) ∪ H = ⋂ n, G n ∪ H := by
        ext x
        by_cases hxH : x ∈ H <;> simp [hxH]
      rw [hEq]
      exact hMmono.2 (fun n => G n ∪ H) (fun n => hG n H hH) (by
        intro n
        exact Set.union_subset_union_left H (hmono n))
  have hDsub : A ⊆ D := by
    intro G hG H hH
    exact generatedMonotoneClass_union_left_base_mem hA hG hH
  have hED : E ∈ D := by
    have h := hE
    rw [generatedMonotoneClass] at h
    exact h D ⟨hDmono, hDsub⟩
  exact hED F hF

private theorem generatedMonotoneClass_finset_biUnion_mem_of_isAlgebra
    {X : Type u} {A : SetFamily X} (hA : IsAlgebra A) {ι : Type*}
    (s : Finset ι) (F : ι → Set X)
    (hF : ∀ i ∈ s, F i ∈ generatedMonotoneClass A) :
    (⋃ i ∈ s, F i) ∈ generatedMonotoneClass A := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using generatedMonotoneClass_mem_of_mem (A := A) hA.1
  | @insert a s ha ih =>
      have ha_mem : F a ∈ generatedMonotoneClass A :=
        hF a (Finset.mem_insert_self a s)
      have hs_mem : (⋃ i ∈ s, F i) ∈ generatedMonotoneClass A :=
        ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      have h_union :=
        generatedMonotoneClass_union_mem_of_isAlgebra hA ha_mem hs_mem
      simpa [ha] using h_union

private theorem generatedMonotoneClass_iUnion_mem_of_isAlgebra {X : Type u}
    {A : SetFamily X} (hA : IsAlgebra A) (F : ℕ → Set X)
    (hF : ∀ n, F n ∈ generatedMonotoneClass A) :
    (⋃ n, F n) ∈ generatedMonotoneClass A := by
  let P : ℕ → Set X := fun n => ⋃ i ∈ Finset.range (n + 1), F i
  have hPmem : ∀ n, P n ∈ generatedMonotoneClass A := by
    intro n
    exact generatedMonotoneClass_finset_biUnion_mem_of_isAlgebra hA
      (Finset.range (n + 1)) F (fun i _hi => hF i)
  have hPmono : ∀ n, P n ⊆ P (n + 1) := by
    intro n x hx
    simp only [P, Set.mem_iUnion, Finset.mem_range] at hx ⊢
    rcases hx with ⟨i, hi, hxi⟩
    exact ⟨i, by omega, hxi⟩
  have hEq : (⋃ n, P n) = ⋃ n, F n := by
    ext x
    constructor
    · intro hx
      simp only [P, Set.mem_iUnion, Finset.mem_range] at hx
      rcases hx with ⟨n, i, _hi, hxi⟩
      exact Set.mem_iUnion.mpr ⟨i, hxi⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      simp only [P, Set.mem_iUnion, Finset.mem_range]
      exact ⟨i, by omega, hxi⟩
  rw [← hEq]
  exact (generatedMonotoneClass_isMonotoneClass A).1 P hPmem hPmono

/--
Source: Theorem 0.1.14, Chapter 0, Section 1.
The sigma-algebra generated by an algebra is the smallest monotone class
containing that algebra.
-/
theorem monotoneClassTheorem {X : Type u} (A : SetFamily X) :
    IsAlgebra A -> generatedSigmaAlgebra A = generatedMonotoneClass A := by
  intro hA
  apply Set.ext
  intro E
  constructor
  · intro hE
    let mM : MeasurableSpace X := {
      MeasurableSet' := generatedMonotoneClass A
      measurableSet_empty := generatedMonotoneClass_mem_of_mem (A := A) hA.1
      measurableSet_compl := fun _ hE =>
        generatedMonotoneClass_compl_mem_of_isAlgebra hA hE
      measurableSet_iUnion := fun F hF =>
        generatedMonotoneClass_iUnion_mem_of_isAlgebra hA F hF }
    have hle : MeasurableSpace.generateFrom A ≤ mM :=
      MeasurableSpace.generateFrom_le
        (fun F hF => generatedMonotoneClass_mem_of_mem (A := A) hF)
    exact hle E hE
  · intro hE
    have hmonoSigma : IsMonotoneClass (generatedSigmaAlgebra A) := by
      letI : MeasurableSpace X := MeasurableSpace.generateFrom A
      refine ⟨?_, ?_⟩
      · intro F hF _hmono
        change MeasurableSet (⋃ n, F n)
        exact MeasurableSet.iUnion (fun n => hF n)
      · intro F hF _hmono
        change MeasurableSet (⋂ n, F n)
        exact MeasurableSet.iInter (fun n => hF n)
    have hsubSigma : A ⊆ generatedSigmaAlgebra A := by
      intro F hF
      exact MeasurableSpace.measurableSet_generateFrom hF
    have h := hE
    rw [generatedMonotoneClass] at h
    exact h (generatedSigmaAlgebra A) ⟨hmonoSigma, hsubSigma⟩

/--
Source: Theorem 0.1.18, Chapter 0, Section 1.
Daniell-Kolmogorov theorem for consistent finite-dimensional distributions on
the two-sided full shift over a finite alphabet.
-/
theorem daniellKolmogorovTheorem
    (k : ℕ) (p : ℕ -> List (Fin k) -> ℝ) :
    HasDaniellKolmogorovMeasure k p := by
  exact Chapter00.daniellKolmogorovTheoremAux k p

/--
Source: Theorem 0.1.28, Chapter 0, Section 1.
Monotone convergence theorem.
-/
theorem monotoneConvergenceTheorem (P : BasicProbabilitySpaceData) :
    MonotoneConvergenceStatement P := by
  intro f hf hstep hbdd
  have hmono : ∀ᵐ x ∂P.μ, Monotone (fun n => f n x) := by
    have hs : ∀ᵐ x ∂P.μ, ∀ n, f n x ≤ f (n + 1) x :=
      MeasureTheory.ae_all_iff.mpr hstep
    filter_upwards [hs] with x hx
    exact monotone_nat_of_le_succ hx
  let q : ℕ → P.X → ENNReal := fun n x => ENNReal.ofReal (f n x - f 0 x)
  let Q : P.X → ENNReal := fun x => ⨆ n, q n x
  have hq_meas : ∀ n, AEMeasurable (q n) P.μ := by
    intro n
    exact ((hf n).1.sub (hf 0).1).aemeasurable.ennreal_ofReal
  have hq_mono : ∀ᵐ x ∂P.μ, Monotone (fun n => q n x) := by
    filter_upwards [hmono] with x hx n m hnm
    exact ENNReal.ofReal_le_ofReal (sub_le_sub_right (hx hnm) _)
  have hq_integral (n : ℕ) :
      ∫⁻ x, q n x ∂P.μ =
        ENNReal.ofReal ((∫ x, f n x ∂P.μ) - ∫ x, f 0 x ∂P.μ) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal,
      MeasureTheory.integral_sub (hf n) (hf 0)]
    · exact (hf n).sub (hf 0)
    · filter_upwards [hmono] with x hx
      exact sub_nonneg.mpr (hx (Nat.zero_le n))
  obtain ⟨M, hM⟩ := hbdd
  have hq_bdd (n : ℕ) :
      ∫⁻ x, q n x ∂P.μ ≤
        ENNReal.ofReal (M - ∫ x, f 0 x ∂P.μ) := by
    rw [hq_integral]
    exact ENNReal.ofReal_le_ofReal (sub_le_sub_right (hM ⟨n, rfl⟩) _)
  have hQ_meas : AEMeasurable Q P.μ := by
    exact AEMeasurable.iSup hq_meas
  have hQ_integral : ∫⁻ x, Q x ∂P.μ ≠ ⊤ := by
    have hle : ∫⁻ x, Q x ∂P.μ ≤
        ENNReal.ofReal (M - ∫ x, f 0 x ∂P.μ) := by
      rw [show (∫⁻ x, Q x ∂P.μ) = ⨆ n, ∫⁻ x, q n x ∂P.μ by
        exact MeasureTheory.lintegral_iSup' hq_meas hq_mono]
      exact iSup_le hq_bdd
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  have hQ_integrable :
      MeasureTheory.Integrable (fun x => (Q x).toReal) P.μ :=
    MeasureTheory.integrable_toReal_of_lintegral_ne_top hQ_meas hQ_integral
  let g : P.X → ℝ := fun x => (Q x).toReal + f 0 x
  have hg : MeasureTheory.Integrable g P.μ := hQ_integrable.add (hf 0)
  have hQ_finite : ∀ᵐ x ∂P.μ, Q x ≠ ⊤ :=
    MeasureTheory.ae_lt_top' hQ_meas hQ_integral |>.mono
      (fun _ hx => hx.ne)
  have htendsto : ∀ᵐ x ∂P.μ,
      Tendsto (fun n => f n x) atTop (nhds (g x)) := by
    filter_upwards [hmono, hQ_finite] with x hx hxQ
    have hq_tendsto : Tendsto (fun n => q n x) atTop (nhds (Q x)) := by
      exact tendsto_atTop_iSup (fun n m hnm =>
        ENNReal.ofReal_le_ofReal (sub_le_sub_right (hx hnm) _))
    have hq_real : Tendsto (fun n => (q n x).toReal) atTop (nhds (Q x).toReal) :=
      (ENNReal.continuousAt_toReal hxQ).tendsto.comp hq_tendsto
    have := hq_real.add_const (f 0 x)
    simpa [q, g, ENNReal.toReal_ofReal (sub_nonneg.mpr (hx (Nat.zero_le _)))] using this
  refine ⟨g, hg, htendsto, ?_⟩
  exact MeasureTheory.integral_tendsto_of_tendsto_of_monotone hf hg hmono htendsto

/--
Source: Theorem 0.1.29, Chapter 0, Section 1.
Fatou lemma.
-/
theorem fatouLemma (P : BasicProbabilitySpaceData) :
    FatouLemmaStatement P := by
  intro f lower hf hlower hbound hfinite
  let q : ℕ → P.X → ENNReal := fun n x => ENNReal.ofReal (f n x - lower x)
  let I : ℕ → ENNReal := fun n => ∫⁻ x, q n x ∂P.μ
  let L : EReal := (∫ x, lower x ∂P.μ : ℝ)
  let J : ℕ → EReal := fun n => (I n : EReal)
  have hq_meas : ∀ n, AEMeasurable (q n) P.μ := by
    intro n
    exact ((hf n).sub hlower.1).aemeasurable.ennreal_ofReal
  have hshift (n : ℕ) : lowerShiftedExtendedIntegral P (f n) lower = L + J n := by
    rfl
  have hlim_shift : Filter.liminf (fun n => lowerShiftedExtendedIntegral P (f n) lower) atTop =
      L + Filter.liminf J atTop := by
    rw [show (fun n => lowerShiftedExtendedIntegral P (f n) lower) =
        fun n => L + J n from funext hshift]
    have hL_bot : Filter.limsup (fun _ : ℕ => L) atTop ≠ ⊥ := by
      simp [L]
    have hL_top : Filter.limsup (fun _ : ℕ => L) atTop ≠ ⊤ := by
      simp [L]
    apply le_antisymm
    · simpa using EReal.liminf_add_le (f := atTop) (u := fun _ : ℕ => L) (v := J)
        (Or.inl hL_bot) (Or.inl hL_top)
    · simpa using EReal.le_liminf_add (u := fun _ : ℕ => L) (v := J) (f := atTop)
  have hJ_liminf_lt : Filter.liminf J atTop < ⊤ := by
    rw [hlim_shift] at hfinite
    by_contra h
    have htop : Filter.liminf J atTop = ⊤ := top_unique (not_lt.mp h)
    rw [htop, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] at hfinite
    exact (lt_irrefl ⊤ hfinite)
  have hmap : ((Filter.liminf I atTop : ENNReal) : EReal) = Filter.liminf J atTop := by
    have hmap0 := Monotone.map_liminf_of_continuousAt (R := ENNReal) (S := EReal)
      EReal.coe_ennreal_strictMono.monotone I
      continuous_coe_ennreal_ereal.continuousAt
      (Filter.isCoboundedUnder_ge_of_le atTop (fun _ => le_top))
      (by exact ⟨0, Eventually.of_forall (fun _ => bot_le)⟩)
    simpa [J, Function.comp_def] using hmap0
  have hI_liminf_ne : Filter.liminf I atTop ≠ ⊤ := by
    intro h
    have : Filter.liminf J atTop = ⊤ := by
      rw [← hmap, h]
      exact EReal.coe_ennreal_eq_top_iff.mpr rfl
    exact hJ_liminf_lt.ne this
  let Q : P.X → ENNReal := fun x => Filter.liminf (fun n => q n x) atTop
  have hQ_meas : AEMeasurable Q P.μ := by
    change AEMeasurable (fun x => Filter.liminf (fun n => q n x) atTop) P.μ
    simp only [Filter.liminf_eq_iSup_iInf_of_nat]
    exact AEMeasurable.iSup fun n => AEMeasurable.iInf fun i =>
      AEMeasurable.iInf fun _ : n ≤ i => hq_meas i
  have hQ_integral : (∫⁻ x, Q x ∂P.μ) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (MeasureTheory.lintegral_liminf_le' hq_meas)
      (lt_top_iff_ne_top.mpr hI_liminf_ne)
  have hQ_integrable : MeasureTheory.Integrable (fun x => (Q x).toReal) P.μ :=
    MeasureTheory.integrable_toReal_of_lintegral_ne_top hQ_meas hQ_integral
  have hQ_finite : ∀ᵐ x ∂P.μ, Q x ≠ ⊤ :=
    MeasureTheory.ae_lt_top' hQ_meas hQ_integral |>.mono fun _ hx => hx.ne
  have hbound_all : ∀ᵐ x ∂P.μ, ∀ n, lower x ≤ f n x :=
    MeasureTheory.ae_all_iff.mpr hbound
  have hpoint : ∀ᵐ x ∂P.μ,
      Filter.liminf (fun n => f n x) atTop = lower x + (Q x).toReal := by
    filter_upwards [hQ_finite, hbound_all] with x hQx hx
    let u : ℕ → NNReal := fun n => ⟨f n x - lower x, sub_nonneg.mpr (hx n)⟩
    have hq_u (n : ℕ) : q n x = (u n : ENNReal) := by
      exact ENNReal.ofReal_eq_coe_nnreal (sub_nonneg.mpr (hx n))
    have hQ_lt : Q x < ⊤ := lt_top_iff_ne_top.mpr hQx
    have hQ_add_lt : Q x < Q x + 1 := by
      exact ENNReal.lt_add_right hQx one_ne_zero
    have hfreq_q : ∃ᶠ n in atTop, q n x < Q x + 1 := by
      apply Filter.frequently_lt_of_liminf_lt
      · exact Filter.isCoboundedUnder_ge_of_le atTop (fun _ => le_top)
      · simpa [Q] using hQ_add_lt
    have hfreq_u : ∃ᶠ n in atTop, u n ≤ (Q x + 1).toNNReal := by
      exact hfreq_q.mono fun n hn => by
        rw [hq_u] at hn
        apply ENNReal.coe_le_coe.mp
        rw [ENNReal.coe_toNNReal (ENNReal.add_ne_top.mpr ⟨hQx, by norm_num⟩)]
        exact hn.le
    have hu_cobdd : atTop.IsCoboundedUnder (fun a b : NNReal => a ≥ b) u :=
      Filter.IsCoboundedUnder.of_frequently_le hfreq_u
    have hu_real_cobdd : atTop.IsCoboundedUnder (fun a b : ℝ => a ≥ b)
        (fun n => (u n : ℝ)) := by
      simpa using hu_cobdd
    have hu_real_bdd : atTop.IsBoundedUnder (fun a b : ℝ => a ≥ b)
        (fun n => (u n : ℝ)) := by
      refine ⟨0, ?_⟩
      simpa only [eventually_map] using
        (Eventually.of_forall fun n : ℕ => (u n).property)
    have hlim_u_enn : ((Filter.liminf u atTop : NNReal) : ENNReal) = Q x := by
      rw [ENNReal.ofNNReal_liminf hu_cobdd]
      simpa [Q, hq_u]
    have hlim_u_real : Filter.liminf (fun n => (u n : ℝ)) atTop = (Q x).toReal := by
      rw [NNReal.toReal_liminf]
      have := congrArg ENNReal.toReal hlim_u_enn
      simpa using this
    calc
      Filter.liminf (fun n => f n x) atTop =
          Filter.liminf (fun n => lower x + (u n : ℝ)) atTop := by
            congr 1
            funext n
            simp [u]
      _ = lower x + Filter.liminf (fun n => (u n : ℝ)) atTop :=
        liminf_const_add atTop (fun n => (u n : ℝ)) (lower x) hu_real_cobdd hu_real_bdd
      _ = lower x + (Q x).toReal := by rw [hlim_u_real]
  let g : P.X → ℝ := fun x => lower x + (Q x).toReal
  have hg : MeasureTheory.Integrable g P.μ := hlower.add hQ_integrable
  have hlim_integrable : MeasureTheory.Integrable
      (fun x => Filter.liminf (fun n => f n x) atTop) P.μ :=
    hg.congr (hpoint.mono fun _ h => h.symm)
  refine ⟨hlim_integrable, ?_⟩
  have hfatou : (∫⁻ x, Q x ∂P.μ) ≤ Filter.liminf I atTop := by
    exact MeasureTheory.lintegral_liminf_le' hq_meas
  have hQ_ae_lt : ∀ᵐ x ∂P.μ, Q x < ⊤ :=
    hQ_finite.mono fun _ hx => lt_top_iff_ne_top.mpr hx
  rw [MeasureTheory.integral_congr_ae hpoint,
    MeasureTheory.integral_add hlower hQ_integrable,
    MeasureTheory.integral_toReal hQ_meas hQ_ae_lt,
    hlim_shift, EReal.coe_add, EReal.coe_ennreal_toReal hQ_integral]
  change L + ((∫⁻ x, Q x ∂P.μ : ENNReal) : EReal) ≤
    L + Filter.liminf J atTop
  apply add_le_add le_rfl
  rw [← hmap]
  exact EReal.coe_ennreal_strictMono.monotone hfatou

/--
Source: Theorem 0.1.30, Chapter 0, Section 1.
Lebesgue dominated convergence theorem.
-/
theorem dominatedConvergenceTheorem (P : BasicProbabilitySpaceData) :
    DominatedConvergenceStatement P := by
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

/--
Source: Theorem 0.1.32, Chapter 0, Section 1.
Norm convergence in `L^p` has an almost everywhere convergent subsequence.
-/
theorem lpNormConvergenceHasAeConvergentSubsequence (P : BasicProbabilitySpaceData) :
    NormConvergentLpSequenceHasAeSubsequence P := by
  intro p hp f limit hf hlimit htendsto
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hmeasure := MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
    hp0 (fun n => (hf n).1) hlimit.1 htendsto
  exact hmeasure.exists_seq_tendsto_ae

/--
Source: Definition 0.1.1, Chapter 0, Section 1.
A sigma-algebra on a nonempty set is a family containing the whole space,
closed under complements, and closed under countable unions.
-/
def sigmaAlgebraDefinition {X : Type u} (𝓧 : SetFamily X) : Prop :=
  IsSigmaAlgebraFamily 𝓧

/--
Source: Definition 0.1.2, Chapter 0, Section 1.
The Borel sigma-algebra is the smallest sigma-algebra containing the open
subsets, and a measurable space is a set equipped with a sigma-algebra.
-/
def borelSigmaAlgebraAndMeasurableSpaceDefinition (X : Type u) [TopologicalSpace X]
    (𝓧 : SetFamily X) : Prop × Prop :=
  (𝓧 = {A : Set X | @MeasurableSet X (borel X) A},
    IsSigmaAlgebraFamily 𝓧)

/--
Source: Definition 0.1.3, Chapter 0, Section 1.
A measure is a countably additive map on a measurable space, and a probability
space is a measurable space with total mass one.
-/
def measureAndProbabilitySpaceDefinition {X : Type u}
    (𝓧 : SetFamily X) (μ : Set X -> ENNReal) : Prop × Prop :=
  (IsMeasureOn 𝓧 μ,
    IsMeasureOn 𝓧 μ ∧ μ Set.univ = 1)

/-- Source: Definition 0.1.3. A finite measure has finite total mass. -/
def finiteMeasureDefinition {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) : Prop :=
  μ Set.univ < ⊤

/-- Source: Definition 0.1.3. A probability measure has total mass one. -/
def probabilityMeasureDefinition {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) : Prop :=
  MeasureTheory.IsProbabilityMeasure μ

/-- Source: Definition 0.1.3. A measure is sigma-finite when the space has a countable
cover by finite-measure measurable sets. -/
def sigmaFiniteMeasureDefinition {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) : Prop :=
  ∃ A : ℕ -> Set X, (∀ n, MeasurableSet (A n)) ∧
    (⋃ n, A n) = Set.univ ∧ ∀ n, μ (A n) < ⊤

/--
Source: Example 0.1.5, Chapter 0, Section 1.
Basic examples of probability spaces, including the trivial probability space.
-/
theorem finiteUniformProbabilityExample (n : ℕ) (hn : 0 < n) :
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

/-- Source: Example 0.1.5(3). Counting measure counts finite sets. -/
theorem countingMeasureExample {X : Type u} [MeasurableSpace X]
    [MeasurableSingletonClass X] (A : Set X) (hA : A.Finite) :
    MeasureTheory.Measure.count A = A.ncard := by
  rw [MeasureTheory.Measure.count_apply_finite A hA]
  norm_cast
  exact (Set.ncard_eq_toFinset_card A hA).symm

/-- Source: Example 0.1.5(4). The Dirac measure at a point is a probability measure. -/
theorem diracProbabilityMeasureExample {X : Type u} [MeasurableSpace X]
    (x : X) [MeasurableSingletonClass X] :
    MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.dirac x) := by
  infer_instance

/-- Source: Example 0.1.5(1). The one-point trivial probability space. -/
theorem trivialProbabilitySpaceExample :
    MeasureTheory.IsProbabilityMeasure
      (@MeasureTheory.Measure.dirac PUnit ⊤ PUnit.unit) := by
  infer_instance

/-- Source: Example 0.1.5(5). Lebesgue measure of the unit interval is one. -/
theorem unitIntervalLebesgueProbabilityExample :
    ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
        (Set.Icc (0 : ℝ) 1)) Set.univ = 1 ∧
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))
        (Set.Icc 0 1) = 1 := by
  constructor
  · rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num
  · rw [MeasureTheory.Measure.restrict_apply (measurableSet_Icc)]
    simp only [Set.inter_self, Real.volume_Icc]
    norm_num

/-- Source: Example 0.1.5(6). The circle/one-torus has normalized Haar measure. -/
theorem oneTorusLebesgueProbabilityExample [MeasurableSpace Circle]
    [BorelSpace Circle] :
    ∃ m : MeasureTheory.Measure Circle,
      MeasureTheory.IsProbabilityMeasure m ∧ m.IsHaarMeasure := by
  let K : TopologicalSpace.PositiveCompacts Circle :=
    ⟨⟨Set.univ, isCompact_univ⟩, 1, by simp⟩
  let m : MeasureTheory.Measure Circle := MeasureTheory.Measure.haarMeasure K
  refine ⟨m, ?_, ?_⟩
  · apply MeasureTheory.IsProbabilityMeasure.mk
    simpa [m] using (MeasureTheory.Measure.haarMeasure_self (K₀ := K))
  · infer_instance

/--
Source: Definition 0.1.6, Chapter 0, Section 1.
A semialgebra is closed under finite intersections, contains the empty set, and
has complements decomposable into finite disjoint unions from the same family.
-/
def semiAlgebraDefinition {X : Type u} (S : SetFamily X) : Prop :=
  IsSemiAlgebra S

/--
Source: Definition 0.1.7, Chapter 0, Section 1.
An algebra of sets contains the empty set and is closed under finite unions and
relative complements.
-/
def algebraOfSetsDefinition {X : Type u} (A : SetFamily X) : Prop :=
  IsAlgebra A

/--
Source: Definition 0.1.13, Chapter 0, Section 1.
A monotone class is closed under increasing countable unions and decreasing
countable intersections.
-/
def monotoneClassDefinition {X : Type u} (M : SetFamily X) : Prop :=
  IsMonotoneClass M

/--
Source: Definition 0.1.16, Chapter 0, Section 1.
A sigma-algebra, measurable space, or probability space is countably generated
when its sigma-algebra is generated by a countable family.
-/
def countablyGeneratedProbabilitySpaceDefinition {X : Type u}
    (𝓧 : SetFamily X) : Prop :=
  CountablyGeneratedFamily 𝓧

/-- Source: discussion following Proposition 0.1.17. Completion by null sets. -/
def completedSigmaAlgebraFamily {X : Type u} (Xsets : SetFamily X)
    (μ : Set X -> ENNReal) : SetFamily X :=
  {E : Set X | ∃ B ∈ Xsets, ∃ N F : Set X,
    F ∈ Xsets ∧ μ F = 0 ∧ N ⊆ F ∧ E = symmDiff B N}

/-- Source: discussion following Proposition 0.1.17. Completeness of a probability space. -/
def completeProbabilitySpaceDefinition {X : Type u} (𝓧 : SetFamily X)
    (μ : Set X -> ENNReal) : Prop :=
  completedSigmaAlgebraFamily 𝓧 μ = 𝓧

/-- Source: discussion following Proposition 0.1.17. Normalized restriction to a positive set. -/
def restrictedProbabilityMeasure {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (A : Set X) : MeasureTheory.Measure X :=
  (μ A)⁻¹ • μ.restrict A

/-- Source: discussion following Proposition 0.1.17. Finite product probability measure. -/
def productProbabilityMeasure {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : MeasureTheory.Measure X) (ν : MeasureTheory.Measure Y) :
    MeasureTheory.Measure (X × Y) :=
  μ.prod ν

/--
Source: discussion following Proposition 0.1.17.
Existence of the two-sided countable product measure with its cylinder formula.
-/
def twoSidedProductCylinderFamily
    (X : ℤ -> Type u) (m : ∀ i, MeasurableSpace (X i)) :
    SetFamily (∀ i, X i) :=
  {C | ∃ i : ℤ, ∃ A : Set (X i),
    @MeasurableSet (X i) (m i) A ∧ C = (fun x => x i) ⁻¹' A}

theorem twoSidedProductProbabilityMeasureExists
    (X : ℤ -> Type u) (m : ∀ i, MeasurableSpace (X i))
    (μ : ∀ i, @MeasureTheory.Measure (X i) (m i))
    (hμ : ∀ i, @MeasureTheory.IsProbabilityMeasure (X i) (m i) (μ i)) :
    ∃ mprod : MeasurableSpace (∀ i, X i),
      mprod = MeasurableSpace.generateFrom (twoSidedProductCylinderFamily X m) ∧
      ∃ μprod : @MeasureTheory.Measure (∀ i, X i) mprod,
        @MeasureTheory.IsProbabilityMeasure (∀ i, X i) mprod μprod ∧
        (∀ s : Finset ℤ, ∀ A : ∀ i, Set (X i),
          (∀ i ∈ s, @MeasurableSet (X i) (m i) (A i)) ->
          μprod {x | ∀ i ∈ s, x i ∈ A i} = s.prod fun i => μ i (A i)) ∧
        ∀ ν : @MeasureTheory.Measure (∀ i, X i) mprod,
          @MeasureTheory.IsProbabilityMeasure (∀ i, X i) mprod ν ->
          (∀ s : Finset ℤ, ∀ A : ∀ i, Set (X i),
            (∀ i ∈ s, @MeasurableSet (X i) (m i) (A i)) ->
            ν {x | ∀ i ∈ s, x i ∈ A i} = s.prod fun i => μ i (A i)) ->
          ν = μprod := by
  letI (i : ℤ) : MeasurableSpace (X i) := m i
  letI (i : ℤ) : MeasureTheory.IsProbabilityMeasure (μ i) := hμ i
  let mprod : MeasurableSpace (∀ i, X i) := inferInstance
  refine ⟨mprod, ?_, MeasureTheory.Measure.infinitePi μ, ?_, ?_, ?_⟩
  · let G : Set (Set (∀ i, X i)) :=
      {C | ∃ (i : ℤ) (A : Set (X i)), MeasurableSet A ∧
        Function.eval i ⁻¹' A = C}
    have hfamily : G = twoSidedProductCylinderFamily X m := by
      dsimp [G, twoSidedProductCylinderFamily]
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

private noncomputable def finiteAlphabetProbabilityMeasure
    (k : ℕ) (p : Fin k -> ℝ) : MeasureTheory.Measure (Fin k) :=
  ∑ i : Fin k, ENNReal.ofReal (p i) • MeasureTheory.Measure.dirac i

private theorem finiteAlphabetProbabilityMeasure_isProbabilityMeasure
    (k : ℕ) (p : Fin k -> ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : Finset.univ.sum p = 1) :
    MeasureTheory.IsProbabilityMeasure (finiteAlphabetProbabilityMeasure k p) := by
  constructor
  change (∑ i : Fin k, (ENNReal.ofReal (p i) • MeasureTheory.Measure.dirac i))
      Set.univ = 1
  rw [MeasureTheory.Measure.finset_sum_apply]
  simp_rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply]
  simp only [Set.indicator_of_mem, Set.mem_univ, smul_eq_mul, Pi.one_apply]
  simp only [mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := p) (by
    intro i _hi
    exact hp i)]
  simp [hsum]

private theorem finiteAlphabetProbabilityMeasure_singleton
    (k : ℕ) (p : Fin k -> ℝ) (i : Fin k) :
    finiteAlphabetProbabilityMeasure k p ({i} : Set (Fin k)) =
      ENNReal.ofReal (p i) := by
  rw [finiteAlphabetProbabilityMeasure]
  rw [MeasureTheory.Measure.finset_sum_apply]
  simp [MeasureTheory.Measure.smul_apply, Pi.single_apply]

private theorem twoSidedWordCylinder_measurable
    (k : ℕ) (h : ℤ) (word : List (Fin k)) :
    MeasurableSet (twoSidedCylinder h word) := by
  let emb : Fin word.length ↪ ℤ :=
    ⟨fun i => h + (i : ℕ), by
      intro i j hij
      apply Fin.ext
      exact Nat.cast_injective (Int.add_left_cancel hij)⟩
  let s : Finset ℤ := Finset.univ.map emb
  let e0 : Fin word.length → {j // j ∈ s} := fun i =>
    ⟨emb i, by simp [s]⟩
  have he0 : Function.Bijective e0 := by
    constructor
    · intro i j hij
      apply emb.injective
      exact congrArg Subtype.val hij
    · intro j
      have hj : j.1 ∈ s := j.2
      change j.1 ∈ Finset.univ.map emb at hj
      rcases Finset.mem_map.1 hj with ⟨i, _hi, hije⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hije
  let e : Fin word.length ≃ {j // j ∈ s} := Equiv.ofBijective e0 he0
  let t : ℤ → Set (Fin k) := fun j =>
    if hj : j ∈ s then {word.get (e.symm ⟨j, hj⟩)} else Set.univ
  have hC : twoSidedCylinder h word = Set.pi s t := by
    ext x
    constructor
    · intro hx j hj
      change j ∈ Finset.univ.map emb at hj
      rcases Finset.mem_map.1 hj with ⟨i, _hi, hije⟩
      have hi_s : emb i ∈ s := by simp [s]
      have hsub : (⟨emb i, hi_s⟩ : {j // j ∈ s}) = e i := by
        apply Subtype.ext
        rfl
      have he : e.symm ⟨emb i, hi_s⟩ = i := by
        rw [hsub, e.symm_apply_apply]
      have hj_eq : j = emb i := hije.symm
      rw [hj_eq]
      rw [show t (emb i) = ({word.get i} : Set (Fin k)) by simp [t, hi_s, he]]
      exact Set.mem_singleton_iff.mpr (by
        have hxi := hx i
        simpa [twoSidedCylinder, emb] using hxi.symm)
    · intro hx i
      have hi : emb i ∈ s := by simp [s]
      have hxi := hx (emb i) hi
      have he : e.symm ⟨emb i, hi⟩ = i := by
        have hsub : (⟨emb i, hi⟩ : {j // j ∈ s}) = e i := by
          apply Subtype.ext
          rfl
        rw [hsub, e.symm_apply_apply]
      have hval : x (h + (i : ℕ)) = word.get i := by
        have hteq : t (emb i) = ({word.get i} : Set (Fin k)) := by
          simp [t, hi, he]
        have hxi' : x (emb i) ∈ ({word.get i} : Set (Fin k)) := by
          rwa [hteq] at hxi
        simpa [emb] using Set.mem_singleton_iff.mp hxi'
      simp [hval]
  rw [hC]
  exact MeasurableSet.pi s.countable_toSet (fun j hj => by
    by_cases hjs : j ∈ s
    · simp [t, hjs]
    · simp [t, hjs])

private theorem twoSidedWordCylinder_measure
    (k : ℕ) (h : ℤ) (word : List (Fin k))
    (p : Fin k -> ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : Finset.univ.sum p = 1) :
    (MeasureTheory.Measure.infinitePi
      (fun _ : ℤ => finiteAlphabetProbabilityMeasure k p))
      (twoSidedCylinder h word) =
      ENNReal.ofReal ((word.map p).prod) := by
  letI : MeasureTheory.IsProbabilityMeasure (finiteAlphabetProbabilityMeasure k p) :=
    finiteAlphabetProbabilityMeasure_isProbabilityMeasure k p hp hsum
  let emb : Fin word.length ↪ ℤ :=
    ⟨fun i => h + (i : ℕ), by
      intro i j hij
      apply Fin.ext
      exact Nat.cast_injective (Int.add_left_cancel hij)⟩
  let s : Finset ℤ := Finset.univ.map emb
  let e0 : Fin word.length → {j // j ∈ s} := fun i =>
    ⟨emb i, by simp [s]⟩
  have he0 : Function.Bijective e0 := by
    constructor
    · intro i j hij
      apply emb.injective
      exact congrArg Subtype.val hij
    · intro j
      have hj : j.1 ∈ s := j.2
      change j.1 ∈ Finset.univ.map emb at hj
      rcases Finset.mem_map.1 hj with ⟨i, _hi, hije⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hije
  let e : Fin word.length ≃ {j // j ∈ s} := Equiv.ofBijective e0 he0
  let t : ℤ → Set (Fin k) := fun j =>
    if hj : j ∈ s then {word.get (e.symm ⟨j, hj⟩)} else Set.univ
  have hC : twoSidedCylinder h word = Set.pi s t := by
    ext x
    constructor
    · intro hx j hj
      change j ∈ Finset.univ.map emb at hj
      rcases Finset.mem_map.1 hj with ⟨i, _hi, hije⟩
      have hi_s : emb i ∈ s := by simp [s]
      have hsub : (⟨emb i, hi_s⟩ : {j // j ∈ s}) = e i := by
        apply Subtype.ext
        rfl
      have he : e.symm ⟨emb i, hi_s⟩ = i := by
        rw [hsub, e.symm_apply_apply]
      have hj_eq : j = emb i := hije.symm
      rw [hj_eq]
      rw [show t (emb i) = ({word.get i} : Set (Fin k)) by simp [t, hi_s, he]]
      exact Set.mem_singleton_iff.mpr (by
        have hxi := hx i
        simpa [twoSidedCylinder, emb] using hxi.symm)
    · intro hx i
      have hi : emb i ∈ s := by simp [s]
      have hxi := hx (emb i) hi
      have he : e.symm ⟨emb i, hi⟩ = i := by
        have hsub : (⟨emb i, hi⟩ : {j // j ∈ s}) = e i := by
          apply Subtype.ext
          rfl
        rw [hsub, e.symm_apply_apply]
      have hval : x (h + (i : ℕ)) = word.get i := by
        have hteq : t (emb i) = ({word.get i} : Set (Fin k)) := by
          simp [t, hi, he]
        have hxi' : x (emb i) ∈ ({word.get i} : Set (Fin k)) := by
          rwa [hteq] at hxi
        simpa [emb] using Set.mem_singleton_iff.mp hxi'
      simp [hval]
  rw [hC, MeasureTheory.Measure.infinitePi_pi]
  · rw [show s = Finset.univ.map emb by rfl, Finset.prod_map]
    have htmap : ∀ i : Fin word.length,
        (finiteAlphabetProbabilityMeasure k p) (t (emb i)) =
          ENNReal.ofReal (p (word.get i)) := by
      intro i
      have hi : emb i ∈ s := by simp [s]
      have hsub : (⟨emb i, hi⟩ : {j // j ∈ s}) = e i := by
        apply Subtype.ext
        rfl
      have he : e.symm ⟨emb i, hi⟩ = i := by
        rw [hsub, e.symm_apply_apply]
      rw [show t (emb i) = ({word.get i} : Set (Fin k)) by simp [t, hi, he]]
      exact finiteAlphabetProbabilityMeasure_singleton k p (word.get i)
    simp_rw [htmap]
    rw [← ENNReal.ofReal_prod_of_nonneg]
    · simp
    · intro i _hi
      exact hp (word.get i)
  · intro j hj
    simp [t, hj]

def twoSidedWordCylinderFamily (k : ℕ) :
    SetFamily (ℤ -> Fin k) :=
  {C : Set (ℤ -> Fin k) | ∃ h : ℤ, ∃ word : List (Fin k),
    C = twoSidedCylinder h word}

private theorem coordinateSingleton_eq_twoSidedCylinder
    (k : ℕ) (i : ℤ) (a : Fin k) :
    {x : ℤ -> Fin k | x i = a} = twoSidedCylinder i [a] := by
  ext x
  simp [twoSidedCylinder, eq_comm]

private theorem coordinatePreimage_measurable_wordGenerate
    (k : ℕ) (i : ℤ) (A : Set (Fin k)) :
    @MeasurableSet (ℤ -> Fin k)
      (MeasurableSpace.generateFrom (twoSidedWordCylinderFamily k))
      ((fun x : ℤ -> Fin k => x i) ⁻¹' A) := by
  classical
  letI : MeasurableSpace (ℤ -> Fin k) :=
    MeasurableSpace.generateFrom (twoSidedWordCylinderFamily k)
  have hsingle : ∀ a : Fin k,
      MeasurableSet {x : ℤ -> Fin k | x i = a} := by
    intro a
    have hbasic :
        twoSidedCylinder i [a] ∈ twoSidedWordCylinderFamily k :=
      ⟨i, [a], rfl⟩
    have hmeas : MeasurableSet (twoSidedCylinder i [a]) :=
      MeasurableSpace.measurableSet_generateFrom hbasic
    rwa [coordinateSingleton_eq_twoSidedCylinder k i a]
  have hEq :
      ((fun x : ℤ -> Fin k => x i) ⁻¹' A) =
        ⋃ a : {a : Fin k // a ∈ A}, {x : ℤ -> Fin k | x i = a.1} := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨⟨x i, hx⟩, rfl⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨a, ha⟩
      change x i ∈ A
      change x i = a.1 at ha
      rw [ha]
      exact a.2
  rw [hEq]
  exact MeasurableSet.iUnion fun a => hsingle a.1

theorem twoSidedWordCylinderFamily_generate (k : ℕ) :
    (inferInstance : MeasurableSpace (ℤ -> Fin k)) =
      MeasurableSpace.generateFrom (twoSidedWordCylinderFamily k) := by
  apply le_antisymm
  · let G : Set (Set (ℤ -> Fin k)) :=
      {C | ∃ i : ℤ, ∃ A : Set (Fin k),
        MeasurableSet A ∧ Function.eval i ⁻¹' A = C}
    have hpi :
        (inferInstance : MeasurableSpace (ℤ -> Fin k)) =
          MeasurableSpace.generateFrom G := by
      calc
        (inferInstance : MeasurableSpace (ℤ -> Fin k)) = MeasurableSpace.pi := rfl
        _ = MeasurableSpace.generateFrom G :=
          MeasurableSpace.pi_eq_generateFrom_projections
    rw [hpi]
    refine MeasurableSpace.generateFrom_le ?_
    intro C hC
    rcases hC with ⟨i, A, _hA, hEq⟩
    rw [← hEq]
    exact coordinatePreimage_measurable_wordGenerate k i A
  · refine MeasurableSpace.generateFrom_le ?_
    intro C hC
    rcases hC with ⟨h, word, rfl⟩
    exact twoSidedWordCylinder_measurable k h word

private theorem probabilityMeasure_eq_of_subsingleton
    {X : Type u} [MeasurableSpace X] [Subsingleton X]
    (μ ν : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.IsProbabilityMeasure ν] :
    μ = ν := by
  apply MeasureTheory.Measure.ext
  intro s _hs
  by_cases hne : s.Nonempty
  · have hs_univ : s = Set.univ := by
      ext x
      constructor
      · intro _hx
        trivial
      · intro _hx
        rcases hne with ⟨y, hy⟩
        have hxy : x = y := Subsingleton.elim x y
        simpa [hxy] using hy
    simp [hs_univ]
  · have hs_empty : s = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim (hne ⟨x, hx⟩)
      · intro hx
        cases hx
    simp [hs_empty]

/--
Source: discussion following Proposition 0.1.17.
Bernoulli product measure on `(Fin k)^ℤ`, characterized on cylinders.
-/
theorem bernoulliProductMeasureExists (k : ℕ) (p : Fin k -> ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : Finset.univ.sum p = 1) :
    ∃ m : MeasurableSpace (ℤ -> Fin k),
      m = MeasurableSpace.generateFrom
        {C : Set (ℤ -> Fin k) | ∃ h : ℤ, ∃ word : List (Fin k),
          C = twoSidedCylinder h word} ∧
      ∃ μ : @MeasureTheory.Measure (ℤ -> Fin k) m,
        @MeasureTheory.IsProbabilityMeasure (ℤ -> Fin k) m μ ∧
        (∀ h : ℤ, ∀ word : List (Fin k),
          μ (twoSidedCylinder h word) =
            ENNReal.ofReal ((word.map p).prod)) ∧
        ∀ ν : @MeasureTheory.Measure (ℤ -> Fin k) m,
          @MeasureTheory.IsProbabilityMeasure (ℤ -> Fin k) m ν ->
          (∀ h : ℤ, ∀ word : List (Fin k),
            ν (twoSidedCylinder h word) = ENNReal.ofReal ((word.map p).prod)) ->
          ν = μ := by
  by_cases hk : 2 ≤ k
  · let q : ℕ → List (Fin k) → ℝ := fun _ word => (word.map p).prod
    have hq_nonneg : ∀ n word, word.length = n + 1 → 0 ≤ q n word := by
      intro n word _hlen
      apply List.prod_nonneg
      intro r hr
      rcases List.mem_map.mp hr with ⟨a, _ha, rfl⟩
      exact hp a
    have hq_sum : ∑ a : Fin k, q 0 [a] = 1 := by
      simpa [q] using hsum
    have hq_right : ∀ n word, word.length = n + 1 →
        q n word = ∑ a : Fin k, q (n + 1) (word ++ [a]) := by
      intro n word _hlen
      simp [q, List.map_append, ← Finset.mul_sum, hsum]
    have hq_left : ∀ n word, word.length = n + 1 →
        q n word = ∑ a : Fin k, q (n + 1) (a :: word) := by
      intro n word _hlen
      simp [q, ← Finset.sum_mul, hsum]
    obtain ⟨m, hm, μ, hμprob, hμcyl, hμunique⟩ :=
      daniellKolmogorovTheorem k q hk hq_nonneg hq_sum hq_right hq_left
    refine ⟨m, hm, μ, hμprob, ?_, ?_⟩
    · intro h word
      cases word with
      | nil =>
          simpa [twoSidedCylinder] using hμprob.measure_univ
      | cons a tail =>
          simpa [q] using hμcyl h tail.length (a :: tail) (by simp)
    · intro ν hνprob hνcyl
      apply hμunique ν hνprob
      intro h n word hlen
      simpa [q] using hνcyl h word
  · have hkpos : 0 < k := by
      by_contra hnot
      have hk0 : k = 0 := by omega
      subst k
      simp at hsum
    have hk1 : k = 1 := by omega
    subst k
    letI : MeasureTheory.IsProbabilityMeasure
        (finiteAlphabetProbabilityMeasure 1 p) :=
      finiteAlphabetProbabilityMeasure_isProbabilityMeasure 1 p hp hsum
    let μ := MeasureTheory.Measure.infinitePi
      (fun _ : ℤ => finiteAlphabetProbabilityMeasure 1 p)
    letI : MeasureTheory.IsProbabilityMeasure μ := by
      dsimp [μ]
      infer_instance
    refine ⟨inferInstance, ?_, μ, inferInstance, ?_, ?_⟩
    · simpa [twoSidedWordCylinderFamily] using
        (twoSidedWordCylinderFamily_generate 1)
    · intro h word
      exact twoSidedWordCylinder_measure 1 h word p hp hsum
    · intro ν hνprob _hνcyl
      letI : MeasureTheory.IsProbabilityMeasure ν := hνprob
      exact probabilityMeasure_eq_of_subsingleton ν μ

/--
Source: Definition 0.1.19, Chapter 0, Section 1.
An extended-real-valued function is measurable when all upper level sets are
measurable.
-/
def measurableExtendedRealFunctionDefinition {X : Type u}
    (𝓧 : SetFamily X) (f : X -> ExtendedReal) : Prop :=
  MeasurableExtendedRealFunction 𝓧 f

/--
Source: Remark 0.1.20, Chapter 0, Section 1.
Equivalent level-set criteria for measurability of extended-real-valued
functions.
-/
theorem measurableFunctionLevelSetCriteriaRemark {X : Type u} [MeasurableSpace X]
    (f : X -> ExtendedReal) :
    Measurable f ↔
      ((∀ c : ℝ, MeasurableSet {x : X | (c : ExtendedReal) < f x}) ∧
        MeasurableSet {x : X | f x = ⊤}) := by
  constructor
  · intro hf
    refine ⟨fun c ↦ ?_, ?_⟩
    · change MeasurableSet (f ⁻¹' Set.Ioi (c : ExtendedReal))
      exact hf measurableSet_Ioi
    · change MeasurableSet (f ⁻¹' {(⊤ : ExtendedReal)})
      exact hf (measurableSet_singleton (⊤ : ExtendedReal))
  · rintro ⟨hlevel, _htop⟩
    have hbot : MeasurableSet {x : X | (⊥ : ExtendedReal) < f x} := by
      have heq : {x : X | (⊥ : ExtendedReal) < f x} =
          ⋃ n : ℕ, {x : X | ((-(n : ℝ) : ℝ) : ExtendedReal) < f x} := by
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

/-- Source: Remark 0.1.20(2). Real-valued measurability is equivalent to
measurability of the preimage of every Borel set. -/
theorem realMeasurableIffBorelPreimages {X : Type u} [MeasurableSpace X]
    (f : X -> ℝ) :
    Measurable f ↔ ∀ B : Set ℝ, MeasurableSet B -> MeasurableSet (f ⁻¹' B) := by
  rfl

/-- Source: Remark 0.1.20(3). Continuous real-valued maps are Borel measurable. -/
theorem continuousRealMapIsBorelMeasurable {X : Type u} [TopologicalSpace X]
    (f : X -> ℝ) (hf : Continuous f) :
    @Measurable X ℝ (borel X) (borel ℝ) f := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  exact hf.measurable

/--
Source: Definition 0.1.22, Chapter 0, Section 1.
Definitions of finite almost everywhere, almost-everywhere equality,
almost-everywhere convergence, convergence in measure, and convergence in
`L^p`.
-/
def finiteAlmostEverywhere {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (f : X -> ExtendedReal) : Prop :=
  ∀ᵐ x ∂μ, f x ≠ ⊤ ∧ f x ≠ ⊥

/-- Source: Definition 0.1.22(2). Almost-everywhere boundedness. -/
def boundedAlmostEverywhere {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (f : X -> ExtendedReal) : Prop :=
  ∃ M : ℝ, 0 < M ∧ ∀ᵐ x ∂μ, (-(M : ExtendedReal)) < f x ∧ f x < (M : ExtendedReal)

/-- Source: Definition 0.1.22(3). Almost-everywhere nonnegativity. -/
def nonnegativeAlmostEverywhere {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (f : X -> ExtendedReal) : Prop :=
  ∀ᵐ x ∂μ, 0 ≤ f x

/-- Source: Definition 0.1.22(4). Equality almost everywhere. -/
def equalAlmostEverywhere {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (f g : X -> ExtendedReal) : Prop :=
  f =ᵐ[μ] g

/-- Source: Definition 0.1.22(5). Pointwise convergence almost everywhere. -/
def convergesAlmostEverywhere {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (f : ℕ -> X -> ExtendedReal)
    (g : X -> ExtendedReal) : Prop :=
  ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds (g x))

/--
Source: Remark 0.1.23, Chapter 0, Section 1.
Null sets may be ignored in almost-everywhere arguments.
-/
theorem nullSetConventionRemark {X : Type u} [MeasurableSpace X]
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

/--
Source: Definition 0.1.24, Chapter 0, Section 1.
The characteristic function of a subset.
-/
def characteristicFunctionDefinition {X : Type u} (A : Set X) : X -> ℝ :=
  fun x => if x ∈ A then 1 else 0

/-- Source: Definition 0.1.24. The indicator is measurable iff the set is measurable. -/
theorem characteristicFunctionMeasurableIff {X : Type u} [MeasurableSpace X]
    (A : Set X) :
    Measurable (characteristicFunctionDefinition A) ↔ MeasurableSet A := by
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

/--
Source: Definition 0.1.25, Chapter 0, Section 1.
A simple function is a measurable function taking only finitely many values.
-/
def simpleFunctionDefinition {X : Type u}
    (𝓧 : SetFamily X) (f : X -> ℝ) : Prop :=
  ∃ n : ℕ, ∃ values : Fin n -> ℝ,
    MeasurableExtendedRealFunction 𝓧 (fun x => (f x : ExtendedReal)) ∧
      ∀ x : X, ∃ i : Fin n, f x = values i

/-- Source: Definition 0.1.25. Integral of a displayed simple function. -/
def simpleFunctionIntegralDefinition {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (n : ℕ) (a : Fin n -> ℝ)
    (A : Fin n -> Set X) : ℝ :=
  Finset.univ.sum fun i => a i * (μ (A i)).toReal

/--
Source: Definition 0.1.26, Chapter 0, Section 1.
The integral of a nonnegative measurable function is defined as the supremum of
integrals of bounded nonnegative simple functions below it.
-/
def nonnegativeMeasurableIntegralDefinition {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (f : X -> ExtendedReal) : ENNReal :=
  ∫⁻ x, (f x).toENNReal ∂μ

/--
Source: Definition 0.1.27, Chapter 0, Section 1.
The positive and negative parts of a measurable function and the resulting
definition of its integral.
-/
def positivePart (f : ExtendedReal) : ExtendedReal :=
  max f 0

/-- Source: Definition 0.1.27. The negative part of an extended-real number. -/
def negativePart (f : ExtendedReal) : ExtendedReal :=
  max (-f) 0

/-- Source: Definition 0.1.27. Integrability means that the positive and negative
parts both have finite nonnegative integral. -/
def positiveNegativePartsAndIntegralDefinition {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (f : X -> ExtendedReal) : Prop :=
  Measurable f ∧
    nonnegativeMeasurableIntegralDefinition μ (fun x => positivePart (f x)) < ⊤ ∧
    nonnegativeMeasurableIntegralDefinition μ (fun x => negativePart (f x)) < ⊤

/-- Source: Definition 0.1.27. The signed integral after both parts are finite. -/
def signedExtendedRealIntegralDefinition {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (f : X -> ExtendedReal) : ℝ :=
  (nonnegativeMeasurableIntegralDefinition μ (fun x => positivePart (f x))).toReal -
    (nonnegativeMeasurableIntegralDefinition μ (fun x => negativePart (f x))).toReal

/-- Source: Definition 0.1.27. Integral over a measurable subset. -/
def integralOnSetDefinition {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (A : Set X) (f : X -> ℝ) : ℝ :=
  ∫ x in A, f x ∂μ

end Section01
end Chapter00
