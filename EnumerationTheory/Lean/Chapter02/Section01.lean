import Chapter02.Common
import Chapter02.Ergodic.ErgodicBridge
import Chapter02.Ergodic.BernoulliMixing
import Chapter02.Spectral.CompactHaarCharacters
import Chapter02.Ergodic.MarkovErgodic
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.AddCircleAdd

noncomputable section

open Filter

namespace Chapter02
namespace Section01

universe u

/-- The chapter's symmetric-difference formulation gives Mathlib's ergodic map. -/
theorem isErgodic_to_mathlibErgodic (M : System.{u})
    (hM : IsErgodic M) : Ergodic M.T M.μ := by
  exact ErgodicBridge.isErgodic_to_mathlibErgodic M hM

/-- Mathlib's standard ergodicity notion gives the chapter's zero-one formulation. -/
theorem mathlibErgodic_to_isErgodic (M : System.{u})
    (hprob : MeasureTheory.IsProbabilityMeasure M.μ)
    (h : Ergodic M.T M.μ) : IsErgodic M := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hprob
  refine ⟨⟨hprob, h.toMeasurePreserving⟩, ?_⟩
  intro A hA hsymm
  have hsets : M.T ⁻¹' A =ᵐ[M.μ] A := by
    rw [← MeasureTheory.measure_symmDiff_eq_zero_iff]
    simpa [Chapter00.symmDiff, Set.symmDiff_def] using hsymm
  rcases h.ae_empty_or_univ_of_preimage_ae_le hA.nullMeasurableSet hsets.le with
      h0 | h1
  · exact Or.inl (MeasureTheory.ae_eq_empty.mp h0)
  · right
    calc
      M.μ A = M.μ Set.univ := MeasureTheory.measure_congr h1
      _ = 1 := hprob.measure_univ

private theorem positiveSetOrbitUnionFull (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : A ∈ M.𝓧) (hpos : 0 < M.μ A) :
    M.μ (⋃ n : ℕ, preimageIter M (n + 1) A) = 1 := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  let U : Set M.X := ⋃ n : ℕ, preimageIter M (n + 1) A
  have hUmeas : MeasurableSet U := by
    apply MeasurableSet.iUnion
    intro n
    exact (hM.1.2.iterate (n + 1)).measurable hA
  have hpre : M.T ⁻¹' U ⊆ U := by
    intro x hx
    simp only [U, Set.mem_preimage, Set.mem_iUnion] at hx ⊢
    obtain ⟨n, hn⟩ := hx
    refine ⟨n + 1, ?_⟩
    simpa [preimageIter, Function.iterate_succ_apply] using hn
  have hzero_or_full :=
    (isErgodic_to_mathlibErgodic M hM).ae_empty_or_univ_of_preimage_ae_le
      hUmeas.nullMeasurableSet (Filter.Eventually.of_forall hpre)
  rcases hzero_or_full with hzero | hfull
  · have hUzero : M.μ U = 0 := MeasureTheory.ae_eq_empty.mp hzero
    have hsub : preimageIter M 1 A ⊆ U := by
      intro x hx
      simp only [U, Set.mem_iUnion]
      exact ⟨0, by simpa using hx⟩
    have hprezero : M.μ (preimageIter M 1 A) = 0 :=
      nonpos_iff_eq_zero.mp (hUzero ▸ MeasureTheory.measure_mono hsub)
    have hmeasure : M.μ (preimageIter M 1 A) = M.μ A := by
      exact (hM.1.2.iterate 1).measure_preimage hA.nullMeasurableSet
    rw [hmeasure] at hprezero
    exact (ne_of_gt hpos hprezero).elim
  · change M.μ U = 1
    calc
      M.μ U = M.μ Set.univ := MeasureTheory.measure_congr hfull
      _ = 1 := hM.1.1.measure_univ

/-- Source: Definition 2.1.1, Chapter 2, Section 1. -/
def ergodicityDefinition (M : System.{u}) : Prop := IsErgodic M

/-- Source: Remark 2.1.2, Chapter 2, Section 1. -/
def nonProbabilityErgodicityAndReturnTimesRemark (M : System.{u}) : Prop :=
  IsErgodicNonProbability M ∧
    ∀ A B : Set M.X, A ∈ M.𝓧 -> B ∈ M.𝓧 ->
      (Chapter01.returnTimes M A B).Nonempty ∨
        realMeasure M A = 0 ∨ realMeasure M B = 0

/-- Source: Theorem 2.1.3, Chapter 2, Section 1. -/
theorem ergodicEquivalentCharacterizations (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    HasErgodicEquivalentCharacterizations M := by
  constructor
  · intro herg
    letI : MeasureTheory.IsProbabilityMeasure M.μ := herg.1.1
    refine ⟨?_, ?_, ?_⟩
    · intro B hB
      exact herg.2 B hB.1 hB.2
    · intro A hA hpos
      exact positiveSetOrbitUnionFull M herg A hA hpos
    · intro A B hA hB hposA hposB
      let U : Set M.X := ⋃ n : ℕ, preimageIter M (n + 1) B
      have hUfull : M.μ U = 1 := positiveSetOrbitUnionFull M herg B hB hposB
      have hUmeas : MeasurableSet U := by
        apply MeasurableSet.iUnion
        intro n
        exact (herg.1.2.iterate (n + 1)).measurable hB
      have hAU : M.μ (A ∩ U) = M.μ A := by
        have hcompl : M.μ Uᶜ = 0 := by
          rw [MeasureTheory.measure_compl hUmeas (by simp [hUfull])]
          simp [hUfull]
        apply MeasureTheory.measure_congr
        filter_upwards [MeasureTheory.ae_eq_univ.mpr hcompl] with x hx
        change (x ∈ A ∩ U) = (x ∈ A)
        have hxU : x ∈ U := hx.mpr trivial
        simp [hxU]
      have hex : ∃ n : ℕ, 0 < M.μ (A ∩ preimageIter M (n + 1) B) := by
        by_contra hnone
        push_neg at hnone
        have hallzero : ∀ n : ℕ,
            M.μ (A ∩ preimageIter M (n + 1) B) = 0 := by
          intro n
          exact nonpos_iff_eq_zero.mp (hnone n)
        have hunionzero : M.μ (⋃ n : ℕ,
            A ∩ preimageIter M (n + 1) B) = 0 :=
          MeasureTheory.measure_iUnion_null hallzero
        have hset : A ∩ U = ⋃ n : ℕ,
            A ∩ preimageIter M (n + 1) B := by
          ext x
          simp [U]
        have : M.μ A = 0 := by
          rw [← hAU, hset, hunionzero]
        exact (ne_of_gt hposA) this
      obtain ⟨n, hn⟩ := hex
      exact ⟨n + 1, by omega, hn⟩
  · rintro ⟨hzeroOne, hcover, hreturn⟩
    refine ⟨hM, ?_⟩
    intro A hA hsymm
    exact hzeroOne A ⟨hA, hsymm⟩

/-- Source: Definition 2.1.4, Chapter 2, Section 1. -/
def syndeticSetDefinition (A : Set ℕ) : Prop := IsSyndetic A

/-- Source: Corollary 2.1.5, Chapter 2, Section 1. -/
theorem returnTimesInErgodicSystemAreSyndetic (M : System.{u})
    (A B : Set M.X) (hM : IsErgodic M) (_hA : A ∈ M.𝓧) (hB : B ∈ M.𝓧)
    (hposA : 0 < M.μ A) (hposB : 0 < M.μ B) :
    IsSyndetic (Chapter01.returnTimes M A B) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  let V : ℕ → Set M.X := fun N => ⋃ n : ℕ, ⋃ (_h : n < N), preimageIter M (n + 1) B
  have hVmeas : ∀ N, MeasurableSet (V N) := by
    intro N
    apply MeasurableSet.iUnion
    intro n
    apply MeasurableSet.iUnion
    intro hn
    exact (hM.1.2.iterate (n + 1)).measurable hB
  have hVmono : Monotone V := by
    intro N K hNK x hx
    simp only [V, Set.mem_iUnion] at hx ⊢
    obtain ⟨n, hnN, hxn⟩ := hx
    exact ⟨n, lt_of_lt_of_le hnN hNK, hxn⟩
  have hVunion : (⋃ N, V N) = ⋃ n : ℕ, preimageIter M (n + 1) B := by
    ext x
    simp only [V, Set.mem_iUnion]
    constructor
    · rintro ⟨N, n, hn, hxn⟩
      exact ⟨n, hxn⟩
    · rintro ⟨n, hxn⟩
      exact ⟨n + 1, n, by omega, hxn⟩
  have hfull : M.μ (⋃ N, V N) = 1 := by
    rw [hVunion]
    exact (Section01.ergodicEquivalentCharacterizations M hM.1).mp hM |>.2.1 B hB hposB
  have hlt : 1 - M.μ A < (1 : ENNReal) :=
    ENNReal.sub_lt_self (by simp) (by simp) (ne_of_gt hposA)
  have htend : Tendsto (fun N => M.μ (V N)) atTop (nhds 1) := by
    convert MeasureTheory.tendsto_measure_iUnion_atTop hVmono using 1
    simp [hfull]
  have hev : ∀ᶠ N in atTop, 1 - M.μ A < M.μ (V N) :=
    htend.eventually (Ioi_mem_nhds hlt)
  obtain ⟨N, hN⟩ := hev.exists
  refine ⟨N + 1, by omega, ?_⟩
  intro i
  let W : Set M.X := preimageIter M i (V N)
  have hWmeas : MeasurableSet W := (hM.1.2.iterate i).measurable (hVmeas N)
  have hWmeasure : M.μ W = M.μ (V N) :=
    (hM.1.2.iterate i).measure_preimage (hVmeas N).nullMeasurableSet
  have hsumgt : 1 < M.μ A + M.μ W := by
    rw [hWmeasure]
    have hAle : M.μ A ≤ (1 : ENNReal) := by
      calc
        M.μ A ≤ M.μ Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
        _ = 1 := hM.1.1.measure_univ
    calc
      (1 : ENNReal) = (1 - M.μ A) + M.μ A :=
        (tsub_add_cancel_of_le hAle).symm
      _ < M.μ (V N) + M.μ A :=
        ENNReal.add_lt_add_right (by simp) hN
      _ = M.μ A + M.μ (V N) := add_comm _ _
  have hinterpos : 0 < M.μ (A ∩ W) := by
    by_contra hzero
    have hinterzero : M.μ (A ∩ W) = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp hzero)
    have hunion : M.μ (A ∪ W) + M.μ (A ∩ W) = M.μ A + M.μ W :=
      MeasureTheory.measure_union_add_inter A hWmeas
    have hle : M.μ (A ∪ W) ≤ 1 := by
      calc
        M.μ (A ∪ W) ≤ M.μ Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
        _ = 1 := hM.1.1.measure_univ
    rw [hinterzero, add_zero] at hunion
    exact (not_lt_of_ge (hunion ▸ hle)) hsumgt
  have hWset : W = ⋃ n : ℕ, ⋃ (_h : n < N),
      preimageIter M (i + n + 1) B := by
    ext x
    simp only [W, V, preimageIter, Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn, hxn⟩
      refine ⟨n, hn, ?_⟩
      change (M.T^[i + n + 1]) x ∈ B
      rw [show i + n + 1 = (n + 1) + i by omega,
        Function.iterate_add_apply]
      exact hxn
    · rintro ⟨n, hn, hxn⟩
      refine ⟨n, hn, ?_⟩
      change (M.T^[n + 1]) ((M.T^[i]) x) ∈ B
      rw [← Function.iterate_add_apply]
      simpa only [show (n + 1) + i = i + n + 1 by omega] using hxn
  have hex : ∃ n : ℕ, n < N ∧ 0 < M.μ (A ∩ preimageIter M (i + n + 1) B) := by
    by_contra hnone
    push_neg at hnone
    have hzero : M.μ (A ∩ W) = 0 := by
      rw [hWset, Set.inter_iUnion]
      apply MeasureTheory.measure_iUnion_null
      intro n
      rw [Set.inter_iUnion]
      apply MeasureTheory.measure_iUnion_null
      intro hn
      exact nonpos_iff_eq_zero.mp (hnone n hn)
    exact (ne_of_gt hinterpos) hzero
  obtain ⟨n, hnN, hnpos⟩ := hex
  refine ⟨i + n + 1, ?_, by omega, by omega⟩
  exact ⟨by omega, hnpos⟩


/-- Source: Definition 2.1.6, Chapter 2, Section 1. -/
def eigenvalueAndEigenfunctionDefinition (M : System.{u}) (lam : ℂ)
    (f : M.X -> ℂ) : Prop :=
  Eigenvalue M lam ∧ Eigenfunction M lam f

/-- Source: Theorem 2.1.7, Chapter 2, Section 1. -/
theorem ergodicityInvariantFunctionCharacterizations (M : System.{u}) :
    HasInvariantFunctionCharacterizations M := by
  intro hpres
  constructor
  · intro hM f hf hinv
    exact (isErgodic_to_mathlibErgodic M hM).ae_eq_const_of_ae_eq_comp_ae
      hf.aestronglyMeasurable hinv
  · intro hconst
    letI : MeasureTheory.IsProbabilityMeasure M.μ := hpres.1
    refine ⟨hpres, ?_⟩
    intro A hA hsymm
    let f : M.X → ℂ := A.indicator fun _ => 1
    have hf : MeasureTheory.MemLp f 2 M.μ := by
      exact MeasureTheory.memLp_indicator_const 2 hA 1
        (Or.inr (by simp))
    have hsets : M.T ⁻¹' A =ᵐ[M.μ] A := by
      rw [← MeasureTheory.measure_symmDiff_eq_zero_iff]
      simpa [Chapter00.symmDiff, Set.symmDiff_def] using hsymm
    have hfinv : IsInvariantFunction M f := by
      filter_upwards [hsets] with x hx
      simp only [Chapter01.koopman]
      by_cases hTx : M.T x ∈ A
      · have hxA : x ∈ A := Eq.mp hx hTx
        simp [f, hTx, hxA]
      · have hxA : x ∉ A := fun h => hTx (Eq.mpr hx h)
        simp [f, hTx, hxA]
    obtain ⟨c, hc⟩ := hconst f hf hfinv
    by_cases hczero : c = 0
    · left
      apply MeasureTheory.ae_eq_empty.mp
      filter_upwards [hc] with x hx
      change (x ∈ A) = (x ∈ (∅ : Set M.X))
      apply propext
      constructor
      · intro hxA
        have : (1 : ℂ) = 0 := by
          simp [f, hxA, hczero] at hx
        exact one_ne_zero this
      · simp
    · right
      have hAuniv : A =ᵐ[M.μ] Set.univ := by
        filter_upwards [hc] with x hx
        change (x ∈ A) = (x ∈ (Set.univ : Set M.X))
        apply propext
        constructor
        · simp
        · intro _
          by_contra hxA
          have : (0 : ℂ) = c := by simpa [f, hxA] using hx
          exact hczero this.symm
      have hcompl : M.μ Aᶜ = 0 := MeasureTheory.ae_eq_univ.mp hAuniv
      calc
        M.μ A = M.μ (Aᶜ)ᶜ := by rw [compl_compl]
        _ = M.μ Set.univ - M.μ Aᶜ :=
          MeasureTheory.measure_compl hA.compl (by simp [hcompl])
        _ = 1 := by simp [hcompl]

/-- Source: Remark 2.1.8, Chapter 2, Section 1. -/
def invariantSigmaAlgebraRemark (M : System.{u}) : SetFamily M.X :=
  invariantSigmaAlgebra M

/-- Source: Lemma 2.1.9, Chapter 2, Section 1. -/
theorem conditionalExpectationCommutesWithKoopmanInvariantSigmaAlgebra
    (M : System.{u}) : ConditionalExpectationInvariant M := by
  intro hM f hf
  have hkoop : MeasureTheory.Integrable (Chapter01.koopman M.T f) M.μ := by
    exact (hM.2.integrable_comp hf.aestronglyMeasurable).2 hf
  let mInv : MeasurableSpace M.X :=
    MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  have hm : mInv ≤ M.measurableSpace := by
    change MeasurableSpace.generateFrom (invariantSigmaAlgebra M) ≤ M.measurableSpace
    apply MeasurableSpace.generateFrom_le
    intro s hs
    exact hs.1
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  have hinv : ∀ s : Set M.X, @MeasurableSet M.X mInv s →
      M.T ⁻¹' s =ᵐ[M.μ] s := by
    intro s hs
    exact MeasurableSpace.generateFrom_induction
      (invariantSigmaAlgebra M)
      (fun t _ => M.T ⁻¹' t =ᵐ[M.μ] t)
      (by
        intro t ht htm
        rw [← MeasureTheory.measure_symmDiff_eq_zero_iff]
        simpa [Chapter00.symmDiff, Set.symmDiff_def] using ht.2)
      (by simp)
      (by
        intro t ht hti
        simpa only [Set.preimage_compl] using hti.compl)
      (by
        intro t ht hti
        have hti' : ∀ᵐ x ∂M.μ, ∀ i, (M.T ⁻¹' t i) x = (t i) x :=
          MeasureTheory.ae_all_iff.mpr hti
        filter_upwards [hti'] with x hx
        change (x ∈ M.T ⁻¹' ⋃ i, t i) = (x ∈ ⋃ i, t i)
        simp only [Set.mem_preimage, Set.mem_iUnion]
        apply propext
        constructor
        · rintro ⟨i, hi⟩
          exact ⟨i, (hx i).mp hi⟩
        · rintro ⟨i, hi⟩
          exact ⟨i, (hx i).mpr hi⟩)
      s hs
  change MeasureTheory.condExp mInv M.μ (Chapter01.koopman M.T f) =ᵐ[M.μ]
    MeasureTheory.condExp mInv M.μ f
  have hsetIntegral : ∀ s : Set M.X, @MeasurableSet M.X mInv s →
      (∫ x in s,
    MeasureTheory.condExp mInv M.μ (Chapter01.koopman M.T f) x ∂M.μ) =
        ∫ x in s, f x ∂M.μ := by
    intro s hs
    letI : MeasurableSpace M.X := M.measurableSpace
    have hs0 : @MeasurableSet M.X M.measurableSpace s := hm s hs
    have hsetinv := hinv s hs
    have hmap_eq :
        (@MeasureTheory.Measure.map M.X M.X M.measurableSpace
          M.measurableSpace M.T M.μ) = M.μ := hM.2.map_eq
    have hgsm : MeasureTheory.AEStronglyMeasurable (s.indicator f)
        (@MeasureTheory.Measure.map M.X M.X M.measurableSpace
          M.measurableSpace M.T M.μ) := by
      rw [hmap_eq]
      exact (hf.indicator hs0).aestronglyMeasurable
    have hmap := MeasureTheory.integral_map
      (μ := M.μ) (φ := M.T) (f := s.indicator f)
      hM.2.measurable.aemeasurable hgsm
    rw [hmap_eq] at hmap
    calc
      (∫ x in s,
          MeasureTheory.condExp mInv M.μ (Chapter01.koopman M.T f) x ∂M.μ) =
          ∫ x in s, Chapter01.koopman M.T f x ∂M.μ :=
        MeasureTheory.setIntegral_condExp hm hkoop hs
      _ = ∫ x, (s.indicator f) (M.T x) ∂M.μ := by
        rw [← MeasureTheory.integral_indicator hs0]
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hsetinv] with x hx
        by_cases hTx : M.T x ∈ s
        · have hxS : x ∈ s := Eq.mp hx hTx
          simp [Set.indicator, hTx, hxS, Chapter01.koopman]
        · have hxS : x ∉ s := fun h => hTx (Eq.mpr hx h)
          simp [Set.indicator, hTx, hxS]
      _ = ∫ x, s.indicator f x ∂M.μ := hmap.symm
      _ = ∫ x in s, f x ∂M.μ := MeasureTheory.integral_indicator hs0
  refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
    (f := f) (g := MeasureTheory.condExp mInv M.μ
      (Chapter01.koopman M.T f)) hm hf ?_ ?_ ?_
  · intro s hs hfin
    exact MeasureTheory.integrable_condExp.integrableOn
  · intro s hs hfin
    exact hsetIntegral s hs
  · exact MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable

/-- Source: Lemma 2.1.10, Chapter 2, Section 1. -/
theorem invariantFunctionIffInvariantSigmaMeasurable (M : System.{u})
    (f : M.X -> ℂ) (hf : MeasureTheory.Integrable f M.μ)
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    IsInvariantFunction M f ↔ HasInvariantSigmaMeasurableRepresentative M f := by
  let mInv : MeasurableSpace M.X :=
    MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  have hinvSets : ∀ s : Set M.X, @MeasurableSet M.X mInv s →
      M.T ⁻¹' s =ᵐ[M.μ] s := by
    intro s hs
    exact MeasurableSpace.generateFrom_induction
      (invariantSigmaAlgebra M)
      (fun t _ => M.T ⁻¹' t =ᵐ[M.μ] t)
      (by
        intro t ht htm
        rw [← MeasureTheory.measure_symmDiff_eq_zero_iff]
        simpa [Chapter00.symmDiff, Set.symmDiff_def] using ht.2)
      (by simp)
      (by
        intro t ht hti
        simpa only [Set.preimage_compl] using hti.compl)
      (by
        intro t ht hti
        have hti' : ∀ᵐ x ∂M.μ, ∀ i, (M.T ⁻¹' t i) x = (t i) x :=
          MeasureTheory.ae_all_iff.mpr hti
        filter_upwards [hti'] with x hx
        change (x ∈ M.T ⁻¹' ⋃ i, t i) = (x ∈ ⋃ i, t i)
        simp only [Set.mem_preimage, Set.mem_iUnion]
        apply propext
        constructor
        · rintro ⟨i, hi⟩
          exact ⟨i, (hx i).mp hi⟩
        · rintro ⟨i, hi⟩
          exact ⟨i, (hx i).mpr hi⟩)
      s hs
  constructor
  · intro hfinv
    let g : M.X → ℂ := hf.aestronglyMeasurable.mk f
    have hg : @Measurable M.X ℂ M.measurableSpace inferInstance g :=
      hf.aestronglyMeasurable.measurable_mk
    have hfg : f =ᵐ[M.μ] g := hf.aestronglyMeasurable.ae_eq_mk
    have hgInv : Chapter01.koopman M.T g =ᵐ[M.μ] g := by
      calc
        Chapter01.koopman M.T g =ᵐ[M.μ] Chapter01.koopman M.T f := by
          letI : MeasurableSpace M.X := M.measurableSpace
          have hpull :=
            @MeasureTheory.Measure.QuasiMeasurePreserving.ae_eq_comp
              M.X M.X ℂ M.measurableSpace M.measurableSpace
              M.μ M.μ M.T g f hM.2.quasiMeasurePreserving hfg.symm
          simpa only [Chapter01.koopman, Function.comp_def] using hpull
        _ =ᵐ[M.μ] f := hfinv
        _ =ᵐ[M.μ] g := hfg
    refine ⟨g, ?_, hfg⟩
    change @Measurable M.X ℂ mInv inferInstance g
    intro s hs
    apply MeasurableSpace.measurableSet_generateFrom
    show g ⁻¹' s ∈ invariantSigmaAlgebra M
    refine ⟨hg hs, ?_⟩
    have hseteq : M.T ⁻¹' (g ⁻¹' s) =ᵐ[M.μ] g ⁻¹' s := by
      filter_upwards [hgInv] with x hx
      change (g (M.T x) ∈ s) = (g x ∈ s)
      change g (M.T x) = g x at hx
      rw [hx]
    simpa [Chapter00.symmDiff, Set.symmDiff_def] using
      (MeasureTheory.measure_symmDiff_eq_zero_iff.mpr hseteq)
  · rintro ⟨g, hg, hfg⟩
    have hRe : ∀ᵐ x ∂M.μ, (g (M.T x)).re = (g x).re := by
      have hall : ∀ᵐ x ∂M.μ, ∀ q : ℚ,
          ((g (M.T x)).re < (q : ℝ)) = ((g x).re < (q : ℝ)) := by
        rw [MeasureTheory.ae_all_iff]
        intro q
        let s : Set M.X := {x | (g x).re < (q : ℝ)}
        have hs : @MeasurableSet M.X mInv s := by
          exact (Complex.continuous_re.measurable.comp hg) measurableSet_Iio
        simpa only [s, Set.mem_setOf_eq, Set.mem_preimage] using hinvSets s hs
      filter_upwards [hall] with x hx
      apply le_antisymm
      · by_contra hle
        have hlt : (g x).re < (g (M.T x)).re := lt_of_not_ge hle
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
        exact (not_lt_of_ge hq2.le) ((hx q).mpr hq1)
      · by_contra hle
        have hlt : (g (M.T x)).re < (g x).re := lt_of_not_ge hle
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
        exact (not_lt_of_ge hq2.le) ((hx q).mp hq1)
    have hIm : ∀ᵐ x ∂M.μ, (g (M.T x)).im = (g x).im := by
      have hall : ∀ᵐ x ∂M.μ, ∀ q : ℚ,
          ((g (M.T x)).im < (q : ℝ)) = ((g x).im < (q : ℝ)) := by
        rw [MeasureTheory.ae_all_iff]
        intro q
        let s : Set M.X := {x | (g x).im < (q : ℝ)}
        have hs : @MeasurableSet M.X mInv s := by
          exact (Complex.continuous_im.measurable.comp hg) measurableSet_Iio
        simpa only [s, Set.mem_setOf_eq, Set.mem_preimage] using hinvSets s hs
      filter_upwards [hall] with x hx
      apply le_antisymm
      · by_contra hle
        have hlt : (g x).im < (g (M.T x)).im := lt_of_not_ge hle
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
        exact (not_lt_of_ge hq2.le) ((hx q).mpr hq1)
      · by_contra hle
        have hlt : (g (M.T x)).im < (g x).im := lt_of_not_ge hle
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
        exact (not_lt_of_ge hq2.le) ((hx q).mp hq1)
    have hgInv : Chapter01.koopman M.T g =ᵐ[M.μ] g := by
      filter_upwards [hRe, hIm] with x hre him
      exact Complex.ext hre him
    calc
      Chapter01.koopman M.T f =ᵐ[M.μ] Chapter01.koopman M.T g := by
        letI : MeasurableSpace M.X := M.measurableSpace
        have hpull :=
          @MeasureTheory.Measure.QuasiMeasurePreserving.ae_eq_comp
            M.X M.X ℂ M.measurableSpace M.measurableSpace
            M.μ M.μ M.T f g hM.2.quasiMeasurePreserving hfg
        simpa only [Chapter01.koopman, Function.comp_def] using hpull
      _ =ᵐ[M.μ] g := hgInv
      _ =ᵐ[M.μ] f := hfg.symm

private noncomputable def cyclicErgodicSystem.{z} (n : ℕ) [NeZero n] : System.{z} where
  X := ULift.{z} (Fin n)
  measurableSpace := ⊤
  μ := ProbabilityTheory.uniformOn Set.univ
  T := fun x => ULift.up (x.down + 1)

/-- Source: Example 2.1.11, Chapter 2, Section 1. -/
theorem nPeriodicSystemIsErgodic (n : ℕ) (hn : 0 < n) :
    ∃ M : System.{u}, Chapter01.IsNPeriodicSystem M n ∧ IsErgodic M := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let M : System.{u} := cyclicErgodicSystem n
  have hpres : Chapter01.IsMeasurePreservingSystem M := by
    constructor
    · change MeasureTheory.IsProbabilityMeasure
        (ProbabilityTheory.uniformOn (Set.univ : Set (ULift.{u} (Fin n))))
      exact ProbabilityTheory.isProbabilityMeasure_uniformOn Set.finite_univ
        Set.univ_nonempty
    · change MeasureTheory.MeasurePreserving
        (fun x : ULift.{u} (Fin n) => ULift.up (x.down + 1))
        (ProbabilityTheory.uniformOn Set.univ)
        (ProbabilityTheory.uniformOn Set.univ)
      refine MeasureTheory.MeasurePreserving.mk (measurable_of_finite _) ?_
      ext A hA
      rw [MeasureTheory.Measure.map_apply (measurable_of_finite _) hA]
      rw [ProbabilityTheory.uniformOn_univ, ProbabilityTheory.uniformOn_univ]
      rw [MeasureTheory.Measure.count_apply (MeasurableSpace.measurableSet_top),
        MeasureTheory.Measure.count_apply (MeasurableSpace.measurableSet_top)]
      rw [Set.encard_preimage_of_bijective]
      exact Equiv.ulift.symm.bijective.comp
        ((Equiv.addRight (1 : Fin n)).bijective.comp Equiv.ulift.bijective)
  refine ⟨M, ⟨hpres, Equiv.ulift, ?_⟩, hpres, ?_⟩
  · intro x
    change (x.down + 1 : Fin n).val = (x.down.val + 1) % n
    simp [Fin.add_def]
  · intro A hA hsymm
    have hpoint : ∀ x : ULift.{u} (Fin n),
        M.μ ({x} : Set (ULift.{u} (Fin n))) ≠ 0 := by
      intro x
      change ProbabilityTheory.uniformOn
        (Set.univ : Set (ULift.{u} (Fin n))) {x} ≠ 0
      simp [ProbabilityTheory.uniformOn_univ]
    have hsd : Chapter00.symmDiff (M.T ⁻¹' A) A = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      have hsub : ({x} : Set (ULift.{u} (Fin n))) ⊆
          Chapter00.symmDiff (M.T ⁻¹' A) A := by
        simpa only [Set.singleton_subset_iff] using hx
      have hle : M.μ ({x} : Set (ULift.{u} (Fin n))) ≤
          M.μ (Chapter00.symmDiff (M.T ⁻¹' A) A) :=
        MeasureTheory.measure_mono hsub
      rw [hsymm] at hle
      exact hpoint x (nonpos_iff_eq_zero.mp hle)
    have heq : M.T ⁻¹' A = A := by
      apply Set.Subset.antisymm
      · intro x hx
        by_contra hxA
        have : x ∈ Chapter00.symmDiff (M.T ⁻¹' A) A := Or.inl ⟨hx, hxA⟩
        rw [hsd] at this
        exact this
      · intro x hx
        by_contra hxpre
        have : x ∈ Chapter00.symmDiff (M.T ⁻¹' A) A := Or.inr ⟨hx, hxpre⟩
        rw [hsd] at this
        exact this
    rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact Or.inl MeasureTheory.measure_empty
    · right
      have hall : A = Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        let k := if a.down.val ≤ x.down.val then
          x.down.val - a.down.val else n + x.down.val - a.down.val
        have hiter : ∀ j : ℕ, ((M.T^[j]) a) ∈ A := by
          intro j
          induction j with
          | zero => simpa using ha
          | succ j ih =>
              have : M.T ((M.T^[j]) a) ∈ A :=
                (Set.ext_iff.mp heq ((M.T^[j]) a)).mpr ih
              simpa [Function.iterate_succ_apply'] using this
        have hk := hiter k
        have hval : (a.down.val + k) % n = x.down.val := by
          dsimp [k]
          have hx : x.down.val < n := x.down.isLt
          split_ifs with hax
          · rw [show a.down.val + (x.down.val - a.down.val) = x.down.val by omega]
            exact Nat.mod_eq_of_lt hx
          · rw [show a.down.val + (n + x.down.val - a.down.val) =
                n + x.down.val by omega]
            simp [Nat.mod_eq_of_lt hx]
        have hiterVal : ∀ j : ℕ,
            ((M.T^[j]) a).down.val = (a.down.val + j) % n := by
          intro j
          induction j with
          | zero =>
              simp only [Function.iterate_zero_apply, Nat.add_zero]
              exact (Nat.mod_eq_of_lt a.down.isLt).symm
          | succ j ih =>
              rw [Function.iterate_succ_apply']
              have ih' :
                  (((fun x : ULift.{u} (Fin n) =>
                    ULift.up (x.down + 1))^[j]) a).down.val =
                    (a.down.val + j) % n := by
                simpa only [M, cyclicErgodicSystem] using ih
              simp only [M, cyclicErgodicSystem, ULift.down_up]
              let y := ((fun x : ULift.{u} (Fin n) =>
                ULift.up (x.down + 1))^[j]) a
              change (y.down + 1).val = (a.down.val + (j + 1)) % n
              have hy : y.down.val = (a.down.val + j) % n := by
                simpa only [y] using ih'
              rw [Fin.add_def, hy]
              rw [show (1 : Fin n).val = 1 % n by rfl]
              change (((a.down.val + j) % n + 1 % n) % n) =
                (a.down.val + (j + 1)) % n
              rw [← Nat.add_mod]
              congr 1
        have hxeq : (M.T^[k]) a = x := by
          apply ULift.ext
          apply Fin.ext
          simpa [hiterVal k] using hval
        simpa [hxeq] using hk
      rw [hall]
      exact hpres.1.measure_univ

private noncomputable def liftedCircleRotationErgodicSystem.{z} (α : ℝ) : System.{z} where
  X := ULift.{z} (AddCircle (1 : ℝ))
  measurableSpace := inferInstance
  μ := MeasureTheory.Measure.map MeasurableEquiv.ulift.symm AddCircle.haarAddCircle
  T := fun x => MeasurableEquiv.ulift.symm
    (MeasurableEquiv.ulift x + (α : AddCircle (1 : ℝ)))

/-- Source: Example 2.1.12, Chapter 2, Section 1. -/
theorem circleRotationErgodicIffIrrational (α : ℝ) :
    ∃ M : System.{u}, Chapter01.IsRotationSystem M α ∧
      (IsErgodic M ↔ Irrational α) := by
  let M : System.{u} := liftedCircleRotationErgodicSystem α
  let e := MeasurableEquiv.ulift (α := AddCircle (1 : ℝ))
  have he : MeasureTheory.MeasurePreserving e M.μ AddCircle.haarAddCircle := by
    refine MeasureTheory.MeasurePreserving.mk e.measurable ?_
    change MeasureTheory.Measure.map e
      (MeasureTheory.Measure.map e.symm AddCircle.haarAddCircle) = _
    rw [MeasureTheory.Measure.map_map e.measurable e.symm.measurable]
    simp [e]
  have hprob : MeasureTheory.IsProbabilityMeasure M.μ := by
    constructor
    change MeasureTheory.Measure.map e.symm AddCircle.haarAddCircle Set.univ = 1
    rw [MeasureTheory.Measure.map_apply_of_aemeasurable
      e.symm.measurable.aemeasurable MeasurableSet.univ]
    simp
  have hpres : Chapter01.IsMeasurePreservingSystem M := by
    refine ⟨hprob, ?_⟩
    have hrot : MeasureTheory.MeasurePreserving
        (fun y : AddCircle (1 : ℝ) => y + (α : AddCircle (1 : ℝ)))
        AddCircle.haarAddCircle AddCircle.haarAddCircle :=
      MeasureTheory.MeasurePreserving.add_right
        AddCircle.haarAddCircle (α : AddCircle (1 : ℝ))
        (MeasureTheory.MeasurePreserving.id _)
    have hconj : M.T = e.symm ∘ (fun y : AddCircle (1 : ℝ) =>
        y + (α : AddCircle (1 : ℝ))) ∘ e := by
      rfl
    rw [hconj]
    exact (he.symm e).comp (hrot.comp he)
  refine ⟨M, ⟨hpres, e.toEquiv, e.measurable, e.symm.measurable,
      he.map_eq, ?_⟩, ?_⟩
  · intro x
    rfl
  · have hconj : e ∘ M.T ∘ e.symm =
        (fun y : AddCircle (1 : ℝ) => y + (α : AddCircle (1 : ℝ))) := by
      funext y
      rfl
    have hergiff : Ergodic M.T M.μ ↔
        Ergodic (fun y : AddCircle (1 : ℝ) =>
          y + (α : AddCircle (1 : ℝ))) AddCircle.haarAddCircle := by
      rw [← he.ergodic_conjugate_iff]
      rw [hconj]
    have hvol :
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
          AddCircle.haarAddCircle := by
      simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
    have hrotiff : Ergodic (fun y : AddCircle (1 : ℝ) =>
          y + (α : AddCircle (1 : ℝ))) AddCircle.haarAddCircle ↔
        Irrational α := by
      rw [← hvol]
      rw [AddCircle.ergodic_add_right]
      rw [← AddCircle.denseRange_zsmul_iff]
      simpa using
        (AddCircle.denseRange_zsmul_coe_iff (a := α) (p := (1 : ℝ)))
    constructor
    · intro hM
      exact hrotiff.mp (hergiff.mp (isErgodic_to_mathlibErgodic M hM))
    · intro hirr
      exact mathlibErgodic_to_isErgodic M hprob
        (hergiff.mpr (hrotiff.mpr hirr))

/-- Source: Example 2.1.13, Chapter 2, Section 1. -/
theorem compactGroupRotationErgodicIffDenseCyclicSubgroup :
    CompactGroupRotationErgodicityStatement := by
  intro G _instGroup _instMetric _instCompact _instMeasurable _instBorel
    _instTopGroup m hprob hinv a
  letI : MeasureTheory.IsProbabilityMeasure m := hprob
  letI : MeasureTheory.IsFiniteMeasure m := ⟨by simp⟩
  letI : m.IsMulLeftInvariant := ⟨fun g => (hinv g).map_eq⟩
  have hiff : Ergodic (fun x : G => a * x) m ↔
      DenseRange (fun n : ℤ => a ^ n) := by
    exact ergodic_mul_left_iff_denseRange_zpow m
  constructor
  · constructor
    · intro hchapter
      have hstd := isErgodic_to_mathlibErgodic
        (compactGroupRotationSystem m a) hchapter
      have hd : DenseRange (fun n : ℤ => a ^ n) := by
        apply hiff.mp
        simpa [compactGroupRotationSystem] using hstd
      exact dense_iff_closure_eq.mp hd
    · intro hd
      apply mathlibErgodic_to_isErgodic
        (compactGroupRotationSystem m a) hprob
      have hstd : Ergodic (fun x : G => a * x) m :=
        hiff.mpr (dense_iff_closure_eq.mpr hd)
      simpa [compactGroupRotationSystem] using hstd
  · intro hchapter x y
    have hstd := isErgodic_to_mathlibErgodic
      (compactGroupRotationSystem m a) hchapter
    have hd : closure (Set.range fun n : ℤ => a ^ n) = Set.univ := by
      exact dense_iff_closure_eq.mp
        (hiff.mp (by simpa [compactGroupRotationSystem] using hstd))
    have ha_comm : ∀ z : G, a * z = z * a := by
      intro z
      let C : Set G := {w | a * w = w * a}
      have hCclosed : IsClosed C := by
        exact isClosed_eq (continuous_const.mul continuous_id)
          (continuous_id.mul continuous_const)
      have hrange : Set.range (fun n : ℤ => a ^ n) ⊆ C := by
        rintro _ ⟨n, rfl⟩
        exact ((Commute.refl a).zpow_right n).eq
      have hclosure : closure (Set.range fun n : ℤ => a ^ n) ⊆ C :=
        hCclosed.closure_subset_iff.mpr hrange
      exact hclosure (by rw [hd]; trivial)
    let Cy : Set G := {w | w * y = y * w}
    have hCclosed : IsClosed Cy := by
      exact isClosed_eq (continuous_id.mul continuous_const)
        (continuous_const.mul continuous_id)
    have hrange : Set.range (fun n : ℤ => a ^ n) ⊆ Cy := by
      rintro _ ⟨n, rfl⟩
      change a ^ n * y = y * a ^ n
      have hay : Commute a y := ha_comm y
      exact (hay.zpow_left n).eq
    have hclosure : closure (Set.range fun n : ℤ => a ^ n) ⊆ Cy :=
      hCclosed.closure_subset_iff.mpr hrange
    exact hclosure (by rw [hd]; trivial)

/-- Source: Example 2.1.14, Chapter 2, Section 1. -/
theorem circleEndomorphismIsErgodic (n : ℕ) (hn : 2 ≤ n) :
    IsErgodic (circleEndomorphismSystem n) := by
  have hprob : MeasureTheory.IsProbabilityMeasure
      (circleEndomorphismSystem n).μ := by
    change MeasureTheory.IsProbabilityMeasure
      (AddCircle.haarAddCircle :
        MeasureTheory.Measure (AddCircle (1 : ℝ)))
    infer_instance
  apply mathlibErgodic_to_isErgodic (circleEndomorphismSystem n) hprob
  have hvol :
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
        AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  change Ergodic (fun x : AddCircle (1 : ℝ) => n • x)
    AddCircle.haarAddCircle
  rw [← hvol]
  simpa [circleEndomorphismSystem] using
    (AddCircle.ergodic_nsmul (T := (1 : ℝ)) (n := n) (by omega))

/-- The forward implication in Example 2.1.15.  A periodic nontrivial
character gives, by summing its finite orbit, a nonconstant invariant
continuous function. -/
theorem ergodic_compactGroupEndomorphism_has_no_nontrivial_periodic_character
    (G : Type u) [CommGroup G] [MetricSpace G] [CompactSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (m : MeasureTheory.Measure G)
    (hprob : MeasureTheory.IsProbabilityMeasure m) (hhaar : m.IsHaarMeasure)
    (A : G →* G) (hAcont : Continuous A) (hAsurj : Function.Surjective A)
    (herg : IsErgodic (compactGroupHaarEndomorphismSystem m A))
    (χ : ContinuousMultiplicativeCircleCharacter G)
    (hperiodic : ∃ n : ℕ, 0 < n ∧
      (fun x => χ.toFun ((A : G → G)^[n] x)) = χ.toFun) :
    ∀ x, χ.toFun x = 1 := by
  letI : MeasureTheory.IsProbabilityMeasure m := hprob
  letI : m.IsHaarMeasure := hhaar
  obtain ⟨n, hn, hperiod⟩ := hperiodic
  have hmp : MeasureTheory.MeasurePreserving A m m :=
    CompactHaarCharacters.haarEndomorphism_measurePreserving
      m A hAcont hAsurj
  have hM : Chapter01.IsMeasurePreservingSystem
      (compactGroupHaarEndomorphismSystem m A) := ⟨hprob, hmp⟩
  have hcriterion := (ergodicityInvariantFunctionCharacterizations
      (compactGroupHaarEndomorphismSystem m A) hM).mp herg
  change ∀ f : G → ℂ, MeasureTheory.MemLp f 2 m →
    Chapter01.koopman (A : G → G) f =ᵐ[m] f →
      ∃ c : ℂ, f =ᵐ[m] fun _ => c at hcriterion
  have hconst := hcriterion
    (CompactHaarCharacters.orbitSum A χ n)
    (CompactHaarCharacters.orbitSum_memLp m A hAcont χ n)
    (Filter.Eventually.of_forall fun x =>
      congrFun (CompactHaarCharacters.orbitSum_invariant_of_periodic
        A χ hn hperiod) x)
  exact CompactHaarCharacters.orbitSum_ae_constant_implies_character_trivial
    m A hAcont χ hn hconst

/-- Source: Example 2.1.15, Chapter 2, Section 1. -/
theorem compactGroupEndomorphismErgodicityCharacterization :
    CompactGroupEndomorphismErgodicityStatement := by
  intro G _ _ _ _ _ _ m hprob hhaar A hAcont hAsurj
  letI : MeasureTheory.IsProbabilityMeasure m := hprob
  letI : m.IsHaarMeasure := hhaar
  constructor
  · intro herg χ hperiodic
    exact
      ergodic_compactGroupEndomorphism_has_no_nontrivial_periodic_character
        G m hprob hhaar A hAcont hAsurj herg χ hperiodic
  · intro haperiodic
    have hmp : MeasureTheory.MeasurePreserving A m m :=
      CompactHaarCharacters.haarEndomorphism_measurePreserving
        m A hAcont hAsurj
    have hM : Chapter01.IsMeasurePreservingSystem
        (compactGroupHaarEndomorphismSystem m A) := ⟨hprob, hmp⟩
    rw [ergodicityInvariantFunctionCharacterizations
      (compactGroupHaarEndomorphismSystem m A) hM]
    intro f hf hinv
    change Chapter01.koopman (A : G → G) f =ᵐ[m] f at hinv
    exact
      CompactHaarCharacters.invariant_function_ae_constant_of_aperiodic_characters
        m A hAcont hAsurj haperiodic f hf hinv

/-- Convert an additive circle character into the same character on the
multiplicative type-tag of the group. -/
def addCharacterToMultiplicative
    {G : Type u} [AddCommGroup G] [TopologicalSpace G]
    (χ : ContinuousCircleCharacter G) :
    ContinuousMultiplicativeCircleCharacter (Multiplicative G) where
  toFun x := χ.toFun x.toAdd
  map_one := χ.map_zero
  map_mul x y := χ.map_add x.toAdd y.toAdd
  continuous := χ.continuous
  unit_norm x := χ.unit_norm x.toAdd

/-- Convert a character on the multiplicative type-tag back to additive
notation. -/
def multiplicativeCharacterToAdd
    {G : Type u} [AddCommGroup G] [TopologicalSpace G]
    (χ : ContinuousMultiplicativeCircleCharacter (Multiplicative G)) :
    ContinuousCircleCharacter G where
  toFun x := χ.toFun (.ofAdd x)
  map_zero := χ.map_one
  map_add x y := χ.map_mul (.ofAdd x) (.ofAdd y)
  continuous := χ.continuous
  unit_norm x := χ.unit_norm (.ofAdd x)

/-- Additive-language form of Example 2.1.15, obtained by the
`Multiplicative` type tag. -/
theorem compactAddGroupEndomorphismErgodicityCharacterization
    (G : Type u) [AddCommGroup G] [MetricSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    (m : MeasureTheory.Measure G)
    (hprob : MeasureTheory.IsProbabilityMeasure m)
    (hhaar : m.IsAddHaarMeasure)
    (A : G →+ G) (hA : Continuous A) (hAsurj : Function.Surjective A) :
    IsErgodic (compactGroupEndomorphismSystem m A) ↔
      ∀ χ : ContinuousCircleCharacter G,
        (∃ n : ℕ, 0 < n ∧
          (fun x => χ.toFun ((A : G → G)^[n] x)) = χ.toFun) →
        ∀ x, χ.toFun x = 1 := by
  letI : MeasureTheory.IsProbabilityMeasure m := hprob
  letI : m.IsAddHaarMeasure := hhaar
  have hborelG : (inferInstance : MeasurableSpace G) = borel G :=
    BorelSpace.measurable_eq
  have hfinite : ∀ ⦃K : Set G⦄, IsCompact K → m K < ⊤ :=
    fun _ hK => hhaar.lt_top_of_isCompact hK
  have hleft : ∀ g : G, MeasureTheory.Measure.map (g + ·) m = m :=
    hhaar.map_add_left_eq_self
  have hopen : ∀ U : Set G, IsOpen U → U.Nonempty → m U ≠ 0 :=
    hhaar.open_pos
  letI : MeasurableSpace (Multiplicative G) :=
    (inferInstance : MeasurableSpace G)
  letI : BorelSpace (Multiplicative G) := ⟨hborelG⟩
  let mm : MeasureTheory.Measure (Multiplicative G) := m
  letI : MeasureTheory.IsProbabilityMeasure mm := hprob
  letI : mm.IsHaarMeasure := {
    lt_top_of_isCompact _ hK := hfinite hK
    map_mul_left_eq_self g := hleft g.toAdd
    open_pos U hU hne := hopen U hU hne }
  have hmul := compactGroupEndomorphismErgodicityCharacterization
    (Multiplicative G) (inferInstance : CommGroup (Multiplicative G))
    (inferInstance : MetricSpace (Multiplicative G))
    (inferInstance : CompactSpace (Multiplicative G))
    (inferInstance : IsTopologicalGroup (Multiplicative G))
    (inferInstance : MeasurableSpace (Multiplicative G))
    (inferInstance : BorelSpace (Multiplicative G))
    mm (by infer_instance) (by infer_instance) A.toMultiplicative hA hAsurj
  change
    (IsErgodic (compactGroupEndomorphismSystem m A) ↔
      ∀ χ : ContinuousMultiplicativeCircleCharacter (Multiplicative G),
        (∃ n : ℕ, 0 < n ∧
          (fun x => χ.toFun (((A.toMultiplicative :
            Multiplicative G →* Multiplicative G) :
              Multiplicative G → Multiplicative G)^[n] x)) = χ.toFun) →
        ∀ x, χ.toFun x = 1) at hmul
  rw [hmul]
  constructor
  · intro h χ hperiod x
    exact h (addCharacterToMultiplicative χ)
      (by simpa [addCharacterToMultiplicative] using hperiod) (.ofAdd x)
  · intro h χ hperiod x
    exact h (multiplicativeCharacterToAdd χ)
      (by simpa [multiplicativeCharacterToAdd] using hperiod) x.toAdd

/-- The integer matrix map on the torus, as an additive homomorphism. -/
def torusMatrixAddHom (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) :
    Chapter01.Torus n →+ Chapter01.Torus n where
  toFun := torusMatrixMap n A
  map_zero' := by
    ext i
    simp [torusMatrixMap]
  map_add' x y := by
    ext i
    simp [torusMatrixMap, Finset.sum_add_distrib]

/-- Source: Example 2.1.16, Chapter 2, Section 1. -/
theorem torusEndomorphismErgodicIffNoRootOfUnityEigenvalue :
    TorusEndomorphismErgodicityStatement := by
  intro n A hsurj
  have hprob : MeasureTheory.IsProbabilityMeasure
      (Chapter01.torusHaarMeasure n) := by
    unfold Chapter01.torusHaarMeasure
    infer_instance
  have hhaar : (Chapter01.torusHaarMeasure n).IsAddHaarMeasure := by
    unfold Chapter01.torusHaarMeasure
    infer_instance
  have hcont : Continuous (torusMatrixAddHom n A) := by
    change Continuous (torusMatrixMap n A)
    unfold torusMatrixMap
    fun_prop
  have hcriterion :=
    compactAddGroupEndomorphismErgodicityCharacterization
      (Chapter01.Torus n) (Chapter01.torusHaarMeasure n)
      hprob hhaar (torusMatrixAddHom n A) hcont hsurj
  change
    (IsErgodic (torusEndomorphismSystem n A) ↔
      ∀ χ : ContinuousCircleCharacter (Chapter01.Torus n),
        (∃ q : ℕ, 0 < q ∧
          (fun x => χ.toFun ((torusMatrixMap n A)^[q] x)) = χ.toFun) →
        ∀ x, χ.toFun x = 1) at hcriterion
  rw [hcriterion]
  constructor
  · intro hno hroot
    obtain ⟨χ, hperiod, x, hx⟩ :=
      (MathCopilotPrior.torus_rootOfUnity_iff_periodic_nontrivial_character
        n A).mp hroot
    exact hx (hno χ hperiod x)
  · intro hnroot χ hperiod x
    by_contra hx
    apply hnroot
    exact
      (MathCopilotPrior.torus_rootOfUnity_iff_periodic_nontrivial_character
        n A).mpr ⟨χ, hperiod, x, hx⟩

/-- Source: Example 2.1.17, Chapter 2, Section 1. -/
theorem bernoulliShiftIsErgodic : BernoulliShiftErgodicityStatement := by
  intro M hB
  have hmix : IsStrongMixing M :=
    BernoulliMixing.bernoulliShiftStrongMixing M hB
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hmix.1.1
  refine ⟨hmix.1, ?_⟩
  intro A hA hnull
  have hiter : ∀ n, preimageIter M n A =ᵐ[M.μ] A := by
    have hstep : M.T ⁻¹' A =ᵐ[M.μ] A := by
      rw [← MeasureTheory.measure_symmDiff_eq_zero_iff]
      simpa [Chapter00.symmDiff, Set.symmDiff_def] using hnull
    intro n
    induction n with
    | zero => simp [preimageIter, Chapter01.iterateMap]
    | succ n ih =>
        have hpre := hmix.1.2.quasiMeasurePreserving.ae_eq_comp ih
        simpa only [preimageIter, Chapter01.iterateMap, Set.preimage_preimage,
          Function.iterate_succ_apply] using hpre.trans hstep
  have hcorr : ∀ n, correlation M A A n = realMeasure M A := by
    intro n
    unfold correlation
    apply congrArg ENNReal.toReal
    apply MeasureTheory.measure_congr
    filter_upwards [hiter n] with x hx
    change (x ∈ preimageIter M n A) = (x ∈ A) at hx
    change (x ∈ A ∧ x ∈ preimageIter M n A) = (x ∈ A)
    rw [hx]
    simp
  have hconst : Tendsto (fun n ↦ correlation M A A n) atTop
      (nhds (realMeasure M A)) := by
    convert tendsto_const_nhds using 1
    funext n
    exact hcorr n
  have heq : realMeasure M A = productMeasureValue M A A :=
    tendsto_nhds_unique hconst (hmix.2 A A hA hA)
  have hidem : realMeasure M A * (realMeasure M A - 1) = 0 := by
    unfold productMeasureValue at heq
    nlinarith
  rcases mul_eq_zero.mp hidem with hzero | hone
  · left
    apply (ENNReal.toReal_eq_toReal_iff' (by simp : M.μ A ≠ ⊤)
      (by simp : (0 : ENNReal) ≠ ⊤)).mp
    simpa [realMeasure] using hzero
  · right
    have hrealone : realMeasure M A = 1 := by nlinarith
    apply (ENNReal.toReal_eq_toReal_iff' (by simp : M.μ A ≠ ⊤)
      (by simp : (1 : ENNReal) ≠ ⊤)).mp
    simpa [realMeasure] using hrealone

/-- Source: Example 2.1.18, Chapter 2, Section 1. -/
theorem markovShiftErgodicIffIrreducible : MarkovShiftErgodicCharacterization := by
  intro M k p P h hp
  exact MarkovErgodic.markovShiftErgodic_iff_irreducible k p P h hp

end Section01
end Chapter02
