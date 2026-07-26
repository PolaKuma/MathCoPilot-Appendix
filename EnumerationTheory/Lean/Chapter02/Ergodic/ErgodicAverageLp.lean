import Chapter02.Ergodic.MeanErgodicL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

noncomputable section

open Filter

namespace Chapter02
namespace ErgodicAverageLp

universe u

lemma ergodicAverage_sub (M : System.{u}) (f g : M.X → ℂ) (n : ℕ) :
    (fun x => ergodicAverage M f n x - ergodicAverage M g n x) =
      ergodicAverage M (f - g) n := by
  classical
  funext x
  unfold ergodicAverage
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false, Pi.sub_apply]
    rw [Finset.sum_sub_distrib]
    ring

lemma ergodicAverage_memLp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (p : ENNReal) (f : M.X → ℂ) (hf : MeasureTheory.MemLp f p M.μ)
    (n : ℕ) : MeasureTheory.MemLp (ergodicAverage M f n) p M.μ := by
  classical
  by_cases hn : n = 0
  · unfold ergodicAverage
    simp [hn]
  · have hsum : MeasureTheory.MemLp
        (fun x => ∑ i ∈ Finset.range n, f ((M.T^[i]) x)) p M.μ := by
      induction Finset.range n using Finset.induction_on with
      | empty =>
          simpa only [Finset.sum_empty] using
            (MeasureTheory.MemLp.zero :
              MeasureTheory.MemLp (0 : M.X → ℂ) p M.μ)
      | @insert i s hi ih =>
          have hterm : MeasureTheory.MemLp
              (fun x => f ((M.T^[i]) x)) p M.μ :=
            hf.comp_measurePreserving (hM.2.iterate i)
          simpa [Finset.sum_insert hi] using hterm.add ih
    unfold ergodicAverage
    simp only [hn, if_false]
    change MeasureTheory.MemLp
      (((n : ℂ)⁻¹) • (fun x => ∑ i ∈ Finset.range n,
        f ((M.T^[i]) x))) p M.μ
    exact hsum.const_smul ((n : ℂ)⁻¹)

set_option maxHeartbeats 600000 in
set_option maxRecDepth 4000 in
lemma eLpNorm_ergodicAverage_le (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (p : ENNReal) (hp : 1 ≤ p) (f : M.X → ℂ)
    (hf : MeasureTheory.MemLp f p M.μ) (n : ℕ) :
    MeasureTheory.eLpNorm (ergodicAverage M f n) p M.μ ≤
      MeasureTheory.eLpNorm f p M.μ := by
  classical
  by_cases hn : n = 0
  · subst n
    unfold ergodicAverage
    simp
  · have hsumAux : MeasureTheory.eLpNorm
          (fun x => ∑ i ∈ Finset.range n, f ((M.T^[i]) x)) p M.μ ≤
          ∑ i ∈ Finset.range n,
            MeasureTheory.eLpNorm (fun x => f ((M.T^[i]) x)) p M.μ ∧
        MeasureTheory.MemLp
          (fun x => ∑ i ∈ Finset.range n, f ((M.T^[i]) x)) p M.μ := by
      refine Finset.induction ?_ ?_ (Finset.range n)
      · constructor
        · change MeasureTheory.eLpNorm (0 : M.X → ℂ) p M.μ ≤ 0
          rw [MeasureTheory.eLpNorm_zero]
        · change MeasureTheory.MemLp (0 : M.X → ℂ) p M.μ
          exact MeasureTheory.MemLp.zero
      · intro i s hi ih
        rcases ih with ⟨ihle, ihm⟩
        have hterm := hf.comp_measurePreserving (hM.2.iterate i)
        constructor
        · simpa only [Finset.sum_insert hi] using
            (MeasureTheory.eLpNorm_add_le hterm.aestronglyMeasurable
              ihm.aestronglyMeasurable hp).trans (add_le_add le_rfl ihle)
        · simpa [Finset.sum_insert hi] using hterm.add ihm
    have hsum := hsumAux.1
    have hiter (i : ℕ) : MeasureTheory.eLpNorm
        (fun x => f ((M.T^[i]) x)) p M.μ =
          MeasureTheory.eLpNorm f p M.μ := by
      change MeasureTheory.eLpNorm (f ∘ (M.T^[i])) p M.μ = _
      exact MeasureTheory.eLpNorm_comp_measurePreserving
        hf.aestronglyMeasurable (hM.2.iterate i)
    unfold ergodicAverage
    simp only [hn, if_false]
    change MeasureTheory.eLpNorm
      (((n : ℂ)⁻¹) • (fun x => ∑ i ∈ Finset.range n,
        f ((M.T^[i]) x))) p M.μ ≤ _
    rw [MeasureTheory.eLpNorm_const_smul]
    calc
      ‖(n : ℂ)⁻¹‖ₑ * MeasureTheory.eLpNorm
          (fun x => ∑ i ∈ Finset.range n, f ((M.T^[i]) x)) p M.μ ≤
          ‖(n : ℂ)⁻¹‖ₑ * ∑ i ∈ Finset.range n,
            MeasureTheory.eLpNorm (fun x => f ((M.T^[i]) x)) p M.μ :=
        mul_le_mul_right hsum _
      _ = MeasureTheory.eLpNorm f p M.μ := by
        simp_rw [hiter]
        have henorm : ‖(n : ℂ)‖ₑ = (n : ENNReal) := by
          apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
          simp
        have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        have henorminv : ‖(n : ℂ)⁻¹‖ₑ = (n : ENNReal)⁻¹ := by
          rw [enorm_inv hnC, henorm]
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hnE : (n : ENNReal) ≠ 0 := by positivity
        rw [henorminv, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← mul_assoc, ENNReal.inv_mul_cancel hnE (by simp), one_mul]

lemma eLpNorm_ergodicAverage_sub_le (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (p : ENNReal) (hp : 1 ≤ p) (f g : M.X → ℂ)
    (hf : MeasureTheory.MemLp f p M.μ)
    (hg : MeasureTheory.MemLp g p M.μ) (n : ℕ) :
    MeasureTheory.eLpNorm
        (fun x => ergodicAverage M f n x - ergodicAverage M g n x) p M.μ ≤
      MeasureTheory.eLpNorm (f - g) p M.μ := by
  rw [ergodicAverage_sub]
  exact eLpNorm_ergodicAverage_le M hM p hp (f - g) (hf.sub hg) n

lemma norm_condExpL1CLM_le_one {X : Type u} {m m₀ : MeasurableSpace X}
    (μ : MeasureTheory.Measure X) (hm : m ≤ m₀)
    [MeasureTheory.SigmaFinite (μ.trim hm)] :
    ‖MeasureTheory.condExpL1CLM ℂ hm μ‖ ≤ 1 := by
  exact MeasureTheory.L1.norm_setToL1_le
    (MeasureTheory.dominatedFinMeasAdditive_condExpInd ℂ hm μ) zero_le_one

lemma condExp_memLp_one {X : Type u} {m m₀ : MeasurableSpace X}
    (μ : MeasureTheory.Measure X) (hm : m ≤ m₀)
    [MeasureTheory.SigmaFinite (μ.trim hm)] (f : X → ℂ) :
    MeasureTheory.MemLp (MeasureTheory.condExp m μ f) 1 μ := by
  rw [MeasureTheory.memLp_one_iff_integrable]
  exact MeasureTheory.integrable_condExp

set_option synthInstance.maxHeartbeats 200000 in
lemma eLpNorm_condExp_le_one {X : Type u} {m m₀ : MeasurableSpace X}
    (μ : MeasureTheory.Measure X) (hm : m ≤ m₀)
    [MeasureTheory.SigmaFinite (μ.trim hm)] (f : X → ℂ)
    (hf : MeasureTheory.MemLp f 1 μ) :
    MeasureTheory.eLpNorm (MeasureTheory.condExp m μ f) 1 μ ≤
      MeasureTheory.eLpNorm f 1 μ := by
  have hfint : MeasureTheory.Integrable f μ :=
    MeasureTheory.memLp_one_iff_integrable.mp hf
  let C := MeasureTheory.condExpL1CLM ℂ hm μ
  let F : MeasureTheory.Lp ℂ 1 μ := hfint.toL1 f
  have hCF : ‖C F‖ ≤ ‖F‖ := by
    calc
      ‖C F‖ ≤ ‖C‖ * ‖F‖ := C.le_opNorm F
      _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right
        (norm_condExpL1CLM_le_one μ hm) (norm_nonneg F)
      _ = ‖F‖ := one_mul _
  have hce := MeasureTheory.condExp_ae_eq_condExpL1CLM hm hfint
  have hleft : MeasureTheory.eLpNorm (MeasureTheory.condExp m μ f) 1 μ < ⊤ :=
    (condExp_memLp_one μ hm f).eLpNorm_lt_top
  have hright : MeasureTheory.eLpNorm f 1 μ < ⊤ := hf.eLpNorm_lt_top
  apply (ENNReal.toReal_le_toReal hleft.ne hright.ne).mp
  rw [← MeasureTheory.Lp.norm_toLp _ (condExp_memLp_one μ hm f),
    ← MeasureTheory.Lp.norm_toLp _ hf]
  have htoLpCE : (condExp_memLp_one μ hm f).toLp
      (MeasureTheory.condExp m μ f) = C F := by
    apply MeasureTheory.Lp.ext
    exact (condExp_memLp_one μ hm f).coeFn_toLp.trans hce
  have htoLpF : hf.toLp f = F := by
    apply MeasureTheory.Lp.ext
    exact hf.coeFn_toLp.trans hfint.coeFn_toL1.symm
  rw [htoLpCE, htoLpF]
  exact hCF

lemma simpleFunc_memLp_two {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ]
    (g : MeasureTheory.SimpleFunc X ℂ) : MeasureTheory.MemLp (⇑g) 2 μ := by
  have htop : MeasureTheory.MemLp (⇑g) ⊤ μ := by
    apply MeasureTheory.memLp_top_of_bound g.aestronglyMeasurable
      (∑ y ∈ g.range, ‖y‖)
    filter_upwards with x
    apply Finset.single_le_sum
    · intro y hy
      exact norm_nonneg y
    · rw [MeasureTheory.SimpleFunc.mem_range]
      exact ⟨x, rfl⟩
  exact htop.mono_exponent (by simp)

set_option synthInstance.maxHeartbeats 400000 in
lemma tendsto_ergodicAverage_condExp_one (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MeasureTheory.MemLp f 1 M.μ) :
    let mInv := MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
    Tendsto (fun n => MeasureTheory.eLpNorm
      (fun x => ergodicAverage M f n x -
        MeasureTheory.condExp mInv M.μ f x) 1 M.μ) atTop (nhds 0) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let mInv := MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  letI : MeasurableSpace M.X := M.measurableSpace
  have hm : mInv ≤ M.measurableSpace := by
    apply MeasurableSpace.generateFrom_le
    intro s hs
    exact hs.1
  letI : Fact (mInv ≤ M.measurableSpace) := ⟨hm⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hquarter : ε / 4 ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨hε.ne', by norm_num⟩
  obtain ⟨g, hfg, hg1⟩ := hf.exists_simpleFunc_eLpNorm_sub_lt
    (by norm_num : (1 : ENNReal) ≠ ⊤) hquarter
  have hg2 := simpleFunc_memLp_two M.μ g
  obtain ⟨gstar, hgstar2, hginv, hconv2, hgce, hgint, hgerg⟩ :=
    MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM (⇑g) hg2
  have hmidle (n : ℕ) : MeasureTheory.eLpNorm
      (fun x => ergodicAverage M (⇑g) n x - gstar x) 1 M.μ ≤
      MeasureTheory.eLpNorm
        (fun x => ergodicAverage M (⇑g) n x - gstar x) 2 M.μ := by
    have hdiff2 : MeasureTheory.MemLp
        (fun x => ergodicAverage M (⇑g) n x - gstar x) 2 M.μ :=
      (ergodicAverage_memLp M hM 2 (⇑g) hg2 n).sub hgstar2
    simpa using
      (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (f := fun x => ergodicAverage M (⇑g) n x - gstar x)
        (μ := M.μ) (by norm_num : (1 : ENNReal) ≤ 2) hdiff2.aestronglyMeasurable)
  have hconv1 : Tendsto (fun n => MeasureTheory.eLpNorm
      (fun x => ergodicAverage M (⇑g) n x - gstar x) 1 M.μ)
      atTop (nhds 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    have hev := (ENNReal.tendsto_nhds_zero.mp hconv2) δ hδ
    filter_upwards [hev] with n hn
    exact (hmidle n).trans hn
  have hevent := (ENNReal.tendsto_nhds_zero.mp hconv1) (ε / 2)
    (ENNReal.div_pos hε.ne' (by norm_num))
  filter_upwards [hevent] with n hn
  have havg : MeasureTheory.eLpNorm
      (fun x => ergodicAverage M f n x - ergodicAverage M (⇑g) n x) 1 M.μ ≤
      MeasureTheory.eLpNorm (f - ⇑g) 1 M.μ :=
    eLpNorm_ergodicAverage_sub_le M hM 1 le_rfl f (⇑g) hf hg1 n
  have hfint : MeasureTheory.Integrable f M.μ :=
    MeasureTheory.memLp_one_iff_integrable.mp hf
  have hgint1 : MeasureTheory.Integrable (⇑g) M.μ :=
    MeasureTheory.memLp_one_iff_integrable.mp hg1
  have hcesub : MeasureTheory.condExp mInv M.μ (⇑g) -
      MeasureTheory.condExp mInv M.μ f =ᵐ[M.μ]
      MeasureTheory.condExp mInv M.μ ((⇑g) - f) := by
    exact (MeasureTheory.condExp_sub hgint1 hfint mInv).symm
  have hceg : MeasureTheory.condExp mInv M.μ (⇑g) =ᵐ[M.μ] gstar :=
    hgce
  have hlastEq : (fun x => gstar x - MeasureTheory.condExp mInv M.μ f x) =ᵐ[M.μ]
      MeasureTheory.condExp mInv M.μ ((⇑g) - f) := by
    exact hceg.symm.sub (EventuallyEq.rfl) |>.trans hcesub
  have hlast : MeasureTheory.eLpNorm
      (fun x => gstar x - MeasureTheory.condExp mInv M.μ f x) 1 M.μ ≤
      MeasureTheory.eLpNorm ((⇑g) - f) 1 M.μ := by
    rw [MeasureTheory.eLpNorm_congr_ae hlastEq]
    exact eLpNorm_condExp_le_one M.μ hm ((⇑g) - f) (hg1.sub hf)
  have hfgsymm : MeasureTheory.eLpNorm ((⇑g) - f) 1 M.μ =
      MeasureTheory.eLpNorm (f - (⇑g)) 1 M.μ := by
    rw [show (⇑g) - f = -(f - ⇑g) by funext x; simp]
    exact MeasureTheory.eLpNorm_neg (f := f - (⇑g)) (p := 1) (μ := M.μ)
  have htri : MeasureTheory.eLpNorm
      (fun x => ergodicAverage M f n x -
        MeasureTheory.condExp mInv M.μ f x) 1 M.μ ≤
      MeasureTheory.eLpNorm
          (fun x => ergodicAverage M f n x - ergodicAverage M (⇑g) n x) 1 M.μ +
        MeasureTheory.eLpNorm
          (fun x => ergodicAverage M (⇑g) n x - gstar x) 1 M.μ +
        MeasureTheory.eLpNorm
          (fun x => gstar x - MeasureTheory.condExp mInv M.μ f x) 1 M.μ := by
    have hmeasA := (ergodicAverage_memLp M hM 1 f hf n).aestronglyMeasurable.sub
      (ergodicAverage_memLp M hM 1 (⇑g) hg1 n).aestronglyMeasurable
    have hgstar1 := hgstar2.mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)
    have hmeasB := (ergodicAverage_memLp M hM 1 (⇑g) hg1 n).aestronglyMeasurable.sub
      hgstar1.aestronglyMeasurable
    have hmeasC := hgstar1.aestronglyMeasurable.sub
      (condExp_memLp_one M.μ hm f).aestronglyMeasurable
    have hfun : (fun x => ergodicAverage M f n x -
        MeasureTheory.condExp mInv M.μ f x) =
        (ergodicAverage M f n - ergodicAverage M (⇑g) n) +
          (ergodicAverage M (⇑g) n - gstar) +
          (gstar - MeasureTheory.condExp mInv M.μ f) := by
      funext x
      change ergodicAverage M f n x - MeasureTheory.condExp mInv M.μ f x =
        (ergodicAverage M f n x - ergodicAverage M (⇑g) n x) +
          (ergodicAverage M (⇑g) n x - gstar x) +
          (gstar x - MeasureTheory.condExp mInv M.μ f x)
      ring
    rw [hfun]
    exact (MeasureTheory.eLpNorm_add_le (hmeasA.add hmeasB) hmeasC le_rfl).trans
      (add_le_add (MeasureTheory.eLpNorm_add_le hmeasA hmeasB le_rfl) le_rfl)
  calc
    MeasureTheory.eLpNorm
        (fun x => ergodicAverage M f n x -
          MeasureTheory.condExp mInv M.μ f x) 1 M.μ ≤ _ := htri
    _ ≤ MeasureTheory.eLpNorm (f - ⇑g) 1 M.μ + ε / 2 +
        MeasureTheory.eLpNorm ((⇑g) - f) 1 M.μ :=
      add_le_add (add_le_add havg hn) hlast
    _ ≤ ε / 4 + ε / 2 + ε / 4 := by
      rw [hfgsymm]
      exact add_le_add (add_le_add hfg.le le_rfl) hfg.le
    _ = ε := by
      simp only [div_eq_mul_inv]
      rw [← mul_add, ← mul_add]
      have hs : (4 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ + (4 : ENNReal)⁻¹ = 1 := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by simp)).mp
        simp [ENNReal.toReal_add, ENNReal.toReal_inv]
        norm_num
      rw [hs, mul_one]

set_option synthInstance.maxHeartbeats 300000 in
theorem meanErgodicSystemStatement_one (M : System.{u}) :
    MeanErgodicSystemStatement M 1 := by
  intro hM f hf
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let mInv : MeasurableSpace M.X :=
    MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  letI : MeasurableSpace M.X := M.measurableSpace
  have hm : mInv ≤ M.measurableSpace := by
    apply MeasurableSpace.generateFrom_le
    intro s hs
    exact hs.1
  letI : Fact (mInv ≤ M.measurableSpace) := ⟨hm⟩
  let fstar : M.X → ℂ := MeasureTheory.condExp mInv M.μ f
  have hfstar : MeasureTheory.MemLp fstar 1 M.μ :=
    condExp_memLp_one M.μ hm f
  have hfint : MeasureTheory.Integrable f M.μ :=
    MeasureTheory.memLp_one_iff_integrable.mp hf
  have hfinv : IsInvariantFunction M fstar := by
    apply (Section01.invariantFunctionIffInvariantSigmaMeasurable M fstar
      (MeasureTheory.integrable_condExp) hM).mpr
    refine ⟨fstar, ?_, EventuallyEq.rfl⟩
    exact MeasureTheory.stronglyMeasurable_condExp.measurable
  refine ⟨fstar, hfstar, hfinv,
    tendsto_ergodicAverage_condExp_one M hM f hf, EventuallyEq.rfl,
    MeasureTheory.integral_condExp hm, ?_⟩
  intro hErg
  obtain ⟨c, hc⟩ :=
    (Section01.isErgodic_to_mathlibErgodic M hErg).ae_eq_const_of_ae_eq_comp_ae
      hfstar.aestronglyMeasurable hfinv
  have hcval : c = ∫ x, f x ∂M.μ := by
    have hint : ∫ x, fstar x ∂M.μ = ∫ x, f x ∂M.μ :=
      MeasureTheory.integral_condExp hm
    rw [MeasureTheory.integral_congr_ae hc] at hint
    simpa using hint
  simpa [hcval] using hc

lemma orbitPartialSum_comp_sub (M : System.{u}) (f : M.X → ℂ)
    (k : ℕ) (x : M.X) :
    (∑ i ∈ Finset.range k, f ((M.T^[i]) (M.T x))) -
        (∑ i ∈ Finset.range k, f ((M.T^[i]) x)) =
      f ((M.T^[k]) x) - f x := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [Finset.sum_range_succ]
      have hit : (M.T^[k]) (M.T x) = (M.T^[k + 1]) x := by
        rw [Function.iterate_succ_apply]
      calc
        (∑ i ∈ Finset.range k, f ((M.T^[i]) (M.T x))) +
              f ((M.T^[k]) (M.T x)) -
            ((∑ i ∈ Finset.range k, f ((M.T^[i]) x)) +
              f ((M.T^[k]) x)) =
            ((∑ i ∈ Finset.range k, f ((M.T^[i]) (M.T x))) -
              (∑ i ∈ Finset.range k, f ((M.T^[i]) x))) +
              (f ((M.T^[k]) (M.T x)) - f ((M.T^[k]) x)) := by ring
        _ = f ((M.T^[k + 1]) x) - f x := by rw [ih, hit]; ring

def coboundaryApproximant (M : System.{u}) (f : M.X → ℂ)
    (N : ℕ) (x : M.X) : ℂ :=
  -((N : ℂ)⁻¹) * ∑ k ∈ Finset.range N,
    ∑ i ∈ Finset.range k, f ((M.T^[i]) x)

lemma coboundaryApproximant_identity (M : System.{u}) (f : M.X → ℂ)
    (N : ℕ) (hN : N ≠ 0) (x : M.X) :
    f x - (coboundaryApproximant M f N (M.T x) -
      coboundaryApproximant M f N x) = ergodicAverage M f N x := by
  classical
  unfold coboundaryApproximant
  have hdiff :
      (∑ k ∈ Finset.range N, ∑ i ∈ Finset.range k,
          f ((M.T^[i]) (M.T x))) -
        (∑ k ∈ Finset.range N, ∑ i ∈ Finset.range k,
          f ((M.T^[i]) x)) =
      ∑ k ∈ Finset.range N, (f ((M.T^[k]) x) - f x) := by
    calc
      _ = ∑ k ∈ Finset.range N,
          ((∑ i ∈ Finset.range k, f ((M.T^[i]) (M.T x))) -
            (∑ i ∈ Finset.range k, f ((M.T^[i]) x))) :=
        by rw [Finset.sum_sub_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        exact orbitPartialSum_comp_sub M f k x
  rw [← mul_sub, hdiff, Finset.sum_sub_distrib]
  unfold ergodicAverage
  simp only [hN, if_false]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp
  ring

lemma coboundaryApproximant_memLp_one (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MeasureTheory.MemLp f 1 M.μ) (N : ℕ) :
    MeasureTheory.MemLp (coboundaryApproximant M f N) 1 M.μ := by
  classical
  have hpartial (k : ℕ) : MeasureTheory.MemLp
      (fun x => ∑ i ∈ Finset.range k, f ((M.T^[i]) x)) 1 M.μ := by
    induction Finset.range k using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using
          (MeasureTheory.MemLp.zero :
            MeasureTheory.MemLp (0 : M.X → ℂ) 1 M.μ)
    | @insert i s hi ih =>
        have hterm := hf.comp_measurePreserving (hM.2.iterate i)
        simpa [Finset.sum_insert hi] using hterm.add ih
  have hsum : MeasureTheory.MemLp
      (fun x => ∑ k ∈ Finset.range N,
        ∑ i ∈ Finset.range k, f ((M.T^[i]) x)) 1 M.μ := by
    induction Finset.range N using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using
          (MeasureTheory.MemLp.zero :
            MeasureTheory.MemLp (0 : M.X → ℂ) 1 M.μ)
    | @insert k s hk ih =>
        simpa [Finset.sum_insert hk] using (hpartial k).add ih
  unfold coboundaryApproximant
  change MeasureTheory.MemLp
    ((-((N : ℂ)⁻¹) : ℂ) • fun x => ∑ k ∈ Finset.range N,
      ∑ i ∈ Finset.range k, f ((M.T^[i]) x)) 1 M.μ
  exact hsum.const_smul (-((N : ℂ)⁻¹))

end ErgodicAverageLp
end Chapter02
