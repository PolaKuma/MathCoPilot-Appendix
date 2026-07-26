import Chapter02.Ergodic.ErgodicAverageLp

noncomputable section

open Filter

namespace Chapter02
namespace LpInterpolation

universe u

lemma complex_norm_condExp_le {X : Type u} {m m0 : MeasurableSpace X}
    (μ : MeasureTheory.Measure X) (hm : m ≤ m0)
    [MeasureTheory.SigmaFinite (μ.trim hm)] (f : X → ℂ)
    (hf : MeasureTheory.Integrable f μ) :
    (fun x => ‖MeasureTheory.condExp m μ f x‖) ≤ᵐ[μ]
      MeasureTheory.condExp m μ (fun x => ‖f x‖) := by
  let z : X → ℂ := MeasureTheory.condExp m μ f
  let phase : X → ℂ := fun x =>
    if z x = 0 then 0 else star (z x) / (‖z x‖ : ℂ)
  have hzmeas : @MeasureTheory.StronglyMeasurable X ℂ _ m z :=
    MeasureTheory.stronglyMeasurable_condExp
  have hphasemeas : @MeasureTheory.StronglyMeasurable X ℂ _ m phase := by
    apply Measurable.stronglyMeasurable
    apply Measurable.ite
    · exact hzmeas.measurable (measurableSet_singleton 0)
    · exact measurable_const
    · exact (Complex.continuous_conj.measurable.comp hzmeas.measurable).div
        ((Complex.continuous_ofReal.comp continuous_norm).measurable.comp hzmeas.measurable)
  have hphase_norm : ∀ x, ‖phase x‖ ≤ 1 := by
    intro x
    by_cases hx : z x = 0
    · simp [phase, hx]
    · have hn : ‖z x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      simp [phase, hx, hn]
  have hphase_mul : ∀ x, (phase x * z x).re = ‖z x‖ := by
    intro x
    by_cases hx : z x = 0
    · simp [phase, hx]
    · have hn : ‖z x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      simp only [phase, if_neg hx]
      rw [div_mul_eq_mul_div]
      have hconj : star (z x) * z x = (Complex.normSq (z x) : ℂ) := by
        simpa using Complex.normSq_eq_conj_mul_self.symm
      rw [hconj, Complex.normSq_eq_norm_sq]
      norm_num [pow_two, hn]
  have hpoint : ∀ x, (phase x * f x).re ≤ ‖f x‖ := by
    intro x
    calc
      (phase x * f x).re ≤ ‖phase x * f x‖ := Complex.re_le_norm _
      _ = ‖phase x‖ * ‖f x‖ := norm_mul _ _
      _ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right (hphase_norm x) (norm_nonneg _)
      _ = ‖f x‖ := one_mul _
  have hphaseint : MeasureTheory.Integrable (fun x => phase x * f x) μ :=
    hf.bdd_mul (hphasemeas.mono hm).aestronglyMeasurable
      (Filter.Eventually.of_forall hphase_norm)
  have hpull := MeasureTheory.condExp_bilin_of_aestronglyMeasurable_left
    (m := m) (.mul ℝ ℂ) hphasemeas.aestronglyMeasurable hphaseint hf
  let reCLM : ℂ →L[ℝ] ℝ := Complex.reCLM
  have hre := reCLM.comp_condExp_comm hphaseint (m := m)
  have hmono := MeasureTheory.condExp_mono
    (m := m) (reCLM.integrable_comp hphaseint) hf.norm
      (Filter.Eventually.of_forall hpoint)
  filter_upwards [hpull, hre, hmono] with x hpullx hrex hmonox
  change ‖z x‖ ≤ MeasureTheory.condExp m μ (fun x => ‖f x‖) x
  calc
    ‖z x‖ = (phase x * z x).re := (hphase_mul x).symm
    _ = (MeasureTheory.condExp m μ (fun y => phase y * f y) x).re := by
      simpa only [ContinuousLinearMap.mul_apply, z] using congrArg Complex.re hpullx.symm
    _ = MeasureTheory.condExp m μ (fun y => (phase y * f y).re) x := hrex
    _ ≤ MeasureTheory.condExp m μ (fun y => ‖f y‖) x := hmonox

lemma eLpNorm_two_sq_eq_lintegral {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (f : X → ℂ) :
    MeasureTheory.eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul]
  norm_num

lemma eLpNorm_le_of_bound {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (f : X → ℂ) (p : ENNReal)
    (hp : 2 ≤ p) (hp_top : p < ⊤) (C : ENNReal)
    (hf : MeasureTheory.AEStronglyMeasurable f μ)
    (hC : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ C) :
    MeasureTheory.eLpNorm f p μ ≤
      (C ^ (p.toReal - 2) * MeasureTheory.eLpNorm f 2 μ ^ 2) ^
        (1 / p.toReal) := by
  have hpne : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 2) hp)
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos hpne (ne_of_lt hp_top)
  have hp2 : 0 ≤ p.toReal - 2 := by
    have : (2 : ℝ) ≤ p.toReal := by
      rw [← ENNReal.toReal_ofNat]
      exact ENNReal.toReal_mono (ne_of_lt hp_top) hp
    linarith
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
    hpne (ne_of_lt hp_top)]
  apply ENNReal.rpow_le_rpow
  calc
    (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ≤
        ∫⁻ x, C ^ (p.toReal - 2) * ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [hC] with x hx
      by_cases hz : ‖f x‖ₑ = 0
      · rw [hz, ENNReal.zero_rpow_of_pos hp0,
          ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
        simp
      · calc
          ‖f x‖ₑ ^ p.toReal =
              ‖f x‖ₑ ^ ((2 : ℝ) + (p.toReal - 2)) := by
            congr 2
            linarith
          _ = ‖f x‖ₑ ^ (2 : ℝ) * ‖f x‖ₑ ^ (p.toReal - 2) :=
            ENNReal.rpow_add (2 : ℝ) (p.toReal - 2) hz (by simp)
          _ ≤ ‖f x‖ₑ ^ (2 : ℝ) * C ^ (p.toReal - 2) := by
            exact mul_le_mul_right (ENNReal.rpow_le_rpow hx hp2) _
          _ = C ^ (p.toReal - 2) * ‖f x‖ₑ ^ (2 : ℝ) := by ac_rfl
    _ = C ^ (p.toReal - 2) * MeasureTheory.eLpNorm f 2 μ ^ 2 := by
      rw [MeasureTheory.lintegral_const_mul'' _
          (hf.enorm.pow_const (2 : ℝ)),
        eLpNorm_two_sq_eq_lintegral]
  positivity

lemma tendsto_eLpNorm_of_tendsto_two_of_bound {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (f : ℕ → X → ℂ) (p : ENNReal)
    (hp : 2 ≤ p) (hp_top : p < ⊤) (C : ENNReal)
    (hC_top : C ≠ ⊤)
    (hf : ∀ n, MeasureTheory.AEStronglyMeasurable (f n) μ)
    (hC : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ₑ ≤ C)
    (h2 : Tendsto (fun n => MeasureTheory.eLpNorm (f n) 2 μ) atTop (nhds 0)) :
    Tendsto (fun n => MeasureTheory.eLpNorm (f n) p μ) atTop (nhds 0) := by
  have hpne : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 2) hp)
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos hpne (ne_of_lt hp_top)
  have hp2 : 0 ≤ p.toReal - 2 := by
    have : (2 : ℝ) ≤ p.toReal := by
      rw [← ENNReal.toReal_ofNat]
      exact ENNReal.toReal_mono (ne_of_lt hp_top) hp
    linarith
  let K : ENNReal := C ^ (p.toReal - 2)
  have hK_top : K ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp2 hC_top
  have hsq : Tendsto
      (fun n => MeasureTheory.eLpNorm (f n) 2 μ ^ 2) atTop (nhds 0) := by
    simpa [pow_two] using ENNReal.Tendsto.mul h2 (Or.inr ENNReal.zero_ne_top)
      h2 (Or.inr ENNReal.zero_ne_top)
  have hin : Tendsto
      (fun n => K * MeasureTheory.eLpNorm (f n) 2 μ ^ 2) atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hsq (Or.inr hK_top)
  have hright : Tendsto
      (fun n => (K * MeasureTheory.eLpNorm (f n) 2 μ ^ 2) ^ (1 / p.toReal))
      atTop (nhds 0) := by
    have h := hin.ennrpow_const (1 / p.toReal)
    simpa only [one_div,
      ENNReal.zero_rpow_of_pos (inv_pos.mpr hp0)] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n => MeasureTheory.eLpNorm (f n) p μ)
    (g := fun _ => 0) (h := fun n =>
      (K * MeasureTheory.eLpNorm (f n) 2 μ ^ 2) ^ (1 / p.toReal))
    tendsto_const_nhds hright
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · exact Filter.Eventually.of_forall (fun n =>
      eLpNorm_le_of_bound μ (f n) p hp hp_top C (hf n) (hC n))

lemma tendsto_eLpNorm_of_tendsto_two_of_le_two {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (f : ℕ → X → ℂ) (p : ENNReal) (hp : p ≤ 2)
    (hf : ∀ n, MeasureTheory.MemLp (f n) 2 μ)
    (h2 : Tendsto (fun n => MeasureTheory.eLpNorm (f n) 2 μ)
      atTop (nhds 0)) :
    Tendsto (fun n => MeasureTheory.eLpNorm (f n) p μ)
      atTop (nhds 0) := by
  have hle (n : ℕ) : MeasureTheory.eLpNorm (f n) p μ ≤
      MeasureTheory.eLpNorm (f n) 2 μ := by
    have h := MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (f := f n) (μ := μ) hp (hf n).aestronglyMeasurable
    simpa using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n => MeasureTheory.eLpNorm (f n) p μ)
    (g := fun _ => 0) (h := fun n => MeasureTheory.eLpNorm (f n) 2 μ)
    tendsto_const_nhds h2
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · exact Filter.Eventually.of_forall hle

lemma tendsto_eLpNorm_of_tendsto_of_le {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (f : ℕ → X → ℂ) (p q : ENNReal) (hpq : p ≤ q)
    (hf : ∀ n, MeasureTheory.MemLp (f n) q μ)
    (hq : Tendsto (fun n => MeasureTheory.eLpNorm (f n) q μ)
      atTop (nhds 0)) :
    Tendsto (fun n => MeasureTheory.eLpNorm (f n) p μ)
      atTop (nhds 0) := by
  have hle (n : ℕ) : MeasureTheory.eLpNorm (f n) p μ ≤
      MeasureTheory.eLpNorm (f n) q μ := by
    have h := MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (f := f n) (μ := μ) hpq (hf n).aestronglyMeasurable
    simpa using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n => MeasureTheory.eLpNorm (f n) p μ)
    (g := fun _ => 0) (h := fun n => MeasureTheory.eLpNorm (f n) q μ)
    tendsto_const_nhds hq
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · exact Filter.Eventually.of_forall hle

set_option synthInstance.maxHeartbeats 400000 in
lemma tendsto_simple_ergodicAverage_condExp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (g : MeasureTheory.SimpleFunc M.X ℂ) (p : ENNReal)
    (_hp : 1 ≤ p) (hp_top : p < ⊤) :
    let mInv := MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
    Tendsto (fun n => MeasureTheory.eLpNorm
      (fun x => ergodicAverage M (⇑g) n x -
        MeasureTheory.condExp mInv M.μ (⇑g) x) p M.μ)
      atTop (nhds 0) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let mInv := MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  letI : MeasurableSpace M.X := M.measurableSpace
  have hm : mInv ≤ M.measurableSpace := by
    apply MeasurableSpace.generateFrom_le
    intro s hs
    exact hs.1
  letI : Fact (mInv ≤ M.measurableSpace) := ⟨hm⟩
  have hg2 := ErgodicAverageLp.simpleFunc_memLp_two M.μ g
  obtain ⟨gstar, hgstar2, _hginv, hconv2, hgce, _hgint, _hgerg⟩ :=
    MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM (⇑g) hg2
  let d : ℕ → M.X → ℂ := fun n x =>
    ergodicAverage M (⇑g) n x - MeasureTheory.condExp mInv M.μ (⇑g) x
  have hd2 (n : ℕ) : MeasureTheory.MemLp (d n) 2 M.μ :=
    (ErgodicAverageLp.ergodicAverage_memLp M hM 2 (⇑g) hg2 n).sub
      hg2.condExp
  have hconv2' : Tendsto (fun n => MeasureTheory.eLpNorm (d n) 2 M.μ)
      atTop (nhds 0) := by
    apply hconv2.congr'
    filter_upwards with n
    apply MeasureTheory.eLpNorm_congr_ae
    exact EventuallyEq.rfl.sub hgce.symm
  by_cases hp_le : p ≤ 2
  · exact tendsto_eLpNorm_of_tendsto_two_of_le_two M.μ d p hp_le hd2 hconv2'
  · have hp_ge : 2 ≤ p := le_of_not_ge hp_le
    let R : ℝ := ∑ y ∈ g.range, ‖y‖
    have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hgR (x : M.X) : ‖g x‖ ≤ R := by
      apply Finset.single_le_sum
      · intro y hy
        exact norm_nonneg y
      · rw [MeasureTheory.SimpleFunc.mem_range]
        exact ⟨x, rfl⟩
    have havgR (n : ℕ) (x : M.X) : ‖ergodicAverage M (⇑g) n x‖ ≤ R := by
      unfold ergodicAverage
      by_cases hn : n = 0
      · simp [hn, hR0]
      · simp only [hn, if_false, norm_mul, norm_inv, Complex.norm_natCast]
        calc
          (n : ℝ)⁻¹ * ‖∑ i ∈ Finset.range n, g ((M.T^[i]) x)‖ ≤
              (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
                ‖g ((M.T^[i]) x)‖ := by
            gcongr
            exact norm_sum_le _ _
          _ ≤ (n : ℝ)⁻¹ * ∑ _i ∈ Finset.range n, R := by
            gcongr with i hi
            exact hgR _
          _ = R := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            field_simp
    have hceNorm := complex_norm_condExp_le M.μ hm (⇑g)
      (hg2.integrable (by norm_num))
    have hmonoReal := MeasureTheory.condExp_mono (m := mInv)
      (hg2.integrable (by norm_num)).norm
        (MeasureTheory.integrable_const (μ := M.μ) R)
      (Filter.Eventually.of_forall hgR)
    have hconstReal := MeasureTheory.condExp_of_stronglyMeasurable hm
      (MeasureTheory.stronglyMeasurable_const :
        @MeasureTheory.StronglyMeasurable M.X ℝ _ mInv (fun _ => R))
      (MeasureTheory.integrable_const (μ := M.μ) R)
    have hceReal : ∀ᵐ x ∂M.μ,
        MeasureTheory.condExp mInv M.μ (fun x => ‖g x‖) x ≤ R := by
      filter_upwards [hmonoReal] with x hx
      simpa [hconstReal] using hx
    have hceR : ∀ᵐ x ∂M.μ,
        ‖MeasureTheory.condExp mInv M.μ (⇑g) x‖ ≤ R :=
      hceNorm.trans hceReal
    have hdR (n : ℕ) : ∀ᵐ x ∂M.μ, ‖d n x‖ₑ ≤ ENNReal.ofReal (2 * R) := by
      filter_upwards [hceR] with x hx
      rw [← ofReal_norm_eq_enorm]
      apply ENNReal.ofReal_le_ofReal
      exact (norm_sub_le _ _).trans (by linarith [havgR n x])
    exact tendsto_eLpNorm_of_tendsto_two_of_bound M.μ d p hp_ge hp_top
      (ENNReal.ofReal (2 * R)) ENNReal.ofReal_ne_top
      (fun n => (hd2 n).aestronglyMeasurable)
      hdR hconv2'

set_option synthInstance.maxHeartbeats 600000 in
lemma cauchySeq_ergodicAverage_toLp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (p : ENNReal) [Fact (1 ≤ p)] (hp : 1 ≤ p) (hp_top : p < ⊤)
    (hf : MeasureTheory.MemLp f p M.μ) :
    let havg : ∀ n, MeasureTheory.MemLp (ergodicAverage M f n) p M.μ :=
      fun n => ErgodicAverageLp.ergodicAverage_memLp M hM p f hf n
    CauchySeq (fun n => (havg n).toLp (ergodicAverage M f n)) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let mInv := MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  letI : MeasurableSpace M.X := M.measurableSpace
  have hm : mInv ≤ M.measurableSpace := by
    apply MeasurableSpace.generateFrom_le
    intro s hs
    exact hs.1
  letI : Fact (mInv ≤ M.measurableSpace) := ⟨hm⟩
  let havg : ∀ n, MeasureTheory.MemLp (ergodicAverage M f n) p M.μ :=
    fun n => ErgodicAverageLp.ergodicAverage_memLp M hM p f hf n
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let δ : ENNReal := ENNReal.ofReal (ε / 8)
  have hδ0 : δ ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    linarith
  obtain ⟨g, hfg, hgp⟩ := hf.exists_simpleFunc_eLpNorm_sub_lt
    (ne_of_lt hp_top) hδ0
  have hgconv := tendsto_simple_ergodicAverage_condExp M hM g p hp hp_top
  have hevent := (ENNReal.tendsto_nhds_zero.mp hgconv) δ (pos_iff_ne_zero.mpr hδ0)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨N, ?_⟩
  intro m hmN n hnN
  have hgm := hN m hmN
  have hgn := hN n hnN
  let ce : M.X → ℂ := MeasureTheory.condExp mInv M.μ (⇑g)
  let a : M.X → ℂ := fun x =>
    ergodicAverage M f m x - ergodicAverage M (⇑g) m x
  let b : M.X → ℂ := fun x => ergodicAverage M (⇑g) m x - ce x
  let c : M.X → ℂ := fun x => ce x - ergodicAverage M (⇑g) n x
  let d : M.X → ℂ := fun x =>
    ergodicAverage M (⇑g) n x - ergodicAverage M f n x
  have hma : MeasureTheory.AEStronglyMeasurable a M.μ :=
    ((havg m).sub
      (ErgodicAverageLp.ergodicAverage_memLp M hM p (⇑g) hgp m)).1
  have hmb : MeasureTheory.AEStronglyMeasurable b M.μ :=
    (ErgodicAverageLp.ergodicAverage_memLp M hM p (⇑g) hgp m).1.sub
      (MeasureTheory.stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
  have hmc : MeasureTheory.AEStronglyMeasurable c M.μ :=
    (MeasureTheory.stronglyMeasurable_condExp.mono hm).aestronglyMeasurable.sub
      (ErgodicAverageLp.ergodicAverage_memLp M hM p (⇑g) hgp n).1
  have hmd : MeasureTheory.AEStronglyMeasurable d M.μ :=
    (ErgodicAverageLp.ergodicAverage_memLp M hM p (⇑g) hgp n).1.sub
      (havg n).1
  have ha : MeasureTheory.eLpNorm a p M.μ ≤
      MeasureTheory.eLpNorm (f - ⇑g) p M.μ := by
    exact ErgodicAverageLp.eLpNorm_ergodicAverage_sub_le
      M hM p hp f (⇑g) hf hgp m
  have hd : MeasureTheory.eLpNorm d p M.μ ≤
      MeasureTheory.eLpNorm (f - ⇑g) p M.μ := by
    have h := ErgodicAverageLp.eLpNorm_ergodicAverage_sub_le
      M hM p hp (⇑g) f hgp hf n
    calc
      MeasureTheory.eLpNorm d p M.μ ≤
          MeasureTheory.eLpNorm ((⇑g) - f) p M.μ := h
      _ = MeasureTheory.eLpNorm (f - ⇑g) p M.μ := by
        rw [show ((⇑g) - f) = -(f - ⇑g) by funext x; simp]
        exact MeasureTheory.eLpNorm_neg (f - ⇑g) p M.μ
  have hc : MeasureTheory.eLpNorm c p M.μ =
      MeasureTheory.eLpNorm
        (fun x => ergodicAverage M (⇑g) n x - ce x) p M.μ := by
    rw [show c = -(fun x => ergodicAverage M (⇑g) n x - ce x) by
      funext x; simp [c]]
    exact MeasureTheory.eLpNorm_neg _ p M.μ
  have hfun : (fun x => ergodicAverage M f m x - ergodicAverage M f n x) =
      a + b + c + d := by
    funext x
    simp only [Pi.add_apply, a, b, c, d, ce]
    ring
  have htri : MeasureTheory.eLpNorm
      (fun x => ergodicAverage M f m x - ergodicAverage M f n x) p M.μ ≤
      MeasureTheory.eLpNorm a p M.μ + MeasureTheory.eLpNorm b p M.μ +
        MeasureTheory.eLpNorm c p M.μ + MeasureTheory.eLpNorm d p M.μ := by
    rw [hfun]
    exact (MeasureTheory.eLpNorm_add_le (hma.add hmb |>.add hmc) hmd hp).trans
      (add_le_add
        ((MeasureTheory.eLpNorm_add_le (hma.add hmb) hmc hp).trans
          (add_le_add (MeasureTheory.eLpNorm_add_le hma hmb hp) le_rfl))
        le_rfl)
  have hbound : MeasureTheory.eLpNorm
      (fun x => ergodicAverage M f m x - ergodicAverage M f n x) p M.μ <
      ENNReal.ofReal ε := by
    calc
      _ ≤ MeasureTheory.eLpNorm a p M.μ + MeasureTheory.eLpNorm b p M.μ +
          MeasureTheory.eLpNorm c p M.μ + MeasureTheory.eLpNorm d p M.μ := htri
      _ ≤ δ + δ + δ + δ := by
        rw [hc]
        have hbm : MeasureTheory.eLpNorm b p M.μ ≤ δ := by
          simpa [b, ce, mInv] using hgm
        have hcn : MeasureTheory.eLpNorm
            (fun x => ergodicAverage M (⇑g) n x - ce x) p M.μ ≤ δ := by
          simpa [ce, mInv] using hgn
        exact add_le_add (add_le_add (add_le_add (ha.trans hfg.le) hbm) hcn)
          (hd.trans hfg.le)
      _ = ENNReal.ofReal (ε / 2) := by
        have hδr : 0 ≤ ε / 8 := by linarith
        simp only [δ]
        rw [← ENNReal.ofReal_add hδr hδr,
          ← ENNReal.ofReal_add (add_nonneg hδr hδr) hδr,
          ← ENNReal.ofReal_add (add_nonneg (add_nonneg hδr hδr) hδr) hδr]
        apply (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).2
        ring
      _ < ENNReal.ofReal ε :=
        (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
  have hdist : dist ((havg m).toLp (ergodicAverage M f m))
      ((havg n).toLp (ergodicAverage M f n)) =
      (MeasureTheory.eLpNorm
        (fun x => ergodicAverage M f m x - ergodicAverage M f n x)
        p M.μ).toReal := by
    rw [dist_eq_norm]
    rw [← (havg m).toLp_sub (havg n)]
    exact MeasureTheory.Lp.norm_toLp _ ((havg m).sub (havg n))
  rw [hdist]
  have hnorm_top : MeasureTheory.eLpNorm
      (fun x => ergodicAverage M f m x - ergodicAverage M f n x) p M.μ ≠ ⊤ :=
    ne_of_lt (hbound.trans ENNReal.ofReal_lt_top)
  have hreal := (ENNReal.toReal_lt_toReal hnorm_top ENNReal.ofReal_ne_top).2 hbound
  simpa [ENNReal.toReal_ofReal (le_of_lt hε)] using hreal

end LpInterpolation
end Chapter02
