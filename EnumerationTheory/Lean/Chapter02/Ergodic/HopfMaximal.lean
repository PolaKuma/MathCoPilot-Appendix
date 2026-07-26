import Chapter02.Common
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open Filter MeasureTheory

namespace Chapter02
namespace HopfMaximal

variable {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}

lemma integral_le_of_eLpNorm_one_le {f g : X → ℝ}
    (hf : MeasureTheory.Integrable f μ) (hg : MeasureTheory.Integrable g μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g)
    (hfg : MeasureTheory.eLpNorm f 1 μ ≤ MeasureTheory.eLpNorm g 1 μ) :
    ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ := by
  have hf_eq : (∫ x, f x ∂μ) = (MeasureTheory.eLpNorm f 1 μ).toReal := by
    rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
    rw [← MeasureTheory.integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hf0] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
  have hg_eq : (∫ x, g x ∂μ) = (MeasureTheory.eLpNorm g 1 μ).toReal := by
    rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
    rw [← MeasureTheory.integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hg0] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
  rw [hf_eq, hg_eq]
  exact ENNReal.toReal_mono (MeasureTheory.memLp_one_iff_integrable.mpr hg).2.ne hfg

lemma positive_linear_map_mono
    (U : (X → ℝ) → X → ℝ)
    (hlin : ∀ f g : X → ℝ, ∀ a b : ℝ,
      U (fun x => a * f x + b * g x) = fun x => a * U f x + b * U g x)
    (hpos : ∀ f, (∀ᵐ x ∂μ, 0 ≤ f x) → ∀ᵐ x ∂μ, 0 ≤ U f x)
    {f g : X → ℝ} (hfg : f ≤ᵐ[μ] g) : U f ≤ᵐ[μ] U g := by
  have hdiff : ∀ᵐ x ∂μ, 0 ≤ (fun x => g x - f x) x := by
    filter_upwards [hfg] with x hx
    exact sub_nonneg.mpr hx
  have hUdiff := hpos (fun x => g x - f x) hdiff
  have hlinear : U (fun x => g x - f x) = fun x => U g x - U f x := by
    simpa [sub_eq_add_neg] using hlin g f 1 (-1)
  filter_upwards [hUdiff] with x hx
  rw [hlinear] at hx
  exact sub_nonneg.mp hx

lemma positivePart_monotone
    (U : (X → ℝ) → X → ℝ)
    (hlin : ∀ f g : X → ℝ, ∀ a b : ℝ,
      U (fun x => a * f x + b * g x) = fun x => a * U f x + b * U g x)
    (hpos : ∀ f, (∀ᵐ x ∂μ, 0 ≤ f x) → ∀ᵐ x ∂μ, 0 ≤ U f x)
    (f : X → ℝ) : ∀ n,
      (fun x => max (maximalRec U f n x) 0) ≤ᵐ[μ]
        (fun x => max (maximalRec U f (n + 1) x) 0) := by
  intro n
  induction n with
  | zero =>
      have hUp := hpos (fun x => max (f x) 0)
        (Eventually.of_forall fun x => le_max_right _ _)
      filter_upwards [hUp] with x hx
      simp only [maximalRec]
      exact max_le_max_right _ (by linarith)
  | succ n ih =>
      have hUmono := positive_linear_map_mono U hlin hpos ih
      filter_upwards [hUmono] with x hx
      change max (f x + U (fun y => max (maximalRec U f n y) 0) x) 0 ≤
        max (f x + U (fun y => max (maximalRec U f (n + 1) y) 0) x) 0
      apply max_le_max_right
      linarith

lemma maximalRec_integrable
    (U : (X → ℝ) → X → ℝ)
    (hcontract : ∀ f, MeasureTheory.Integrable f μ →
      MeasureTheory.Integrable (U f) μ ∧
        MeasureTheory.eLpNorm (U f) 1 μ ≤ MeasureTheory.eLpNorm f 1 μ)
    (f : X → ℝ) (hf : MeasureTheory.Integrable f μ) :
    ∀ n, MeasureTheory.Integrable (maximalRec U f n) μ := by
  intro n
  induction n with
  | zero => exact hf
  | succ n ih =>
      exact hf.add (hcontract _ ih.pos_part).1

theorem positiveContractionMaximal (M : System) :
    PositiveContractionMaximalStatement M := by
  intro U hU f hf N
  let r : ℕ → M.X → ℝ := maximalRec U f
  let p : ℕ → M.X → ℝ := fun n x => max (r n x) 0
  have hr_int : ∀ n, MeasureTheory.Integrable (r n) M.μ := by
    exact maximalRec_integrable U hU.2.2 f hf
  have hp_int : ∀ n, MeasureTheory.Integrable (p n) M.μ :=
    fun n => (hr_int n).pos_part
  have hp0 : ∀ n, 0 ≤ᵐ[M.μ] p n :=
    fun n => Eventually.of_forall fun x => le_max_right _ _
  have hUp_int : ∀ n, MeasureTheory.Integrable (U (p n)) M.μ :=
    fun n => (hU.2.2 _ (hp_int n)).1
  have hUp0 : ∀ n, 0 ≤ᵐ[M.μ] U (p n) :=
    fun n => hU.2.1 _ (hp0 n)
  have hpmono : ∀ n, p n ≤ᵐ[M.μ] p (n + 1) := by
    exact positivePart_monotone U hU.1 hU.2.1 f
  let A : Set M.X := {x | 0 < r N x}
  have hA : NullMeasurableSet A M.μ := by
    exact nullMeasurableSet_lt
      aemeasurable_const (hr_int N).aestronglyMeasurable.aemeasurable
  refine ⟨hA, ?_⟩
  cases N with
  | zero =>
      rw [← MeasureTheory.integral_indicator₀ hA]
      apply MeasureTheory.integral_nonneg
      intro x
      simp only [Set.indicator, A, r, maximalRec]
      split_ifs with hx
      · exact hx.le
      · exact le_rfl
  | succ n =>
      have hp_integral_mono :
          (∫ x, p n x ∂M.μ) ≤ ∫ x, p (n + 1) x ∂M.μ :=
        MeasureTheory.integral_mono_ae (hp_int n) (hp_int (n + 1)) (hpmono n)
      have hU_integral :
          (∫ x, U (p n) x ∂M.μ) ≤ ∫ x, p n x ∂M.μ := by
        exact integral_le_of_eLpNorm_one_le (hUp_int n) (hp_int n)
          (hUp0 n) (hp0 n) (hU.2.2 _ (hp_int n)).2
      have hU_set :
          (∫ x in A, U (p n) x ∂M.μ) ≤ ∫ x, U (p n) x ∂M.μ :=
        MeasureTheory.setIntegral_le_integral (hUp_int n) (hUp0 n)
      have hp_set_eq :
          (∫ x in A, p (n + 1) x ∂M.μ) = ∫ x, p (n + 1) x ∂M.μ := by
        rw [← MeasureTheory.integral_indicator₀ hA]
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        simp only [Set.indicator, A, p]
        split_ifs with hx
        · rfl
        · rw [max_eq_right]
          exact le_of_not_gt hx
      have hpoint : ∀ x ∈ A, f x = p (n + 1) x - U (p n) x := by
        intro x hx
        have hrpos : 0 < r (n + 1) x := hx
        have hp_eq : p (n + 1) x = r (n + 1) x := max_eq_left hrpos.le
        simp only [r, maximalRec] at hp_eq
        linarith
      calc
        (∫ x in A, f x ∂M.μ) =
            ∫ x in A, (p (n + 1) x - U (p n) x) ∂M.μ := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards [MeasureTheory.ae_restrict_mem₀ hA] with x hx
              exact hpoint x hx
        _ = (∫ x in A, p (n + 1) x ∂M.μ) -
            ∫ x in A, U (p n) x ∂M.μ := by
              rw [MeasureTheory.integral_sub]
              · exact (hp_int (n + 1)).integrableOn
              · exact (hUp_int n).integrableOn
        _ = (∫ x, p (n + 1) x ∂M.μ) -
            ∫ x in A, U (p n) x ∂M.μ := by rw [hp_set_eq]
        _ ≥ (∫ x, p (n + 1) x ∂M.μ) -
            ∫ x, U (p n) x ∂M.μ := sub_le_sub_left hU_set _
        _ ≥ (∫ x, p (n + 1) x ∂M.μ) -
            ∫ x, p n x ∂M.μ := sub_le_sub_left hU_integral _
        _ ≥ 0 := sub_nonneg.mpr hp_integral_mono

def orbitSum (M : System) (f : M.X → ℝ) (n : ℕ) (x : M.X) : ℝ :=
  ∑ i ∈ Finset.range n, f ((M.T^[i]) x)

lemma orbitSum_succ (M : System) (f : M.X → ℝ) (n : ℕ) (x : M.X) :
    orbitSum M f (n + 1) x = f x + orbitSum M f n (M.T x) := by
  rw [orbitSum, Finset.sum_range_succ']
  simp only [orbitSum, Function.iterate_add_apply, Function.iterate_one]
  simp [add_comm]

lemma orbitSum_le_maximalRec_koopman (M : System) (f : M.X → ℝ) :
    ∀ N k x, 0 < k → k ≤ N + 1 →
      orbitSum M f k x ≤ maximalRec (fun g => g ∘ M.T) f N x := by
  intro N
  induction N with
  | zero =>
      intro k x hk hkN
      have hk1 : k = 1 := by omega
      subst k
      simp [orbitSum, maximalRec]
  | succ N ih =>
      intro k x hk hkN
      rcases k with _ | k
      · omega
      rw [orbitSum_succ]
      simp only [maximalRec, Function.comp_apply]
      by_cases hk0 : k = 0
      · subst k
        have hmax : 0 ≤ max (maximalRec (fun g => g ∘ M.T) f N (M.T x)) 0 :=
          le_max_right _ _
        simp only [orbitSum, Finset.sum_range_zero]
        linarith
      · have hkle : k ≤ N + 1 := by omega
        have htail := ih k (M.T x) (Nat.pos_of_ne_zero hk0) hkle
        have hmax := htail.trans (le_max_left
          (maximalRec (fun g => g ∘ M.T) f N (M.T x)) 0)
        linarith

lemma maximalRec_koopman_eq_orbitSum_of_pos (M : System) (f : M.X → ℝ) :
    ∀ N x, 0 < maximalRec (fun g => g ∘ M.T) f N x →
      ∃ k : ℕ, 0 < k ∧ k ≤ N + 1 ∧
        orbitSum M f k x = maximalRec (fun g => g ∘ M.T) f N x := by
  intro N
  induction N with
  | zero =>
      intro x hx
      refine ⟨1, by omega, by omega, ?_⟩
      simp [orbitSum, maximalRec]
  | succ N ih =>
      intro x hx
      simp only [maximalRec, Function.comp_apply] at hx ⊢
      by_cases htail : 0 < maximalRec (fun g => g ∘ M.T) f N (M.T x)
      · obtain ⟨k, hk, hkN, hkeq⟩ := ih (M.T x) htail
        refine ⟨k + 1, by omega, by omega, ?_⟩
        rw [orbitSum_succ, hkeq, max_eq_left htail.le]
      · have hnonpos : maximalRec (fun g => g ∘ M.T) f N (M.T x) ≤ 0 :=
          le_of_not_gt htail
        refine ⟨1, by omega, by omega, ?_⟩
        simp [orbitSum, max_eq_right hnonpos]

lemma maximalRec_koopman_pos_iff (M : System) (f : M.X → ℝ) (N : ℕ) (x : M.X) :
    0 < maximalRec (fun g => g ∘ M.T) f N x ↔
      ∃ k : ℕ, 0 < k ∧ k ≤ N + 1 ∧ 0 < orbitSum M f k x := by
  constructor
  · intro h
    obtain ⟨k, hk, hkN, hkeq⟩ := maximalRec_koopman_eq_orbitSum_of_pos M f N x h
    exact ⟨k, hk, hkN, hkeq.symm ▸ h⟩
  · rintro ⟨k, hk, hkN, hsum⟩
    exact hsum.trans_le (orbitSum_le_maximalRec_koopman M f N k x hk hkN)

theorem maximalErgodic (M : System) : MaximalErgodicStatement M := by
  intro hM f hf α
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let g : M.X → ℝ := fun x => f x - α
  let U : (M.X → ℝ) → M.X → ℝ := fun q => q ∘ M.T
  have hg : Integrable g M.μ := hf.sub (integrable_const α)
  have hU : IsPositiveL1Contraction M U := by
    constructor
    · intro q r a b
      funext x
      rfl
    constructor
    · intro q hq
      exact hM.2.quasiMeasurePreserving.tendsto_ae.eventually hq
    · intro q hq
      constructor
      · exact hM.2.integrable_comp_of_integrable hq
      · exact (eLpNorm_comp_measurePreserving hq.aestronglyMeasurable hM.2).le
  let A : ℕ → Set M.X := fun N => {x | 0 < maximalRec U g N x}
  let B : Set M.X := {x | ∃ n : ℕ, 0 < n ∧ α < realErgodicAverage M f n x}
  have hfinite := positiveContractionMaximal M U hU g hg
  have hA_null : ∀ N, NullMeasurableSet (A N) M.μ := fun N => (hfinite N).1
  have hAineq : ∀ N,
      α * realMeasure M (A N) ≤ ∫ x in A N, f x ∂M.μ := by
    intro N
    have hnonneg := (hfinite N).2
    have hsplit : (∫ x in A N, g x ∂M.μ) =
        (∫ x in A N, f x ∂M.μ) - α * realMeasure M (A N) := by
      rw [show g = fun x => f x - α by rfl, MeasureTheory.integral_sub]
      · simp [realMeasure, MeasureTheory.Measure.real, mul_comm]
      · exact hf.integrableOn
      · exact (integrable_const α).integrableOn
    rw [hsplit] at hnonneg
    linarith
  have horbit_g (n : ℕ) (x : M.X) :
      orbitSum M g n x = orbitSum M f n x - (n : ℝ) * α := by
    simp only [orbitSum, g, Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_range]
    simp [nsmul_eq_mul]
  have havg_iff (n : ℕ) (hn : 0 < n) (x : M.X) :
      α < realErgodicAverage M f n x ↔ 0 < orbitSum M g n x := by
    rw [horbit_g]
    simp only [realErgodicAverage, if_neg (Nat.ne_of_gt hn), orbitSum]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    constructor <;> intro h
    · have := (lt_inv_mul_iff₀ hnR).mp h
      nlinarith
    · have h' : (n : ℝ) * α < ∑ i ∈ Finset.range n, f ((M.T^[i]) x) := by
        nlinarith
      have := (lt_inv_mul_iff₀ hnR).mpr h'
      exact this
  have hA_char (N : ℕ) (x : M.X) :
      x ∈ A N ↔ ∃ n : ℕ, 0 < n ∧ n ≤ N + 1 ∧
        α < realErgodicAverage M f n x := by
    rw [show (x ∈ A N) = (0 < maximalRec U g N x) by rfl]
    rw [show U = fun q => q ∘ M.T by rfl,
      maximalRec_koopman_pos_iff M g N x]
    constructor
    · rintro ⟨n, hn, hnN, hsum⟩
      exact ⟨n, hn, hnN, (havg_iff n hn x).2 hsum⟩
    · rintro ⟨n, hn, hnN, havg⟩
      exact ⟨n, hn, hnN, (havg_iff n hn x).1 havg⟩
  have hA_mono : Monotone A := by
    intro N K hNK x hx
    obtain ⟨n, hn, hnN, havg⟩ := (hA_char N x).1 hx
    exact (hA_char K x).2 ⟨n, hn, hnN.trans (Nat.add_le_add_right hNK 1), havg⟩
  have hUnion : (⋃ N, A N) = B := by
    ext x
    simp only [Set.mem_iUnion, B, Set.mem_setOf_eq]
    constructor
    · rintro ⟨N, hx⟩
      obtain ⟨n, hn, hnN, havg⟩ := (hA_char N x).1 hx
      exact ⟨n, hn, havg⟩
    · rintro ⟨n, hn, havg⟩
      exact ⟨n, (hA_char n x).2 ⟨n, hn, by omega, havg⟩⟩
  have hBnull : NullMeasurableSet B M.μ := by
    rw [← hUnion]
    exact NullMeasurableSet.iUnion hA_null
  refine ⟨hBnull, ?_⟩
  let C : ℕ → Set M.X := fun N =>
    ⋃ k : Fin (N + 1), toMeasurable M.μ (A k)
  have hCmeas : ∀ N, MeasurableSet (C N) := by
    intro N
    exact MeasurableSet.iUnion fun k => measurableSet_toMeasurable _ _
  have hCA : ∀ N, C N =ᵐ[M.μ] A N := by
    intro N
    have hall : ∀ᵐ x ∂M.μ, ∀ k : Fin (N + 1),
        (x ∈ toMeasurable M.μ (A k) ↔ x ∈ A k) := by
      exact Filter.eventually_all.mpr fun k =>
        (hA_null k).toMeasurable_ae_eq.mono fun x hx => iff_of_eq hx
    filter_upwards [hall] with x hx
    apply propext
    change x ∈ C N ↔ x ∈ A N
    rw [show C N = ⋃ k : Fin (N + 1), toMeasurable M.μ (A k) by rfl]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hxk⟩
      exact hA_mono (Nat.le_of_lt_succ k.isLt) ((hx k).1 hxk)
    · intro hxN
      let kN : Fin (N + 1) := ⟨N, Nat.lt_succ_self N⟩
      exact ⟨kN, (hx kN).2 hxN⟩
  have hCmono : Monotone C := by
    intro N K hNK x hx
    change x ∈ C N at hx
    rw [show C N = ⋃ k : Fin (N + 1), toMeasurable M.μ (A k) by rfl] at hx
    rw [show C K = ⋃ k : Fin (K + 1), toMeasurable M.μ (A k) by rfl]
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨k, hxk⟩ := hx
    let k' : Fin (K + 1) := ⟨k, lt_of_lt_of_le k.isLt (Nat.add_le_add_right hNK 1)⟩
    exact ⟨k', hxk⟩
  have hCB : (⋃ N, C N) =ᵐ[M.μ] B := by
    have hall : ∀ᵐ x ∂M.μ, ∀ N, (x ∈ C N ↔ x ∈ A N) := by
      exact ae_all_iff.mpr fun N =>
        (hCA N).mono fun x hx => iff_of_eq hx
    filter_upwards [hall] with x hx
    apply propext
    rw [← hUnion]
    change x ∈ ⋃ N, C N ↔ x ∈ ⋃ N, A N
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨N, hxN⟩
      exact ⟨N, (hx N).1 hxN⟩
    · rintro ⟨N, hxN⟩
      exact ⟨N, (hx N).2 hxN⟩
  have hCineq : ∀ N,
      α * realMeasure M (C N) ≤ ∫ x in C N, f x ∂M.μ := by
    intro N
    have hmeasure : realMeasure M (C N) = realMeasure M (A N) := by
      unfold realMeasure
      rw [measure_congr (hCA N)]
    have hint : (∫ x in C N, f x ∂M.μ) = ∫ x in A N, f x ∂M.μ := by
      rw [show M.μ.restrict (C N) = M.μ.restrict (A N) from
        MeasureTheory.Measure.restrict_congr_set (hCA N)]
    rw [hmeasure, hint]
    exact hAineq N
  have hμlimE : Tendsto (fun N => M.μ (C N)) atTop
      (nhds (M.μ (⋃ N, C N))) := tendsto_measure_iUnion_atTop hCmono
  have hμlim : Tendsto (fun N => realMeasure M (C N)) atTop
      (nhds (realMeasure M B)) := by
    have hrealC : Tendsto (fun N => realMeasure M (C N)) atTop
        (nhds (M.μ (⋃ N, C N)).toReal) :=
      (ENNReal.continuousAt_toReal (measure_ne_top M.μ _)).tendsto.comp hμlimE
    convert hrealC using 1
    unfold realMeasure
    rw [measure_congr hCB]
  have hleft : Tendsto (fun N => α * realMeasure M (C N)) atTop
      (nhds (α * realMeasure M B)) := tendsto_const_nhds.mul hμlim
  have hintlim : Tendsto (fun N => ∫ x in C N, f x ∂M.μ) atTop
      (nhds (∫ x in B, f x ∂M.μ)) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone
      hCmeas hCmono hf.integrableOn
    convert h using 1
    rw [show M.μ.restrict (⋃ N, C N) = M.μ.restrict B from
      MeasureTheory.Measure.restrict_congr_set hCB]
  exact le_of_tendsto_of_tendsto' hleft hintlim (fun N => hCineq N)

lemma norm_ergodicAverage_le_realErgodicAverage_norm
    (M : System) (f : M.X → ℂ) (n : ℕ) (x : M.X) :
    ‖ergodicAverage M f n x‖ ≤
      realErgodicAverage M (fun y => ‖f y‖) n x := by
  by_cases hn : n = 0
  · simp [ergodicAverage, realErgodicAverage, hn]
  · have hn0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    have hsum : ‖∑ i ∈ Finset.range n, f ((M.T^[i]) x)‖ ≤
        ∑ i ∈ Finset.range n, ‖f ((M.T^[i]) x)‖ := norm_sum_le _ _
    simp only [ergodicAverage, realErgodicAverage, hn, if_false, norm_mul,
      norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hsum hn0

theorem weakTypeMaximal (M : System) : WeakTypeMaximalInequalityStatement M := by
  intro hM f hf α hα
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let g : M.X → ℝ := fun x => ‖f x‖
  let E : Set M.X := {x | ∃ n : ℕ, 0 < n ∧ α < ‖ergodicAverage M f n x‖}
  let B : Set M.X := {x | ∃ n : ℕ, 0 < n ∧ α < realErgodicAverage M g n x}
  have hg : Integrable g M.μ := (hf.integrable (by norm_num)).norm
  have hmax := maximalErgodic M hM g hg α
  have hEB : E ⊆ B := by
    intro x hx
    obtain ⟨n, hn, hnorm⟩ := hx
    exact ⟨n, hn, hnorm.trans_le
      (norm_ergodicAverage_le_realErgodicAverage_norm M f n x)⟩
  have hμEB : realMeasure M E ≤ realMeasure M B := by
    exact MeasureTheory.measureReal_mono hEB (measure_ne_top M.μ B)
  have hset_le : (∫ x in B, g x ∂M.μ) ≤ ∫ x, g x ∂M.μ :=
    MeasureTheory.setIntegral_le_integral hg
      (Eventually.of_forall fun x => norm_nonneg (f x))
  have hreal : α * realMeasure M E ≤
      (MeasureTheory.eLpNorm f 1 M.μ).toReal := by
    have hmax' := hmax.2
    have hchain : α * realMeasure M E ≤ ∫ x, g x ∂M.μ :=
      (mul_le_mul_of_nonneg_left hμEB hα.le).trans (hmax'.trans hset_le)
    have hnormeq : (∫ x, g x ∂M.μ) =
        (MeasureTheory.eLpNorm f 1 M.μ).toReal := by
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
      rw [← MeasureTheory.integral_norm_eq_lintegral_enorm
        hf.aestronglyMeasurable]
    rwa [hnormeq] at hchain
  apply (ENNReal.toReal_le_toReal (measure_ne_top M.μ E) (by finiteness)).mp
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hα.le]
  rw [ENNReal.toReal_ofReal (MeasureTheory.eLpNorm f 1 M.μ).toReal_nonneg]
  have hαne : α ≠ 0 := ne_of_gt hα
  exact (le_div_iff₀ hα).2 (by simpa [mul_comm] using hreal)

end HopfMaximal
end Chapter02
