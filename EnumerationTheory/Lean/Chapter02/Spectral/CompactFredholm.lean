import Chapter02.Common
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

noncomputable section

open Classical

namespace Chapter02.CompactFredholm

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {T : X →L[𝕜] X} {μ : 𝕜}

open Module End

open Filter Topology in
theorem antilipschitz_of_not_hasEigenvalue
    (hT : IsCompactOperator T) (hμ : μ ≠ 0)
    (h : ¬ HasEigenvalue (T : End 𝕜 X) μ) :
    ∃ K, AntilipschitzWith K (T - μ • 1 : X →L[𝕜] X) := by
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  contrapose! h
  replace hK : ∀ K > 0, ∃ x, ‖(T - μ • 1) x‖ < K * ‖x‖ := h
  replace hK : ∃ c > 0, ∀ ε > 0, ∃ x,
      ‖x‖ ≤ 1 ∧ c ≤ ‖x‖ ∧ ‖(T - μ • 1) x‖ < ε := by
    obtain ⟨C, hC⟩ := NormedField.exists_one_lt_norm 𝕜
    refine ⟨‖C‖⁻¹, by positivity, fun ε hε ↦ ?_⟩
    obtain ⟨x, hx⟩ := hK ε (by positivity)
    have : x ≠ 0 := by aesop
    obtain ⟨η, hη, h₁, h₂, h₃⟩ :=
      rescale_to_shell hC (ε := 1) (by simp) this
    refine ⟨η • x, h₁.le, by simpa using h₂, ?_⟩
    grw [map_smul, norm_smul, hx, mul_left_comm, ← norm_smul]
    linear_combination ε * h₁
  obtain ⟨c, hc₀, hc⟩ := hK
  obtain ⟨φ, hφ_anti, hφ_pos, hφ⟩ :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have (n : ℕ) : ∃ x, ‖x‖ ≤ 1 ∧ c ≤ ‖x‖ ∧
      ‖(T - μ • 1) x‖ < φ n := hc (φ n) (hφ_pos n)
  choose x hx_norm_upper hx_norm_lower hx_bound using this
  have hx_lim : Tendsto (fun n ↦ (T - μ • 1) (x n))
      atTop (𝓝 0) := squeeze_zero_norm (by grind) hφ
  let y_ (n : ℕ) : X := T (x n)
  have hy_lower : ∃ d > 0, ∀ᶠ n in atTop, d ≤ ‖y_ n‖ := by
    refine ⟨(‖μ‖ * c) / 2, by positivity, ?_⟩
    filter_upwards
      [hφ.eventually_le_const
        (show (‖μ‖ * c) / 2 > 0 by positivity)] with n hn
    have h₁ : ‖T (x n) - μ • x n‖ < φ n := by
      simpa using hx_bound n
    have h₂ : ‖μ‖ * ‖x n‖ ≤
        ‖T (x n)‖ + ‖T (x n) - μ • x n‖ := by
      simpa [norm_smul] using
        norm_le_norm_add_norm_sub (T (x n)) (μ • x n)
    linear_combination h₂ + h₁ + hn + ‖μ‖ * hx_norm_lower n
  obtain ⟨K, hK, hK'⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y, hyK, ψ, hψ, hψy⟩ :=
    hK.tendsto_subseq (x := y_)
      (fun n ↦ hK' ⟨x n, by simp [*], rfl⟩)
  have hy_lim : Tendsto (fun n ↦ (T - μ • 1) (y_ n))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      T.continuous.continuousAt.tendsto.comp hx_lim
  have hy_eigen' : (T - μ • 1) y = 0 := by
    apply tendsto_nhds_unique _ (hy_lim.comp hψ.tendsto_atTop)
    have : Continuous (T - μ • 1 : X →L[𝕜] X) := by fun_prop
    exact this.continuousAt.tendsto.comp hψy
  have hy_ne : y ≠ 0 := by
    obtain ⟨d, hd₀, hd⟩ := hy_lower
    rintro rfl
    suffices ∀ᶠ n : ℕ in atTop, False by
      rwa [eventually_const] at this
    have hψynorm : Tendsto (fun n ↦ ‖y_ (ψ n)‖)
        atTop (𝓝 0) := by
      simpa using hψy.norm
    have hsmall : ∀ᶠ n in atTop, ‖y_ (ψ n)‖ < d :=
      (tendsto_order.1 hψynorm).2 d hd₀
    filter_upwards
      [hψ.tendsto_atTop.eventually hd, hsmall]
      using by grind
  have : HasEigenvector (T : End 𝕜 X) μ y := by
    simpa [hasEigenvector_iff, mem_genEigenspace_one, hy_ne,
      sub_eq_zero] using hy_eigen'
  exact hasEigenvalue_of_hasEigenvector this

private theorem exists_seq
    {S : End 𝕜 X} (hS_not_surj : ¬ (S : X → X).Surjective)
    (hS_anti : Topology.IsClosedEmbedding S)
    {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R) :
    ∃ f : ℕ → X,
      (∀ n, 1 ≤ ‖f n‖) ∧
      (∀ n, ‖f n‖ ≤ R) ∧
      (∀ n, f n ∈ (S ^ n).range) ∧
      (∀ n, ∀ y ∈ (S ^ (n + 1)).range, 1 ≤ ‖f n - y‖) := by
  let V (n : ℕ) : Submodule 𝕜 X := S.iterateRange n
  have hV_succ (n : ℕ) :
      V (n + 1) = (V n).map (S : End 𝕜 X) :=
    LinearMap.iterateRange_succ
  have hV_closed (n : ℕ) : IsClosed (V n : Set X) := by
    induction n with
    | zero => simp [V, Module.End.one_eq_id]
    | succ n ih =>
      rw [hV_succ]
      apply hS_anti.isClosedMap _ ih
  have x (n : ℕ) : ∃ x ∈ V n, 1 ≤ ‖x‖ ∧ ‖x‖ ≤ R ∧
      ∀ y ∈ V (n + 1), 1 ≤ ‖x - y‖ := by
    have h₁ : IsClosed
        ((V (n + 1)).comap (V n).subtype : Set (V n)) := by
      exact (hV_closed (n + 1)).preimage continuous_subtype_val
    have h₂ : ∃ x : V n,
        x ∉ (V (n + 1)).comap (V n).subtype := by
      simpa [iterate_succ, V,
        (iterate_injective hS_anti.injective n).eq_iff,
        Function.Surjective] using hS_not_surj
    obtain ⟨⟨x, hx⟩, hxn, hxy⟩ :=
      riesz_lemma_of_norm_lt hc hR h₁ h₂
    simp only [Submodule.mem_comap, Submodule.subtype_apply,
      Subtype.forall] at hxn hxy
    exact ⟨x, hx, by simpa using hxy 0, hxn,
      fun y hy ↦ hxy y
        (S.iterateRange.monotone (by simp) hy) hy⟩
  choose x hxv hxn hxn' hxy using x
  exact ⟨x, hxn, hxn', hxv, hxy⟩

variable [CompleteSpace X]

theorem hasEigenvalue_or_mem_resolventSet
    (hT : IsCompactOperator T) (hμ : μ ≠ 0) :
    HasEigenvalue (T : End 𝕜 X) μ ∨
      μ ∈ resolventSet 𝕜 T := by
  by_contra!
  obtain ⟨h₁, h₂⟩ := this
  let S := T - μ • 1
  obtain ⟨K, hK : AntilipschitzWith K S⟩ :=
    antilipschitz_of_not_hasEigenvalue hT hμ h₁
  replace h₂ : ¬ (S : X → X).Bijective := by
    rw [spectrum.mem_resolventSet_iff, ← IsUnit.neg_iff,
      ContinuousLinearMap.isUnit_iff_bijective] at h₂
    have hS :
        -(algebraMap 𝕜 (X →L[𝕜] X) μ - T) = S := by
      ext x
      simp [S]
    rwa [hS] at h₂
  replace h₂ : ¬ (S : X → X).Surjective := by
    grind [Function.Bijective, hK.injective]
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨f, hf_norm_lower, hf_norm_upper, hf_mem, hf_far⟩ :=
    exists_seq h₂ (hK.isClosedEmbedding S.uniformContinuous)
      hc (R := ‖c‖ + 1) (by simp)
  replace hf_mem {n m : ℕ} (h : m ≤ n) :
      f n ∈ ((S : End 𝕜 X) ^ m).range :=
    (S : End 𝕜 X).iterateRange.monotone (by lia) (hf_mem _)
  have hf_mem' {n m : ℕ} (h : m ≤ n) :
      S (f n) ∈ ((S : End 𝕜 X) ^ (m + 1)).range := by
    rw [iterate_succ', LinearMap.range_comp]
    exact ⟨f n, hf_mem h, rfl⟩
  have hp_lt : ∀ {m n : ℕ}, m < n →
      ‖μ‖ ≤ ‖T (f m) - T (f n)‖ := by
    intro m n hmn
    let u : X :=
      μ⁻¹ • (S (f n) - S (f m) + μ • f n)
    have hu : μ • (f m - u) =
        T (f m) - T (f n) := by
      rw [smul_sub, smul_inv_smul₀ hμ]
      simp [S]
      linear_combination (norm := module)
    have : u ∈ ((S : End 𝕜 X) ^ (m + 1)).range := by
      apply Submodule.smul_mem _ _ (Submodule.add_mem _ _ _)
      · exact Submodule.sub_mem _
          (hf_mem' hmn.le) (hf_mem' le_rfl)
      · exact Submodule.smul_mem _ μ (hf_mem hmn)
    grw [← hu, norm_smul, mul_comm, ← hf_far _ u this, one_mul]
  have hp : Pairwise fun x₁ x₂ ↦
      ‖μ‖ ≤ ‖T (f x₁) - T (f x₂)‖ := by
    intro m n hmn
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · exact hp_lt hlt
    · simpa [norm_sub_rev] using hp_lt hgt
  obtain ⟨K, hK, hK'⟩ :=
    hT.image_closedBall_subset_compact (‖c‖ + 1)
  obtain ⟨y, hyK, ψ, hψ, hψy⟩ :=
    hK.tendsto_subseq
      (fun n ↦ hK' ⟨f n, by simp [*], rfl⟩)
  replace hψy := hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hψy
  obtain ⟨N, hN⟩ := hψy ‖μ‖ (by positivity)
  have : ‖T (f (ψ (N + 1))) -
      T (f (ψ N))‖ < ‖μ‖ := by
    simpa [dist_eq_norm_sub] using hN (N + 1)
  refine this.not_ge (hp ?_)
  simp [hψ.injective.eq_iff]

theorem hasEigenvalue_iff_mem_spectrum
    (hT : IsCompactOperator T) (hμ : μ ≠ 0) :
    HasEigenvalue (T : End 𝕜 X) μ ↔
      μ ∈ spectrum 𝕜 T := by
  have hspectrum :
      spectrum 𝕜 T =
        spectrum 𝕜 (T : Module.End 𝕜 X) := by
    ext z
    rw [spectrum.mem_iff, spectrum.mem_iff,
      ContinuousLinearMap.isUnit_iff_bijective,
      Module.End.isUnit_iff]
    change
      ¬ Function.Bijective (fun x : X ↦ z • x - T x) ↔
        ¬ Function.Bijective (fun x : X ↦ z • x - T x)
    rfl
  constructor
  · intro hμ'
    rw [hspectrum]
    exact hμ'.mem_spectrum
  · exact
      (hasEigenvalue_or_mem_resolventSet hT hμ).resolve_right

end Chapter02.CompactFredholm
