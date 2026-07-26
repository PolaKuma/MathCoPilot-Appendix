import Chapter02.Spectral.EigenfunctionLemmas

noncomputable section

namespace Chapter02
namespace Section05

universe u

set_option maxHeartbeats 800000 in

theorem eigenspaces_countable (M : System.{u}) :
    EigenspacesAndCountabilityStatement M := by
  intro hM
  constructor
  · exact same_eigenvalue_proportional M hM
  · rintro ⟨d, hdLp, hdense⟩
    letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
    let E := {lam : ℂ | Eigenvalue M lam}
    let f : E → M.X → ℂ := fun a => Classical.choose a.property
    have hf : ∀ a : E, Eigenfunction M a.1 (f a) := fun a =>
      Classical.choose_spec a.property
    let F : E → MeasureTheory.Lp ℂ 2 M.μ := fun a => (hf a).1.toLp (f a)
    have hFne (a : E) : F a ≠ 0 := by
      intro hzero
      apply (hf a).2.1
      apply ((hf a).1.toLp_eq_toLp_iff (MeasureTheory.memLp_const 0)).mp
      simpa [F] using hzero
    let U : E → MeasureTheory.Lp ℂ 2 M.μ := fun a =>
      ((‖F a‖ : ℂ)⁻¹) • F a
    have hUnorm (a : E) : ‖U a‖ = 1 := by
      simp [U, norm_smul, hFne a]
    have hForth (a b : E) (hab : a ≠ b) : inner ℂ (F a) (F b) = 0 := by
      rw [MeasureTheory.L2.inner_def]
      calc
        (∫ x, inner ℂ ((F a : MeasureTheory.Lp ℂ 2 M.μ) x)
            ((F b : MeasureTheory.Lp ℂ 2 M.μ) x) ∂M.μ) =
            ∫ x, f b x * star (f a x) ∂M.μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [(hf a).1.coeFn_toLp, (hf b).1.coeFn_toLp] with x hax hbx
          simp [F, hax, hbx, RCLike.inner_apply]
        _ = 0 := by
          apply eigen_orthogonal M hM b.1 a.1
          · intro hba
            apply hab
            exact Subtype.ext hba.symm
          · exact hf b
          · exact hf a
    have hUorth (a b : E) (hab : a ≠ b) : inner ℂ (U a) (U b) = 0 := by
      rw [show U a = ((‖F a‖ : ℂ)⁻¹) • F a by rfl,
        show U b = ((‖F b‖ : ℂ)⁻¹) • F b by rfl,
        inner_smul_left, inner_smul_right, hForth a b hab]
      simp
    have hUsep (a b : E) (hab : a ≠ b) : ‖U a - U b‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), hUnorm a, hUnorm b, hUorth a b hab]
      norm_num
    let D : ℕ → MeasureTheory.Lp ℂ 2 M.μ := fun n => (hdLp n).toLp (d n)
    have hclose (a : E) : ∃ n : ℕ, ‖U a - D n‖ < (1 / 4 : ℝ) := by
      obtain ⟨n, hn⟩ := hdense (⇑(U a)) (MeasureTheory.Lp.memLp (U a))
        (1 / 4 : ℝ) (by norm_num)
      refine ⟨n, ?_⟩
      have hnormeq : ‖U a - D n‖ =
          (MeasureTheory.eLpNorm (fun x => (U a) x - d n x) 2 M.μ).toReal := by
        let hdiffLp := (MeasureTheory.Lp.memLp (U a)).sub (hdLp n)
        have hdiff : U a - D n = hdiffLp.toLp (fun x => (U a) x - d n x) := by
          calc
            U a - D n =
                (MeasureTheory.Lp.memLp (U a)).toLp (⇑(U a)) -
                  (hdLp n).toLp (d n) := by
              rw [MeasureTheory.Lp.toLp_coeFn]
            _ = hdiffLp.toLp (fun x => (U a) x - d n x) := by
              exact ((MeasureTheory.Lp.memLp (U a)).toLp_sub (hdLp n)).symm
        rw [hdiff, MeasureTheory.Lp.norm_toLp]
      rw [hnormeq]
      have hreal := (ENNReal.toReal_lt_toReal (ne_top_of_lt hn) (by simp)).mpr hn
      simpa using hreal
    let index : E → ℕ := fun a => Classical.choose (hclose a)
    have hindexclose (a : E) : ‖U a - D (index a)‖ < (1 / 4 : ℝ) :=
      Classical.choose_spec (hclose a)
    have hindexinj : Function.Injective index := by
      intro a b habindex
      by_contra hab
      have htriangle : ‖U a - U b‖ < (1 / 2 : ℝ) := by
        calc
          ‖U a - U b‖ = ‖(U a - D (index a)) + (D (index b) - U b)‖ := by
            rw [habindex]
            congr 1
            abel
          _ ≤ ‖U a - D (index a)‖ + ‖D (index b) - U b‖ := norm_add_le _ _
          _ = ‖U a - D (index a)‖ + ‖U b - D (index b)‖ := by
            congr 1
            exact norm_sub_rev _ _
          _ < 1 / 4 + 1 / 4 := add_lt_add (hindexclose a) (hindexclose b)
          _ = 1 / 2 := by norm_num
      have hsquarelt : ‖U a - U b‖ ^ 2 < (1 / 2 : ℝ) ^ 2 := by
        exact pow_lt_pow_left₀ htriangle (norm_nonneg _) (by norm_num)
      rw [hUsep a b hab] at hsquarelt
      norm_num at hsquarelt
    exact Set.countable_iff_exists_injective.mpr ⟨index, hindexinj⟩

end Section05
end Chapter02
