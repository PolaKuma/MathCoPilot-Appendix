import Chapter02.Ergodic.ErgodicBridge

noncomputable section

open Filter

namespace Chapter02
namespace Section05

universe u

lemma eigen_norm_modulus (M : System.{u}) (hM : IsErgodic M)
    (lam : ℂ) (f : M.X → ℂ) (hf : Eigenfunction M lam f) :
    ‖lam‖ = 1 ∧ ∃ c : ℝ, 0 < c ∧
      (fun x => ‖f x‖) =ᵐ[M.μ] fun _ => c := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  have hcomp : MeasureTheory.eLpNorm (f ∘ M.T) 2 M.μ =
      MeasureTheory.eLpNorm f 2 M.μ :=
    MeasureTheory.eLpNorm_comp_measurePreserving hf.1.1 hM.1.2
  have hscale : MeasureTheory.eLpNorm (lam • f) 2 M.μ =
      MeasureTheory.eLpNorm f 2 M.μ := by
    calc
      MeasureTheory.eLpNorm (lam • f) 2 M.μ =
          MeasureTheory.eLpNorm (Chapter01.koopman M.T f) 2 M.μ :=
        MeasureTheory.eLpNorm_congr_ae hf.2.2.symm
      _ = MeasureTheory.eLpNorm f 2 M.μ := by
        simpa only [Chapter01.koopman, Function.comp_def] using hcomp
  rw [MeasureTheory.eLpNorm_const_smul] at hscale
  have hLzero : MeasureTheory.eLpNorm f 2 M.μ ≠ 0 := by
    intro hz
    apply hf.2.1
    exact (MeasureTheory.eLpNorm_eq_zero_iff hf.1.1 (by norm_num)).mp hz
  have hLtop : MeasureTheory.eLpNorm f 2 M.μ ≠ ⊤ := hf.1.2.ne
  have hLpos : 0 < (MeasureTheory.eLpNorm f 2 M.μ).toReal :=
    ENNReal.toReal_pos hLzero hLtop
  have hscaleReal := congrArg ENNReal.toReal hscale
  have hlam : ‖lam‖ = 1 := by
    simp only [ENNReal.toReal_mul, enorm_eq_nnnorm, ENNReal.coe_toReal] at hscaleReal
    have hscaleReal' : ‖lam‖ * (MeasureTheory.eLpNorm f 2 M.μ).toReal =
        (MeasureTheory.eLpNorm f 2 M.μ).toReal := by
      simpa using hscaleReal
    nlinarith
  refine ⟨hlam, ?_⟩
  have hmodInv : (fun x => ‖f x‖) ∘ M.T =ᵐ[M.μ] fun x => ‖f x‖ := by
    filter_upwards [hf.2.2] with x hx
    change ‖f (M.T x)‖ = ‖f x‖
    change f (M.T x) = lam * f x at hx
    rw [hx, norm_mul, hlam, one_mul]
  obtain ⟨c, hc⟩ :=
    (ErgodicBridge.isErgodic_to_mathlibErgodic M hM).ae_eq_const_of_ae_eq_comp_ae
      hf.1.1.norm hmodInv
  have hcpos : 0 < c := by
    have hcnonneg : 0 ≤ c := by
      obtain ⟨x, hx⟩ := hc.exists
      simpa only [Function.const_apply, hx] using norm_nonneg (f x)
    refine lt_of_le_of_ne hcnonneg ?_
    intro hczero
    apply hf.2.1
    filter_upwards [hc] with x hx
    apply norm_eq_zero.mp
    simpa [hczero] using hx
  exact ⟨c, hcpos, hc⟩

lemma eigen_orthogonal (M : System.{u}) (hM : IsErgodic M)
    (lam xi : ℂ) (hne : lam ≠ xi) (f g : M.X → ℂ)
    (hf : Eigenfunction M lam f) (hg : Eigenfunction M xi g) :
    ∫ x, f x * star (g x) ∂M.μ = 0 := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  let F := hf.1.toLp f
  let G := hg.1.toLp g
  have hinner := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) G F
  have hint : MeasureTheory.Integrable (fun x => f x * star (g x)) M.μ := by
    apply hinner.congr
    filter_upwards [hf.1.coeFn_toLp, hg.1.coeFn_toLp] with x hfx hgx
    simp [F, G, hfx, hgx, RCLike.inner_apply]
  let h : M.X → ℂ := fun x => f x * star (g x)
  have hgsm : MeasureTheory.AEStronglyMeasurable h
      (MeasureTheory.Measure.map M.T M.μ) := by
    rw [hM.1.2.map_eq]
    exact hint.aestronglyMeasurable
  have hmap := MeasureTheory.integral_map
    (μ := M.μ) (φ := M.T) (f := h)
    hM.1.2.measurable.aemeasurable hgsm
  rw [hM.1.2.map_eq] at hmap
  have htrans : (fun x => h (M.T x)) =ᵐ[M.μ]
      fun x => (lam * star xi) * h x := by
    filter_upwards [hf.2.2, hg.2.2] with x hfx hgx
    change f (M.T x) * star (g (M.T x)) =
      (lam * star xi) * (f x * star (g x))
    change f (M.T x) = lam * f x at hfx
    change g (M.T x) = xi * g x at hgx
    rw [hfx, hgx, star_mul]
    ring
  have hIeq : (∫ x, h x ∂M.μ) =
      (lam * star xi) * ∫ x, h x ∂M.μ := by
    calc
      (∫ x, h x ∂M.μ) = ∫ x, h (M.T x) ∂M.μ := hmap
      _ = ∫ x, (lam * star xi) * h x ∂M.μ :=
        MeasureTheory.integral_congr_ae htrans
      _ = (lam * star xi) * ∫ x, h x ∂M.μ :=
        MeasureTheory.integral_const_mul (lam * star xi) h
  have hxi : ‖xi‖ = 1 := (eigen_norm_modulus M hM xi g hg).1
  have hxinonzero : xi ≠ 0 := by
    intro hz
    simp [hz] at hxi
  have hstar : star xi = xi⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hxi]
    norm_num
  have hfactor : lam * star xi ≠ 1 := by
    rw [hstar]
    intro heq
    apply hne
    calc
      lam = (lam * xi⁻¹) * xi := by simp [hxinonzero]
      _ = 1 * xi := by rw [heq]
      _ = xi := one_mul _
  change (∫ x, h x ∂M.μ) = 0
  by_contra hzero
  apply hfactor
  apply mul_right_cancel₀ hzero
  simpa using hIeq.symm

lemma same_eigenvalue_proportional (M : System.{u}) (hM : IsErgodic M)
    (lam : ℂ) (f g : M.X → ℂ)
    (hf : Eigenfunction M lam f) (hg : Eigenfunction M lam g) :
    ∃ c : ℂ, f =ᵐ[M.μ] fun x => c * g x := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  obtain ⟨hlam, _, _, _⟩ := eigen_norm_modulus M hM lam f hf
  obtain ⟨_, cg, hcgpos, hcg⟩ := eigen_norm_modulus M hM lam g hg
  let h : M.X → ℂ := fun x => f x * star (g x)
  have hhmeas : MeasureTheory.AEStronglyMeasurable h M.μ :=
    hf.1.1.mul hg.1.1.star
  have hhinv : h ∘ M.T =ᵐ[M.μ] h := by
    filter_upwards [hf.2.2, hg.2.2] with x hfx hgx
    change f (M.T x) * star (g (M.T x)) = f x * star (g x)
    change f (M.T x) = lam * f x at hfx
    change g (M.T x) = lam * g x at hgx
    rw [hfx, hgx, star_mul]
    calc
      (lam * f x) * (star (g x) * star lam) =
      (lam * star lam) * (f x * star (g x)) := by ring
      _ = f x * star (g x) := by
        change (lam * (starRingEnd ℂ) lam) * (f x * star (g x)) = _
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hlam]
        norm_num
  obtain ⟨d, hd⟩ :=
    (ErgodicBridge.isErgodic_to_mathlibErgodic M hM).ae_eq_const_of_ae_eq_comp_ae
      hhmeas hhinv
  refine ⟨d / (cg ^ 2 : ℂ), ?_⟩
  filter_upwards [hd, hcg] with x hdx hcgx
  have hcgne : (cg : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hcgpos
  have hnormsq : g x * star (g x) = (cg ^ 2 : ℂ) := by
    change g x * (starRingEnd ℂ) (g x) = (cg ^ 2 : ℂ)
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hcgx]
    norm_num
  change f x * star (g x) = d at hdx
  apply (mul_right_cancel₀ hcgne)
  apply (mul_right_cancel₀ hcgne)
  calc
    f x * (cg : ℂ) * (cg : ℂ) = f x * (cg ^ 2 : ℂ) := by ring
    _ = f x * (g x * star (g x)) := by rw [hnormsq]
    _ = (f x * star (g x)) * g x := by ring
    _ = d * g x := by rw [hdx]
    _ = ((d / (cg ^ 2 : ℂ)) * g x) * (cg : ℂ) * (cg : ℂ) := by
      field_simp

lemma eigenvalues_group_property (M : System.{u}) (hM : IsErgodic M) :
    1 ∈ {lam : ℂ | Eigenvalue M lam} ∧
      ∀ lam xi : ℂ, Eigenvalue M lam → Eigenvalue M xi →
        Eigenvalue M (lam * xi⁻¹) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  constructor
  · change Eigenvalue M 1
    refine ⟨fun _ => (1 : ℂ), MeasureTheory.memLp_const 1, ?_, ?_⟩
    · intro hzero
      have := hzero.exists
      simp at this
    · filter_upwards [] with x
      simp [Chapter01.koopman]
  · intro lam xi hlam hxi
    obtain ⟨f, hfLp, hfne, hftrans⟩ := hlam
    obtain ⟨g, hgLp, hgne, hgtrans⟩ := hxi
    have hf : Eigenfunction M lam f := ⟨hfLp, hfne, hftrans⟩
    have hg : Eigenfunction M xi g := ⟨hgLp, hgne, hgtrans⟩
    obtain ⟨hlamnorm, cf, hcfpos, hcf⟩ := eigen_norm_modulus M hM lam f hf
    obtain ⟨hxinorm, cg, hcgpos, hcg⟩ := eigen_norm_modulus M hM xi g hg
    let h : M.X → ℂ := fun x => f x * star (g x)
    have hhmeas : MeasureTheory.AEStronglyMeasurable h M.μ :=
      hfLp.1.mul hgLp.1.star
    have hhbound : ∀ᵐ x ∂M.μ, ‖h x‖ ≤ cf * cg := by
      filter_upwards [hcf, hcg] with x hcfx hcgx
      change ‖f x * star (g x)‖ ≤ cf * cg
      rw [norm_mul, norm_star, hcfx, hcgx]
    have hhLp : MeasureTheory.MemLp h 2 M.μ :=
      (MeasureTheory.memLp_top_of_bound hhmeas (cf * cg) hhbound).mono_exponent
        (by simp)
    have hhne : ¬ h =ᵐ[M.μ] 0 := by
      intro hz
      have hmodzero : (∀ᵐ x ∂M.μ, ‖h x‖ = 0) := by
        filter_upwards [hz] with x hx
        rw [hx]
        norm_num
      have hmodpos : (∀ᵐ x ∂M.μ, ‖h x‖ = cf * cg) := by
        filter_upwards [hcf, hcg] with x hcfx hcgx
        change ‖f x * star (g x)‖ = cf * cg
        rw [norm_mul, norm_star, hcfx, hcgx]
      obtain ⟨x, hxzero, hxpos⟩ := (hmodzero.and hmodpos).exists
      rw [hxzero] at hxpos
      exact (mul_pos hcfpos hcgpos).ne' hxpos.symm
    have hxine : xi ≠ 0 := by
      intro hx
      simp [hx] at hxinorm
    have hxistar : star xi = xi⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hxinorm]
      norm_num
    refine ⟨h, hhLp, hhne, ?_⟩
    filter_upwards [hftrans, hgtrans] with x hfx hgx
    change f (M.T x) * star (g (M.T x)) =
      (lam * xi⁻¹) * (f x * star (g x))
    change f (M.T x) = lam * f x at hfx
    change g (M.T x) = xi * g x at hgx
    rw [hfx, hgx, star_mul, hxistar]
    ring

end Section05
end Chapter02
