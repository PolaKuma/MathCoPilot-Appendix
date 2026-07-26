import Chapter04.Spectral.LebesgueSpectrum

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter04.LebesgueSpectrum

universe u

theorem zeroMean_correlations_tendsto_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (U : MeasureIntegerActionData M) (fbase : ℕ → M.X → ℂ)
    (hbasis : (∀ i, M.lpMember 2 (fbase i) ∧ ∫ x, fbase i x ∂M.μ = 0) ∧
      (∀ i j m n, l2Inner M
        (Chapter01.koopman (U.act m) (fbase i))
        (Chapter01.koopman (U.act n) (fbase j)) =
          if i = j ∧ m = n then 1 else 0) ∧
      IsTotalInZeroMeanL2 M
        {g | ∃ i n, g = Chapter01.koopman (U.act n) (fbase i)})
    (f g : M.X → ℂ) (hf : M.lpMember 2 f) (hg : M.lpMember 2 g)
    (hf0 : ∫ x, f x ∂M.μ = 0) (hg0 : ∫ x, g x ∂M.μ = 0) :
    Tendsto (fun n => Chapter02.functionCorrelation M f g n) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let a : ℝ := (MeasureTheory.eLpNorm f 2 M.μ).toReal
  let b : ℝ := (MeasureTheory.eLpNorm g 2 M.μ).toReal
  let C : ℝ := a + b + 1
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hC : 0 < C := by dsimp [C]; linarith
  let δ : ℝ := min 1 (ε / (2 * C))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) hC))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδq : δ ≤ ε / (2 * C) := min_le_right _ _
  have hδC : δ * C ≤ ε / 2 := by
    apply (mul_le_mul_of_nonneg_right hδq hC.le).trans_eq
    field_simp
  have hC1 : 1 ≤ C := by dsimp [C]; linarith
  have hδhalf : δ ≤ ε / 2 := by nlinarith
  obtain ⟨s, hsV, c, hfs⟩ := hbasis.2.2 f hf hf0 δ hδ
  obtain ⟨t, htV, d, hgt⟩ := hbasis.2.2 g hg hg0 δ hδ
  let F : M.X → ℂ := combination s c
  let G : M.X → ℂ := combination t d
  have hFLp : M.lpMember 2 F :=
    combination_memLp M s c (fun q hq => by
      rcases hsV hq with ⟨i, z, rfl⟩
      exact (hbasis.1 i).1.comp_measurePreserving (U.measure_preserving z))
  have hGLp : M.lpMember 2 G :=
    combination_memLp M t d (fun q hq => by
      rcases htV hq with ⟨i, z, rfl⟩
      exact (hbasis.1 i).1.comp_measurePreserving (U.measure_preserving z))
  have hef : M.lpMember 2 (fun x => f x - F x) := hf.sub hFLp
  have heg : M.lpMember 2 (fun x => g x - G x) := hg.sub hGLp
  have hfsR : (MeasureTheory.eLpNorm (fun x => f x - F x) 2 M.μ).toReal < δ := by
    have ht := (ENNReal.toReal_lt_toReal hef.2.ne (by simp)).mpr hfs
    simpa [ENNReal.toReal_ofReal hδ.le] using ht
  have hgtR : (MeasureTheory.eLpNorm (fun x => g x - G x) 2 M.μ).toReal < δ := by
    have ht := (ENNReal.toReal_lt_toReal heg.2.ne (by simp)).mpr hgt
    simpa [ENNReal.toReal_ofReal hδ.le] using ht
  have hFnorm : (MeasureTheory.eLpNorm F 2 M.μ).toReal ≤
      a + (MeasureTheory.eLpNorm (fun x => f x - F x) 2 M.μ).toReal := by
    have hsub := hf.toLp_sub hFLp
    have hvec : hFLp.toLp F = hf.toLp f - hef.toLp (fun x => f x - F x) := by
      have hsub' : hef.toLp (fun x => f x - F x) =
          hf.toLp f - hFLp.toLp F := by
        simpa only [Pi.sub_apply] using hsub
      rw [hsub']
      abel
    calc
      (MeasureTheory.eLpNorm F 2 M.μ).toReal = ‖hFLp.toLp F‖ :=
        (MeasureTheory.Lp.norm_toLp F hFLp).symm
      _ = ‖hf.toLp f - hef.toLp (fun x => f x - F x)‖ := by rw [hvec]
      _ ≤ ‖hf.toLp f‖ + ‖hef.toLp (fun x => f x - F x)‖ := norm_sub_le _ _
      _ = _ := by rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp]
  choose isS msS hsrep using fun q : {q // q ∈ s} => hsV q.2
  choose itS mtS htrep using fun q : {q // q ∈ t} => htV q.2
  let is : (M.X → ℂ) → ℕ := fun q => if hq : q ∈ s then isS ⟨q, hq⟩ else 0
  let ms : (M.X → ℂ) → ℤ := fun q => if hq : q ∈ s then msS ⟨q, hq⟩ else 0
  let it : (M.X → ℂ) → ℕ := fun q => if hq : q ∈ t then itS ⟨q, hq⟩ else 0
  let mt : (M.X → ℂ) → ℤ := fun q => if hq : q ∈ t then mtS ⟨q, hq⟩ else 0
  have hsrep' (q : M.X → ℂ) (hq : q ∈ s) :
      q = Chapter01.koopman (U.act (ms q)) (fbase (is q)) := by
    simpa [is, ms, hq] using hsrep ⟨q, hq⟩
  have htrep' (q : M.X → ℂ) (hq : q ∈ t) :
      q = Chapter01.koopman (U.act (mt q)) (fbase (it q)) := by
    simpa [it, mt, hq] using htrep ⟨q, hq⟩
  obtain ⟨N, hN⟩ := finite_orbit_combinations_eventually_zero M hM U fbase
    (fun i => (hbasis.1 i).1) hbasis.2.1 s t c d is ms it mt hsrep' htrep'
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  have hzero := hN n hn
  have hdiff := functionCorrelation_difference M hM f g F G hf hg hFLp hGLp n
  have heq : Chapter02.functionCorrelation M f g n =
      Chapter02.functionCorrelation M (fun x => f x - F x) g n +
        Chapter02.functionCorrelation M F (fun x => g x - G x) n := by
    rw [hzero] at hdiff
    simpa only [sub_zero] using hdiff
  rw [heq]
  calc
    ‖Chapter02.functionCorrelation M (fun x => f x - F x) g n +
        Chapter02.functionCorrelation M F (fun x => g x - G x) n‖ ≤
      ‖Chapter02.functionCorrelation M (fun x => f x - F x) g n‖ +
        ‖Chapter02.functionCorrelation M F (fun x => g x - G x) n‖ := norm_add_le _ _
    _ ≤ (MeasureTheory.eLpNorm (fun x => f x - F x) 2 M.μ).toReal * b +
        (MeasureTheory.eLpNorm F 2 M.μ).toReal *
          (MeasureTheory.eLpNorm (fun x => g x - G x) 2 M.μ).toReal :=
      add_le_add (norm_functionCorrelation_le M hM _ _ hef hg n)
        (norm_functionCorrelation_le M hM _ _ hFLp heg n)
    _ < ε := by
      have hFnorm' : (MeasureTheory.eLpNorm F 2 M.μ).toReal < a + δ :=
        lt_of_le_of_lt hFnorm (by simpa [add_comm] using add_lt_add_left hfsR a)
      nlinarith [ENNReal.toReal_nonneg (a := MeasureTheory.eLpNorm F 2 M.μ),
        ENNReal.toReal_nonneg (a := MeasureTheory.eLpNorm (fun x => f x - F x) 2 M.μ),
        ENNReal.toReal_nonneg (a := MeasureTheory.eLpNorm (fun x => g x - G x) 2 M.μ)]

end Chapter04.LebesgueSpectrum
