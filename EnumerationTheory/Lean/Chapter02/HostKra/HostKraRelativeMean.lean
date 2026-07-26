import Chapter02.Recurrence.MultipleKhintchineUniform

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter02.HostKraRelativeMean

universe u

/-- The invariant part of an `L²` function, represented by the output of the
checked mean ergodic theorem.  This definition is independent of ergodicity
and is therefore available on Cartesian powers, where the invariant
sigma-algebra is generally nontrivial. -/
def invariantMeanLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) : Lp ℂ 2 M.μ :=
  let result :=
    MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM f hf
  result.choose_spec.1.toLp result.choose

lemma invariantMeanLp_coe
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    (fun x ↦ invariantMeanLp M hM f hf x) =ᵐ[M.μ]
      (MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM f hf).choose := by
  exact
    (MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM f hf).choose_spec
      |>.1.coeFn_toLp

/-- The checked mean-ergodic invariant mean is represented almost
everywhere by conditional expectation onto the invariant sigma-algebra. -/
theorem invariantMeanLp_ae_eq_condExp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    (fun x ↦ invariantMeanLp M hM f hf x) =ᵐ[M.μ]
      condExp
        (MeasurableSpace.generateFrom (invariantSigmaAlgebra M))
        M.μ f := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let result :=
    MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM f hf
  let fstar : M.X → ℂ := result.choose
  have hmean :
      (fun x ↦ invariantMeanLp M hM f hf x) =ᵐ[M.μ] fstar := by
    simpa only [result, fstar] using invariantMeanLp_coe M hM f hf
  have hresult :
      fstar =ᵐ[M.μ]
        condExp
          (MeasurableSpace.generateFrom (invariantSigmaAlgebra M))
          M.μ f := by
    exact result.choose_spec.2.2.2.1.symm
  exact hmean.trans hresult

/-- The invariant mean is exactly the orthogonal projection onto the fixed
subspace of the Koopman operator.  This identifies the analytic output of
the mean ergodic theorem with the Hilbert-space object used in the
Host--Kra recursion. -/
theorem invariantMeanLp_eq_fixedProjection
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    let D := MultipleKhintchineCharacteristic.KData M hM
    let S : Submodule ℂ (Lp ℂ 2 M.μ) :=
      LinearMap.eqLocus D.U (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)
    invariantMeanLp M hM f hf =
      (S.orthogonalProjection (hf.toLp f) : Lp ℂ 2 M.μ) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  dsimp only
  let mInv : MeasurableSpace M.X :=
    MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  let hm : mInv ≤ M.measurableSpace := by
    apply MeasurableSpace.generateFrom_le
    intro s hs
    exact hs.1
  let CE : Lp ℂ 2 M.μ :=
    ↑((condExpL2 (m := mInv) (m0 := M.measurableSpace)
      (μ := M.μ) ℂ ℂ hm) (hf.toLp f))
  have hproj :
      ((LinearMap.eqLocus
        (MultipleKhintchineCharacteristic.KData M hM).U
        (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)).orthogonalProjection
          (hf.toLp f)).1 = CE := by
    simpa only [CE, mInv, hm] using
      (MeanErgodicL2.fixedProjection_eq_condExpL2 M hM (hf.toLp f))
  change invariantMeanLp M hM f hf =
    ((LinearMap.eqLocus
      (MultipleKhintchineCharacteristic.KData M hM).U
      (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)).orthogonalProjection
        (hf.toLp f)).val
  rw [hproj]
  apply Lp.ext
  have hmean := invariantMeanLp_coe M hM f hf
  have hce :
      (fun x ↦ CE x) =ᵐ[M.μ] condExp mInv M.μ f := by
    simpa only [CE] using
      hf.condExpL2_ae_eq_condExp' hm
        (hf.integrable (by norm_num))
  have hresult :=
    (MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM f hf).choose_spec
      |>.2.2.2.1
  exact hmean.trans (hresult.symm.trans hce.symm)

/-- The correlation with the invariant mean is its Hilbert energy.  In
particular this quantity vanishes exactly when the fixed-space projection
vanishes. -/
theorem inner_invariantMeanLp_eq_self
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    @inner ℂ (Lp ℂ 2 M.μ) _ (hf.toLp f)
        (invariantMeanLp M hM f hf) =
      @inner ℂ (Lp ℂ 2 M.μ) _
        (invariantMeanLp M hM f hf)
        (invariantMeanLp M hM f hf) := by
  let D := MultipleKhintchineCharacteristic.KData M hM
  let S : Submodule ℂ (Lp ℂ 2 M.μ) :=
    LinearMap.eqLocus D.U (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)
  let F : Lp ℂ 2 M.μ := hf.toLp f
  let G : Lp ℂ 2 M.μ := (S.orthogonalProjection F).val
  have hmean : invariantMeanLp M hM f hf = G := by
    simpa only [D, S, F, G] using
      invariantMeanLp_eq_fixedProjection M hM f hf
  rw [hmean]
  have hGmem : G ∈ S :=
    (S.orthogonalProjection F).property
  have horth : F - G ∈ Sᗮ :=
    S.sub_starProjection_mem_orthogonal F
  have hz : @inner ℂ (Lp ℂ 2 M.μ) _ (F - G) G = 0 :=
    S.inner_left_of_mem_orthogonal hGmem horth
  calc
    @inner ℂ (Lp ℂ 2 M.μ) _ F G =
        @inner ℂ (Lp ℂ 2 M.μ) _ ((F - G) + G) G := by
          congr 1
          abel
    _ = @inner ℂ (Lp ℂ 2 M.μ) _ (F - G) G +
        @inner ℂ (Lp ℂ 2 M.μ) _ G G := inner_add_left _ _ _
    _ = _ := by rw [hz, zero_add]

theorem inner_invariantMeanLp_eq_zero_iff
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    @inner ℂ (Lp ℂ 2 M.μ) _ (hf.toLp f)
        (invariantMeanLp M hM f hf) = 0 ↔
      invariantMeanLp M hM f hf = 0 := by
  rw [inner_invariantMeanLp_eq_self M hM f hf, inner_self_eq_zero]

/-- Relative, translated-uniform mean ergodic theorem for correlations.
Unlike the ergodic specialization in `MultipleKhintchineUniform`, the limit
is the pairing with the invariant projection rather than the product of
ordinary means.  This is the form needed on Host--Kra Cartesian powers. -/
theorem uniform_shifted_cesaroFunctionCorrelations_invariantMean
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f g : M.X → ℂ) (hf : M.lpMember 2 f) (hg : M.lpMember 2 g) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
              functionCorrelation M f g (i + n))
          (@inner ℂ (Lp ℂ 2 M.μ) _
            (hg.toLp g) (invariantMeanLp M hM f hf)) < ε := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let result :=
    MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM f hf
  let fstar : M.X → ℂ := result.choose
  have hfstar : M.lpMember 2 fstar := result.choose_spec.1
  have hfinv : IsInvariantFunction M fstar :=
    result.choose_spec.2.1
  have hconv :
      Tendsto
        (fun n ↦ eLpNorm
          (fun x ↦ ergodicAverage M f n x - fstar x) 2 M.μ)
        atTop (nhds 0) :=
    result.choose_spec.2.2.1
  let havg (N : ℕ) :=
    ErgodicAverageLp.ergodicAverage_memLp M hM 2 f hf N
  let H (N : ℕ) : Lp ℂ 2 M.μ :=
    (havg N).toLp (ergodicAverage M f N)
  let Fstar : Lp ℂ 2 M.μ := invariantMeanLp M hM f hf
  let G : Lp ℂ 2 M.μ := hg.toLp g
  let D := MultipleKhintchineCharacteristic.KData M hM
  have hFstarCoe : (fun x ↦ Fstar x) =ᵐ[M.μ] fstar := by
    simpa only [Fstar, fstar, result] using
      invariantMeanLp_coe M hM f hf
  have hHF : Tendsto H atTop (nhds Fstar) := by
    simpa only [H, Fstar, invariantMeanLp, result, fstar] using
      (CorrelationMean.tendsto_toLp_of_tendsto_eLpNorm_sub M.μ
        (fun N ↦ ergodicAverage M f N) fstar havg hfstar hconv)
  have hFstarOne : D.U Fstar = Fstar := by
    apply Lp.ext
    have hiter :=
      MultipleKhintchineKronecker.koopmanData_iter_ae M hM 1 Fstar
    have hcoeShift :=
      hM.2.quasiMeasurePreserving.ae_eq_comp hFstarCoe
    filter_upwards [hiter, hcoeShift, hfinv, hFstarCoe] with
        x hiterx hshift hinvx hcoex
    simp only [Function.iterate_one] at hiterx
    rw [hiterx]
    have hshift' : Fstar (M.T x) = fstar (M.T x) := by
      simpa only [Function.comp_apply] using hshift
    change fstar (M.T x) = fstar x at hinvx
    exact hshift'.trans (hinvx.trans hcoex.symm)
  have hFstarInv (i : ℕ) : (D.U^[i]) Fstar = Fstar := by
    induction i with
    | zero => rfl
    | succ i ih =>
        rw [Function.iterate_succ_apply', ih, hFstarOne]
  have hinner_shifted (i N : ℕ) :
      @inner ℂ (Lp ℂ 2 M.μ) _ G ((D.U^[i]) (H N)) =
        if N = 0 then 0 else
          ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
            functionCorrelation M f g (i + n) := by
    rw [L2.inner_def]
    have hcoeG := hg.coeFn_toLp
    have hcoeH := (havg N).coeFn_toLp
    have hiterH :=
      MultipleKhintchineKronecker.koopmanData_iter_ae M hM i (H N)
    have hcoeHshift :=
      (hM.2.iterate i).quasiMeasurePreserving.ae_eq hcoeH
    have hfun :
        (fun x ↦ @inner ℂ ℂ _ (G x)
          ((show Lp ℂ 2 M.μ from (D.U^[i]) (H N)) x)) =ᵐ[M.μ]
          fun x ↦ ergodicAverage M f N ((M.T^[i]) x) * star (g x) := by
      filter_upwards [hcoeG, hiterH, hcoeHshift] with x hgx hix hHx
      simp only [RCLike.inner_apply, starRingEnd_apply]
      have hHx' :
          H N ((M.T^[i]) x) =
            ergodicAverage M f N ((M.T^[i]) x) := by
        simpa only [Function.comp_apply] using hHx
      rw [hgx, hix, hHx']
    rw [integral_congr_ae hfun]
    unfold ergodicAverage functionCorrelation
    by_cases hN : N = 0
    · simp [hN]
    · simp only [hN, if_false]
      simp_rw [mul_assoc, Finset.sum_mul]
      rw [integral_const_mul]
      rw [integral_finset_sum]
      · congr 1
        apply Finset.sum_congr rfl
        intro n hn
        apply integral_congr_ae
        filter_upwards with x
        rw [← Function.iterate_add_apply]
        rw [Nat.add_comm n i]
      · intro n hn
        have hfshift :=
          hf.comp_measurePreserving (hM.2.iterate (n + i))
        simpa only [Function.comp_apply, ← Function.iterate_add_apply] using
          hfshift.integrable_mul hg.star
  rw [Metric.tendsto_atTop] at hHF
  intro ε hε
  let δ : ℝ := ε / (‖G‖ + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨N₀, hN₀⟩ := hHF δ hδ
  refine eventually_atTop.2 ⟨N₀, ?_⟩
  intro N hN i
  have hclose : ‖H N - Fstar‖ < δ := by
    simpa [dist_eq_norm] using hN₀ N hN
  have hiterSub :
      (D.U^[i]) (H N - Fstar) =
        (D.U^[i]) (H N) - (D.U^[i]) Fstar := by
    induction i with
    | zero => simp
    | succ k ih =>
        simp only [Function.iterate_succ_apply']
        rw [ih]
        exact map_sub D.U _ _
  have hnorm :
      ‖(show Lp ℂ 2 M.μ from (D.U^[i]) (H N)) - Fstar‖ =
        ‖H N - Fstar‖ := by
    calc
      _ = ‖(show Lp ℂ 2 M.μ from (D.U^[i]) (H N)) -
          (show Lp ℂ 2 M.μ from (D.U^[i]) Fstar)‖ := by
            rw [hFstarInv i]
      _ = ‖(show Lp ℂ 2 M.μ from
          (D.U^[i]) (H N - Fstar))‖ := by rw [hiterSub]
      _ = ‖H N - Fstar‖ :=
        AlmostPeriodicIsometry.iterate_norm
          D
          (fun X ↦
            (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map X)
          (H N - Fstar) i
  rw [← hinner_shifted i N, dist_eq_norm, ← inner_sub_right]
  calc
    ‖@inner ℂ (Lp ℂ 2 M.μ) _
        G ((show Lp ℂ 2 M.μ from
          (D.U^[i]) (H N)) - Fstar)‖ ≤
        ‖G‖ * ‖(show Lp ℂ 2 M.μ from
          (D.U^[i]) (H N)) - Fstar‖ :=
      norm_inner_le_norm _ _
    _ = ‖G‖ * ‖H N - Fstar‖ := by rw [hnorm]
    _ ≤ ‖G‖ * δ := by
      exact mul_le_mul_of_nonneg_left hclose.le (norm_nonneg G)
    _ < ε := by
      dsimp [δ]
      have hden : 0 < ‖G‖ + 1 := by positivity
      rw [div_eq_mul_inv]
      calc
        ‖G‖ * (ε * (‖G‖ + 1)⁻¹) =
            ε * (‖G‖ / (‖G‖ + 1)) := by ring
        _ < ε * 1 := by
          apply mul_lt_mul_of_pos_left _ hε
          rw [div_lt_one hden]
          linarith
        _ = ε := mul_one _

end Chapter02.HostKraRelativeMean
