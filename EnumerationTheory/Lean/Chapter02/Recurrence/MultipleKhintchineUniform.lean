import Chapter02.Recurrence.MultipleKhintchineCharacteristic

open Classical Filter Set MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate

noncomputable section

namespace Chapter02.MultipleKhintchineUniform

universe u

/-- In an ergodic system, the Cesàro convergence of two-function
correlations to the product of means is uniform in the starting time of the
averaging interval.  This is the uniform mean-ergodic input needed for
syndetic, rather than merely positive-density, multiple recurrence. -/
theorem ergodic_uniform_shifted_cesaroFunctionCorrelations
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (hErg : IsErgodic M)
    (f g : M.X → ℂ) (hf : M.lpMember 2 f) (hg : M.lpMember 2 g) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
              functionCorrelation M f g (i + n))
          (productOfMeans M f g) < ε := by
  letI : IsProbabilityMeasure M.μ := hM.1
  obtain ⟨fstar, hfstar, _hinv, hconv, _hce, _hint, hconst⟩ :=
    MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM f hf
  have hconst' : fstar =ᵐ[M.μ] fun _ ↦ ∫ x, f x ∂M.μ :=
    hconst hErg
  let havg (N : ℕ) :=
    ErgodicAverageLp.ergodicAverage_memLp M hM 2 f hf N
  let H (N : ℕ) : MeasureTheory.Lp ℂ 2 M.μ :=
    (havg N).toLp (ergodicAverage M f N)
  let Fstar : MeasureTheory.Lp ℂ 2 M.μ := hfstar.toLp fstar
  let G : MeasureTheory.Lp ℂ 2 M.μ := hg.toLp g
  let D := MultipleKhintchineCharacteristic.KData M hM
  have hHF : Tendsto H atTop (nhds Fstar) :=
    CorrelationMean.tendsto_toLp_of_tendsto_eLpNorm_sub M.μ
      (fun N ↦ ergodicAverage M f N) fstar havg hfstar hconv
  have hFcoe :
      (fun x ↦ Fstar x) =ᵐ[M.μ] fun _ ↦ ∫ y, f y ∂M.μ :=
    hfstar.coeFn_toLp.trans hconst'
  have hFstarInv (i : ℕ) : (D.U^[i]) Fstar = Fstar := by
    apply MeasureTheory.Lp.ext
    filter_upwards [
      MultipleKhintchineKronecker.koopmanData_iter_ae M hM i Fstar,
      hFcoe,
      (hM.2.iterate i).quasiMeasurePreserving.ae_eq hFcoe] with
        x hiter hx hxi
    have hxi' :
        Fstar ((M.T^[i]) x) = ∫ y, f y ∂M.μ := by
      simpa only [Function.comp_apply] using hxi
    rw [hiter, hxi', hx]
  have hinner_limit :
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G Fstar =
        productOfMeans M f g := by
    rw [MeasureTheory.L2.inner_def]
    have hcoeG := hg.coeFn_toLp
    have hcoeF := hfstar.coeFn_toLp
    calc
      ∫ x, @inner ℂ ℂ _ (G x) (Fstar x) ∂M.μ =
          ∫ x, (∫ y, f y ∂M.μ) * star (g x) ∂M.μ := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [hcoeG, hcoeF, hconst'] with x hgx hfx hcx
            simp only [RCLike.inner_apply, starRingEnd_apply]
            rw [hgx, hfx, hcx]
      _ = (∫ y, f y ∂M.μ) * ∫ x, star (g x) ∂M.μ := by
            rw [MeasureTheory.integral_const_mul]
      _ = productOfMeans M f g := by
            unfold productOfMeans
            change (∫ y, f y ∂M.μ) * ∫ x, conj (g x) ∂M.μ =
              (∫ x, f x ∂M.μ) * conj (∫ x, g x ∂M.μ)
            rw [integral_conj]
  have hinner_shifted (i N : ℕ) :
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G ((D.U^[i]) (H N)) =
        if N = 0 then 0 else
          ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
            functionCorrelation M f g (i + n) := by
    rw [MeasureTheory.L2.inner_def]
    have hcoeG := hg.coeFn_toLp
    have hcoeH := (havg N).coeFn_toLp
    have hiterH :=
      MultipleKhintchineKronecker.koopmanData_iter_ae M hM i (H N)
    have hcoeHshift :=
      (hM.2.iterate i).quasiMeasurePreserving.ae_eq hcoeH
    have hfun :
        (fun x ↦ @inner ℂ ℂ _ (G x)
          ((show MeasureTheory.Lp ℂ 2 M.μ from (D.U^[i]) (H N)) x)) =ᵐ[M.μ]
          fun x ↦ ergodicAverage M f N ((M.T^[i]) x) * star (g x) := by
      filter_upwards [hcoeG, hiterH, hcoeHshift] with x hgx hix hHx
      simp only [RCLike.inner_apply, starRingEnd_apply]
      have hHx' :
          H N ((M.T^[i]) x) =
            ergodicAverage M f N ((M.T^[i]) x) := by
        simpa only [Function.comp_apply] using hHx
      rw [hgx, hix, hHx']
    rw [MeasureTheory.integral_congr_ae hfun]
    unfold ergodicAverage functionCorrelation
    by_cases hN : N = 0
    · simp [hN]
    · simp only [hN, if_false]
      simp_rw [mul_assoc, Finset.sum_mul]
      rw [MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_finset_sum]
      · congr 1
        apply Finset.sum_congr rfl
        intro n hn
        apply MeasureTheory.integral_congr_ae
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
  refine Filter.eventually_atTop.2 ⟨N₀, ?_⟩
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
      ‖(show MeasureTheory.Lp ℂ 2 M.μ from (D.U^[i]) (H N)) -
          Fstar‖ = ‖H N - Fstar‖ := by
    calc
      _ = ‖(show MeasureTheory.Lp ℂ 2 M.μ from (D.U^[i]) (H N)) -
          (show MeasureTheory.Lp ℂ 2 M.μ from (D.U^[i]) Fstar)‖ := by
            rw [hFstarInv i]
      _ = ‖(show MeasureTheory.Lp ℂ 2 M.μ from
          (D.U^[i]) (H N - Fstar))‖ := by rw [hiterSub]
      _ = ‖H N - Fstar‖ :=
        AlmostPeriodicIsometry.iterate_norm
          D
          (fun X ↦
            (MeasureTheory.Lp.compMeasurePreservingₗᵢ
              ℂ M.T hM.2).norm_map X)
          (H N - Fstar) i
  rw [← hinner_shifted i N, ← hinner_limit, dist_eq_norm,
    ← inner_sub_right]
  calc
    ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        G ((show MeasureTheory.Lp ℂ 2 M.μ from
          (D.U^[i]) (H N)) - Fstar)‖ ≤
        ‖G‖ * ‖(show MeasureTheory.Lp ℂ 2 M.μ from
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

/-- Real parts commute with the chapter's `N + 1` Cesàro convention. -/
lemma cesaroAverage_re_eq
    (a : ℕ → ℂ) (N : ℕ) :
    cesaroAverage (fun n ↦ (a n).re) N =
      ((((N + 1 : ℕ) : ℂ)⁻¹) *
        ∑ n ∈ Finset.range (N + 1), a n).re := by
  unfold cesaroAverage
  have hscalar :
      (((N + 1 : ℕ) : ℂ)⁻¹) =
        ((((N + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
    exact (Complex.ofReal_inv (((N + 1 : ℕ) : ℝ))).symm
  rw [hscalar, Complex.re_ofReal_mul]
  have hre :
      (∑ n ∈ Finset.range (N + 1), a n).re =
        ∑ n ∈ Finset.range (N + 1), (a n).re := by
    change Complex.reAddGroupHom
      (∑ n ∈ Finset.range (N + 1), a n) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rfl
  rw [hre, Finset.mul_sum]

/-- The fixed van der Corput pair limits uniformly over translated averaging
intervals. -/
lemma uniform_shifted_cesaro_re_inner_doubleKoopmanProduct
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (hErg : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MeasureTheory.MemLp (fun x ↦ G x) ⊤ M.μ)
    (h k : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        |cesaroAverage
            (fun n ↦
              (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
                (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                  M hM F G hFtop (i + (n + k)))
                (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                  M hM F G hFtop (i + (n + h)))).re) N -
          (productOfMeans M
            (MultipleKhintchineCharacteristic.rightPairFunction
              M hM G h k)
            (fun x ↦ star
              (MultipleKhintchineCharacteristic.leftPairFunction
                M hM F h k x))).re| < ε := by
  intro ε hε
  have hu :=
    ergodic_uniform_shifted_cesaroFunctionCorrelations
      M hM hErg
      (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)
      (fun x ↦ star
        (MultipleKhintchineCharacteristic.leftPairFunction M hM F h k x))
      (MultipleKhintchineCharacteristic.rightPairFunction_memLp
        M hM G hGtop h k)
      (MultipleKhintchineCharacteristic.star_leftPairFunction_memLp
        M hM F hFtop h k)
      ε hε
  have hu' := (tendsto_add_atTop_nat 1).eventually hu
  filter_upwards [hu'] with N hN
  intro i
  have hc := hN i
  simp only [Nat.add_eq_zero, one_ne_zero, and_false, if_false] at hc
  let L : ℂ :=
    productOfMeans M
      (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)
      (fun x ↦ star
        (MultipleKhintchineCharacteristic.leftPairFunction M hM F h k x))
  let b : ℕ → ℂ := fun n ↦
    @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F G hFtop (i + (n + k)))
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F G hFtop (i + (n + h)))
  have hb (n : ℕ) :
      b n =
        functionCorrelation M
          (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)
          (fun x ↦ star
            (MultipleKhintchineCharacteristic.leftPairFunction
              M hM F h k x))
          (i + n) := by
    dsimp only [b]
    rw [show i + (n + k) = (i + n) + k by omega,
      show i + (n + h) = (i + n) + h by omega,
      MultipleKhintchineCharacteristic.inner_doubleKoopmanProduct_add
        M hM F G hFtop (i + n) h k,
      MultipleKhintchineCharacteristic.inner_shiftedProducts_eq_functionCorrelation
        M hM F G hFtop (i + n) h k]
  have hcomplex :
      (((N + 1 : ℕ) : ℂ)⁻¹) *
          ∑ n ∈ Finset.range (N + 1), b n =
        (((N + 1 : ℕ) : ℂ)⁻¹) *
          ∑ n ∈ Finset.range (N + 1),
            functionCorrelation M
              (MultipleKhintchineCharacteristic.rightPairFunction
                M hM G h k)
              (fun x ↦ star
                (MultipleKhintchineCharacteristic.leftPairFunction
                  M hM F h k x))
              (i + n) := by
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    exact hb n
  change
    |cesaroAverage (fun n ↦ (b n).re) N - L.re| < ε
  calc
    |cesaroAverage (fun n ↦ (b n).re) N - L.re| =
        |(((((N + 1 : ℕ) : ℂ)⁻¹) *
          ∑ n ∈ Finset.range (N + 1), b n) - L).re| := by
            rw [cesaroAverage_re_eq, Complex.sub_re]
    _ ≤ ‖((((N + 1 : ℕ) : ℂ)⁻¹) *
          ∑ n ∈ Finset.range (N + 1), b n) - L‖ :=
      Complex.abs_re_le_norm _
    _ < ε := by
      rw [hcomplex, ← dist_eq_norm]
      exact hc

/-- Uniform block decay for the bilinear progression when its second factor
is continuous-spectral. -/
theorem doubleKoopmanProduct_hasUniformBlockDecay
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (hErg : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MeasureTheory.MemLp (fun x ↦ G x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (hGcont :
      InContinuousSpectralSubspace
        (MultipleKhintchineCharacteristic.KData M hM) G) :
    VanDerCorput.HasUniformVanDerCorputBlockDecay
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F G hFtop) := by
  intro δ hδ
  let η : ℝ := δ / (4 * (C ^ 2 + 1))
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨H, hH, heven⟩ :=
    MultipleKhintchineCharacteristic.exists_small_evenAutocorrelation_sum
      M hM G hGcont η hη
  refine ⟨H, hH, ?_⟩
  let L : ℝ :=
    (Finset.range H).sum (fun h ↦
      (Finset.range H).sum (fun k ↦
        (productOfMeans M
          (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)
          (fun x ↦ star
            (MultipleKhintchineCharacteristic.leftPairFunction
              M hM F h k x))).re))
  have hLnorm :
      L ≤ (Finset.range H).sum (fun h ↦
        (Finset.range H).sum (fun k ↦
          ‖productOfMeans M
            (MultipleKhintchineCharacteristic.rightPairFunction
              M hM G h k)
            (fun x ↦ star
              (MultipleKhintchineCharacteristic.leftPairFunction
                M hM F h k x))‖)) := by
    dsimp [L]
    gcongr with h hh k hk
    exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hsumBound :=
    MultipleKhintchineCharacteristic.sum_pairLimit_norm_le
      M hM F G C hC hFbound H
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hstrict : L < δ * (H : ℝ) ^ 2 := by
    calc
      L ≤ (Finset.range H).sum (fun h ↦
          (Finset.range H).sum (fun k ↦
            ‖productOfMeans M
              (MultipleKhintchineCharacteristic.rightPairFunction
                M hM G h k)
              (fun x ↦ star
                (MultipleKhintchineCharacteristic.leftPairFunction
                  M hM F h k x))‖)) := hLnorm
      _ ≤ 2 * (H : ℝ) * C ^ 2 *
          (Finset.range H).sum
            (MultipleKhintchineCharacteristic.evenAutocorrelationNorm
              M hM G) := hsumBound
      _ ≤ 2 * (H : ℝ) * C ^ 2 * (η * (H : ℝ)) := by
        have hcoef : 0 ≤ 2 * (H : ℝ) * C ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left heven.le hcoef
      _ < δ * (H : ℝ) ^ 2 := by
        have hratio : 2 * C ^ 2 * η < δ := by
          dsimp [η]
          have hden : 0 < 4 * (C ^ 2 + 1) := by positivity
          rw [div_eq_mul_inv]
          calc
            2 * C ^ 2 * (δ * (4 * (C ^ 2 + 1))⁻¹) =
                δ * (2 * C ^ 2 / (4 * (C ^ 2 + 1))) := by ring
            _ < δ * 1 := by
              apply mul_lt_mul_of_pos_left _ hδ
              rw [div_lt_one hden]
              nlinarith [sq_nonneg C]
            _ = δ := mul_one _
        nlinarith [sq_pos_of_pos hHreal]
  let ρ : ℝ :=
    (δ * (H : ℝ) ^ 2 - L) /
      (2 * ((H : ℝ) ^ 2 + 1))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    apply div_pos
    · linarith
    · positivity
  have hall :
      ∀ᶠ N : ℕ in atTop,
        ∀ h ∈ Finset.range H, ∀ k ∈ Finset.range H, ∀ i : ℕ,
          |cesaroAverage
              (fun n ↦
                (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
                  (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                    M hM F G hFtop (i + (n + k)))
                  (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                    M hM F G hFtop (i + (n + h)))).re) N -
            (productOfMeans M
              (MultipleKhintchineCharacteristic.rightPairFunction
                M hM G h k)
              (fun x ↦ star
                (MultipleKhintchineCharacteristic.leftPairFunction
                  M hM F h k x))).re| < ρ := by
    rw [Filter.eventually_all_finset]
    intro h hh
    rw [Filter.eventually_all_finset]
    intro k hk
    exact uniform_shifted_cesaro_re_inner_doubleKoopmanProduct
      M hM hErg F G hFtop hGtop h k ρ hρ
  filter_upwards [hall] with N hN
  intro i
  let A : ℕ → ℕ → ℝ := fun h k ↦
    cesaroAverage
      (fun n ↦
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          (MultipleKhintchineCharacteristic.doubleKoopmanProduct
            M hM F G hFtop (i + (n + k)))
          (MultipleKhintchineCharacteristic.doubleKoopmanProduct
            M hM F G hFtop (i + (n + h)))).re) N
  let Q : ℕ → ℕ → ℝ := fun h k ↦
    (productOfMeans M
      (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)
      (fun x ↦ star
        (MultipleKhintchineCharacteristic.leftPairFunction
          M hM F h k x))).re
  have hdecomp :
      cesaroAverage
        (fun n ↦ ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
          (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
            (MultipleKhintchineCharacteristic.doubleKoopmanProduct
              M hM F G hFtop (i + (n + k)))
            (MultipleKhintchineCharacteristic.doubleKoopmanProduct
              M hM F G hFtop (i + (n + h)))).re) N =
        ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, A h k := by
    unfold A cesaroAverage
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h hh
    rw [Finset.sum_comm]
  have hdiff :
      |(∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, A h k) - L| ≤
        (H : ℝ) ^ 2 * ρ := by
    have hLQ :
        L = ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, Q h k := by
      rfl
    rw [hLQ, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    calc
      |∑ h ∈ Finset.range H,
          ∑ k ∈ Finset.range H, (A h k - Q h k)| ≤
          ∑ h ∈ Finset.range H,
            |∑ k ∈ Finset.range H, (A h k - Q h k)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h ∈ Finset.range H,
          ∑ k ∈ Finset.range H, |A h k - Q h k| := by
        gcongr with h hh
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h ∈ Finset.range H,
          ∑ _k ∈ Finset.range H, ρ := by
        gcongr with h hh k hk
        exact (hN h hh k hk i).le
      _ = (H : ℝ) ^ 2 * ρ := by
        simp
        ring
  rw [hdecomp]
  have hρsmall :
      (H : ℝ) ^ 2 * ρ < δ * (H : ℝ) ^ 2 - L := by
    dsimp [ρ]
    have hgap : 0 < δ * (H : ℝ) ^ 2 - L := sub_pos.mpr hstrict
    have hden : 0 < 2 * ((H : ℝ) ^ 2 + 1) := by positivity
    rw [div_eq_mul_inv]
    calc
      (H : ℝ) ^ 2 *
          ((δ * (H : ℝ) ^ 2 - L) *
            (2 * ((H : ℝ) ^ 2 + 1))⁻¹) =
          (δ * (H : ℝ) ^ 2 - L) *
            ((H : ℝ) ^ 2 / (2 * ((H : ℝ) ^ 2 + 1))) := by ring
      _ < (δ * (H : ℝ) ^ 2 - L) * 1 := by
        apply mul_lt_mul_of_pos_left _ hgap
        rw [div_lt_one hden]
        nlinarith [sq_nonneg (H : ℝ)]
      _ = δ * (H : ℝ) ^ 2 - L := mul_one _
  have hlower :=
    (le_abs_self
      ((∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, A h k) - L))
  linarith

/-- Uniformly over the starting point of the averaging interval, a bilinear
progression vanishes when its second factor is continuous-spectral. -/
theorem doubleKoopmanProduct_uniform_cesaro_zero
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (hErg : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MeasureTheory.MemLp (fun x ↦ G x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (hGcont :
      InContinuousSpectralSubspace
        (MultipleKhintchineCharacteristic.KData M hM) G) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1),
            MultipleKhintchineCharacteristic.doubleKoopmanProduct
              M hM F G hFtop (i + n)‖ < ε := by
  exact VanDerCorput.vectorCesaro_uniform_tendsto_zero_of_blockDecay
    (MultipleKhintchineCharacteristic.doubleKoopmanProduct
      M hM F G hFtop)
    (C * ‖G‖)
    (MultipleKhintchineCharacteristic.norm_doubleKoopmanProduct_le
      M hM F G hFtop C hC hFbound)
    (doubleKoopmanProduct_hasUniformBlockDecay
      M hM hErg F G hFtop hGtop C hC hFbound hGcont)

/-- Symmetric uniform block decay: the first dynamic factor is
continuous-spectral and the second factor is essentially bounded. -/
theorem doubleKoopmanProduct_hasUniformBlockDecay_left
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (hErg : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MeasureTheory.MemLp (fun x ↦ G x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ C)
    (hFcont :
      InContinuousSpectralSubspace
        (MultipleKhintchineCharacteristic.KData M hM) F) :
    VanDerCorput.HasUniformVanDerCorputBlockDecay
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F G hFtop) := by
  intro δ hδ
  let η : ℝ := δ / (4 * (C ^ 2 + 1))
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨H, hH, hcorr⟩ :=
    MultipleKhintchineCharacteristic.exists_small_autocorrelation_sum
      M hM F hFcont η hη
  refine ⟨H, hH, ?_⟩
  let L : ℝ :=
    (Finset.range H).sum (fun h ↦
      (Finset.range H).sum (fun k ↦
        (productOfMeans M
          (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)
          (fun x ↦ star
            (MultipleKhintchineCharacteristic.leftPairFunction
              M hM F h k x))).re))
  have hLnorm :
      L ≤ (Finset.range H).sum (fun h ↦
        (Finset.range H).sum (fun k ↦
          ‖productOfMeans M
            (MultipleKhintchineCharacteristic.rightPairFunction
              M hM G h k)
            (fun x ↦ star
              (MultipleKhintchineCharacteristic.leftPairFunction
                M hM F h k x))‖)) := by
    dsimp [L]
    gcongr with h hh k hk
    exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hsumBound :=
    MultipleKhintchineCharacteristic.sum_pairLimit_norm_le_left
      M hM F G C hC hGbound H
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hstrict : L < δ * (H : ℝ) ^ 2 := by
    calc
      L ≤ (Finset.range H).sum (fun h ↦
          (Finset.range H).sum (fun k ↦
            ‖productOfMeans M
              (MultipleKhintchineCharacteristic.rightPairFunction
                M hM G h k)
              (fun x ↦ star
                (MultipleKhintchineCharacteristic.leftPairFunction
                  M hM F h k x))‖)) := hLnorm
      _ ≤ 2 * (H : ℝ) * C ^ 2 *
          (Finset.range H).sum
            (MultipleKhintchineCharacteristic.autocorrelationNorm
              M hM F) := hsumBound
      _ ≤ 2 * (H : ℝ) * C ^ 2 * (η * (H : ℝ)) := by
        have hcoef : 0 ≤ 2 * (H : ℝ) * C ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left hcorr.le hcoef
      _ < δ * (H : ℝ) ^ 2 := by
        have hratio : 2 * C ^ 2 * η < δ := by
          dsimp [η]
          have hden : 0 < 4 * (C ^ 2 + 1) := by positivity
          rw [div_eq_mul_inv]
          calc
            2 * C ^ 2 * (δ * (4 * (C ^ 2 + 1))⁻¹) =
                δ * (2 * C ^ 2 / (4 * (C ^ 2 + 1))) := by ring
            _ < δ * 1 := by
              apply mul_lt_mul_of_pos_left _ hδ
              rw [div_lt_one hden]
              nlinarith [sq_nonneg C]
            _ = δ := mul_one _
        nlinarith [sq_pos_of_pos hHreal]
  let ρ : ℝ :=
    (δ * (H : ℝ) ^ 2 - L) /
      (2 * ((H : ℝ) ^ 2 + 1))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    apply div_pos
    · linarith
    · positivity
  have hall :
      ∀ᶠ N : ℕ in atTop,
        ∀ h ∈ Finset.range H, ∀ k ∈ Finset.range H, ∀ i : ℕ,
          |cesaroAverage
              (fun n ↦
                (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
                  (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                    M hM F G hFtop (i + (n + k)))
                  (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                    M hM F G hFtop (i + (n + h)))).re) N -
            (productOfMeans M
              (MultipleKhintchineCharacteristic.rightPairFunction
                M hM G h k)
              (fun x ↦ star
                (MultipleKhintchineCharacteristic.leftPairFunction
                  M hM F h k x))).re| < ρ := by
    rw [Filter.eventually_all_finset]
    intro h hh
    rw [Filter.eventually_all_finset]
    intro k hk
    exact uniform_shifted_cesaro_re_inner_doubleKoopmanProduct
      M hM hErg F G hFtop hGtop h k ρ hρ
  filter_upwards [hall] with N hN
  intro i
  let A : ℕ → ℕ → ℝ := fun h k ↦
    cesaroAverage
      (fun n ↦
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          (MultipleKhintchineCharacteristic.doubleKoopmanProduct
            M hM F G hFtop (i + (n + k)))
          (MultipleKhintchineCharacteristic.doubleKoopmanProduct
            M hM F G hFtop (i + (n + h)))).re) N
  let Q : ℕ → ℕ → ℝ := fun h k ↦
    (productOfMeans M
      (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)
      (fun x ↦ star
        (MultipleKhintchineCharacteristic.leftPairFunction
          M hM F h k x))).re
  have hdecomp :
      cesaroAverage
        (fun n ↦ ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
          (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
            (MultipleKhintchineCharacteristic.doubleKoopmanProduct
              M hM F G hFtop (i + (n + k)))
            (MultipleKhintchineCharacteristic.doubleKoopmanProduct
              M hM F G hFtop (i + (n + h)))).re) N =
        ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, A h k := by
    unfold A cesaroAverage
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h hh
    rw [Finset.sum_comm]
  have hdiff :
      |(∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, A h k) - L| ≤
        (H : ℝ) ^ 2 * ρ := by
    have hLQ :
        L = ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, Q h k := by
      rfl
    rw [hLQ, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    calc
      |∑ h ∈ Finset.range H,
          ∑ k ∈ Finset.range H, (A h k - Q h k)| ≤
          ∑ h ∈ Finset.range H,
            |∑ k ∈ Finset.range H, (A h k - Q h k)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h ∈ Finset.range H,
          ∑ k ∈ Finset.range H, |A h k - Q h k| := by
        gcongr with h hh
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h ∈ Finset.range H,
          ∑ _k ∈ Finset.range H, ρ := by
        gcongr with h hh k hk
        exact (hN h hh k hk i).le
      _ = (H : ℝ) ^ 2 * ρ := by
        simp
        ring
  rw [hdecomp]
  have hρsmall :
      (H : ℝ) ^ 2 * ρ < δ * (H : ℝ) ^ 2 - L := by
    dsimp [ρ]
    have hgap : 0 < δ * (H : ℝ) ^ 2 - L := sub_pos.mpr hstrict
    have hden : 0 < 2 * ((H : ℝ) ^ 2 + 1) := by positivity
    rw [div_eq_mul_inv]
    calc
      (H : ℝ) ^ 2 *
          ((δ * (H : ℝ) ^ 2 - L) *
            (2 * ((H : ℝ) ^ 2 + 1))⁻¹) =
          (δ * (H : ℝ) ^ 2 - L) *
            ((H : ℝ) ^ 2 / (2 * ((H : ℝ) ^ 2 + 1))) := by ring
      _ < (δ * (H : ℝ) ^ 2 - L) * 1 := by
        apply mul_lt_mul_of_pos_left _ hgap
        rw [div_lt_one hden]
        nlinarith [sq_nonneg (H : ℝ)]
      _ = δ * (H : ℝ) ^ 2 - L := mul_one _
  have hlower :=
    (le_abs_self
      ((∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, A h k) - L))
  linarith

/-- Uniformly over translated averaging intervals, the bilinear progression
also vanishes when its first factor is continuous-spectral. -/
theorem doubleKoopmanProduct_uniform_cesaro_zero_left
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (hErg : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MeasureTheory.MemLp (fun x ↦ G x) ⊤ M.μ)
    (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ CF)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ CG)
    (hFcont :
      InContinuousSpectralSubspace
        (MultipleKhintchineCharacteristic.KData M hM) F) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1),
            MultipleKhintchineCharacteristic.doubleKoopmanProduct
              M hM F G hFtop (i + n)‖ < ε := by
  exact VanDerCorput.vectorCesaro_uniform_tendsto_zero_of_blockDecay
    (MultipleKhintchineCharacteristic.doubleKoopmanProduct
      M hM F G hFtop)
    (CF * ‖G‖)
    (MultipleKhintchineCharacteristic.norm_doubleKoopmanProduct_le
      M hM F G hFtop CF hCF hFbound)
    (doubleKoopmanProduct_hasUniformBlockDecay_left
      M hM hErg F G hFtop hGtop CG hCG hGbound hFcont)

/-- Applying a fixed scalar inner-product functional preserves uniform
translated Cesàro convergence to zero. -/
lemma uniform_cesaro_re_inner_of_vector
    (M : System.{u})
    (F : MeasureTheory.Lp ℂ 2 M.μ)
    (v : ℕ → MeasureTheory.Lp ℂ 2 M.μ)
    (hv :
      ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
            ∑ n ∈ Finset.range (N + 1), v (i + n)‖ < ε) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      |cesaroAverage
          (fun n ↦
            (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F (v (i + n))).re) N| <
        ε := by
  intro ε hε
  let δ : ℝ := ε / (‖F‖ + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  filter_upwards [hv δ hδ] with N hN
  intro i
  let V : MeasureTheory.Lp ℂ 2 M.μ :=
    (((N + 1 : ℕ) : ℂ)⁻¹) •
      ∑ n ∈ Finset.range (N + 1), v (i + n)
  have heq :
      cesaroAverage
          (fun n ↦
            (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F (v (i + n))).re) N =
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F V).re := by
    unfold cesaroAverage V
    simp only [inner_smul_right, inner_sum, Complex.mul_re,
      Complex.inv_re, Complex.inv_im]
    simp only [Complex.natCast_re, Complex.natCast_im,
      Complex.normSq_natCast, zero_div, neg_zero, zero_mul, sub_zero]
    have hsum_re :
        (∑ n ∈ Finset.range (N + 1),
          @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F (v (i + n))).re =
        ∑ n ∈ Finset.range (N + 1),
          (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F (v (i + n))).re := by
      change Complex.reAddGroupHom
        (∑ n ∈ Finset.range (N + 1),
          @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F (v (i + n))) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rfl
    rw [hsum_re]
    have hNR : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp
  rw [heq]
  have hre :
      |(@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F V).re| ≤
        ‖F‖ * ‖V‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have hV : ‖V‖ < δ := hN i
  have hmul : ‖F‖ * ‖V‖ < ε := by
    calc
      ‖F‖ * ‖V‖ ≤ ‖F‖ * δ := by
        exact mul_le_mul_of_nonneg_left hV.le (norm_nonneg F)
      _ < (‖F‖ + 1) * δ := by
        exact mul_lt_mul_of_pos_right (by linarith) hδ
      _ = ε := by
        dsimp [δ]
        field_simp
  exact lt_of_le_of_lt hre hmul

/-- The original triple correlation and its forward-Kronecker model differ
by a sequence whose Cesàro averages vanish uniformly on translated blocks. -/
theorem tripleCorrelation_sub_forwardKronecker_uniform_cesaro_zero
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      |cesaroAverage
          (fun n ↦
            MultipleKhintchineSyndetic.tripleCorrelation M A (i + n) -
              ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
                M hM A hA (i + n)) N| < ε := by
  let F := MultipleKhintchineCharacteristic.indicatorLp M hM.1 A hA
  let G :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  let R := F - G
  have hFtop :=
    MultipleKhintchineCharacteristic.indicatorLp_mem_top M hM.1 A hA
  have hGtop :=
    MultipleKhintchineCharacteristic.forwardKroneckerIndicatorLp_mem_top
      M hM A hA
  have hRtop :=
    MultipleKhintchineCharacteristic.indicatorResidual_mem_top M hM A hA
  have hRcont :=
    MultipleKhintchineCharacteristic.indicator_sub_forwardKronecker_continuous
      M hM A hA
  have hright :=
    doubleKoopmanProduct_uniform_cesaro_zero
      M hM.1 hM F R hFtop hRtop 1 (by norm_num)
      (MultipleKhintchineCharacteristic.indicatorLp_norm_le_one
        M hM.1 A hA) hRcont
  have hleft :=
    doubleKoopmanProduct_uniform_cesaro_zero_left
      M hM.1 hM R G hRtop hGtop 2 1
      (by norm_num) (by norm_num)
      (MultipleKhintchineCharacteristic.indicatorResidual_norm_le_two
        M hM A hA)
      (MultipleKhintchineCharacteristic.forwardKroneckerIndicatorLp_norm_le_one
        M hM A hA)
      hRcont
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hr :=
    uniform_cesaro_re_inner_of_vector M F
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM.1 F R hFtop) hright (ε / 2) hε2
  have hl :=
    uniform_cesaro_re_inner_of_vector M F
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM.1 R G hRtop) hleft (ε / 2) hε2
  filter_upwards [hr, hl] with N hrN hlN
  intro i
  have hid :
      cesaroAverage
          (fun n ↦
            MultipleKhintchineSyndetic.tripleCorrelation M A (i + n) -
              ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
                M hM A hA (i + n)) N =
        cesaroAverage
            (fun n ↦
              (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F
                (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                  M hM.1 F R hFtop (i + n))).re) N +
          cesaroAverage
            (fun n ↦
              (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F
                (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                  M hM.1 R G hRtop (i + n))).re) N := by
    unfold cesaroAverage
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 2
    funext n
    exact MultipleKhintchineCharacteristic.tripleCorrelation_sub_forwardKronecker
      M hM A hA (i + n)
  rw [hid]
  calc
    |_ + _| ≤
        |cesaroAverage
          (fun n ↦
            (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F
              (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                M hM.1 F R hFtop (i + n))).re) N| +
        |cesaroAverage
          (fun n ↦
            (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F
              (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                M hM.1 R G hRtop (i + n))).re) N| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hrN i) (hlN i)
    _ = ε := by ring

end Chapter02.MultipleKhintchineUniform
