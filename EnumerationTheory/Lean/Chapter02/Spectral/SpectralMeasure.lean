import Chapter02.Spectral.Herglotz

open Classical MeasureTheory Filter Topology
open scoped BigOperators ComplexOrder ENNReal

noncomputable section

namespace Chapter02.SpectralMeasure

theorem circleFourierCoefficient_neg_nat (μ : CircleMeasureData) (n : ℕ) :
    circleFourierCoefficient μ (-((n : ℤ))) = star (circleFourierCoefficient μ n) := by
  rw [circleFourierCoefficient, circleFourierCoefficient]
  calc
    (∫ z : Circle, (z : ℂ) ^ (-((n : ℤ))) ∂μ.μ) =
        ∫ z : Circle, star ((z : ℂ) ^ (n : ℤ)) ∂μ.μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      change (z : ℂ) ^ (-((n : ℤ))) = (starRingEnd ℂ) ((z : ℂ) ^ (n : ℤ))
      rw [map_zpow₀]
      rw [starRingEnd_apply]
      rw [show star (z : ℂ) = (z : ℂ)⁻¹ by
        apply Complex.ext <;> simp [Complex.inv_def]]
      simp
    _ = star (∫ z : Circle, (z : ℂ) ^ (n : ℤ) ∂μ.μ) := integral_conj

theorem eq_of_nat_moments (μ ν : CircleMeasureData)
    (h : ∀ n : ℕ, circleFourierCoefficient μ n = circleFourierCoefficient ν n) : μ = ν := by
  apply Herglotz.measure_eq_of_circleFourierCoefficient
  intro j
  cases j with
  | ofNat n => exact h n
  | negSucc n =>
      change circleFourierCoefficient μ (-(((n + 1 : ℕ) : ℤ))) =
        circleFourierCoefficient ν (-(((n + 1 : ℕ) : ℤ)))
      rw [circleFourierCoefficient_neg_nat, circleFourierCoefficient_neg_nat, h]

noncomputable def unitaryEquiv (D : HilbertOperatorData) (hD : IsUnitary D) :
    D.H ≃ₗᵢ[ℂ] D.H :=
  LinearIsometryEquiv.ofSurjective
    ({ toLinearMap := D.U.toLinearMap
       norm_map' := hD.2 } : D.H →ₗᵢ[ℂ] D.H) hD.1

@[simp] theorem unitaryEquiv_apply (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) : unitaryEquiv D hD x = D.U x := rfl

theorem inner_negPower_negPower (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (m n : ℤ) :
    @inner ℂ D.H _ (((unitaryEquiv D hD) ^ (-m)) x)
        (((unitaryEquiv D hD) ^ (-n)) x) =
      @inner ℂ D.H _ x (((unitaryEquiv D hD) ^ (m - n)) x) := by
  rw [← ((unitaryEquiv D hD) ^ m).inner_map_map]
  rw [zpow_neg, zpow_neg]
  have hcancel : ((unitaryEquiv D hD) ^ m)
      ((((unitaryEquiv D hD) ^ m)⁻¹) x) = x := by
    exact ((unitaryEquiv D hD) ^ m).apply_symm_apply x
  rw [hcancel]
  change @inner ℂ D.H _ x
    ((((unitaryEquiv D hD) ^ m) * (((unitaryEquiv D hD) ^ n)⁻¹)) x) = _
  rw [← zpow_neg]
  rw [← zpow_add]
  congr 3

noncomputable def vectorCorrelation (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (j : ℤ) : ℂ :=
  @inner ℂ D.H _ x (((unitaryEquiv D hD) ^ j) x)

theorem vectorCorrelation_neg_nat (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (n : ℕ) :
    vectorCorrelation D hD x (-((n : ℤ))) =
      star (vectorCorrelation D hD x (n : ℤ)) := by
  let V := unitaryEquiv D hD
  have hcancel : (V ^ (n : ℤ)) ((V ^ (-((n : ℤ)))) x) = x := by
    change ((V ^ (n : ℤ)) * (V ^ (-((n : ℤ))))) x = x
    rw [← zpow_add]
    simp
  calc
    vectorCorrelation D hD x (-((n : ℤ))) =
        @inner ℂ D.H _ ((V ^ (n : ℤ)) x)
          ((V ^ (n : ℤ)) ((V ^ (-((n : ℤ)))) x)) := by
      exact ((V ^ (n : ℤ)).inner_map_map x ((V ^ (-((n : ℤ)))) x)).symm
    _ = @inner ℂ D.H _ ((V ^ (n : ℤ)) x) x := by rw [hcancel]
    _ = star (vectorCorrelation D hD x (n : ℤ)) := by
      simpa [vectorCorrelation, V] using
        (inner_conj_symm x ((V ^ (n : ℤ)) x)).symm

theorem vectorCorrelation_positiveDefinite (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) : IsPositiveDefinite (vectorCorrelation D hD x) := by
  intro N a
  let y : D.H := ∑ m : Fin (N + 1),
    star (a m) • (((unitaryEquiv D hD) ^ (-((m : ℕ) : ℤ))) x)
  have hq :
      (∑ m : Fin (N + 1), ∑ n : Fin (N + 1),
        a m * star (a n) * vectorCorrelation D hD x
          (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ))) = @inner ℂ D.H _ y y := by
    simp only [y, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      inner_negPower_negPower, vectorCorrelation]
    simp_rw [Finset.mul_sum]
    nth_rewrite 2 [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    simp
    ring
  dsimp only
  rw [hq]
  constructor
  · exact inner_self_im (𝕜 := ℂ) y
  · have hre : (@inner ℂ D.H _ y y).re = ‖y‖ ^ 2 := by
      simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) y)
    rw [hre]
    positivity

theorem unitaryEquiv_zpow_nat (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (n : ℕ) :
    ((unitaryEquiv D hD) ^ (n : ℤ)) x = (D.U^[n]) x := by
  rw [zpow_natCast]
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change D.U (((unitaryEquiv D hD) ^ n) x) = (D.U^[n + 1]) x
      rw [ih]
      rw [Function.iterate_succ_apply']

theorem full_moment_of_hasSpectralMeasure (D : HilbertOperatorData)
    (hD : IsUnitary D) (x : D.H) (μ : CircleMeasureData)
    (hμ : HasSpectralMeasure D x μ) (j : ℤ) :
    circleFourierCoefficient μ j = vectorCorrelation D hD x j := by
  cases j with
  | ofNat n =>
      change circleFourierCoefficient μ (n : ℤ) = vectorCorrelation D hD x (n : ℤ)
      rw [hμ n]
      exact congrArg (fun y : D.H => @inner ℂ D.H _ x y)
        (unitaryEquiv_zpow_nat D hD x n).symm
  | negSucc n =>
      change circleFourierCoefficient μ (-(((n + 1 : ℕ) : ℤ))) =
        vectorCorrelation D hD x (-(((n + 1 : ℕ) : ℤ)))
      rw [circleFourierCoefficient_neg_nat, vectorCorrelation_neg_nat, hμ]
      congr 2
      exact (unitaryEquiv_zpow_nat D hD x (n + 1)).symm

theorem spectralMeasure (D : HilbertOperatorData) : SpectralMeasureStatement D := by
  intro hD x
  obtain ⟨μ, hμ, _⟩ := Herglotz.herglotz (vectorCorrelation D hD x)
    (vectorCorrelation_positiveDefinite D hD x)
  have hμspec : HasSpectralMeasure D x μ := by
    intro n
    rw [hμ (n : ℤ)]
    exact congrArg (fun y : D.H => @inner ℂ D.H _ x y)
      (unitaryEquiv_zpow_nat D hD x n)
  refine ⟨μ, hμspec, ?_⟩
  intro ν hν
  exact eq_of_nat_moments ν μ (fun n => (hν n).trans (hμspec n).symm)

end Chapter02.SpectralMeasure
