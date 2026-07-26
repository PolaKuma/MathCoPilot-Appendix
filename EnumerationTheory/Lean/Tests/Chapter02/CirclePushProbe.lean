import Chapter02.Spectral.Herglotz

open Classical MeasureTheory Filter Topology
open scoped BigOperators ComplexOrder

noncomputable section

namespace Chapter02.HerglotzPushProbe

private noncomputable def e : AddCircle (1 : ℝ) ≃ₜ Circle :=
  AddCircle.homeomorphCircle one_ne_zero

theorem character_comp_e (n : ℤ) (x : AddCircle (1 : ℝ)) :
    (((e x : Circle) : ℂ) ^ n) = fourier (T := (1 : ℝ)) n x := by
  rw [e, AddCircle.homeomorphCircle_apply, fourier_apply,
    AddCircle.toCircle_zsmul]
  rfl

noncomputable def push (ν : FiniteMeasure (AddCircle (1 : ℝ))) : CircleMeasureData where
  μ := ν.map e
  isFinite := inferInstance

theorem circleFourierCoefficient_push (ν : FiniteMeasure (AddCircle (1 : ℝ))) (n : ℤ) :
    circleFourierCoefficient (push ν) n =
      ∫ x, fourier (T := (1 : ℝ)) n x ∂(ν : Measure (AddCircle (1 : ℝ))) := by
  change (∫ z : Circle, (z : ℂ) ^ n
      ∂Measure.map e (ν : Measure (AddCircle (1 : ℝ)))) = _
  rw [e.isClosedEmbedding.integral_map]
  apply integral_congr_ae
  filter_upwards [] with x
  exact character_comp_e n x

theorem measure_eq_of_moments (μ ν : CircleMeasureData)
    (h : ∀ n : ℤ, circleFourierCoefficient μ n = circleFourierCoefficient ν n) : μ = ν := by
  have hall : ∀ q : C(Circle, ℂ), q ∈ CircleLaurent.span →
      ∫ z, q z ∂μ.μ = ∫ z, q z ∂ν.μ := by
    intro q hq
    refine Submodule.span_induction (p := fun q _ =>
      ∫ z, q z ∂μ.μ = ∫ z, q z ∂ν.μ) ?_ ?_ ?_ ?_ hq
    · intro q hq
      obtain ⟨n, rfl⟩ := hq
      exact h n
    · simp
    · intro f g _ _ hf hg
      change (∫ z, f z + g z ∂μ.μ) = ∫ z, f z + g z ∂ν.μ
      rw [integral_add, integral_add, hf, hg]
      · exact Continuous.integrable_of_hasCompactSupport f.continuous
          (HasCompactSupport.of_compactSpace _)
      · exact Continuous.integrable_of_hasCompactSupport g.continuous
          (HasCompactSupport.of_compactSpace _)
      · exact Continuous.integrable_of_hasCompactSupport f.continuous
          (HasCompactSupport.of_compactSpace _)
      · exact Continuous.integrable_of_hasCompactSupport g.continuous
          (HasCompactSupport.of_compactSpace _)
    · intro a f _ hf
      simp only [ContinuousMap.smul_apply]
      rw [integral_smul, integral_smul, hf]
  have heq : μ.μ = ν.μ := by
    apply ext_of_forall_mem_subalgebra_integral_eq_of_polish
      CircleFourierUniqueness.laurentBCFAlgebra_separates
    intro q hq
    exact hall q.toContinuousMap hq
  cases μ
  cases ν
  cases heq
  rfl

theorem phi_eq_zero_of_zero {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ) (h0 : φ 0 = 0) :
    φ = 0 := by
  have hnat : ∀ n : ℕ, φ n = 0 := by
    intro n
    let i0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    let x : Fin (n + 1) → ℂ := Pi.single i0 1
    have hquad : dotProduct (star x) ((Herglotz.toeplitz φ n).mulVec x) = 0 := by
      simp [x, i0, Herglotz.toeplitz, h0]
    have hv := ((Herglotz.toeplitz_posSemidef hφ n).dotProduct_mulVec_zero_iff x).mp hquad
    have hn := congrFun hv (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
    simpa [x, i0, Herglotz.toeplitz, Matrix.mulVec] using hn
  funext j
  cases j with
  | ofNat n => exact hnat n
  | negSucc n =>
      change φ (-((n + 1 : ℕ) : ℤ)) = 0
      rw [Herglotz.phi_neg_nat hφ, hnat]
      simp

theorem herglotz : HerglotzStatement := by
  intro φ hφ
  by_cases h0 : φ 0 = 0
  · have hz := phi_eq_zero_of_zero hφ h0
    let μ0 : CircleMeasureData := ⟨0, inferInstance⟩
    refine ⟨μ0, ?_, ?_⟩
    · intro n
      simp [μ0, circleFourierCoefficient, hz]
    · intro ν hν
      apply measure_eq_of_moments
      intro n
      rw [hν n]
      simp [μ0, circleFourierCoefficient, hz]
  · obtain ⟨μ, ψ, hψ, ht⟩ := Herglotz.exists_fejerProbability_limit hφ
    let ρ := push (Herglotz.scaledProbabilityLimit hφ μ)
    have hρ : ∀ n : ℤ, circleFourierCoefficient ρ n = φ n := by
      intro n
      change circleFourierCoefficient
        (push (Herglotz.scaledProbabilityLimit hφ μ)) n = φ n
      rw [circleFourierCoefficient_push]
      exact Herglotz.integral_fourier_scaledProbabilityLimit hφ h0 μ ψ hψ ht n
    refine ⟨ρ, hρ, ?_⟩
    intro ν hν
    apply measure_eq_of_moments
    intro n
    rw [hρ n, hν n]

end Chapter02.HerglotzPushProbe
