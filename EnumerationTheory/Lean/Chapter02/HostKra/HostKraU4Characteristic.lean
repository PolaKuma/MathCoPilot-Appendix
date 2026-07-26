import Chapter02.HostKra.HostKraU4ProgressionDecay
import Chapter02.Recurrence.MultipleKhintchineCartesian

open Classical Filter MeasureTheory Set

noncomputable section

namespace Chapter02.HostKraU4Characteristic

universe u

open HostKraU4ProgressionDecay
open HostKraCubeSeminorm

/-- Pairing a three-factor Koopman product against the conjugate of a
fixed zeroth factor is exactly the corresponding four-function progression
integral. -/
lemma inner_lpStar_tripleKoopmanProduct_eq_integral_quadruple
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F₀ F₁ F₂ F₃ : Lp ℂ 2 M.μ)
    (hF₁top : MemLp (fun x ↦ F₁ x) ⊤ M.μ)
    (hF₂top : MemLp (fun x ↦ F₂ x) ⊤ M.μ)
    (n : ℕ) :
    @inner ℂ (Lp ℂ 2 M.μ) _
        (ForwardKroneckerFactor.lpStar M F₀)
        (tripleKoopmanProduct M hM F₁ F₂ F₃ hF₁top hF₂top n) =
      ∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
        (fun x ↦ F₀ x) (fun x ↦ F₁ x)
        (fun x ↦ F₂ x) (fun x ↦ F₃ x) n x ∂M.μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    ForwardKroneckerFactor.lpStar_coe M F₀,
    tripleKoopmanProduct_coe
      M hM F₁ F₂ F₃ hF₁top hF₂top n,
    MultipleKhintchineKronecker.koopmanData_iter_ae M hM n F₁,
    MultipleKhintchineKronecker.koopmanData_iter_ae M hM (2 * n) F₂,
    MultipleKhintchineKronecker.koopmanData_iter_ae M hM (3 * n) F₃]
      with x hstar hprod h₁ h₂ h₃
  rw [hstar, hprod, h₁, h₂, h₃]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_star,
    MultipleKhintchineCartesian.quadrupleIntegrand]
  ring

/-- The checked Hilbert-valued `U⁴` decay implies uniform translated
cancellation of every scalar four-function progression with the
`U⁴`-null vector in the last dynamic position. -/
theorem integral_quadruple_uniform_cesaro_zero_of_hasZeroHostKraU4
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F₀ F₁ F₂ F₃ : Lp ℂ 2 M.μ)
    (hF₁top : MemLp (fun x ↦ F₁ x) ⊤ M.μ)
    (hF₂top : MemLp (fun x ↦ F₂ x) ⊤ M.μ)
    (hF₃top : MemLp (fun x ↦ F₃ x) ⊤ M.μ)
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hF₁bound : ∀ᵐ x ∂M.μ, ‖F₁ x‖ ≤ C₁)
    (hF₂bound : ∀ᵐ x ∂M.μ, ‖F₂ x‖ ≤ C₂)
    (hzero : HasZeroHostKraU4 M hM (fun x ↦ F₃ x) hF₃top) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        |cesaroAverage
          (fun n ↦
            (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
              (fun x ↦ F₀ x) (fun x ↦ F₁ x)
              (fun x ↦ F₂ x) (fun x ↦ F₃ x)
              (i + n) x ∂M.μ).re) N| < ε := by
  have hvec :=
    tripleKoopmanProduct_uniform_cesaro_norm_zero_of_hasZeroHostKraU4
      M hM hErg F₁ F₂ F₃ hF₁top hF₂top hF₃top
      C₁ C₂ hC₁ hC₂ hF₁bound hF₂bound hzero
  have hscalar :=
    MultipleKhintchineUniform.uniform_cesaro_re_inner_of_vector
      M (ForwardKroneckerFactor.lpStar M F₀)
      (tripleKoopmanProduct M hM F₁ F₂ F₃ hF₁top hF₂top)
      hvec
  simpa only [
    inner_lpStar_tripleKoopmanProduct_eq_integral_quadruple
      M hM F₀ F₁ F₂ F₃ hF₁top hF₂top] using hscalar

/-- The Cartesian-square cancellation premise is exactly uniform translated
mean-square decay of the original complex fourfold integral.  This
base-system formulation avoids any need to assume that the Cartesian square
is ergodic. -/
theorem cartesianQuadrupleUniformZero_iff_uniform_norm_sq
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f₀ f₁ f₂ f₃ : M.X → ℂ) :
    MultipleKhintchineCartesian.CartesianQuadrupleUniformZero
        M f₀ f₁ f₂ f₃ ↔
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
          cesaroAverage
            (fun n ↦
              ‖∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
                f₀ f₁ f₂ f₃ (i + n) x ∂M.μ‖ ^ 2) N < ε := by
  constructor
  · intro hzero ε hε
    filter_upwards [hzero ε hε] with N hN
    intro i
    simpa only [
      MultipleKhintchineCartesian.norm_integral_quadrupleIntegrand_sq
        M hM f₀ f₁ f₂ f₃] using hN i
  · intro hzero ε hε
    filter_upwards [hzero ε hε] with N hN
    intro i
    simpa only [
      MultipleKhintchineCartesian.norm_integral_quadrupleIntegrand_sq
        M hM f₀ f₁ f₂ f₃] using hN i

/-- Uniform translated mean-square decay on the original system is a
direct sufficient condition for BHK uniform-density cancellation of the
real fourfold integral. -/
theorem integral_quadruple_uniformDensity_of_uniform_norm_sq
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (hzero :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
          cesaroAverage
            (fun n ↦
              ‖∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
                f₀ f₁ f₂ f₃ (i + n) x ∂M.μ‖ ^ 2) N < ε) :
    MultipleKhintchineSyndetic.TendsToZeroInUniformDensity
      (fun n ↦
        (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
          f₀ f₁ f₂ f₃ n x ∂M.μ).re) := by
  apply
    MultipleKhintchineCartesian.uniformDensity_re_integral_quadruple_of_cartesian_zero
      M hM f₀ f₁ f₂ f₃
  exact
    (cartesianQuadrupleUniformZero_iff_uniform_norm_sq
      M hM f₀ f₁ f₂ f₃).2 hzero

/-- The set-theoretic fourfold progression correlation is the real part
of the corresponding indicator progression integral. -/
lemma quadrupleCorrelation_eq_re_integral_indicator
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) :
    MultipleKhintchineSyndetic.quadrupleCorrelation M A n =
      (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
        (fun x ↦
          MultipleKhintchineCharacteristic.indicatorLp M hM A hA x)
        (fun x ↦
          MultipleKhintchineCharacteristic.indicatorLp M hM A hA x)
        (fun x ↦
          MultipleKhintchineCharacteristic.indicatorLp M hM A hA x)
        (fun x ↦
          MultipleKhintchineCharacteristic.indicatorLp M hM A hA x)
        n x ∂M.μ).re := by
  let F := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  let C : Set M.X :=
    A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A ∩
      preimageIter M (3 * n) A
  have hC : MeasurableSet C := by
    dsimp only [C]
    exact ((hA.inter
      (hA.preimage (hM.2.measurable.iterate n))).inter
      (hA.preimage (hM.2.measurable.iterate (2 * n)))).inter
      (hA.preimage (hM.2.measurable.iterate (3 * n)))
  have hfun :
      (fun x ↦ MultipleKhintchineCartesian.quadrupleIntegrand M
        (fun x ↦ F x) (fun x ↦ F x) (fun x ↦ F x) (fun x ↦ F x)
        n x) =ᵐ[M.μ]
        CorrelationMean.indicatorComplex C := by
    have hshift (r : ℕ) :
        (fun x ↦ F ((M.T^[r]) x)) =ᵐ[M.μ]
          (fun x ↦
            CorrelationMean.indicatorComplex A ((M.T^[r]) x)) := by
      simpa only [F, Function.comp_apply] using
        (hM.2.iterate r).quasiMeasurePreserving.ae_eq_comp
          (MultipleKhintchineCharacteristic.indicatorLp_coe
            M hM A hA)
    filter_upwards [
      MultipleKhintchineCharacteristic.indicatorLp_coe M hM A hA,
      hshift n, hshift (2 * n), hshift (3 * n)]
        with x hzero h₁ h₂ h₃
    simp only [MultipleKhintchineCartesian.quadrupleIntegrand]
    rw [hzero, h₁, h₂, h₃]
    by_cases hx0 : x ∈ A <;>
      by_cases hx1 : (M.T^[n]) x ∈ A <;>
      by_cases hx2 : (M.T^[2 * n]) x ∈ A <;>
      by_cases hx3 : (M.T^[3 * n]) x ∈ A <;>
      simp [CorrelationMean.indicatorComplex, Set.indicator, C,
        preimageIter, Chapter01.iterateMap, hx0, hx1, hx2, hx3]
  unfold MultipleKhintchineSyndetic.quadrupleCorrelation
  rw [integral_congr_ae hfun,
    CorrelationMean.integral_indicatorComplex M C hC]
  simp [C]

end Chapter02.HostKraU4Characteristic
