import Chapter02.HostKra.HostKraSevenDualFactor
import Chapter02.HostKra.HostKraU3NonergodicFourTerm
import Chapter02.HostKra.HostKraU4Characteristic

open Classical Filter MeasureTheory Set

noncomputable section

namespace Chapter02.HostKraU3IndicatorCharacteristic

universe u

open HostKraU4ProgressionDecay

/-- The checked Hilbert-valued `U³` estimate, paired against the fixed
zeroth factor, gives translated-uniform signed Cesàro cancellation for a
four-term scalar progression. -/
theorem integral_quadruple_uniform_cesaro_zero_of_hasZeroHostKraU3
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
    (hzero : HostKraCubeSeminorm.HasZeroHostKraU3
      M hM (fun x ↦ F₃ x) hF₃top) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        |cesaroAverage
          (fun n ↦
            (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
              (fun x ↦ F₀ x) (fun x ↦ F₁ x)
              (fun x ↦ F₂ x) (fun x ↦ F₃ x)
              (i + n) x ∂M.μ).re) N| < ε := by
  have hvec :=
    HostKraU3OptimalProgressionDecay.tripleKoopmanProduct_uniform_cesaro_norm_zero_of_hasZeroHostKraU3
      M hM hErg F₁ F₂ F₃ hF₁top hF₂top hF₃top
      C₁ C₂ hC₁ hC₂ hF₁bound hF₂bound hzero
  have hscalar :=
    MultipleKhintchineUniform.uniform_cesaro_re_inner_of_vector
      M (ForwardKroneckerFactor.lpStar M F₀)
      (tripleKoopmanProduct M hM F₁ F₂ F₃ hF₁top hF₂top)
      hvec
  simpa only [
    HostKraU4Characteristic.inner_lpStar_tripleKoopmanProduct_eq_integral_quadruple
      M hM F₀ F₁ F₂ F₃ hF₁top hF₂top] using hscalar

/-- The fourfold correlation with the indicator conditionally projected to
the seven-dual (`Z₂`) factor in the final slot. -/
def sevenDualStructuredCorrelation
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) : ℝ :=
  let F := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  let P := HostKraDualSigma.condExpL2Value M.μ
    (HostKraSevenDualFactor.sevenDualMeasurableSpace_le M hM) F
  (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
    (fun x ↦ F x) (fun x ↦ F x)
    (fun x ↦ F x) (fun x ↦ P x) n x ∂M.μ).re

/-- Subtracting the seven-dual structured term leaves exactly the
four-term progression with the `U³`-null residual in its last slot. -/
theorem quadrupleCorrelation_sub_sevenDualStructured_eq_residual
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) :
    let F := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
    let R := HostKraSevenDualFactor.sevenDualResidual M hM F
    MultipleKhintchineSyndetic.quadrupleCorrelation M A n -
        sevenDualStructuredCorrelation M hM A hA n =
      (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
        (fun x ↦ F x) (fun x ↦ F x)
        (fun x ↦ F x) (fun x ↦ R x) n x ∂M.μ).re := by
  dsimp only
  letI : IsProbabilityMeasure M.μ := hM.1
  let F := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  let P := HostKraDualSigma.condExpL2Value M.μ
    (HostKraSevenDualFactor.sevenDualMeasurableSpace_le M hM) F
  let R := HostKraSevenDualFactor.sevenDualResidual M hM F
  have hFtop :=
    MultipleKhintchineCharacteristic.indicatorLp_mem_top M hM A hA
  have hPtop : MemLp (fun x ↦ P x) ⊤ M.μ :=
    HostKraDualSigma.condExpL2Value_memLp_top M.μ
      (HostKraSevenDualFactor.sevenDualMeasurableSpace_le M hM)
      F hFtop
  have hfull :
      MultipleKhintchineSyndetic.quadrupleCorrelation M A n =
        (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
          (fun x ↦ F x) (fun x ↦ F x)
          (fun x ↦ F x) (fun x ↦ F x) n x ∂M.μ).re := by
    simpa only [F] using
      HostKraU4Characteristic.quadrupleCorrelation_eq_re_integral_indicator
        M hM A hA n
  have hsplit :
      (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
        (fun x ↦ F x) (fun x ↦ F x)
        (fun x ↦ F x) (fun x ↦ R x) n x ∂M.μ) =
      (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
        (fun x ↦ F x) (fun x ↦ F x)
        (fun x ↦ F x) (fun x ↦ F x) n x ∂M.μ) -
      (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
        (fun x ↦ F x) (fun x ↦ F x)
        (fun x ↦ F x) (fun x ↦ P x) n x ∂M.μ) := by
    rw [← integral_sub
      (HostKraU3NonergodicFourTerm.quadrupleIntegrand_memLp_top
        M hM F F F F hFtop hFtop hFtop hFtop n
        |>.integrable (by simp))
      (HostKraU3NonergodicFourTerm.quadrupleIntegrand_memLp_top
        M hM F F F P hFtop hFtop hFtop hPtop n
        |>.integrable (by simp))]
    apply integral_congr_ae
    have hcoe :=
      (hM.2.iterate (3 * n)).quasiMeasurePreserving.ae_eq
        (MeasureTheory.Lp.coeFn_sub F P)
    filter_upwards [hcoe] with x hx
    simp only [Function.comp_apply] at hx
    simp only [MultipleKhintchineCartesian.quadrupleIntegrand,
      R, HostKraSevenDualFactor.sevenDualResidual]
    rw [hx]
    simp only [Pi.sub_apply]
    ring
  rw [hfull, sevenDualStructuredCorrelation, hsplit, Complex.sub_re]

/-- The seven-dual residual is negligible for translated block means in
the signed sense needed by the classical `Z₂` characteristic-factor
argument. -/
theorem quadrupleCorrelation_sub_sevenDualStructured_uniform_cesaro_zero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        |cesaroAverage
          (fun n ↦
            MultipleKhintchineSyndetic.quadrupleCorrelation M A (i + n) -
              sevenDualStructuredCorrelation M hM A hA (i + n)) N| < ε := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let F := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  let R := HostKraSevenDualFactor.sevenDualResidual M hM F
  let hFtop :=
    MultipleKhintchineCharacteristic.indicatorLp_mem_top M hM A hA
  let hRtop :=
    HostKraSevenDualFactor.sevenDualResidual_memLp_top
      M hM F hFtop
  have hzero :
      HostKraCubeSeminorm.HasZeroHostKraU3
        M hM (fun x ↦ R x) hRtop := by
    simpa only [R, hRtop] using
      HostKraSevenDualFactor.sub_sevenDualProjection_hasZeroHostKraU3
        M hM F hFtop
  have hdecay :=
    integral_quadruple_uniform_cesaro_zero_of_hasZeroHostKraU3
      M hM hErg F F F R hFtop hFtop hRtop
      1 1 (by norm_num) (by norm_num)
      (MultipleKhintchineCharacteristic.indicatorLp_norm_le_one
        M hM A hA)
      (MultipleKhintchineCharacteristic.indicatorLp_norm_le_one
        M hM A hA)
      hzero
  intro ε hε
  filter_upwards [hdecay ε hε] with N hN
  intro i
  simpa only [
    quadrupleCorrelation_sub_sevenDualStructured_eq_residual
      M hM A hA] using hN i

end Chapter02.HostKraU3IndicatorCharacteristic
