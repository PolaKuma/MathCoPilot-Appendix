import Chapter02.Recurrence.MultipleKhintchineCartesian
import Chapter02.Recurrence.MultipleKhintchineCharacteristic

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter02.MultipleKhintchineCartesianCharacteristic

universe u

/-- A scalar functional of the Hilbert-valued bilinear progression is the
integral of the corresponding three-function progression. -/
lemma inner_doubleKoopmanProduct_eq_integral_triple
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F₀ F₁ F₂ : MeasureTheory.Lp ℂ 2 M.μ)
    (hF₁top : MeasureTheory.MemLp (fun x ↦ F₁ x) ⊤ M.μ)
    (n : ℕ) :
    @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F₀
        (MultipleKhintchineCharacteristic.doubleKoopmanProduct
          M hM F₁ F₂ hF₁top n) =
      ∫ x,
        MultipleKhintchineCartesian.tripleIntegrand M
          (fun x ↦ star (F₀ x)) (fun x ↦ F₁ x) (fun x ↦ F₂ x) n x
        ∂M.μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    MultipleKhintchineCharacteristic.doubleKoopmanProduct_coe
      M hM F₁ F₂ hF₁top n,
    MultipleKhintchineKronecker.koopmanData_iter_ae M hM n F₁,
    MultipleKhintchineKronecker.koopmanData_iter_ae M hM (2 * n) F₂]
      with x hprod h₁ h₂
  rw [hprod, h₁, h₂]
  simp only [MultipleKhintchineCartesian.tripleIntegrand,
    RCLike.inner_apply]
  simp only [starRingEnd_apply]
  ring

/-- Cartesian-square uniform cancellation upgrades a scalar functional of
the bilinear Koopman progression to BHK uniform-density cancellation. -/
theorem uniformDensity_re_inner_doubleKoopmanProduct_of_cartesian_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F₀ F₁ F₂ : MeasureTheory.Lp ℂ 2 M.μ)
    (hF₁top : MeasureTheory.MemLp (fun x ↦ F₁ x) ⊤ M.μ)
    (hzero :
      ∀ ε > 0, ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ℕ,
        cesaroAverage
          (fun n ↦
            (∫ p,
              MultipleKhintchineCartesian.tripleIntegrand
                (MultipleKhintchineCartesian.productSystem M M)
                (MultipleKhintchineCartesian.cartesianSquare
                  (fun x ↦ star (F₀ x)))
                (MultipleKhintchineCartesian.cartesianSquare
                  (fun x ↦ F₁ x))
                (MultipleKhintchineCartesian.cartesianSquare
                  (fun x ↦ F₂ x))
                (i + n) p
              ∂(MultipleKhintchineCartesian.productSystem M M).μ).re) N <
          ε) :
    MultipleKhintchineSyndetic.TendsToZeroInUniformDensity
      (fun n ↦
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F₀
          (MultipleKhintchineCharacteristic.doubleKoopmanProduct
            M hM F₁ F₂ hF₁top n)).re) := by
  have hud :=
    Chapter02.MultipleKhintchineCartesian.uniformDensity_re_integral_triple_of_cartesian_zero
        M hM (fun x ↦ star (F₀ x)) (fun x ↦ F₁ x)
        (fun x ↦ F₂ x) hzero
  simpa only [
    inner_doubleKoopmanProduct_eq_integral_triple
      M hM F₀ F₁ F₂ hF₁top] using hud

/-- The exact triple characteristic-factor error is zero in BHK uniform
density once the two residual terms produced by telescoping vanish after
Cartesian squaring. -/
theorem tripleCharacteristic_uniformDensity_of_cartesian
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hright :
      MultipleKhintchineCartesian.CartesianTripleUniformZero M
        (fun x ↦ star
          (MultipleKhintchineCharacteristic.indicatorLp M hM.1 A hA x))
        (fun x ↦
          MultipleKhintchineCharacteristic.indicatorLp M hM.1 A hA x)
        (fun x ↦
          (MultipleKhintchineCharacteristic.indicatorLp M hM.1 A hA -
            ForwardKroneckerFactor.forwardKroneckerIndicatorLp
              M hM A hA) x))
    (hleft :
      MultipleKhintchineCartesian.CartesianTripleUniformZero M
        (fun x ↦ star
          (MultipleKhintchineCharacteristic.indicatorLp M hM.1 A hA x))
        (fun x ↦
          (MultipleKhintchineCharacteristic.indicatorLp M hM.1 A hA -
            ForwardKroneckerFactor.forwardKroneckerIndicatorLp
              M hM A hA) x)
        (fun x ↦
          ForwardKroneckerFactor.forwardKroneckerIndicatorLp
            M hM A hA x)) :
    MultipleKhintchineSyndetic.TendsToZeroInUniformDensity
      (fun n ↦
        MultipleKhintchineSyndetic.tripleCorrelation M A n -
          ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
            M hM A hA n) := by
  let F :=
    MultipleKhintchineCharacteristic.indicatorLp M hM.1 A hA
  let G :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  let R := F - G
  have hudRight :=
    uniformDensity_re_inner_doubleKoopmanProduct_of_cartesian_zero
      M hM.1 F F R
      (MultipleKhintchineCharacteristic.indicatorLp_mem_top
        M hM.1 A hA)
      (by simpa only [MultipleKhintchineCartesian.CartesianTripleUniformZero,
          F, G, R] using hright)
  have hudLeft :=
    uniformDensity_re_inner_doubleKoopmanProduct_of_cartesian_zero
      M hM.1 F R G
      (MultipleKhintchineCharacteristic.indicatorResidual_mem_top
        M hM A hA)
      (by simpa only [MultipleKhintchineCartesian.CartesianTripleUniformZero,
          F, G, R] using hleft)
  have hud := hudRight.add hudLeft
  simpa only [F, G, R,
    MultipleKhintchineCharacteristic.tripleCorrelation_sub_forwardKronecker
      M hM A hA] using hud

end Chapter02.MultipleKhintchineCartesianCharacteristic
