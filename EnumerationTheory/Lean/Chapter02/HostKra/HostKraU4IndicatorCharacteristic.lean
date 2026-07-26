import Chapter02.HostKra.HostKraFifteenDualFactor
import Chapter02.HostKra.HostKraU4Characteristic
import Chapter02.HostKra.HostKraU4UniformNormSq

open Classical Filter MeasureTheory Set

noncomputable section

namespace Chapter02.HostKraU4IndicatorCharacteristic

universe u

/-- The indicator residual from projection to the fifteen-dual factor
contributes zero to uniform translated scalar Cesàro averages when it
occupies the last position of the fourfold progression. -/
theorem indicator_fifteenDualResidual_last_uniform_cesaro_zero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    let F :=
      MultipleKhintchineCharacteristic.indicatorLp M hM A hA
    let R :=
      HostKraFifteenDualFactor.fifteenDualResidual M hM F
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        |cesaroAverage
          (fun n ↦
            (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
              (fun x ↦ F x) (fun x ↦ F x)
              (fun x ↦ F x) (fun x ↦ R x)
              (i + n) x ∂M.μ).re) N| < ε := by
  dsimp only
  let F :=
    MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  let hFtop :=
    MultipleKhintchineCharacteristic.indicatorLp_mem_top M hM A hA
  let R :=
    HostKraFifteenDualFactor.fifteenDualResidual M hM F
  let hRtop :=
    HostKraFifteenDualFactor.fifteenDualResidual_memLp_top
      M hM F hFtop
  exact
    HostKraU4Characteristic.integral_quadruple_uniform_cesaro_zero_of_hasZeroHostKraU4
      M hM hErg F F F R hFtop hFtop hRtop
      1 1 (by norm_num) (by norm_num)
      (MultipleKhintchineCharacteristic.indicatorLp_norm_le_one
        M hM A hA)
      (MultipleKhintchineCharacteristic.indicatorLp_norm_le_one
        M hM A hA)
      (by
        simpa only [R, hRtop] using
          HostKraFifteenDualFactor.sub_fifteenDualProjection_hasZeroHostKraU4
            M hM F hFtop)

/-- The exact remaining Cartesian-square obligation upgrades the checked
signed cancellation of the fifteen-dual residual to BHK's `UD-Lim`.  This
statement introduces no dynamical hypothesis: its sole premise is precisely
the product-system cancellation that still has to be derived from `U⁴`
nullity. -/
theorem indicator_fifteenDualResidual_last_uniformDensity_of_cartesian
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hcart :
      let F :=
        MultipleKhintchineCharacteristic.indicatorLp M hM A hA
      let R :=
        HostKraFifteenDualFactor.fifteenDualResidual M hM F
      MultipleKhintchineCartesian.CartesianQuadrupleUniformZero M
        (fun x ↦ F x) (fun x ↦ F x) (fun x ↦ F x) (fun x ↦ R x)) :
    let F :=
      MultipleKhintchineCharacteristic.indicatorLp M hM A hA
    let R :=
      HostKraFifteenDualFactor.fifteenDualResidual M hM F
    MultipleKhintchineSyndetic.TendsToZeroInUniformDensity
      (fun n ↦
        (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
          (fun x ↦ F x) (fun x ↦ F x)
          (fun x ↦ F x) (fun x ↦ R x) n x ∂M.μ).re) := by
  dsimp only
  exact
    MultipleKhintchineCartesian.uniformDensity_re_integral_quadruple_of_cartesian_zero
      M hM _ _ _ _ (by simpa only using hcart)

/-- Base-system form of the exact remaining generalized-von-Neumann
obligation for the indicator residual.  Its conclusion is already the BHK
uniform-density error estimate. -/
theorem indicator_fifteenDualResidual_last_uniformDensity_of_uniform_norm_sq
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hzero :
      let F :=
        MultipleKhintchineCharacteristic.indicatorLp M hM A hA
      let R :=
        HostKraFifteenDualFactor.fifteenDualResidual M hM F
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
          cesaroAverage
            (fun n ↦
              ‖∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
                (fun x ↦ F x) (fun x ↦ F x)
                (fun x ↦ F x) (fun x ↦ R x)
                (i + n) x ∂M.μ‖ ^ 2) N < ε) :
    let F :=
      MultipleKhintchineCharacteristic.indicatorLp M hM A hA
    let R :=
      HostKraFifteenDualFactor.fifteenDualResidual M hM F
    MultipleKhintchineSyndetic.TendsToZeroInUniformDensity
      (fun n ↦
        (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
          (fun x ↦ F x) (fun x ↦ F x)
          (fun x ↦ F x) (fun x ↦ R x) n x ∂M.μ).re) := by
  dsimp only
  exact
    HostKraU4Characteristic.integral_quadruple_uniformDensity_of_uniform_norm_sq
      M hM _ _ _ _ (by simpa only using hzero)

/-- The fifteen-dual residual is negligible in BHK uniform density.  This
closes the former Cartesian-square premise using `U⁴` nullity, without an
ergodicity assumption on the product system. -/
theorem indicator_fifteenDualResidual_last_uniformDensity
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    let F :=
      MultipleKhintchineCharacteristic.indicatorLp M hM A hA
    let R :=
      HostKraFifteenDualFactor.fifteenDualResidual M hM F
    MultipleKhintchineSyndetic.TendsToZeroInUniformDensity
      (fun n ↦
        (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
          (fun x ↦ F x) (fun x ↦ F x)
          (fun x ↦ F x) (fun x ↦ R x) n x ∂M.μ).re) := by
  dsimp only
  let F :=
    MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  let hFtop :=
    MultipleKhintchineCharacteristic.indicatorLp_mem_top M hM A hA
  let R :=
    HostKraFifteenDualFactor.fifteenDualResidual M hM F
  let hRtop :=
    HostKraFifteenDualFactor.fifteenDualResidual_memLp_top
      M hM F hFtop
  apply indicator_fifteenDualResidual_last_uniformDensity_of_uniform_norm_sq
    M hM A hA
  dsimp only
  exact
    Chapter02.HostKraU4UniformNormSq.uniform_norm_sq_of_hasZeroHostKraU4
      M hM hErg
      (fun x ↦ F x) (fun x ↦ F x) (fun x ↦ F x) (fun x ↦ R x)
      hFtop hFtop hFtop hRtop
      (by
        simpa only [R, hRtop] using
          HostKraFifteenDualFactor.sub_fifteenDualProjection_hasZeroHostKraU4
            M hM F hFtop)

end Chapter02.HostKraU4IndicatorCharacteristic
