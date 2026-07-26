import Chapter02.Recurrence.MultipleKhintchineUniform

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter02.HostKraCubeTwo

universe u

/-- The multiplicative first derivative used in the two-dimensional
Host--Kra cube. -/
def cubeDerivative
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) (n : ℕ) : M.X → ℂ :=
  MultipleKhintchineCharacteristic.leftPairFunction M hM F n 0

lemma cubeDerivative_ae_eq
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) (n : ℕ) :
    cubeDerivative M hM F n =ᵐ[M.μ]
      fun x ↦ F ((M.T^[n]) x) * star (F x) := by
  filter_upwards [
    MultipleKhintchineKronecker.koopmanData_iter_ae M hM n F] with x hnx
  simp only [cubeDerivative,
    MultipleKhintchineCharacteristic.leftPairFunction,
    Function.iterate_zero_apply]
  rw [hnx]

lemma cubeDerivative_memLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    MemLp (cubeDerivative M hM F n) 2 M.μ := by
  exact
    MultipleKhintchineCharacteristic.leftPairFunction_memLp
      M hM F hFtop n 0

lemma cubeDerivative_memLp_top
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    MemLp (cubeDerivative M hM F n) ⊤ M.μ := by
  unfold cubeDerivative
  have hleft :
      MemLp (fun x ↦
        (show Lp ℂ 2 M.μ from
          ((MultipleKhintchineCharacteristic.KData M hM).U^[n]) F) x)
        ⊤ M.μ :=
    MultipleKhintchineKronecker.koopmanData_iter_memLp_top
      M hM n F hFtop
  have hright :
      MemLp (fun x ↦ star
        ((show Lp ℂ 2 M.μ from
          ((MultipleKhintchineCharacteristic.KData M hM).U^[0]) F) x))
        ⊤ M.μ :=
    (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
      M hM 0 F hFtop).star
  exact hright.mul (r := ⊤) hleft

/-- The mean of a cube derivative is the corresponding Koopman
autocorrelation. -/
lemma integral_cubeDerivative
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) (n : ℕ) :
    ∫ x, cubeDerivative M hM F n x ∂M.μ =
      @inner ℂ (Lp ℂ 2 M.μ) _
        F (((MultipleKhintchineCharacteristic.KData M hM).U^[n]) F) := by
  rw [L2.inner_def]
  rfl

/-- The four vertices of the two-dimensional multiplicative cube with
edge lengths `n` and `m`. -/
def cubeTwoIntegrand
    (M : System.{u}) (F : Lp ℂ 2 M.μ) (n m : ℕ) (x : M.X) : ℂ :=
  F ((M.T^[n + m]) x) * star (F ((M.T^[m]) x)) *
    star (F ((M.T^[n]) x)) * F x

/-- An ordinary self-correlation of a first cube derivative is exactly
the integral over the corresponding four-vertex Host--Kra cube. -/
lemma functionCorrelation_cubeDerivative
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) (n m : ℕ) :
    functionCorrelation M
        (cubeDerivative M hM F n) (cubeDerivative M hM F n) m =
      ∫ x, cubeTwoIntegrand M F n m x ∂M.μ := by
  apply integral_congr_ae
  have hn :=
    MultipleKhintchineKronecker.koopmanData_iter_ae M hM n F
  have hnm :=
    (hM.2.iterate m).quasiMeasurePreserving.ae_eq_comp hn
  filter_upwards [hn, hnm] with x hnx hnmx
  simp only [cubeDerivative,
    MultipleKhintchineCharacteristic.leftPairFunction,
    cubeTwoIntegrand, star_mul, star_star]
  rw [hnx]
  have hnmx' :
      (show Lp ℂ 2 M.μ from
        ((MultipleKhintchineKronecker.koopmanData M hM).U^[n]) F)
          ((M.T^[m]) x) =
        F ((M.T^[n + m]) x) := by
    simpa only [Function.comp_apply, Function.iterate_add_apply] using hnmx
  rw [hnmx']
  simp only [Function.iterate_zero_apply]
  ring

/-- The inner averaging direction of the two-dimensional Host--Kra cube:
for every fixed first edge, translated averages of the second-edge
correlations converge uniformly to the squared modulus of the first-edge
autocorrelation. -/
theorem cubeDerivative_uniform_correlation_limit
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ m ∈ Finset.range N,
              functionCorrelation M
                (cubeDerivative M hM F n)
                (cubeDerivative M hM F n) (i + m))
          ((‖@inner ℂ (Lp ℂ 2 M.μ) _
              F (((MultipleKhintchineCharacteristic.KData M hM).U^[n]) F)‖
              ^ 2 : ℝ) : ℂ) < ε := by
  have hD := cubeDerivative_memLp M hM F hFtop n
  have hu :=
    MultipleKhintchineUniform.ergodic_uniform_shifted_cesaroFunctionCorrelations
      M hM hErg
      (cubeDerivative M hM F n)
      (cubeDerivative M hM F n)
      hD hD
  intro ε hε
  have huv := hu ε hε
  filter_upwards [huv] with N hN
  intro i
  have hi := hN i
  rw [show productOfMeans M
      (cubeDerivative M hM F n)
      (cubeDerivative M hM F n) =
        ((‖@inner ℂ (Lp ℂ 2 M.μ) _
            F (((MultipleKhintchineCharacteristic.KData M hM).U^[n]) F)‖
            ^ 2 : ℝ) : ℂ) by
    unfold productOfMeans
    rw [integral_cubeDerivative M hM F n]
    change
      @inner ℂ (Lp ℂ 2 M.μ) _
          F (((MultipleKhintchineCharacteristic.KData M hM).U^[n]) F) *
        (starRingEnd ℂ)
          (@inner ℂ (Lp ℂ 2 M.μ) _
            F (((MultipleKhintchineCharacteristic.KData M hM).U^[n]) F)) =
        ((‖@inner ℂ (Lp ℂ 2 M.μ) _
            F (((MultipleKhintchineCharacteristic.KData M hM).U^[n]) F)‖
            ^ 2 : ℝ) : ℂ)
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]]
    at hi
  exact hi

/-- Four-vertex formulation of
`cubeDerivative_uniform_correlation_limit`.  This is the checked
two-dimensional cube recursion used by the next Host--Kra layer. -/
theorem cubeTwo_uniform_inner_limit
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ m ∈ Finset.range N,
              ∫ x, cubeTwoIntegrand M F n (i + m) x ∂M.μ)
          ((‖@inner ℂ (Lp ℂ 2 M.μ) _
              F (((MultipleKhintchineCharacteristic.KData M hM).U^[n]) F)‖
              ^ 2 : ℝ) : ℂ) < ε := by
  simpa only [functionCorrelation_cubeDerivative] using
    cubeDerivative_uniform_correlation_limit M hM hErg F hFtop n

end Chapter02.HostKraCubeTwo
