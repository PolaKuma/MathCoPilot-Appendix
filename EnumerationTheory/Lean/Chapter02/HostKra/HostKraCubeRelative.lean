import Chapter02.HostKra.HostKraCubeThree
import Chapter02.HostKra.HostKraRelativeMean

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter02.HostKraCubeRelative

universe u

/-- Relative four-vertex recursion.  On a nonergodic system (in particular
on a Cartesian square), the second-edge average converges uniformly over
translated intervals to the pairing of the first derivative with its
invariant component. -/
theorem cubeTwo_relative_uniform_inner_limit
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ m ∈ Finset.range N,
              ∫ x,
                HostKraCubeTwo.cubeTwoIntegrand M F n (i + m) x
                ∂M.μ)
          (@inner ℂ (Lp ℂ 2 M.μ) _
            (HostKraCubeThree.cubeDerivativeLp M hM F hFtop n)
            (HostKraRelativeMean.invariantMeanLp M hM
              (HostKraCubeTwo.cubeDerivative M hM F n)
              (HostKraCubeTwo.cubeDerivative_memLp
                M hM F hFtop n))) < ε := by
  have hD :=
    HostKraCubeTwo.cubeDerivative_memLp M hM F hFtop n
  simpa only [
    HostKraCubeTwo.functionCorrelation_cubeDerivative,
    HostKraCubeThree.cubeDerivativeLp] using
    (HostKraRelativeMean.uniform_shifted_cesaroFunctionCorrelations_invariantMean
        M hM
        (HostKraCubeTwo.cubeDerivative M hM F n)
        (HostKraCubeTwo.cubeDerivative M hM F n)
        hD hD)

/-- Energy form of the relative four-vertex recursion. -/
theorem cubeTwo_relative_uniform_energy_limit
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    let I :=
      HostKraRelativeMean.invariantMeanLp M hM
        (HostKraCubeTwo.cubeDerivative M hM F n)
        (HostKraCubeTwo.cubeDerivative_memLp M hM F hFtop n)
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ m ∈ Finset.range N,
              ∫ x,
                HostKraCubeTwo.cubeTwoIntegrand M F n (i + m) x
                ∂M.μ)
          (@inner ℂ (Lp ℂ 2 M.μ) _ I I) < ε := by
  dsimp only
  simpa only [
    HostKraCubeThree.cubeDerivativeLp,
    HostKraRelativeMean.inner_invariantMeanLp_eq_self
      M hM
      (HostKraCubeTwo.cubeDerivative M hM F n)
      (HostKraCubeTwo.cubeDerivative_memLp M hM F hFtop n)] using
    cubeTwo_relative_uniform_inner_limit M hM F hFtop n

theorem cubeTwo_relative_uniform_zero_limit
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ)
    (hzero :
      HostKraRelativeMean.invariantMeanLp M hM
        (HostKraCubeTwo.cubeDerivative M hM F n)
        (HostKraCubeTwo.cubeDerivative_memLp M hM F hFtop n) = 0) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ m ∈ Finset.range N,
              ∫ x,
                HostKraCubeTwo.cubeTwoIntegrand M F n (i + m) x
                ∂M.μ)
          0 < ε := by
  simpa only [hzero, inner_zero_right] using
    cubeTwo_relative_uniform_energy_limit M hM F hFtop n

/-- Canonical `L²` representative of the twice-iterated derivative. -/
def cubeSecondDerivativeLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n m : ℕ) : Lp ℂ 2 M.μ :=
  (HostKraCubeThree.cubeSecondDerivative_memLp
    M hM F hFtop n m).toLp
      (HostKraCubeThree.cubeSecondDerivative M hM F hFtop n m)

/-- Relative eight-vertex recursion.  This is the form required when the
Host--Kra construction is iterated on a Cartesian power whose invariant
sigma-algebra is not trivial. -/
theorem cubeThree_relative_uniform_inner_limit
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n m : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ k ∈ Finset.range N,
              ∫ x,
                HostKraCubeThree.cubeThreeIntegrand
                  M hM F hFtop n m (i + k) x
                ∂M.μ)
          (@inner ℂ (Lp ℂ 2 M.μ) _
            (cubeSecondDerivativeLp M hM F hFtop n m)
            (HostKraRelativeMean.invariantMeanLp M hM
              (HostKraCubeThree.cubeSecondDerivative
                M hM F hFtop n m)
              (HostKraCubeThree.cubeSecondDerivative_memLp
                M hM F hFtop n m))) < ε := by
  have hD :=
    HostKraCubeThree.cubeSecondDerivative_memLp
      M hM F hFtop n m
  simpa only [
    HostKraCubeThree.functionCorrelation_cubeSecondDerivative,
    cubeSecondDerivativeLp] using
    (HostKraRelativeMean.uniform_shifted_cesaroFunctionCorrelations_invariantMean
        M hM
        (HostKraCubeThree.cubeSecondDerivative M hM F hFtop n m)
        (HostKraCubeThree.cubeSecondDerivative M hM F hFtop n m)
        hD hD)

/-- Energy form of the relative eight-vertex recursion. -/
theorem cubeThree_relative_uniform_energy_limit
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n m : ℕ) :
    let I :=
      HostKraRelativeMean.invariantMeanLp M hM
        (HostKraCubeThree.cubeSecondDerivative M hM F hFtop n m)
        (HostKraCubeThree.cubeSecondDerivative_memLp
          M hM F hFtop n m)
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ k ∈ Finset.range N,
              ∫ x,
                HostKraCubeThree.cubeThreeIntegrand
                  M hM F hFtop n m (i + k) x
                ∂M.μ)
          (@inner ℂ (Lp ℂ 2 M.μ) _ I I) < ε := by
  dsimp only
  simpa only [
    cubeSecondDerivativeLp,
    HostKraRelativeMean.inner_invariantMeanLp_eq_self
      M hM
      (HostKraCubeThree.cubeSecondDerivative M hM F hFtop n m)
      (HostKraCubeThree.cubeSecondDerivative_memLp
        M hM F hFtop n m)] using
    cubeThree_relative_uniform_inner_limit M hM F hFtop n m

theorem cubeThree_relative_uniform_zero_limit
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n m : ℕ)
    (hzero :
      HostKraRelativeMean.invariantMeanLp M hM
        (HostKraCubeThree.cubeSecondDerivative M hM F hFtop n m)
        (HostKraCubeThree.cubeSecondDerivative_memLp
          M hM F hFtop n m) = 0) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ k ∈ Finset.range N,
              ∫ x,
                HostKraCubeThree.cubeThreeIntegrand
                  M hM F hFtop n m (i + k) x
                ∂M.μ)
          0 < ε := by
  simpa only [hzero, inner_zero_right] using
    cubeThree_relative_uniform_energy_limit M hM F hFtop n m

end Chapter02.HostKraCubeRelative
