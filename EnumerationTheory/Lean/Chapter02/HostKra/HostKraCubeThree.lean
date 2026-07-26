import Chapter02.HostKra.HostKraCubeTwo

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter02.HostKraCubeThree

universe u

-- This module records the recursive cube layer independently of the
-- characteristic-factor construction that will consume it.

/-- The first multiplicative derivative, represented canonically in `L²`
so that the cube construction can be iterated. -/
def cubeDerivativeLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) : Lp ℂ 2 M.μ :=
  (HostKraCubeTwo.cubeDerivative_memLp M hM F hFtop n).toLp
    (HostKraCubeTwo.cubeDerivative M hM F n)

lemma cubeDerivativeLp_coe
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    (fun x ↦ cubeDerivativeLp M hM F hFtop n x) =ᵐ[M.μ]
      HostKraCubeTwo.cubeDerivative M hM F n := by
  exact
    (HostKraCubeTwo.cubeDerivative_memLp M hM F hFtop n).coeFn_toLp

lemma cubeDerivativeLp_memLp_top
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    MemLp (fun x ↦ cubeDerivativeLp M hM F hFtop n x) ⊤ M.μ := by
  exact MemLp.ae_eq
    (cubeDerivativeLp_coe M hM F hFtop n).symm
    (HostKraCubeTwo.cubeDerivative_memLp_top M hM F hFtop n)

/-- The twice-iterated multiplicative derivative.  Its values contain the
eight vertices of the three-dimensional Host--Kra cube, modulo the canonical
`L²` representative chosen above. -/
def cubeSecondDerivative
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n m : ℕ) : M.X → ℂ :=
  HostKraCubeTwo.cubeDerivative M hM
    (cubeDerivativeLp M hM F hFtop n) m

lemma cubeSecondDerivative_memLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n m : ℕ) :
    MemLp (cubeSecondDerivative M hM F hFtop n m) 2 M.μ := by
  exact HostKraCubeTwo.cubeDerivative_memLp M hM
    (cubeDerivativeLp M hM F hFtop n)
    (cubeDerivativeLp_memLp_top M hM F hFtop n) m

lemma cubeSecondDerivative_memLp_top
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n m : ℕ) :
    MemLp (cubeSecondDerivative M hM F hFtop n m) ⊤ M.μ := by
  exact HostKraCubeTwo.cubeDerivative_memLp_top M hM
    (cubeDerivativeLp M hM F hFtop n)
    (cubeDerivativeLp_memLp_top M hM F hFtop n) m

/-- The mean of the second derivative is the autocorrelation of the first
derivative in its canonical `L²` realization. -/
lemma integral_cubeSecondDerivative
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n m : ℕ) :
    ∫ x, cubeSecondDerivative M hM F hFtop n m x ∂M.μ =
      @inner ℂ (Lp ℂ 2 M.μ) _
        (cubeDerivativeLp M hM F hFtop n)
        (((MultipleKhintchineCharacteristic.KData M hM).U^[m])
          (cubeDerivativeLp M hM F hFtop n)) := by
  exact HostKraCubeTwo.integral_cubeDerivative M hM
    (cubeDerivativeLp M hM F hFtop n) m

/-- The eight-vertex, three-dimensional Host--Kra cube integrand.  It is
written using the canonical `L²` representative of the first derivative;
expanding `cubeDerivativeLp` gives the vertices indexed by
`{0,1}³` with edge lengths `n`, `m`, and `k`. -/
def cubeThreeIntegrand
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n m k : ℕ) (x : M.X) : ℂ :=
  HostKraCubeTwo.cubeTwoIntegrand M
    (cubeDerivativeLp M hM F hFtop n) m k x

/-- An ordinary self-correlation of the twice-iterated derivative is the
integral over the corresponding eight-vertex Host--Kra cube. -/
lemma functionCorrelation_cubeSecondDerivative
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n m k : ℕ) :
    functionCorrelation M
        (cubeSecondDerivative M hM F hFtop n m)
        (cubeSecondDerivative M hM F hFtop n m) k =
      ∫ x, cubeThreeIntegrand M hM F hFtop n m k x ∂M.μ := by
  exact HostKraCubeTwo.functionCorrelation_cubeDerivative M hM
    (cubeDerivativeLp M hM F hFtop n) m k

/-- The innermost averaging direction of the three-dimensional cube,
uniformly over translated intervals. -/
theorem cubeSecondDerivative_uniform_correlation_limit
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n m : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ k ∈ Finset.range N,
              functionCorrelation M
                (cubeSecondDerivative M hM F hFtop n m)
                (cubeSecondDerivative M hM F hFtop n m) (i + k))
          ((‖@inner ℂ (Lp ℂ 2 M.μ) _
              (cubeDerivativeLp M hM F hFtop n)
              (((MultipleKhintchineCharacteristic.KData M hM).U^[m])
                (cubeDerivativeLp M hM F hFtop n))‖ ^ 2 : ℝ) : ℂ) < ε := by
  exact HostKraCubeTwo.cubeDerivative_uniform_correlation_limit
    M hM hErg
    (cubeDerivativeLp M hM F hFtop n)
    (cubeDerivativeLp_memLp_top M hM F hFtop n) m

/-- Eight-vertex formulation of
`cubeSecondDerivative_uniform_correlation_limit`.  This is the checked
three-dimensional cube recursion needed before constructing the `Z₂`
characteristic factor. -/
theorem cubeThree_uniform_inner_limit
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n m : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ k ∈ Finset.range N,
              ∫ x, cubeThreeIntegrand M hM F hFtop n m (i + k) x ∂M.μ)
          ((‖@inner ℂ (Lp ℂ 2 M.μ) _
              (cubeDerivativeLp M hM F hFtop n)
              (((MultipleKhintchineCharacteristic.KData M hM).U^[m])
                (cubeDerivativeLp M hM F hFtop n))‖ ^ 2 : ℝ) : ℂ) < ε := by
  simpa only [functionCorrelation_cubeSecondDerivative] using
    cubeSecondDerivative_uniform_correlation_limit M hM hErg F hFtop n m

end Chapter02.HostKraCubeThree
