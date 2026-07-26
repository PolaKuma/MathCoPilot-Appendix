import Chapter02.HostKra.HostKraU2Continuous
import Chapter02.HostKra.HostKraRelativeJoiningComplex
import Chapter02.Recurrence.MultipleKhintchineUniform

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HostKraU3ProgressionDecay

universe u

open HostKraCubeSeminorm

/-- On an ergodic standard Borel system, vanishing `U³` places the
original function in the continuous spectral subspace of the forward
Koopman isometry.  This packages the recursive `U³ → U²` implication
with the isometric Wiener criterion. -/
theorem hasZeroHostKraU3_implies_continuous
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : HasZeroHostKraU3 M hM f hf) :
    let hf2 : M.lpMember 2 f := by
      letI : IsProbabilityMeasure M.μ := hM.1
      exact hf.mono_exponent (by simp)
    InContinuousSpectralSubspace
      (MultipleKhintchineCharacteristic.KData M hM) (hf2.toLp f) := by
  dsimp only
  let hf2 : M.lpMember 2 f := by
    letI : IsProbabilityMeasure M.μ := hM.1
    exact hf.mono_exponent (by simp)
  have hU2 :
      hostKraU2Power M hM f hf = 0 :=
    Chapter02.HostKraRelativeJoiningComplex.hostKraU2Power_eq_zero_of_hasZeroHostKraU3
      M hM f hf hzero
  have hcont :=
    Chapter02.HostKraU2Continuous.hostKraU2Power_eq_zero_implies_continuous
      M hM hErg f hf hU2
  simpa only [WeakSpectrum.koopmanData,
    MultipleKhintchineCharacteristic.KData,
    MultipleKhintchineKronecker.koopmanData] using hcont

/-- A `U³`-null second factor gives the existing uniform van der Corput
block decay for the bilinear progression `(T^n F) (T^(2n) g)`. -/
theorem doubleKoopmanProduct_hasUniformBlockDecay_of_hasZeroHostKraU3
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F : Lp ℂ 2 M.μ)
    (g : M.X → ℂ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hg : MemLp g ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (hzero : HasZeroHostKraU3 M hM g hg) :
    let hg2 : M.lpMember 2 g := by
      letI : IsProbabilityMeasure M.μ := hM.1
      exact hg.mono_exponent (by simp)
    VanDerCorput.HasUniformVanDerCorputBlockDecay
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F (hg2.toLp g) hFtop) := by
  dsimp only
  let hg2 : M.lpMember 2 g := by
    letI : IsProbabilityMeasure M.μ := hM.1
    exact hg.mono_exponent (by simp)
  have hGtop : MemLp (fun x ↦ (hg2.toLp g) x) ⊤ M.μ := by
    exact (memLp_congr_ae hg2.coeFn_toLp).2 hg
  exact
    MultipleKhintchineUniform.doubleKoopmanProduct_hasUniformBlockDecay
      M hM hErg F (hg2.toLp g) hFtop hGtop C hC hFbound
      (hasZeroHostKraU3_implies_continuous M hM hErg g hg hzero)

/-- Consequently the translated Cesàro averages of the same bilinear
progression converge uniformly to zero. -/
theorem doubleKoopmanProduct_uniform_cesaro_zero_of_hasZeroHostKraU3
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F : Lp ℂ 2 M.μ)
    (g : M.X → ℂ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hg : MemLp g ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (hzero : HasZeroHostKraU3 M hM g hg) :
    let hg2 : M.lpMember 2 g := by
      letI : IsProbabilityMeasure M.μ := hM.1
      exact hg.mono_exponent (by simp)
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1),
            MultipleKhintchineCharacteristic.doubleKoopmanProduct
              M hM F (hg2.toLp g) hFtop (i + n)‖ < ε := by
  dsimp only
  let hg2 : M.lpMember 2 g := by
    letI : IsProbabilityMeasure M.μ := hM.1
    exact hg.mono_exponent (by simp)
  have hGtop : MemLp (fun x ↦ (hg2.toLp g) x) ⊤ M.μ := by
    exact (memLp_congr_ae hg2.coeFn_toLp).2 hg
  exact
    MultipleKhintchineUniform.doubleKoopmanProduct_uniform_cesaro_zero
      M hM hErg F (hg2.toLp g) hFtop hGtop C hC hFbound
      (hasZeroHostKraU3_implies_continuous M hM hErg g hg hzero)

end Chapter02.HostKraU3ProgressionDecay
