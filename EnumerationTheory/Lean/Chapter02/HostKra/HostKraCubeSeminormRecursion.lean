import Chapter02.HostKra.HostKraCubeSeminormDynamics

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HostKraCubeSeminormRecursion

universe u

open HostKraCubeSeminorm HostKraStandardRelativeJoining

/-- The invariant energy is the translated-uniform Cesàro limit of the
self-correlation sequence.  This is the time-average form of the recursive
Host--Kra seminorm definition. -/
theorem uniform_shifted_cesaro_selfCorrelation_invariantEnergy
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
              functionCorrelation M f f (i + n))
          ((invariantEnergy M hM f hf : ℝ) : ℂ) < ε := by
  intro ε hε
  have hlimit :=
    HostKraRelativeMean.uniform_shifted_cesaroFunctionCorrelations_invariantMean
      M hM f f hf hf ε hε
  have hinner :
      @inner ℂ (Lp ℂ 2 M.μ) _ (hf.toLp f)
          (HostKraRelativeMean.invariantMeanLp M hM f hf) =
        ((invariantEnergy M hM f hf : ℝ) : ℂ) := by
    rw [HostKraRelativeMean.inner_invariantMeanLp_eq_self M hM f hf]
    rw [inner_self_eq_norm_sq_to_K]
    simp only [invariantEnergy, Complex.ofReal_pow]
    rfl
  simpa only [hinner] using hlimit

/-- `U³(f)^8` as a translated-uniform time average on the genuine
four-vertex Host--Kra cube system. -/
theorem hostKraU3Power_uniform_cubeCorrelation
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
              functionCorrelation
                (relativeCubeSystemTwo M hM)
                (cubeLiftTwo M hM f) (cubeLiftTwo M hM f) (i + n))
          ((hostKraU3Power M hM f hf : ℝ) : ℂ) < ε := by
  simpa only [hostKraU3Power] using
    (uniform_shifted_cesaro_selfCorrelation_invariantEnergy
      (relativeCubeSystemTwo M hM)
      (relativeCubeSystemTwo_mps M hM)
      (cubeLiftTwo M hM f)
      (cubeLiftTwo_memLp_two M hM f hf))

/-- `U⁴(f)^16` as a translated-uniform time average on the genuine
eight-vertex Host--Kra cube system. -/
theorem hostKraU4Power_uniform_cubeCorrelation
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
              functionCorrelation
                (relativeCubeSystemThree M hM)
                (cubeLiftThree M hM f) (cubeLiftThree M hM f) (i + n))
          ((hostKraU4Power M hM f hf : ℝ) : ℂ) < ε := by
  simpa only [hostKraU4Power] using
    (uniform_shifted_cesaro_selfCorrelation_invariantEnergy
      (relativeCubeSystemThree M hM)
      (relativeCubeSystemThree_mps M hM)
      (cubeLiftThree M hM f)
      (cubeLiftThree_memLp_two M hM f hf))

/-- The time-average form of `HasZeroHostKraU3`. -/
theorem hasZeroHostKraU3_uniform_cubeCorrelation_zero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : HasZeroHostKraU3 M hM f hf) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
              functionCorrelation
                (relativeCubeSystemTwo M hM)
                (cubeLiftTwo M hM f) (cubeLiftTwo M hM f) (i + n))
          0 < ε := by
  change hostKraU3Power M hM f hf = 0 at hzero
  intro ε hε
  simpa only [hzero, Complex.ofReal_zero] using
    (hostKraU3Power_uniform_cubeCorrelation M hM f hf ε hε)

/-- The time-average form of `HasZeroHostKraU4`. -/
theorem hasZeroHostKraU4_uniform_cubeCorrelation_zero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : HasZeroHostKraU4 M hM f hf) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
              functionCorrelation
                (relativeCubeSystemThree M hM)
                (cubeLiftThree M hM f) (cubeLiftThree M hM f) (i + n))
          0 < ε := by
  change hostKraU4Power M hM f hf = 0 at hzero
  intro ε hε
  simpa only [hzero, Complex.ofReal_zero] using
    (hostKraU4Power_uniform_cubeCorrelation M hM f hf ε hε)

end Chapter02.HostKraCubeSeminormRecursion
