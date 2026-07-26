import Chapter02.HostKra.HostKraErgodicRelativeJoining
import Chapter02.HostKra.HostKraCubeSeminormRecursion

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HostKraU2Continuous

universe u

open HostKraCubeSeminorm HostKraStandardRelativeJoining

/-- On an ergodic system, the self-correlation of the first Host--Kra cube
lift is the squared modulus of the base self-correlation. -/
theorem cubeLiftOne_selfCorrelation_eq_norm_sq
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (f : M.X → ℂ) (n : ℕ) :
    functionCorrelation
        (relativeCubeSystemOne M hM)
        (cubeLiftOne M hM f) (cubeLiftOne M hM f) n =
      ((‖functionCorrelation M f f n‖ ^ 2 : ℝ) : ℂ) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  rw [functionCorrelation]
  rw [show (relativeCubeSystemOne M hM).μ =
      HostKraStandardRelativeJoining.relativeJoiningMeasure M hM by rfl]
  rw [Chapter02.HostKraErgodicRelativeJoining.relativeJoiningMeasure_eq_prod_of_ergodic
    M hM hErg]
  change
    (∫ p : M.X × M.X,
      cubeLiftOne M hM f (((relativeCubeSystemOne M hM).T^[n]) p) *
        star (cubeLiftOne M hM f p) ∂M.μ.prod M.μ) =
      ((‖functionCorrelation M f f n‖ ^ 2 : ℝ) : ℂ)
  rw [show
      (fun p : M.X × M.X =>
        cubeLiftOne M hM f
            (((relativeCubeSystemOne M hM).T^[n]) p) *
          star (cubeLiftOne M hM f p)) =
        MultipleKhintchineCartesian.cartesianSquare
          (fun x => f ((M.T^[n]) x) * star (f x)) by
    funext p
    rw [show
        (((relativeCubeSystemOne M hM).T^[n]) p) =
          ((M.T^[n]) p.1, (M.T^[n]) p.2) by
      change
        (((MultipleKhintchineCartesian.productSystem M M).T^[n]) p) =
          ((M.T^[n]) p.1, (M.T^[n]) p.2)
      exact MultipleKhintchineCartesian.product_iter M M n p]
    simp only [cubeLiftOne, cubeLift,
      MultipleKhintchineCartesian.cartesianSquare,
      starRingEnd_apply, star_mul, star_star]
    ring]
  rw [MultipleKhintchineCartesian.integral_cartesianSquare]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rfl

/-- On an ergodic system, `U²(f)^4` is the translated-uniform Cesaro limit
of squared base Koopman autocorrelations. -/
theorem hostKraU2Power_uniform_autocorrelation_sq
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
              ((‖functionCorrelation M f f (i + n)‖ ^ 2 : ℝ) : ℂ))
          ((hostKraU2Power M hM f hf : ℝ) : ℂ) < ε := by
  unfold hostKraU2Power
  simpa only [cubeLiftOne_selfCorrelation_eq_norm_sq M hM hErg f] using
    (Chapter02.HostKraCubeSeminormRecursion.uniform_shifted_cesaro_selfCorrelation_invariantEnergy
        (relativeCubeSystemOne M hM)
        (relativeCubeSystemOne_mps M hM)
        (cubeLiftOne M hM f)
        (cubeLiftOne_memLp_two M hM f hf))

/-- Vanishing `U²` gives translated-uniform decay of the squared base
autocorrelation sequence. -/
theorem hostKraU2Power_eq_zero_uniform_autocorrelation_sq
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : hostKraU2Power M hM f hf = 0) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
              ((‖functionCorrelation M f f (i + n)‖ ^ 2 : ℝ) : ℂ))
          0 < ε := by
  intro ε hε
  simpa only [hzero, Complex.ofReal_zero] using
    (hostKraU2Power_uniform_autocorrelation_sq
      M hM hErg f hf ε hε)

/-- Raw function correlation is the Hilbert-space Koopman coefficient for
the forward Koopman isometry. -/
theorem functionCorrelation_eq_koopman_inner
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) (n : ℕ) :
    functionCorrelation M f f n =
      @inner ℂ (Lp ℂ 2 M.μ) _
        (hf.toLp f)
        (((WeakSpectrum.koopmanData M hM).U^[n]) (hf.toLp f)) := by
  rw [CorrelationMean.functionCorrelation_eq_innerLp M hM f f hf hf n]
  rw [← CorrelationMean.koopmanIterLp_apply_toLp M hM n f hf]
  congr 1
  exact
    (WeakSpectrum.koopmanData_iter_eq_koopmanIterLp
      M hM n (hf.toLp f)).symm

/-- Ordinary (unshifted) Wiener square-correlation decay extracted from
vanishing `U²`. -/
theorem hostKraU2Power_eq_zero_autocorrelation_sq_tendsto_zero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : hostKraU2Power M hM f hf = 0) :
    let hf2 : M.lpMember 2 f := by
      letI : IsProbabilityMeasure M.μ := hM.1
      exact hf.mono_exponent (by simp)
    Tendsto
      (fun N : ℕ => if N = 0 then 0 else
        ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
          ‖@inner ℂ (Lp ℂ 2 M.μ) _
            (((WeakSpectrum.koopmanData M hM).U^[n]) (hf2.toLp f))
            (hf2.toLp f)‖ ^ 2)
      atTop (nhds 0) := by
  dsimp only
  let hf2 : M.lpMember 2 f := by
    letI : IsProbabilityMeasure M.μ := hM.1
    exact hf.mono_exponent (by simp)
  have huniform :=
    hostKraU2Power_eq_zero_uniform_autocorrelation_sq
      M hM hErg f hf hzero
  have hcomplex :
      Tendsto
        (fun N : ℕ => if N = 0 then 0 else
          ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
            ((‖functionCorrelation M f f n‖ ^ 2 : ℝ) : ℂ))
        atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := (eventually_atTop.1 (huniform ε hε))
    refine ⟨N, ?_⟩
    intro n hn
    simpa using hN n hn 0
  rw [show
      (fun N : ℕ => if N = 0 then 0 else
        ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
          ((‖functionCorrelation M f f n‖ ^ 2 : ℝ) : ℂ)) =
        fun N : ℕ => ((if N = 0 then 0 else
          ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
            ‖@inner ℂ (Lp ℂ 2 M.μ) _
              (((WeakSpectrum.koopmanData M hM).U^[n]) (hf2.toLp f))
              (hf2.toLp f)‖ ^ 2 : ℝ) : ℂ) by
    funext N
    by_cases hN : N = 0
    · simp [hN]
    · simp only [hN, if_false,
        functionCorrelation_eq_koopman_inner M hM f hf2,
        norm_inner_symm]
      push_cast
      rfl] at hcomplex
  simpa only [Function.comp_apply, Complex.ofReal_re, Complex.zero_re] using
    (Complex.continuous_re.continuousAt.tendsto.comp hcomplex)

/-- For a possibly non-surjective linear isometry, an atomless Herglotz
measure of the forward autocorrelation still forces orthogonality to every
eigenvector.  This is the converse half of the isometric Wiener bridge. -/
theorem continuous_measure_implies_continuous_subspace_isometry
    (D : HilbertOperatorData.{u})
    (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ n : ℕ, circleFourierCoefficient μ n =
      @inner ℂ D.H _ x ((D.U^[n]) x))
    (hcont : IsContinuousCircleMeasure μ) :
    InContinuousSpectralSubspace D x := by
  intro y hy
  obtain ⟨hy0, lam, hlam⟩ := hy
  have hlamNorm :
      ‖lam‖ = 1 :=
    AlmostPeriodicIsometry.eigenvalue_norm_one D hU y hy0 lam hlam
  let z : Circle :=
    ⟨lam, mem_sphere_zero_iff_norm.mpr hlamNorm⟩
  let V := IsometryWiener.modulatedOperator D z
  let S : Submodule ℂ D.H :=
    LinearMap.eqLocus V (1 : D.H →L[ℂ] D.H)
  have hyS : y ∈ S := by
    change V y = y
    change star lam • D.U y = y
    rw [hlam, smul_smul]
    have hunit : star lam * lam = 1 := by
      change (starRingEnd ℂ) lam * lam = 1
      rw [← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq, hlamNorm]
      norm_num
    rw [hunit, one_smul]
  have havg :
      Tendsto
        (fun N : ℕ =>
          birkhoffAverage ℂ V _root_.id N x)
        atTop (nhds (S.orthogonalProjection x : D.H)) := by
    exact V.tendsto_birkhoffAverage_orthogonalProjection
      (IsometryWiener.modulatedOperator_norm_le_one D hU z) x
  have hinnerProjection :
      Tendsto
        (fun N : ℕ =>
          @inner ℂ D.H _ x
            (birkhoffAverage ℂ V _root_.id N x))
        atTop
        (nhds (@inner ℂ D.H _ x
          (S.orthogonalProjection x : D.H))) := by
    exact tendsto_const_nhds.inner havg
  have hkernel :=
    IsometryWiener.tendsto_integral_pointKernel μ z
  rw [IsometryWiener.integral_pointKernel_limit] at hkernel
  have hinnerZero :
      Tendsto
        (fun N : ℕ =>
          @inner ℂ D.H _ x
            (birkhoffAverage ℂ V _root_.id N x))
        atTop (nhds 0) := by
    have heq :
        (fun N : ℕ =>
          ∫ w, IsometryWiener.pointKernel z N w ∂μ.μ) =
        fun N : ℕ =>
          @inner ℂ D.H _ x
            (birkhoffAverage ℂ V _root_.id N x) := by
      funext N
      exact IsometryWiener.integral_pointKernel_eq
        D x μ hμ z N
    rw [heq] at hkernel
    have hzreal : μ.μ.real {z} = 0 :=
      (measureReal_eq_zero_iff).2 (hcont z)
    simpa [hzreal] using hkernel
  have hxp :
      @inner ℂ D.H _ x (S.orthogonalProjection x : D.H) = 0 :=
    tendsto_nhds_unique hinnerProjection hinnerZero
  let p : D.H := S.orthogonalProjection x
  have hpS : p ∈ S :=
    S.starProjection_apply_mem x
  have hxmp : x - p ∈ Sᗮ :=
    S.sub_starProjection_mem_orthogonal x
  have hpp : @inner ℂ D.H _ p p = 0 := by
    have horth : @inner ℂ D.H _ (x - p) p = 0 :=
      S.inner_left_of_mem_orthogonal hpS hxmp
    have hxp' : @inner ℂ D.H _ x p = 0 := by
      simpa only [p] using hxp
    calc
      @inner ℂ D.H _ p p =
          @inner ℂ D.H _ x p -
            @inner ℂ D.H _ (x - p) p := by
              rw [inner_sub_left]
              ring
      _ = 0 := by rw [hxp', horth, sub_zero]
  have hp0 : p = 0 := inner_self_eq_zero.mp hpp
  have hxy : @inner ℂ D.H _ (x - p) y = 0 :=
    S.inner_left_of_mem_orthogonal hyS hxmp
  simpa [hp0] using hxy

/-- Full Wiener equivalence for a forward linear isometry, with no
surjectivity assumption. -/
theorem autocorrelation_sq_tendsto_zero_iff_continuous_isometry
    (D : HilbertOperatorData.{u})
    (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) :
    Tendsto
      (fun N : ℕ => if N = 0 then 0 else
        ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
          ‖@inner ℂ D.H _ ((D.U^[n]) x) x‖ ^ 2)
      atTop (nhds 0) ↔
      InContinuousSpectralSubspace D x := by
  constructor
  · intro hdecay
    obtain ⟨μ, hμ⟩ :=
      IsometryWiener.exists_spectralMeasure D hU x
    have hwiener :
        Tendsto
          (fun N : ℕ => if N = 0 then 0 else
            ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
              ‖circleFourierCoefficient μ n‖ ^ 2)
          atTop (nhds 0) := by
      convert hdecay using 1
      funext N
      by_cases hN : N = 0
      · simp [hN]
      · simp only [hN, if_false]
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        rw [hμ n, norm_inner_symm]
    have hcont :=
      (SpectralWiener.circle_wiener_zero_iff_continuous μ).1 hwiener
    exact continuous_measure_implies_continuous_subspace_isometry
      D hU x μ hμ hcont
  · exact IsometryWiener.continuous_autocorrelation_sq_tendsto_zero
      D hU x

/-- On an ergodic standard Borel system, vanishing `U²` places the original
function in the continuous spectral subspace of the forward Koopman
isometry. -/
theorem hostKraU2Power_eq_zero_implies_continuous
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : hostKraU2Power M hM f hf = 0) :
    let hf2 : M.lpMember 2 f := by
      letI : IsProbabilityMeasure M.μ := hM.1
      exact hf.mono_exponent (by simp)
    InContinuousSpectralSubspace
      (WeakSpectrum.koopmanData M hM) (hf2.toLp f) := by
  dsimp only
  let hf2 : M.lpMember 2 f := by
    letI : IsProbabilityMeasure M.μ := hM.1
    exact hf.mono_exponent (by simp)
  apply
    (autocorrelation_sq_tendsto_zero_iff_continuous_isometry
      (WeakSpectrum.koopmanData M hM)
      (fun F => (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map F)
      (hf2.toLp f)).1
  exact hostKraU2Power_eq_zero_autocorrelation_sq_tendsto_zero
    M hM hErg f hf hzero

end Chapter02.HostKraU2Continuous
