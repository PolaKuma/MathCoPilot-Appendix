import Chapter02.HostKra.HostKraU4IndicatorCharacteristic

open Classical Filter MeasureTheory Set

noncomputable section

namespace Chapter02.HostKraFourfoldStructuredReduction

universe u

/-- The fourfold correlation after removing exactly the last-slot
fifteen-dual residual.  This is the structured correlation sequence whose
recurrence is the only remaining fourfold structure obligation. -/
def fifteenDualStructuredCorrelation
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) : ℝ :=
  let F := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  let R := HostKraFifteenDualFactor.fifteenDualResidual M hM F
  MultipleKhintchineSyndetic.quadrupleCorrelation M A n -
    (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
      (fun x ↦ F x) (fun x ↦ F x)
      (fun x ↦ F x) (fun x ↦ R x) n x ∂M.μ).re

/-- The preceding difference definition is exactly the progression with
the conditional projection in the last slot. -/
theorem fifteenDualStructuredCorrelation_eq_projectionIntegral
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) :
    let F := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
    let P := HostKraDualSigma.condExpL2Value M.μ
      (HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM) F
    fifteenDualStructuredCorrelation M hM A hA n =
      (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
        (fun x ↦ F x) (fun x ↦ F x)
        (fun x ↦ F x) (fun x ↦ P x) n x ∂M.μ).re := by
  dsimp only
  letI : IsProbabilityMeasure M.μ := hM.1
  let F := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  let hFtop :=
    MultipleKhintchineCharacteristic.indicatorLp_mem_top M hM A hA
  let P := HostKraDualSigma.condExpL2Value M.μ
    (HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM) F
  let hPtop : MemLp (fun x ↦ P x) ⊤ M.μ :=
    HostKraDualSigma.condExpL2Value_memLp_top M.μ
      (HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM)
      F hFtop
  let R := HostKraFifteenDualFactor.fifteenDualResidual M hM F
  let hRtop :=
    HostKraFifteenDualFactor.fifteenDualResidual_memLp_top
      M hM F hFtop
  let I : ℂ :=
    ∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
      (fun x ↦ F x) (fun x ↦ F x)
      (fun x ↦ F x) (fun x ↦ F x) n x ∂M.μ
  let J : ℂ :=
    ∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
      (fun x ↦ F x) (fun x ↦ F x)
      (fun x ↦ F x) (fun x ↦ P x) n x ∂M.μ
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
      (Chapter02.HostKraU3NonergodicFourTerm.quadrupleIntegrand_memLp_top
        M hM F F F F hFtop hFtop hFtop hFtop n |>.integrable (by simp))
      (Chapter02.HostKraU3NonergodicFourTerm.quadrupleIntegrand_memLp_top
        M hM F F F P hFtop hFtop hFtop hPtop n |>.integrable (by simp))]
    apply integral_congr_ae
    have hcoe :=
      (hM.2.iterate (3 * n)).quasiMeasurePreserving.ae_eq
        (MeasureTheory.Lp.coeFn_sub F P)
    filter_upwards [hcoe] with x hx
    simp only [Function.comp_apply] at hx
    simp only [MultipleKhintchineCartesian.quadrupleIntegrand,
      R, HostKraFifteenDualFactor.fifteenDualResidual]
    rw [hx]
    simp only [Pi.sub_apply]
    ring
  have hcorr :
      MultipleKhintchineSyndetic.quadrupleCorrelation M A n =
        (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
          (fun x ↦ F x) (fun x ↦ F x)
          (fun x ↦ F x) (fun x ↦ F x) n x ∂M.μ).re := by
    simpa only [F] using
      Chapter02.HostKraU4Characteristic.quadrupleCorrelation_eq_re_integral_indicator
        M hM A hA n
  rw [fifteenDualStructuredCorrelation, hcorr, hsplit]
  change I.re - (I - J).re = J.re
  rw [Complex.sub_re]
  ring

/-- At time zero, the fifteen-dual structured correlation is exactly the
square of the `L²` norm of the conditional projection. -/
theorem fifteenDualStructuredCorrelation_zero_eq_projection_norm_sq
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    let F := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
    let P := HostKraDualSigma.condExpL2Value M.μ
      (HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM) F
    fifteenDualStructuredCorrelation M hM A hA 0 = ‖P‖ ^ 2 := by
  dsimp only
  letI : IsProbabilityMeasure M.μ := hM.1
  let F := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  let hm :=
    HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM
  let P := HostKraDualSigma.condExpL2Value M.μ hm F
  have hPmeas :
      @AEStronglyMeasurable M.X ℂ _
        (HostKraFifteenDualFactor.fifteenDualMeasurableSpace M hM)
        M.measurableSpace (fun x ↦ P x) M.μ := by
    exact
      ((MeasureTheory.condExpL2 ℂ ℂ hm) F).2
  have horth :
      @inner ℂ (Lp ℂ 2 M.μ) _ (F - P) P = 0 :=
    HostKraDualSigma.inner_sub_condExpL2Value_eq_zero
      M.μ hm F P hPmeas
  have hFP :
      @inner ℂ (Lp ℂ 2 M.μ) _ F P =
        @inner ℂ (Lp ℂ 2 M.μ) _ P P := by
    rw [inner_sub_left] at horth
    exact sub_eq_zero.mp horth
  rw [fifteenDualStructuredCorrelation_eq_projectionIntegral]
  have hpoint :
      (fun x ↦ MultipleKhintchineCartesian.quadrupleIntegrand M
        (fun x ↦ F x) (fun x ↦ F x) (fun x ↦ F x)
        (fun x ↦ P x) 0 x) =ᵐ[M.μ]
        (fun x ↦ @inner ℂ ℂ _ (F x) (P x)) := by
    filter_upwards [
      MultipleKhintchineCharacteristic.indicatorLp_coe M hM A hA]
        with x hx
    simp only [MultipleKhintchineCartesian.quadrupleIntegrand,
      Function.iterate_zero, id_eq, RCLike.inner_apply]
    change F x = CorrelationMean.indicatorComplex A x at hx
    by_cases hxin : x ∈ A
    · have hFx : F x = 1 := by
        rw [hx]
        simp [CorrelationMean.indicatorComplex, Set.indicator, hxin]
      simp [hFx]
    · have hFx : F x = 0 := by
        rw [hx]
        simp [CorrelationMean.indicatorComplex, Set.indicator, hxin]
      simp [hFx]
  rw [integral_congr_ae hpoint, ← MeasureTheory.L2.inner_def, hFP,
    inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The time-zero structured term has the sharp lower bound required by the
fourfold Khintchine argument. -/
theorem fifteenDualStructuredCorrelation_zero_lower_bound
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    (realMeasure M A) ^ 4 ≤
      fifteenDualStructuredCorrelation M hM A hA 0 := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let F := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  let hm :=
    HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM
  let P := HostKraDualSigma.condExpL2Value M.μ hm F
  have hPmeas :
      @AEStronglyMeasurable M.X ℂ _
        (HostKraFifteenDualFactor.fifteenDualMeasurableSpace M hM)
        M.measurableSpace (fun x ↦ P x) M.μ := by
    exact ((MeasureTheory.condExpL2 ℂ ℂ hm) F).2
  have honeMeas :
      @AEStronglyMeasurable M.X ℂ _
        (HostKraFifteenDualFactor.fifteenDualMeasurableSpace M hM)
        M.measurableSpace
        (fun x ↦ (CorrelationMean.oneLp M hM : Lp ℂ 2 M.μ) x) M.μ := by
    exact
      (stronglyMeasurable_const :
        @StronglyMeasurable M.X ℂ _
          (HostKraFifteenDualFactor.fifteenDualMeasurableSpace M hM)
          (fun _ ↦ (1 : ℂ))).aestronglyMeasurable.congr
        (WeakSpectrum.oneLp_coe M hM).symm
  have horthOne :
      @inner ℂ (Lp ℂ 2 M.μ) _ (F - P)
        (CorrelationMean.oneLp M hM) = 0 :=
    HostKraDualSigma.inner_sub_condExpL2Value_eq_zero
      M.μ hm F (CorrelationMean.oneLp M hM) honeMeas
  have hmean :
      @inner ℂ (Lp ℂ 2 M.μ) _
          (CorrelationMean.oneLp M hM) P =
        (realMeasure M A : ℂ) := by
    have hright :
        @inner ℂ (Lp ℂ 2 M.μ) _ F
            (CorrelationMean.oneLp M hM) =
          @inner ℂ (Lp ℂ 2 M.μ) _ P
            (CorrelationMean.oneLp M hM) := by
      rw [inner_sub_left] at horthOne
      exact sub_eq_zero.mp horthOne
    have hleft :
        @inner ℂ (Lp ℂ 2 M.μ) _
            (CorrelationMean.oneLp M hM) P =
          @inner ℂ (Lp ℂ 2 M.μ) _
            (CorrelationMean.oneLp M hM) F := by
      calc
        @inner ℂ (Lp ℂ 2 M.μ) _
            (CorrelationMean.oneLp M hM) P =
            star (@inner ℂ (Lp ℂ 2 M.μ) _ P
              (CorrelationMean.oneLp M hM)) :=
          (inner_conj_symm _ _).symm
        _ = star (@inner ℂ (Lp ℂ 2 M.μ) _ F
              (CorrelationMean.oneLp M hM)) :=
          congrArg star hright.symm
        _ = @inner ℂ (Lp ℂ 2 M.μ) _
              (CorrelationMean.oneLp M hM) F :=
          inner_conj_symm _ _
    rw [hleft, ← CorrelationMean.integral_eq_inner_oneLp]
    rw [integral_congr_ae
      (MultipleKhintchineCharacteristic.indicatorLp_coe M hM A hA)]
    exact CorrelationMean.integral_indicatorComplex M A hA
  have hnormOne : ‖CorrelationMean.oneLp M hM‖ = 1 := by
    have hone := WeakSpectrum.inner_oneLp_self M hM
    rw [inner_self_eq_norm_sq_to_K] at hone
    have hsquare : ‖CorrelationMean.oneLp M hM‖ ^ 2 = 1 := by
      exact Complex.ofReal_injective (by simpa using hone)
    nlinarith [norm_nonneg (CorrelationMean.oneLp M hM)]
  have hmu0 : 0 ≤ realMeasure M A :=
    MeasureTheory.measureReal_nonneg
  have hmuSq : (realMeasure M A) ^ 2 ≤ ‖P‖ ^ 2 := by
    have hcauchy :=
      norm_inner_le_norm (𝕜 := ℂ) (CorrelationMean.oneLp M hM) P
    rw [hmean, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hmu0, hnormOne, one_mul] at hcauchy
    exact pow_le_pow_left₀ hmu0 hcauchy 2
  have hmuOne : realMeasure M A ≤ 1 := by
    change M.μ.real A ≤ 1
    calc
      M.μ.real A ≤ M.μ.real Set.univ :=
        MeasureTheory.measureReal_mono (Set.subset_univ A) (by simp)
      _ = 1 := by simp [MeasureTheory.Measure.real]
  have hmuFourth : (realMeasure M A) ^ 4 ≤ (realMeasure M A) ^ 2 := by
    nlinarith [sq_nonneg (realMeasure M A),
      mul_nonneg hmu0 (sub_nonneg.mpr hmuOne)]
  calc
    (realMeasure M A) ^ 4 ≤ (realMeasure M A) ^ 2 := hmuFourth
    _ ≤ ‖P‖ ^ 2 := hmuSq
    _ = fifteenDualStructuredCorrelation M hM A hA 0 :=
      (fifteenDualStructuredCorrelation_zero_eq_projection_norm_sq
        M hM A hA).symm

/-- Uniform-density negligibility of the fifteen-dual residual says exactly
that the original fourfold correlation and its structured part differ by a
uniform-density-zero sequence. -/
theorem quadrupleCorrelation_sub_fifteenDualStructured_uniformDensity
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    MultipleKhintchineSyndetic.TendsToZeroInUniformDensity
      (fun n ↦
        MultipleKhintchineSyndetic.quadrupleCorrelation M A n -
          fifteenDualStructuredCorrelation M hM A hA n) := by
  have hres :=
    Chapter02.HostKraU4IndicatorCharacteristic.indicator_fifteenDualResidual_last_uniformDensity
      M hM hErg A hA
  simpa only [fifteenDualStructuredCorrelation, sub_sub_cancel] using hres

/-- A real sequence that returns syndetically to its initial value has
syndetic superlevel sets below that initial value. -/
theorem isSyndetic_superlevel_of_syndetic_returns_to_zero
    (s : ℕ → ℝ) (c : ℝ)
    (hzero : c ≤ s 0)
    (hreturns :
      ∀ δ : ℝ, 0 < δ →
        IsSyndetic {n : ℕ | |s n - s 0| < δ}) :
    ∀ δ : ℝ, 0 < δ →
      IsSyndetic {n : ℕ | s n > c - δ} := by
  intro δ hδ
  rcases hreturns δ hδ with ⟨N, hN, hreturnsN⟩
  refine ⟨N, hN, ?_⟩
  intro i
  rcases hreturnsN i with ⟨n, hn, hin, hni⟩
  refine ⟨n, ?_, hin, hni⟩
  change |s n - s 0| < δ at hn
  have hlower := (abs_lt.mp hn).1
  change s n > c - δ
  linarith

/-- Thus the fourfold structured recurrence obligation splits into the
sharp lower bound at time zero and syndetic return to that value. -/
theorem fifteenDualStructured_recurrence_of_zero_and_returns
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hzero :
      (realMeasure M A) ^ 4 ≤
        fifteenDualStructuredCorrelation M hM A hA 0)
    (hreturns :
      ∀ δ : ℝ, 0 < δ →
        IsSyndetic {n : ℕ |
          |fifteenDualStructuredCorrelation M hM A hA n -
            fifteenDualStructuredCorrelation M hM A hA 0| < δ}) :
    ∀ δ : ℝ, 0 < δ →
      IsSyndetic {n : ℕ |
        fifteenDualStructuredCorrelation M hM A hA n >
          (realMeasure M A) ^ 4 - δ} :=
  isSyndetic_superlevel_of_syndetic_returns_to_zero
    (fifteenDualStructuredCorrelation M hM A hA)
    ((realMeasure M A) ^ 4) hzero hreturns

/-- Recurrence of the structured sequence, together with the checked
uniform-density characteristic error, gives the exact four-term
Khintchine conclusion.  No additional hypothesis is introduced into the
eventual theorem: `hstructured` is the remaining theorem to prove about the
constructed fifteen-dual factor. -/
theorem quadruple_syndetic_of_fifteenDualStructured_recurrence
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hstructured :
      ∀ δ : ℝ, 0 < δ →
        IsSyndetic {n : ℕ |
          fifteenDualStructuredCorrelation M hM A hA n >
            (realMeasure M A) ^ 4 - δ})
    (ε : ℝ) (hε : 0 < ε) :
    IsSyndetic {n : ℕ |
      MultipleKhintchineSyndetic.quadrupleCorrelation M A n >
        (realMeasure M A) ^ 4 - ε} := by
  let η : ℝ := ε / 2
  have hη : 0 < η := by
    dsimp [η]
    positivity
  apply
    MultipleKhintchineSyndetic.isSyndetic_superlevel_of_uniformDensity_close
      (MultipleKhintchineSyndetic.quadrupleCorrelation M A)
      (fifteenDualStructuredCorrelation M hM A hA)
      ((realMeasure M A) ^ 4 - ε) η hη
  · convert hstructured η hη using 1
    ext n
    simp only [Set.mem_setOf_eq]
    dsimp only [η]
    ring_nf
  · exact
      quadrupleCorrelation_sub_fifteenDualStructured_uniformDensity
        M hM hErg A hA

end Chapter02.HostKraFourfoldStructuredReduction
