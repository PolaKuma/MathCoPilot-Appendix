import Chapter02.Dynamics.CompactConfigurationMeasureOrbit

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.CompactUniqueErgodicCesaro

universe u

/-- The empirical probability measure of the first `N + 1` points of an
orbit. -/
def empiricalMeasure
    {X : Type u} [MeasurableSpace X] [MeasurableSingletonClass X]
    (T : X → X) (x : X) (N : ℕ) : Measure X :=
  (((N + 1 : ℕ) : ENNReal)⁻¹) •
    ∑ j : Fin (N + 1), Measure.dirac ((T^[j.val]) x)

theorem empiricalMeasure_isProbability
    {X : Type u} [MeasurableSpace X] [MeasurableSingletonClass X]
    (T : X → X) (x : X) (N : ℕ) :
    IsProbabilityMeasure (empiricalMeasure T x N) := by
  apply IsProbabilityMeasure.mk
  simp [empiricalMeasure]
  apply ENNReal.inv_mul_cancel
  · simp
  · simp

/-- The preceding empirical measure packaged in Mathlib's compact space of
probability measures. -/
def empiricalProbability
    {X : Type u} [MeasurableSpace X] [MeasurableSingletonClass X]
    (T : X → X) (x : X) (N : ℕ) : ProbabilityMeasure X :=
  ⟨empiricalMeasure T x N, empiricalMeasure_isProbability T x N⟩

theorem integral_empiricalMeasure
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (T : X → X) (x : X) (N : ℕ) (f : C(X, ℝ)) :
    ∫ y, f y ∂(empiricalMeasure T x N) =
      cesaroAverage (fun n ↦ f ((T^[n]) x)) N := by
  have hsum :
      (∫ y, f y ∂(∑ j : Fin (N + 1),
        Measure.dirac ((T^[j.val]) x))) =
        ∑ j : Fin (N + 1), f ((T^[j.val]) x) := by
    rw [integral_finset_sum_measure]
    · simp
    · intro j hj
      rw [← integrableOn_univ]
      exact ContinuousOn.integrableOn_compact
        (μ := Measure.dirac ((T^[j.val]) x))
        isCompact_univ f.continuous.continuousOn
  simp only [empiricalMeasure, integral_smul_measure, hsum,
    cesaroAverage, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun n ↦ f ((T^[n]) x)) (N + 1)

/-- Invariance expressed only through continuous real test functions.  This
is the form naturally closed under weak convergence of probability
measures. -/
def IsIntegralInvariant
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (T : X → X) (ν : ProbabilityMeasure X) : Prop :=
  ∀ f : C(X, ℝ),
    ∫ x, f (T x) ∂(ν : Measure X) =
      ∫ x, f x ∂(ν : Measure X)

/-- Exact telescoping identity for two consecutive orbit averages. -/
theorem cesaroAverage_comp_sub
    {X : Type u} (T : X → X) (x : X) (N : ℕ) (f : X → ℝ) :
    cesaroAverage (fun n ↦ f (T ((T^[n]) x))) N -
        cesaroAverage (fun n ↦ f ((T^[n]) x)) N =
      (((N + 1 : ℕ) : ℝ)⁻¹) *
        (f ((T^[N + 1]) x) - f x) := by
  have hsucc (n : ℕ) :
      f (T ((T^[n]) x)) = f ((T^[n + 1]) x) := by
    rw [Function.iterate_succ_apply']
  simp_rw [hsucc]
  unfold cesaroAverage
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  let u : ℕ → ℝ := fun n ↦ f ((T^[n]) x)
  calc
    (∑ n ∈ Finset.range (N + 1), (u (n + 1) - u n)) =
        -(∑ n ∈ Finset.range (N + 1), (u n - u (n + 1))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = -(u 0 - u (N + 1)) := by
      rw [Finset.sum_range_sub']
    _ = f ((T^[N + 1]) x) - f x := by
      simp only [u, Function.iterate_zero_apply]
      ring

/-- Empirical measures along orbit segments whose lengths tend to infinity
have invariant weak limits.  The base point may vary with the segment. -/
theorem integralInvariant_of_empiricalProbability_limit
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (T : X → X) (hT : Continuous T)
    (x : ℕ → X) (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure X)
    (hlim :
      Tendsto (fun k ↦ empiricalProbability T (x k) (N k))
        atTop (nhds ν)) :
    IsIntegralInvariant T ν := by
  intro f
  let fT : C(X, ℝ) := f.comp ⟨T, hT⟩
  have hleft :
      Tendsto
        (fun k ↦
          ∫ y, fT y
            ∂((empiricalProbability T (x k) (N k) :
              ProbabilityMeasure X) : Measure X))
        atTop
        (nhds (∫ y, fT y ∂(ν : Measure X))) :=
    (ProbabilityMeasure.continuous_integral_continuousMap fT)
      |>.continuousAt.tendsto.comp hlim
  have hright :
      Tendsto
        (fun k ↦
          ∫ y, f y
            ∂((empiricalProbability T (x k) (N k) :
              ProbabilityMeasure X) : Measure X))
        atTop
        (nhds (∫ y, f y ∂(ν : Measure X))) :=
    (ProbabilityMeasure.continuous_integral_continuousMap f)
      |>.continuousAt.tendsto.comp hlim
  have hdiff :
      Tendsto
        (fun k ↦
          (∫ y, fT y
              ∂((empiricalProbability T (x k) (N k) :
                ProbabilityMeasure X) : Measure X)) -
            ∫ y, f y
              ∂((empiricalProbability T (x k) (N k) :
                ProbabilityMeasure X) : Measure X))
        atTop
        (nhds ((∫ y, fT y ∂(ν : Measure X)) -
          ∫ y, f y ∂(ν : Measure X))) :=
    hleft.sub hright
  have hinv :
      Tendsto
        (fun k ↦ (((N k + 1 : ℕ) : ℝ)⁻¹))
        atTop (nhds 0) := by
    exact
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp
          (tendsto_add_atTop_nat 1))).comp hN
  have hboundary :
      Tendsto
        (fun k ↦ (((N k + 1 : ℕ) : ℝ)⁻¹) *
          (f ((T^[N k + 1]) (x k)) - f (x k)))
        atTop (nhds 0) := by
    have hbound :
        ∀ k,
          ‖(((N k + 1 : ℕ) : ℝ)⁻¹) *
              (f ((T^[N k + 1]) (x k)) - f (x k))‖ ≤
            (((N k + 1 : ℕ) : ℝ)⁻¹) * (2 * ‖f‖) := by
      intro k
      rw [norm_mul, Real.norm_of_nonneg (by positivity)]
      gcongr
      calc
        ‖f ((T^[N k + 1]) (x k)) - f (x k)‖ ≤
            ‖f ((T^[N k + 1]) (x k))‖ + ‖f (x k)‖ :=
          norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add
          (ContinuousMap.norm_coe_le_norm f _)
          (ContinuousMap.norm_coe_le_norm f _)
        _ = 2 * ‖f‖ := by ring
    have hmajor :
        Tendsto
          (fun k ↦ (((N k + 1 : ℕ) : ℝ)⁻¹) * (2 * ‖f‖))
          atTop (nhds 0) := by
      simpa using hinv.mul_const (2 * ‖f‖)
    exact squeeze_zero_norm hbound hmajor
  have hempirical :
      Tendsto
        (fun k ↦
          (∫ y, fT y
              ∂((empiricalProbability T (x k) (N k) :
                ProbabilityMeasure X) : Measure X)) -
            ∫ y, f y
              ∂((empiricalProbability T (x k) (N k) :
                ProbabilityMeasure X) : Measure X))
        atTop (nhds 0) := by
    apply hboundary.congr'
    filter_upwards with k
    rw [show
        ((empiricalProbability T (x k) (N k) :
          ProbabilityMeasure X) : Measure X) =
            empiricalMeasure T (x k) (N k) by rfl,
      integral_empiricalMeasure T (x k) (N k) fT,
      integral_empiricalMeasure T (x k) (N k) f]
    simpa only [fT, ContinuousMap.comp_apply] using
      (cesaroAverage_comp_sub T (x k) (N k) f).symm
  have hzero :
      (∫ y, fT y ∂(ν : Measure X)) -
          ∫ y, f y ∂(ν : Measure X) = 0 :=
    tendsto_nhds_unique hdiff hempirical
  exact sub_eq_zero.mp hzero

/-- Every continuous self-map of a nonempty compact metric space admits an
invariant probability measure, expressed against continuous real test
functions.  This is the Krylov--Bogolyubov construction from an empirical
orbit and compactness of the probability-measure space. -/
theorem exists_integralInvariant
    {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (T : X → X) (hT : Continuous T) :
    ∃ ν : ProbabilityMeasure X, IsIntegralInvariant T ν := by
  let x : X := Classical.choice inferInstance
  obtain ⟨ν, ψ, hψ, hlim⟩ :=
    CompactSpace.tendsto_subseq
      (fun N ↦ empiricalProbability T x N)
  refine ⟨ν,
    integralInvariant_of_empiricalProbability_limit
      T hT (fun _ ↦ x) ψ hψ.tendsto_atTop ν ?_⟩
  simpa only [Function.comp_apply] using hlim

/-- A specified invariant probability measure is the unique probability
measure invariant against continuous real test functions. -/
def HasUniqueIntegralInvariant
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (T : X → X) (μ : ProbabilityMeasure X) : Prop :=
  IsIntegralInvariant T μ ∧
    ∀ ν : ProbabilityMeasure X, IsIntegralInvariant T ν → ν = μ

/-- To prove uniqueness it is enough to identify the integral of every
continuous real observable under every invariant probability measure. -/
theorem hasUniqueIntegralInvariant_of_integral_eq
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (T : X → X) (μ : ProbabilityMeasure X)
    (hμ : IsIntegralInvariant T μ)
    (hidentify :
      ∀ ν : ProbabilityMeasure X, IsIntegralInvariant T ν →
        ∀ f : C(X, ℝ),
          ∫ x, f x ∂(ν : Measure X) =
            ∫ x, f x ∂(μ : Measure X)) :
    HasUniqueIntegralInvariant T μ := by
  refine ⟨hμ, ?_⟩
  intro ν hν
  have hlim :
      Tendsto (fun _ : ℕ ↦ ν) atTop (nhds μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    let g : C(X, ℝ) := ⟨f, f.continuous⟩
    have hfg := hidentify ν hν g
    change (∫ x, f x ∂(ν : Measure X)) =
      ∫ x, f x ∂(μ : Measure X) at hfg
    rw [hfg]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- Unique invariance implies uniform convergence of all orbit-segment
Cesàro averages of a continuous observable. -/
theorem uniform_cesaro_of_uniqueIntegralInvariant
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (T : X → X) (hT : Continuous T)
    (μ : ProbabilityMeasure X)
    (hunique : HasUniqueIntegralInvariant T μ)
    (f : C(X, ℝ)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ x : X,
        |cesaroAverage (fun n ↦ f ((T^[n]) x)) N -
          ∫ y, f y ∂(μ : Measure X)| < ε := by
  intro ε hε
  by_contra hnot
  rw [eventually_atTop] at hnot
  push_neg at hnot
  let K : ℕ → ℕ := fun k ↦ Classical.choose (hnot k)
  have hKle (k : ℕ) : k ≤ K k :=
    (Classical.choose_spec (hnot k)).1
  let x : ℕ → X := fun k ↦
    Classical.choose (Classical.choose_spec (hnot k)).2
  have hbad (k : ℕ) :
      ε ≤
        |cesaroAverage (fun n ↦ f ((T^[n]) (x k))) (K k) -
          ∫ y, f y ∂(μ : Measure X)| := by
    simpa only [x, K] using
      (Classical.choose_spec
        (Classical.choose_spec (hnot k)).2)
  have hKtop : Tendsto K atTop atTop := by
    refine tendsto_atTop.2 fun b ↦ ?_
    filter_upwards [eventually_ge_atTop b] with k hk
    exact hk.trans (hKle k)
  obtain ⟨ν, ψ, hψ, hlim⟩ :=
    CompactSpace.tendsto_subseq
      (fun k ↦ empiricalProbability T (x k) (K k))
  have hNsub : Tendsto (fun k ↦ K (ψ k)) atTop atTop :=
    hKtop.comp hψ.tendsto_atTop
  have hνinv : IsIntegralInvariant T ν :=
    integralInvariant_of_empiricalProbability_limit
      T hT (x ∘ ψ) (K ∘ ψ) hNsub ν (by
        simpa only [Function.comp_apply] using hlim)
  have hν : ν = μ := hunique.2 ν hνinv
  have hint :
      Tendsto
        (fun k ↦
          ∫ y, f y
            ∂((empiricalProbability T (x (ψ k)) (K (ψ k)) :
              ProbabilityMeasure X) : Measure X))
        atTop
        (nhds (∫ y, f y ∂(μ : Measure X))) := by
    rw [← hν]
    exact
      (ProbabilityMeasure.continuous_integral_continuousMap f)
        |>.continuousAt.tendsto.comp hlim
  have havg :
      Tendsto
        (fun k ↦
          cesaroAverage
            (fun n ↦ f ((T^[n]) (x (ψ k)))) (K (ψ k)))
        atTop
        (nhds (∫ y, f y ∂(μ : Measure X))) := by
    apply hint.congr'
    filter_upwards with k
    rw [show
        ((empiricalProbability T (x (ψ k)) (K (ψ k)) :
          ProbabilityMeasure X) : Measure X) =
            empiricalMeasure T (x (ψ k)) (K (ψ k)) by rfl]
    exact integral_empiricalMeasure T (x (ψ k)) (K (ψ k)) f
  have hclose :=
    (Metric.tendsto_atTop.mp havg) ε hε
  obtain ⟨k, hkall⟩ := hclose
  have hk := hkall k le_rfl
  rw [Real.dist_eq] at hk
  exact (not_lt_of_ge (hbad (ψ k))) hk

/-- The same uniform convergence holds on every translated interval of
every orbit. -/
theorem uniform_translated_cesaro_of_uniqueIntegralInvariant
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (T : X → X) (hT : Continuous T)
    (μ : ProbabilityMeasure X)
    (hunique : HasUniqueIntegralInvariant T μ)
    (f : C(X, ℝ)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ x : X, ∀ i : ℕ,
        |cesaroAverage (fun n ↦ f ((T^[i + n]) x)) N -
          ∫ y, f y ∂(μ : Measure X)| < ε := by
  intro ε hε
  filter_upwards [
    uniform_cesaro_of_uniqueIntegralInvariant
      T hT μ hunique f ε hε] with N hN
  intro x i
  have hi := hN ((T^[i]) x)
  simpa only [← Function.iterate_add_apply, Nat.add_comm] using hi

end Chapter02.CompactUniqueErgodicCesaro
