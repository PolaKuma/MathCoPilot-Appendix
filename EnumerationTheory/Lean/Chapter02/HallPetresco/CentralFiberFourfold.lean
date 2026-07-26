import Chapter02.Dynamics.CompactHaarFourfold

open Classical MeasureTheory Set

noncomputable section

namespace Chapter02.CentralFiberFourfold

universe u v

variable {G : Type u} [CommGroup G] [MetricSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- The average of one continuous function along a compact central fiber. -/
def fiberMean {X : Type v} (m : Measure G) (F : X → C(G, ℝ)) (x : X) : ℝ :=
  ∫ u, F x u ∂m

/-- The fourfold central-fiber expression occurring in BHK equation (8.5). -/
def fiberFourfold {X : Type v} (m : Measure G)
    (F : X → C(G, ℝ)) (x : X) : ℝ :=
  ∫ w, ∫ g, ∫ h,
    F x g * F x h * F x (h * w) * F x (g * w ^ 3) ∂m ∂m ∂m

/-- The compact-abelian Fourier estimate holds on every individual central
fiber. -/
theorem fiberMean_pow_four_le
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    {X : Type v} (F : X → C(G, ℝ)) (x : X) :
    (fiberMean m F x) ^ 4 ≤ fiberFourfold m F x := by
  exact CompactHaarFourfold.compactAbelian_fourfold_lower_bound
    m hcube (F x)

/-- Jensen's inequality followed by the pointwise compact-abelian Fourier
estimate.  This is the analytic content of the passage from BHK (8.5) to
the sharp fourth power of the global mean.

The measurability and integrability assumptions are separated explicitly:
they are exactly what the later nilmanifold disintegration supplies. -/
theorem integral_fiberMean_pow_four_le_integral_fiberFourfold
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    {X : Type v} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (F : X → C(G, ℝ))
    (hFnonneg : ∀ x u, 0 ≤ F x u)
    (hmean : Integrable (fiberMean m F) μ)
    (hmean4 : Integrable (fun x ↦ (fiberMean m F x) ^ 4) μ)
    (hfour : Integrable (fiberFourfold m F) μ) :
    (∫ x, fiberMean m F x ∂μ) ^ 4 ≤
      ∫ x, fiberFourfold m F x ∂μ := by
  have hmean_nonneg : ∀ᵐ x ∂μ, fiberMean m F x ∈ Set.Ici (0 : ℝ) := by
    filter_upwards with x
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun u ↦ hFnonneg x u)
  have hJensen :
      (∫ x, fiberMean m F x ∂μ) ^ 4 ≤
        ∫ x, (fiberMean m F x) ^ 4 ∂μ := by
    exact
      (convexOn_pow (𝕜 := ℝ) 4).map_integral_le
        (continuous_pow 4).continuousOn isClosed_Ici
        hmean_nonneg hmean
        (by simpa only [Function.comp_apply] using hmean4)
  refine hJensen.trans ?_
  exact integral_mono_ae hmean4 hfour
    (Filter.Eventually.of_forall fun x ↦ fiberMean_pow_four_le m hcube F x)

/-- A jointly continuous function, viewed as a continuous family of
continuous functions on the central group. -/
def fiberFamily
    {X : Type v} [MetricSpace X] [CompactSpace X]
    (φ : C(X × G, ℝ)) (x : X) : C(G, ℝ) :=
  φ.curry x

lemma fiberFamily_apply
    {X : Type v} [MetricSpace X] [CompactSpace X]
    (φ : C(X × G, ℝ)) (x : X) (u : G) :
    fiberFamily φ x u = φ (x, u) :=
  rfl

theorem continuous_fiberFamily
    {X : Type v} [MetricSpace X] [CompactSpace X]
    (φ : C(X × G, ℝ)) :
    Continuous (fiberFamily φ) :=
  φ.curry.continuous

/-- Integration over the compact central group preserves continuity in the
base point. -/
theorem continuous_fiberMean_fiberFamily
    (m : Measure G) [IsProbabilityMeasure m]
    {X : Type v} [MetricSpace X] [CompactSpace X]
    (φ : C(X × G, ℝ)) :
    Continuous (fiberMean m (fiberFamily φ)) := by
  have h :=
    continuous_parametric_integral_of_continuous
      (μ := m) (f := fun x u ↦ φ (x, u))
      φ.continuous isCompact_univ
  simpa only [fiberMean, fiberFamily, ContinuousMap.curry_apply,
    Measure.restrict_univ] using h

/-- The jointly continuous integrand behind the three central Haar
integrations in BHK (8.5). -/
def fiberFourfoldIntegrand
    {X : Type v} [MetricSpace X] [CompactSpace X]
    (φ : C(X × G, ℝ)) (x : X) (w g h : G) : ℝ :=
  φ (x, g) * φ (x, h) * φ (x, h * w) * φ (x, g * w ^ 3)

lemma continuous_fiberFourfoldIntegrand
    {X : Type v} [MetricSpace X] [CompactSpace X]
    (φ : C(X × G, ℝ)) :
    Continuous (fun p : ((X × G) × G) × G ↦
      fiberFourfoldIntegrand φ p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  unfold fiberFourfoldIntegrand
  fun_prop

/-- The complete central fourfold expression depends continuously on the
base point. -/
theorem continuous_fiberFourfold_fiberFamily
    (m : Measure G) [IsProbabilityMeasure m]
    {X : Type v} [MetricSpace X] [CompactSpace X]
    (φ : C(X × G, ℝ)) :
    Continuous (fiberFourfold m (fiberFamily φ)) := by
  have hinner :
      Continuous (fun p : (X × G) × G ↦
        ∫ h, fiberFourfoldIntegrand φ p.1.1 p.1.2 p.2 h ∂m) := by
    have h :=
      continuous_parametric_integral_of_continuous
        (μ := m)
        (f := fun p : (X × G) × G ↦ fun h ↦
          fiberFourfoldIntegrand φ p.1.1 p.1.2 p.2 h)
        (continuous_fiberFourfoldIntegrand φ) isCompact_univ
    simpa only [Measure.restrict_univ] using h
  have hmiddle :
      Continuous (fun p : X × G ↦
        ∫ g, ∫ h,
          fiberFourfoldIntegrand φ p.1 p.2 g h ∂m ∂m) := by
    have h :=
      continuous_parametric_integral_of_continuous
        (μ := m)
        (f := fun p : X × G ↦ fun g ↦
          ∫ h, fiberFourfoldIntegrand φ p.1 p.2 g h ∂m)
        hinner isCompact_univ
    simpa only [Measure.restrict_univ] using h
  have houter :
      Continuous (fun x : X ↦
        ∫ w, ∫ g, ∫ h,
          fiberFourfoldIntegrand φ x w g h ∂m ∂m ∂m) := by
    have h :=
      continuous_parametric_integral_of_continuous
        (μ := m)
        (f := fun x : X ↦ fun w ↦
          ∫ g, ∫ h, fiberFourfoldIntegrand φ x w g h ∂m ∂m)
        hmiddle isCompact_univ
    simpa only [Measure.restrict_univ] using h
  simpa only [fiberFourfold, fiberFamily_apply,
    fiberFourfoldIntegrand] using houter

/-- Fully automatic compact-base form of the central-fiber estimate.  All
measurability and integrability obligations follow from joint continuity
and compactness. -/
theorem continuous_family_global_fourfold_lower_bound
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (φ : C(X × G, ℝ))
    (hφnonneg : ∀ x u, 0 ≤ φ (x, u)) :
    (∫ x, fiberMean m (fiberFamily φ) x ∂μ) ^ 4 ≤
      ∫ x, fiberFourfold m (fiberFamily φ) x ∂μ := by
  have hcmean := continuous_fiberMean_fiberFamily m φ
  have hcfour := continuous_fiberFourfold_fiberFamily m φ
  have hmean : Integrable (fiberMean m (fiberFamily φ)) μ := by
    simpa using
      (ContinuousOn.integrableOn_compact (μ := μ)
        isCompact_univ hcmean.continuousOn)
  have hmean4 :
      Integrable (fun x ↦ (fiberMean m (fiberFamily φ) x) ^ 4) μ := by
    simpa using
      (ContinuousOn.integrableOn_compact (μ := μ)
        isCompact_univ (hcmean.pow 4).continuousOn)
  have hfour : Integrable (fiberFourfold m (fiberFamily φ)) μ := by
    simpa using
      (ContinuousOn.integrableOn_compact (μ := μ)
        isCompact_univ hcfour.continuousOn)
  exact integral_fiberMean_pow_four_le_integral_fiberFourfold
    m hcube μ (fiberFamily φ)
    (fun x u ↦ hφnonneg x u) hmean hmean4 hfour

/-- The topological and measure-theoretic data of a compact central action.
The embedding field records that each fiber translation is a measurable
copy of the base; it is automatic for the homeomorphisms arising from a
nilmanifold action. -/
structure CompactCentralAction
    (G : Type u) (X : Type v)
    [TopologicalSpace G] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure X) where
  act : G → X → X
  continuous_act : Continuous (Function.uncurry act)
  measurePreserving_act : ∀ u, MeasurePreserving (act u) μ μ
  measurableEmbedding_act : ∀ u, MeasurableEmbedding (act u)

/-- A continuous nonnegative observation pulled back along the central
action, with the base point as first coordinate. -/
def orbitFiberMap
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : CompactCentralAction G X μ) (f : C(X, ℝ)) :
    C(X × G, ℝ) where
  toFun p := f (C.act p.2 p.1)
  continuous_toFun := by
    exact f.continuous.comp
      (C.continuous_act.comp
        (continuous_snd.prodMk continuous_fst))

@[simp]
lemma orbitFiberMap_apply
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : CompactCentralAction G X μ) (f : C(X, ℝ))
    (x : X) (u : G) :
    orbitFiberMap C f (x, u) = f (C.act u x) :=
  rfl

/-- Averaging a function along a measure-preserving compact central action
does not change its global integral. -/
theorem integral_fiberMean_orbit_eq
    (m : Measure G) [IsProbabilityMeasure m]
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : CompactCentralAction G X μ) (f : C(X, ℝ)) :
    ∫ x, fiberMean m (fiberFamily (orbitFiberMap C f)) x ∂μ =
      ∫ x, f x ∂μ := by
  have hprod :
      Integrable
        (fun p : X × G ↦ f (C.act p.2 p.1))
        (μ.prod m) := by
    have hc :
        Continuous (fun p : X × G ↦ f (C.act p.2 p.1)) :=
      (orbitFiberMap C f).continuous
    simpa using
      (ContinuousOn.integrableOn_compact (μ := μ.prod m)
        isCompact_univ hc.continuousOn)
  calc
    ∫ x, fiberMean m (fiberFamily (orbitFiberMap C f)) x ∂μ =
        ∫ u, ∫ x, f (C.act u x) ∂μ ∂m := by
      simpa only [fiberMean, fiberFamily_apply, orbitFiberMap_apply] using
        (integral_integral_swap hprod)
    _ = ∫ u, ∫ x, f x ∂μ ∂m := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u ↦
        C.measurePreserving_act u
          |>.integral_comp (C.measurableEmbedding_act u) f
    _ = ∫ x, f x ∂μ := by simp

/-- BHK (8.5), now specialized to an honest continuous,
measure-preserving compact central action. -/
theorem compactCentralAction_fourfold_lower_bound
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : CompactCentralAction G X μ)
    (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    (∫ x, f x ∂μ) ^ 4 ≤
      ∫ x,
        fiberFourfold m (fiberFamily (orbitFiberMap C f)) x ∂μ := by
  rw [← integral_fiberMean_orbit_eq m μ C f]
  exact continuous_family_global_fourfold_lower_bound
    m hcube μ (orbitFiberMap C f) (fun x u ↦ hf (C.act u x))

/-- A continuous real function on a nonempty compact probability space
attains a value at least as large as its integral. -/
theorem exists_integral_le_value
    {Q : Type v} [MetricSpace Q] [CompactSpace Q] [Nonempty Q]
    [MeasurableSpace Q] [BorelSpace Q]
    (ν : Measure Q) [IsProbabilityMeasure ν] (q : C(Q, ℝ)) :
    ∃ z : Q, (∫ y, q y ∂ν) ≤ q z := by
  obtain ⟨z, _hzmem, hzmax⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty q.continuous.continuousOn
  refine ⟨z, ?_⟩
  have hq : Integrable (fun y ↦ q y) ν := by
    simpa using
      (ContinuousOn.integrableOn_compact (μ := ν)
        isCompact_univ q.continuous.continuousOn)
  calc
    ∫ y, q y ∂ν ≤ ∫ _y : Q, q z ∂ν := by
      exact integral_mono_ae hq (integrable_const (q z))
        (Filter.Eventually.of_forall fun y ↦ hzmax (Set.mem_univ y))
    _ = q z := by simp

end Chapter02.CentralFiberFourfold
