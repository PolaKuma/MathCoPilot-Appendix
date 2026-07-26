import Chapter02.HallPetresco.CentralFiberFourfold

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraCentralChangeVariables

universe u v

open Chapter02.CentralFiberFourfold

variable {G : Type u} [CommGroup G] [MetricSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- The four entries of the reduced two-step Hall--Petresco
parametrization, evaluated along the compact central action. -/
def hallCentralIntegrand
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : CompactCentralAction G X μ) (f : C(X, ℝ))
    (x : X) (v g h u : G) : ℝ :=
  f (C.act g x) *
    f (C.act (g * h * v) x) *
    f (C.act (g * h ^ 2 * u * v ^ 2) x) *
    f (C.act (g * h ^ 3 * u ^ 3 * v ^ 3) x)

/-- After the first triangular Haar substitution `w = h u v`. -/
def hallAfterU
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : CompactCentralAction G X μ) (f : C(X, ℝ))
    (x : X) (v g h w : G) : ℝ :=
  f (C.act g x) *
    f (C.act (g * h * v) x) *
    f (C.act ((g * h * v) * w) x) *
    f (C.act (g * w ^ 3) x)

/-- After the second triangular Haar substitution `b = g h v`. -/
def hallReducedIntegrand
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : CompactCentralAction G X μ) (f : C(X, ℝ))
    (x : X) (g b w : G) : ℝ :=
  f (C.act g x) * f (C.act b x) *
    f (C.act (b * w) x) * f (C.act (g * w ^ 3) x)

lemma hallCentralIntegrand_eq_afterU
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : CompactCentralAction G X μ) (f : C(X, ℝ))
    (x : X) (v g h u : G) :
    hallCentralIntegrand C f x v g h u =
      hallAfterU C f x v g h ((h * v) * u) := by
  have hthird :
      g * h ^ 2 * u * v ^ 2 =
        (g * h * v) * ((h * v) * u) := by
    simp only [pow_two]
    ac_rfl
  have hfourth :
      g * h ^ 3 * u ^ 3 * v ^ 3 =
        g * (((h * v) * u) ^ 3) := by
    simp only [pow_succ, pow_zero, mul_one]
    ac_rfl
  unfold hallCentralIntegrand hallAfterU
  rw [hthird, hfourth]

lemma hallAfterU_eq_reduced
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : CompactCentralAction G X μ) (f : C(X, ℝ))
    (x : X) (v g h w : G) :
    hallAfterU C f x v g h w =
      hallReducedIntegrand C f x g ((g * v) * h) w := by
  unfold hallAfterU hallReducedIntegrand
  congr 3 <;> ac_rfl

/-- The two triangular changes of variables used in BHK (8.5), stated
before the remaining Fubini permutation. -/
theorem integral_hallCentral_eq_reduced
    (m : Measure G) [m.IsHaarMeasure]
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : CompactCentralAction G X μ) (f : C(X, ℝ))
    (x : X) (v : G) :
    (∫ g, ∫ h, ∫ u,
      hallCentralIntegrand C f x v g h u ∂m ∂m ∂m) =
      ∫ g, ∫ b, ∫ w,
        hallReducedIntegrand C f x g b w ∂m ∂m ∂m := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun g ↦ by
    calc
      (∫ h, ∫ u, hallCentralIntegrand C f x v g h u ∂m ∂m) =
          ∫ h, ∫ w, hallAfterU C f x v g h w ∂m ∂m := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun h ↦ by
          calc
            (∫ u, hallCentralIntegrand C f x v g h u ∂m) =
                ∫ u, hallAfterU C f x v g h ((h * v) * u) ∂m := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun u ↦
                hallCentralIntegrand_eq_afterU C f x v g h u
            _ = ∫ w, hallAfterU C f x v g h w ∂m :=
              integral_mul_left_eq_self
                (fun w ↦ hallAfterU C f x v g h w) (h * v)
      _ = ∫ b, ∫ w, hallReducedIntegrand C f x g b w ∂m ∂m := by
        calc
          (∫ h, ∫ w, hallAfterU C f x v g h w ∂m ∂m) =
              ∫ h, ∫ w,
                hallReducedIntegrand C f x g ((g * v) * h) w ∂m ∂m := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun h ↦ by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun w ↦
                hallAfterU_eq_reduced C f x v g h w
          _ = ∫ b, ∫ w, hallReducedIntegrand C f x g b w ∂m ∂m :=
            integral_mul_left_eq_self
              (fun b ↦ ∫ w, hallReducedIntegrand C f x g b w ∂m)
              (g * v)

/-- The remaining two Fubini swaps put the reduced integral in the precise
order used by `fiberFourfold`. -/
theorem integral_reduced_eq_fiberFourfold
    (m : Measure G) [IsProbabilityMeasure m]
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : CompactCentralAction G X μ) (f : C(X, ℝ))
    (x : X) :
    (∫ g, ∫ b, ∫ w,
      hallReducedIntegrand C f x g b w ∂m ∂m ∂m) =
      fiberFourfold m (fiberFamily (orbitFiberMap C f)) x := by
  have hswap_inner (g : G) :
      (∫ b, ∫ w, hallReducedIntegrand C f x g b w ∂m ∂m) =
        ∫ w, ∫ b, hallReducedIntegrand C f x g b w ∂m ∂m := by
    apply integral_integral_swap
    have hact : Continuous (fun a : G ↦ C.act a x) :=
      C.continuous_act.comp (continuous_id.prodMk continuous_const)
    have hc :
        Continuous (fun p : G × G ↦
          hallReducedIntegrand C f x g p.1 p.2) := by
      unfold hallReducedIntegrand
      exact
        ((continuous_const.mul
          (f.continuous.comp (hact.comp continuous_fst))).mul
          (f.continuous.comp
            (hact.comp (continuous_fst.mul continuous_snd)))).mul
          (f.continuous.comp
            (hact.comp (continuous_const.mul (continuous_snd.pow 3))))
    rw [← integrableOn_univ]
    exact
      ContinuousOn.integrableOn_compact (μ := m.prod m)
        isCompact_univ hc.continuousOn
  calc
    (∫ g, ∫ b, ∫ w,
        hallReducedIntegrand C f x g b w ∂m ∂m ∂m) =
        ∫ g, ∫ w, ∫ b,
          hallReducedIntegrand C f x g b w ∂m ∂m ∂m := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hswap_inner
    _ = ∫ w, ∫ g, ∫ b,
          hallReducedIntegrand C f x g b w ∂m ∂m ∂m := by
      apply integral_integral_swap
      have hact : Continuous (fun a : G ↦ C.act a x) :=
        C.continuous_act.comp (continuous_id.prodMk continuous_const)
      have hintegrand :
          Continuous (fun q : (G × G) × G ↦
            hallReducedIntegrand C f x q.1.1 q.2 q.1.2) := by
        unfold hallReducedIntegrand
        have hg : Continuous (fun q : (G × G) × G ↦ q.1.1) :=
          continuous_fst.comp continuous_fst
        have hw : Continuous (fun q : (G × G) × G ↦ q.1.2) :=
          continuous_snd.comp continuous_fst
        have hb : Continuous (fun q : (G × G) × G ↦ q.2) :=
          continuous_snd
        have h₁ := f.continuous.comp (hact.comp hg)
        have h₂ := f.continuous.comp (hact.comp hb)
        have h₃ := f.continuous.comp
          (hact.comp (hb.mul hw))
        have h₄ := f.continuous.comp
          (hact.comp (hg.mul (hw.pow 3)))
        exact ((h₁.mul h₂).mul h₃).mul h₄
      have hc :
          Continuous (fun p : G × G ↦
            ∫ b, hallReducedIntegrand C f x p.1 b p.2 ∂m) := by
        have h :=
          continuous_parametric_integral_of_continuous
            (μ := m)
            (f := fun p : G × G ↦ fun b ↦
              hallReducedIntegrand C f x p.1 b p.2)
            hintegrand isCompact_univ
        simpa only [Measure.restrict_univ] using h
      rw [← integrableOn_univ]
      exact
        ContinuousOn.integrableOn_compact (μ := m.prod m)
          isCompact_univ hc.continuousOn
    _ = fiberFourfold m (fiberFamily (orbitFiberMap C f)) x := by
      unfold fiberFourfold hallReducedIntegrand
      rfl

/-- The Hall--Petresco integrand with its three polynomial parameters and
the base/fiber variables packed into two product blocks. -/
def packedHallIntegrand
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : CompactCentralAction G X μ) (f : C(X, ℝ))
    (q : (G × G) × G) (r : X × G) : ℝ :=
  hallCentralIntegrand C f r.1 r.2 q.1.1 q.1.2 q.2

lemma continuous_packedHallIntegrand
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : CompactCentralAction G X μ) (f : C(X, ℝ)) :
    Continuous (fun z : (((G × G) × G) × (X × G)) ↦
      packedHallIntegrand C f z.1 z.2) := by
  have hg : Continuous
      (fun z : (((G × G) × G) × (X × G)) ↦ z.1.1.1) :=
    (continuous_fst.comp continuous_fst).comp continuous_fst
  have hh : Continuous
      (fun z : (((G × G) × G) × (X × G)) ↦ z.1.1.2) :=
    (continuous_snd.comp continuous_fst).comp continuous_fst
  have hu : Continuous
      (fun z : (((G × G) × G) × (X × G)) ↦ z.1.2) :=
    continuous_snd.comp continuous_fst
  have hx : Continuous
      (fun z : (((G × G) × G) × (X × G)) ↦ z.2.1) :=
    continuous_fst.comp continuous_snd
  have hv : Continuous
      (fun z : (((G × G) × G) × (X × G)) ↦ z.2.2) :=
    continuous_snd.comp continuous_snd
  have hobs
      (a : (((G × G) × G) × (X × G)) → G)
      (ha : Continuous a) :
      Continuous (fun z ↦ f (C.act (a z) z.2.1)) :=
    f.continuous.comp (C.continuous_act.comp (ha.prodMk hx))
  unfold packedHallIntegrand hallCentralIntegrand
  have h₁ := hobs _ hg
  have h₂ := hobs _ ((hg.mul hh).mul hv)
  have h₃ := hobs _ (((hg.mul (hh.pow 2)).mul hu).mul (hv.pow 2))
  have h₄ := hobs _ (((hg.mul (hh.pow 3)).mul (hu.pow 3)).mul (hv.pow 3))
  exact ((h₁.mul h₂).mul h₃).mul h₄

/-- The continuous Hall--Petresco correlation at fixed polynomial
parameters, integrating its base point and compact central fiber together. -/
def centralHallValue
    (m : Measure G)
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] (μ : Measure X)
    (C : CompactCentralAction G X μ) (f : C(X, ℝ))
    (g h u : G) : ℝ :=
  ∫ r, packedHallIntegrand C f ((g, h), u) r ∂(μ.prod m)

lemma continuous_centralHallValue
    (m : Measure G) [IsProbabilityMeasure m]
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ]
    (C : CompactCentralAction G X μ) (f : C(X, ℝ)) :
    Continuous (fun q : (G × G) × G ↦
      centralHallValue m μ C f q.1.1 q.1.2 q.2) := by
  have h :=
    continuous_parametric_integral_of_continuous
      (μ := μ.prod m)
      (f := fun q : (G × G) × G ↦ fun r : X × G ↦
        packedHallIntegrand C f q r)
      (continuous_packedHallIntegrand C f) isCompact_univ
  simpa only [centralHallValue, Measure.restrict_univ] using h

/-- BHK (8.5), including both triangular Haar substitutions and the full
Fubini permutation: the averaged Hall--Petresco correlation is exactly the
central-fiber fourfold expression. -/
theorem integral_centralHallValue_eq_fiberFourfold
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : CompactCentralAction G X μ) (f : C(X, ℝ)) :
    (∫ g, ∫ h, ∫ u, centralHallValue m μ C f g h u ∂m ∂m ∂m) =
      ∫ x, fiberFourfold m (fiberFamily (orbitFiberMap C f)) x ∂μ := by
  let qμ : Measure ((G × G) × G) := (m.prod m).prod m
  let rμ : Measure (X × G) := μ.prod m
  let F : (((G × G) × G) × (X × G)) → ℝ :=
    fun z ↦ packedHallIntegrand C f z.1 z.2
  have hF : Integrable F (qμ.prod rμ) := by
    rw [← integrableOn_univ]
    exact ContinuousOn.integrableOn_compact (μ := qμ.prod rμ)
      isCompact_univ (continuous_packedHallIntegrand C f).continuousOn
  have hq :
      Integrable
        (fun q : (G × G) × G ↦
          centralHallValue m μ C f q.1.1 q.1.2 q.2) qμ := by
    simpa only [centralHallValue, qμ, rμ, F] using hF.integral_prod_left
  have hgh :
      Integrable
        (fun gh : G × G ↦
          ∫ u, centralHallValue m μ C f gh.1 gh.2 u ∂m)
        (m.prod m) := by
    simpa only [qμ] using hq.integral_prod_left
  have htriple :
      (∫ g, ∫ h, ∫ u, centralHallValue m μ C f g h u ∂m ∂m ∂m) =
        ∫ q, centralHallValue m μ C f q.1.1 q.1.2 q.2 ∂qμ := by
    calc
      (∫ g, ∫ h, ∫ u, centralHallValue m μ C f g h u ∂m ∂m ∂m) =
          ∫ gh, ∫ u, centralHallValue m μ C f gh.1 gh.2 u ∂m
            ∂(m.prod m) :=
        (integral_prod _ hgh).symm
      _ = ∫ q, centralHallValue m μ C f q.1.1 q.1.2 q.2 ∂qμ := by
        simpa only [qμ] using (integral_prod _ hq).symm
  have hswap :
      (∫ q, centralHallValue m μ C f q.1.1 q.1.2 q.2 ∂qμ) =
        ∫ r, ∫ q, packedHallIntegrand C f q r ∂qμ ∂rμ := by
    calc
      (∫ q, centralHallValue m μ C f q.1.1 q.1.2 q.2 ∂qμ) =
          ∫ z, F z ∂(qμ.prod rμ) := by
        simpa only [centralHallValue, qμ, rμ, F] using
          (integral_prod F hF).symm
      _ = ∫ r, ∫ q, packedHallIntegrand C f q r ∂qμ ∂rμ := by
        simpa only [F] using integral_prod_symm F hF
  have hpoint (r : X × G) :
      (∫ q, packedHallIntegrand C f q r ∂qμ) =
        fiberFourfold m (fiberFamily (orbitFiberMap C f)) r.1 := by
    have hcq :
        Continuous (fun q : (G × G) × G ↦
          packedHallIntegrand C f q r) :=
      (continuous_packedHallIntegrand C f).comp
        (continuous_id.prodMk continuous_const)
    have hiq : Integrable
        (fun q : (G × G) × G ↦ packedHallIntegrand C f q r) qμ := by
      rw [← integrableOn_univ]
      exact ContinuousOn.integrableOn_compact (μ := qμ)
        isCompact_univ hcq.continuousOn
    have hpair :
        Integrable
          (fun gh : G × G ↦
            ∫ u, packedHallIntegrand C f (gh, u) r ∂m)
          (m.prod m) := by
      simpa only [qμ] using hiq.integral_prod_left
    calc
      (∫ q, packedHallIntegrand C f q r ∂qμ) =
          ∫ g, ∫ h, ∫ u,
            hallCentralIntegrand C f r.1 r.2 g h u ∂m ∂m ∂m := by
        rw [show (∫ q, packedHallIntegrand C f q r ∂qμ) =
            ∫ gh, ∫ u, packedHallIntegrand C f (gh, u) r ∂m
              ∂(m.prod m) by
          simpa only [qμ] using integral_prod _ hiq]
        simpa only [packedHallIntegrand] using integral_prod _ hpair
      _ = ∫ g, ∫ b, ∫ w,
            hallReducedIntegrand C f r.1 g b w ∂m ∂m ∂m :=
        integral_hallCentral_eq_reduced m C f r.1 r.2
      _ = fiberFourfold m (fiberFamily (orbitFiberMap C f)) r.1 :=
        integral_reduced_eq_fiberFourfold m C f r.1
  have hcfour :
      Continuous
        (fiberFourfold m (fiberFamily (orbitFiberMap C f))) :=
    continuous_fiberFourfold_fiberFamily m (orbitFiberMap C f)
  have hr : Integrable
      (fun r : X × G ↦
        fiberFourfold m (fiberFamily (orbitFiberMap C f)) r.1) rμ := by
    rw [← integrableOn_univ]
    exact ContinuousOn.integrableOn_compact (μ := rμ)
      isCompact_univ (hcfour.comp continuous_fst).continuousOn
  calc
    (∫ g, ∫ h, ∫ u, centralHallValue m μ C f g h u ∂m ∂m ∂m) =
        ∫ r, ∫ q, packedHallIntegrand C f q r ∂qμ ∂rμ :=
      htriple.trans hswap
    _ = ∫ r,
        fiberFourfold m (fiberFamily (orbitFiberMap C f)) r.1 ∂rμ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ x, fiberFourfold m
        (fiberFamily (orbitFiberMap C f)) x ∂μ := by
      have hr' : Integrable
          (fun r : X × G ↦
            fiberFourfold m (fiberFamily (orbitFiberMap C f)) r.1)
          (μ.prod m) := by
        simpa only [rμ] using hr
      rw [integral_prod _ hr']
      simp

/-- The sharp inequality in BHK (8.5): the Hall--Petresco central average
dominates the fourth power of the mean. -/
theorem mean_pow_four_le_integral_centralHallValue
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : CompactCentralAction G X μ)
    (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    (∫ x, f x ∂μ) ^ 4 ≤
      ∫ g, ∫ h, ∫ u,
        centralHallValue m μ C f g h u ∂m ∂m ∂m := by
  rw [integral_centralHallValue_eq_fiberFourfold m μ C f]
  exact compactCentralAction_fourfold_lower_bound m hcube μ C f hf

/-- Pointwise sharp form of the central calculation: some Hall--Petresco
parameter attains at least the fourth power of the mean. -/
theorem exists_centralHallValue_ge_mean_pow_four
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : CompactCentralAction G X μ)
    (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    ∃ g h u : G,
      (∫ x, f x ∂μ) ^ 4 ≤ centralHallValue m μ C f g h u := by
  let ν : Measure ((G × G) × G) := (m.prod m).prod m
  let q : C(((G × G) × G), ℝ) :=
    ⟨fun z ↦ centralHallValue m μ C f z.1.1 z.1.2 z.2,
      continuous_centralHallValue m μ C f⟩
  have hq : Integrable (fun z ↦ q z) ν := by
    rw [← integrableOn_univ]
    exact ContinuousOn.integrableOn_compact (μ := ν)
      isCompact_univ q.continuous.continuousOn
  have hgh :
      Integrable
        (fun gh : G × G ↦
          ∫ u, centralHallValue m μ C f gh.1 gh.2 u ∂m)
        (m.prod m) := by
    simpa only [ν, q] using hq.integral_prod_left
  have havg :
      (∫ z, q z ∂ν) =
        ∫ g, ∫ h, ∫ u,
          centralHallValue m μ C f g h u ∂m ∂m ∂m := by
    calc
      (∫ z, q z ∂ν) =
          ∫ gh, ∫ u,
            centralHallValue m μ C f gh.1 gh.2 u ∂m
              ∂(m.prod m) := by
        simpa only [ν, q] using integral_prod _ hq
      _ = ∫ g, ∫ h, ∫ u,
            centralHallValue m μ C f g h u ∂m ∂m ∂m := by
        simpa using integral_prod _ hgh
  obtain ⟨z, hz⟩ := exists_integral_le_value ν q
  refine ⟨z.1.1, z.1.2, z.2, ?_⟩
  calc
    (∫ x, f x ∂μ) ^ 4 ≤
        ∫ g, ∫ h, ∫ u,
          centralHallValue m μ C f g h u ∂m ∂m ∂m :=
      mean_pow_four_le_integral_centralHallValue m hcube μ C f hf
    _ = ∫ y, q y ∂ν := havg.symm
    _ ≤ q z := hz
    _ = centralHallValue m μ C f z.1.1 z.1.2 z.2 := rfl

end Chapter02.HostKraCentralChangeVariables
