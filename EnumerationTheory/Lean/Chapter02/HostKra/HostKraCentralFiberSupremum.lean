import Chapter02.HostKra.HostKraCentralChangeVariables
import Chapter02.HostKra.HostKraStructuredRecurrence

open Classical MeasureTheory Set

noncomputable section

namespace Chapter02.HostKraCentralFiberSupremum

universe u v

open Chapter02.CentralFiberFourfold
open Chapter02.HostKraCentralChangeVariables
open Chapter02.HostKraStructuredRecurrence

variable {G : Type u} [CommGroup G] [MetricSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- The exact Hall--Petresco orbit model needed after the central-fiber
calculation.

`param` is the three-central-parameter family used in BHK Section 8.
The final equality is the change-of-variables identity leading to (8.5).
All other fields say that `ψ` is observed on a compact minimal orbit. -/
def HasHallPetrescoCentralModel
    (m : Measure G)
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X]
    (μ : Measure X) (C : CompactCentralAction G X μ)
    (f : C(X, ℝ)) : Prop :=
  ∃ P : Type, ∃ _metric : MetricSpace P, ∃ _compact : CompactSpace P,
    ∃ T : P → P, ∃ p₀ : P, ∃ ψ : P → ℝ,
    ∃ param : ((G × G) × G) → P,
      Continuous T ∧ EveryOrbitHitsOpen T ∧ Continuous ψ ∧
      Continuous param ∧
      (∫ g, ∫ h, ∫ u, ψ (param ((g, h), u)) ∂m ∂m ∂m) =
        ∫ x, fiberFourfold m (fiberFamily (orbitFiberMap C f)) x ∂μ

/-- A pointwise realization of the actual Hall--Petresco correlation on a
compact minimal system.  Unlike `HasHallPetrescoCentralModel`, this
interface does not assume the averaged identity: that identity is now a
theorem of `HostKraCentralChangeVariables`. -/
def HasHallPetrescoOrbitRealization
    (m : Measure G)
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] (μ : Measure X)
    (C : CompactCentralAction G X μ) (f : C(X, ℝ)) : Prop :=
  ∃ P : Type, ∃ _metric : MetricSpace P, ∃ _compact : CompactSpace P,
    ∃ T : P → P, ∃ p₀ : P, ∃ ψ : P → ℝ,
    ∃ param : ((G × G) × G) → P,
      Continuous T ∧ EveryOrbitHitsOpen T ∧ Continuous ψ ∧
      Continuous param ∧
      ∀ q : (G × G) × G,
        ψ (param q) =
          centralHallValue m μ C f q.1.1 q.1.2 q.2

/-- The checked fivefold Fubini/change-of-variables formula turns a
pointwise Hall--Petresco orbit realization into the averaged model needed
by the compact-minimal supremum argument. -/
theorem centralModel_of_orbitRealization
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : CompactCentralAction G X μ) (f : C(X, ℝ))
    (hreal : HasHallPetrescoOrbitRealization m μ C f) :
    HasHallPetrescoCentralModel m μ C f := by
  obtain ⟨P, metricP, compactP, T, p₀, ψ, param,
      hT, hdense, hψ, hparam, hpoint⟩ := hreal
  refine ⟨P, metricP, compactP, T, p₀, ψ, param,
    hT, hdense, hψ, hparam, ?_⟩
  calc
    (∫ g, ∫ h, ∫ u, ψ (param ((g, h), u)) ∂m ∂m ∂m) =
        ∫ g, ∫ h, ∫ u,
          centralHallValue m μ C f g h u ∂m ∂m ∂m := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g ↦ by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun h ↦ by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun u ↦ hpoint ((g, h), u)
    _ = ∫ x, fiberFourfold m
          (fiberFamily (orbitFiberMap C f)) x ∂μ :=
      integral_centralHallValue_eq_fiberFourfold m μ C f

/-- A Hall--Petresco central model turns any lower bound for the central
average into a compact-minimal orbit sequence attaining the same bound up
to every positive error. -/
theorem exists_minimalOrbitSequence_high_of_centralModel
    (m : Measure G) [IsProbabilityMeasure m]
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X]
    (μ : Measure X) (C : CompactCentralAction G X μ)
    (f : C(X, ℝ))
    (hmodel : HasHallPetrescoCentralModel m μ C f)
    (c : ℝ)
    (hcentral :
      c ≤ ∫ x, fiberFourfold m (fiberFamily (orbitFiberMap C f)) x ∂μ) :
    ∃ a : ℕ → ℝ,
      IsMinimalOrbitSequence.{0} a ∧
      ∀ δ : ℝ, 0 < δ → ∃ n : ℕ, c - δ < a n := by
  obtain ⟨P, metricP, compactP, T, p₀, ψ, param,
      hT, hdense, hψ, hparam, havg⟩ := hmodel
  letI : MetricSpace P := metricP
  letI : CompactSpace P := compactP
  let q : C(((G × G) × G), ℝ) :=
    ⟨fun z ↦ ψ (param z), hψ.comp hparam⟩
  let ν : Measure ((G × G) × G) := (m.prod m).prod m
  have hqprod : Integrable (fun z ↦ q z) ν := by
    change Integrable (q : ((G × G) × G) → ℝ) ν
    rw [← integrableOn_univ]
    exact
      ContinuousOn.integrableOn_compact (μ := ν)
        isCompact_univ q.continuous.continuousOn
  have hqfirst :
      (∫ z, q z ∂ν) =
        ∫ gh, ∫ u, ψ (param (gh, u)) ∂m ∂(m.prod m) := by
    simpa only [ν, q] using integral_prod (fun z ↦ q z) hqprod
  have hqleft :
      Integrable
        (fun gh : G × G ↦ ∫ u, ψ (param (gh, u)) ∂m)
        (m.prod m) := by
    simpa only [ν, q] using hqprod.integral_prod_left
  have hqsecond :
      (∫ gh, ∫ u, ψ (param (gh, u)) ∂m ∂(m.prod m)) =
        ∫ g, ∫ h, ∫ u, ψ (param ((g, h), u)) ∂m ∂m ∂m := by
    simpa using
      integral_prod
        (fun gh : G × G ↦ ∫ u, ψ (param (gh, u)) ∂m)
        hqleft
  obtain ⟨z, hz⟩ := exists_integral_le_value ν q
  have hcz : c ≤ ψ (param z) := by
    calc
      c ≤ ∫ x, fiberFourfold m
          (fiberFamily (orbitFiberMap C f)) x ∂μ := hcentral
      _ = ∫ g, ∫ h, ∫ u,
          ψ (param ((g, h), u)) ∂m ∂m ∂m := havg.symm
      _ = ∫ y, q y ∂ν := (hqfirst.trans hqsecond).symm
      _ ≤ q z := hz
      _ = ψ (param z) := rfl
  let a : ℕ → ℝ := fun n ↦ ψ ((T^[n]) p₀)
  refine ⟨a, ?_, ?_⟩
  · exact
      ⟨P, inferInstance, inferInstance, T, p₀, ψ,
        hT, hdense, hψ, fun n ↦ rfl⟩
  · intro δ hδ
    let U : Set P := ψ ⁻¹' Set.Ioi (c - δ)
    have hUopen : IsOpen U := isOpen_Ioi.preimage hψ
    have hUne : U.Nonempty := by
      refine ⟨param z, ?_⟩
      change c - δ < ψ (param z)
      linarith
    obtain ⟨n, hn⟩ := hdense p₀ U hUopen hUne
    exact ⟨n, hn⟩

/-- The checked compact-central Fourier inequality supplies the hypothesis
of the preceding Hall--Petresco orbit lemma. -/
theorem exists_sharp_minimalOrbitSequence_of_centralModel
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : CompactCentralAction G X μ)
    (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x)
    (hmodel : HasHallPetrescoCentralModel m μ C f) :
    ∃ a : ℕ → ℝ,
      IsMinimalOrbitSequence.{0} a ∧
      ∀ δ : ℝ, 0 < δ →
        ∃ n : ℕ, (∫ x, f x ∂μ) ^ 4 - δ < a n := by
  exact exists_minimalOrbitSequence_high_of_centralModel
    m μ C f hmodel ((∫ x, f x ∂μ) ^ 4)
    (compactCentralAction_fourfold_lower_bound m hcube μ C f hf)

/-- Pointwise Hall--Petresco realization is now the only geometric input
needed for the sharp compact-minimal sequence: the averaged identity and
the Fourier lower bound are both checked theorems. -/
theorem exists_sharp_minimalOrbitSequence_of_orbitRealization
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : CompactCentralAction G X μ)
    (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x)
    (hreal : HasHallPetrescoOrbitRealization m μ C f) :
    ∃ a : ℕ → ℝ,
      IsMinimalOrbitSequence.{0} a ∧
      ∀ δ : ℝ, 0 < δ →
        ∃ n : ℕ, (∫ x, f x ∂μ) ^ 4 - δ < a n := by
  exact exists_sharp_minimalOrbitSequence_of_centralModel
    m hcube μ C f hf
    (centralModel_of_orbitRealization m μ C f hreal)

end Chapter02.HostKraCentralFiberSupremum
