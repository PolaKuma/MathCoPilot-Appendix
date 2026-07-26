import Chapter02.HostKra.HostKraCentralFiberSupremum

open Classical MeasureTheory Set

noncomputable section

namespace Chapter02.HostKraHallPetrescoCorrelation

universe u v

open Chapter02.CentralFiberFourfold
open Chapter02.HostKraCentralChangeVariables
open Chapter02.HostKraStructuredRecurrence

variable {G : Type u} [CommGroup G] [MetricSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- A semantically complete Hall--Petresco model for one fixed correlation
sequence.  The same observation `ψ` both generates the sequence along the
distinguished minimal orbit and realizes every central Hall parameter. -/
def HasHallPetrescoCorrelationOrbit
    (m : Measure G)
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] (μ : Measure X)
    (C : CompactCentralAction G X μ) (f : C(X, ℝ))
    (a : ℕ → ℝ) : Prop :=
  ∃ P : Type, ∃ _top : TopologicalSpace P, ∃ _compact : CompactSpace P,
    ∃ T : P → P, ∃ p₀ : P, ∃ ψ : P → ℝ,
    ∃ param : ((G × G) × G) → P,
      Continuous T ∧ EveryOrbitHitsOpen T ∧ Continuous ψ ∧
      Continuous param ∧
      (∀ n : ℕ, a n = ψ ((T^[n]) p₀)) ∧
      ∀ q : (G × G) × G,
        ψ (param q) =
          centralHallValue m μ C f q.1.1 q.1.2 q.2

omit [CompactSpace G] [IsTopologicalGroup G] [BorelSpace G] in
theorem isMinimalOrbitSequence_of_correlationOrbit
    {m : Measure G}
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    {C : CompactCentralAction G X μ} {f : C(X, ℝ)}
    {a : ℕ → ℝ}
    (ha : HasHallPetrescoCorrelationOrbit m μ C f a) :
    IsMinimalOrbitSequence.{0} a := by
  obtain ⟨P, topP, compactP, T, p₀, ψ, param,
      hT, hdense, hψ, _hparam, haeq, _hpoint⟩ := ha
  letI : TopologicalSpace P := topP
  letI : CompactSpace P := compactP
  exact ⟨P, inferInstance, inferInstance, T, p₀, ψ,
    hT, hdense, hψ, haeq⟩

/-- The Fourier/Haar estimate is attained on the very same minimal orbit
that represents the given correlation sequence. -/
theorem exists_high_of_correlationOrbit
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : CompactCentralAction G X μ)
    (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x)
    (a : ℕ → ℝ)
    (ha : HasHallPetrescoCorrelationOrbit m μ C f a) :
    ∀ δ : ℝ, 0 < δ →
      ∃ n : ℕ, (∫ x, f x ∂μ) ^ 4 - δ < a n := by
  obtain ⟨P, topP, compactP, T, p₀, ψ, param,
      hT, hdense, hψ, hparam, haeq, hpoint⟩ := ha
  letI : TopologicalSpace P := topP
  letI : CompactSpace P := compactP
  obtain ⟨g, h, u, hhigh⟩ :=
    exists_centralHallValue_ge_mean_pow_four m hcube μ C f hf
  intro δ hδ
  let U : Set P := ψ ⁻¹' Set.Ioi ((∫ x, f x ∂μ) ^ 4 - δ)
  have hUopen : IsOpen U := isOpen_Ioi.preimage hψ
  have hUne : U.Nonempty := by
    refine ⟨param ((g, h), u), ?_⟩
    change (∫ x, f x ∂μ) ^ 4 - δ <
      ψ (param ((g, h), u))
    rw [hpoint]
    linarith
  obtain ⟨n, hn⟩ := hdense p₀ U hUopen hUne
  refine ⟨n, ?_⟩
  rw [haeq]
  exact hn

theorem sharp_minimalOrbitSequence_of_correlationOrbit
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : CompactCentralAction G X μ)
    (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x)
    (a : ℕ → ℝ)
    (ha : HasHallPetrescoCorrelationOrbit m μ C f a) :
    IsMinimalOrbitSequence.{0} a ∧
      ∀ δ : ℝ, 0 < δ →
        ∃ n : ℕ, (∫ x, f x ∂μ) ^ 4 - δ < a n :=
  ⟨isMinimalOrbitSequence_of_correlationOrbit ha,
    exists_high_of_correlationOrbit m hcube μ C f hf a ha⟩

end Chapter02.HostKraHallPetrescoCorrelation
