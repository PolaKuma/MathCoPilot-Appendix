import Chapter02.Dynamics.CompactUniqueErgodicCesaro
import Chapter02.HostKra.HostKraCentralFiberSupremum
import Chapter02.HostKra.HostKraU3UniformBlockReduction

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HostKraHallPetrescoUniformMean

universe u v w

open Chapter02.CentralFiberFourfold
open Chapter02.HostKraCentralChangeVariables

variable {G : Type u} [CommGroup G] [MetricSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- A genuine uniquely ergodic Hall--Petresco mean model for one scalar
correlation sequence.  Besides representing the sequence on an actual
compact orbit, it identifies the integral of the observation against the
unique invariant probability measure with the checked three-parameter
central Haar average. -/
def HasUniqueHallPetrescoMeanOrbit
    (m : Measure G)
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X]
    (μ : Measure X) (C : CompactCentralAction G X μ)
    (f : C(X, ℝ)) (a : ℕ → ℝ) : Prop :=
  ∃ P : Type w, ∃ _metric : MetricSpace P, ∃ _compact : CompactSpace P,
    ∃ _meas : MeasurableSpace P, ∃ _borel : BorelSpace P,
    ∃ T : P → P, ∃ p₀ : P, ∃ ψ : C(P, ℝ),
    ∃ ν : ProbabilityMeasure P,
      Continuous T ∧
      CompactUniqueErgodicCesaro.HasUniqueIntegralInvariant T ν ∧
      (∀ n : ℕ, a n = ψ ((T^[n]) p₀)) ∧
      (∫ y, ψ y ∂(ν : Measure P)) =
        ∫ g, ∫ h, ∫ u,
          centralHallValue m μ C f g h u ∂m ∂m ∂m

/-- The unique Hall--Petresco mean orbit has translated-uniform Cesàro
liminf at least the central Haar average. -/
theorem uniformLiminfAtLeast_centralAverage
    (m : Measure G)
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X]
    (μ : Measure X) (C : CompactCentralAction G X μ)
    (f : C(X, ℝ)) (a : ℕ → ℝ)
    (ha : HasUniqueHallPetrescoMeanOrbit m μ C f a) :
    HostKraU3UniformBlockReduction.HasUniformCesaroLiminfAtLeast a
      (∫ g, ∫ h, ∫ u,
        centralHallValue m μ C f g h u ∂m ∂m ∂m) := by
  obtain ⟨P, metricP, compactP, measP, borelP,
    T, p₀, ψ, ν, hT, hunique, haeq, hmean⟩ := ha
  letI : MetricSpace P := metricP
  letI : CompactSpace P := compactP
  letI : MeasurableSpace P := measP
  letI : BorelSpace P := borelP
  intro ε hε
  filter_upwards [
    CompactUniqueErgodicCesaro.uniform_translated_cesaro_of_uniqueIntegralInvariant
      T hT ν hunique ψ ε hε] with N hN
  intro i
  have hi := hN p₀ i
  rw [hmean] at hi
  have hlower := (abs_lt.mp hi).1
  have heq :
      cesaroAverage (fun n ↦ a (i + n)) N =
        cesaroAverage (fun n ↦ ψ ((T^[i + n]) p₀)) N := by
    apply congrArg
      (fun s : ℕ → ℝ ↦ cesaroAverage s N)
    funext n
    exact haeq (i + n)
  rw [heq]
  linarith

/-- The checked central Fourier/Haar inequality upgrades the preceding
central-average lower limit to the sharp fourth power of the observation
mean. -/
theorem sharp_uniformLiminfAtLeast
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : CompactCentralAction G X μ)
    (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x)
    (a : ℕ → ℝ)
    (ha : HasUniqueHallPetrescoMeanOrbit m μ C f a) :
    HostKraU3UniformBlockReduction.HasUniformCesaroLiminfAtLeast a
      ((∫ x, f x ∂μ) ^ 4) := by
  have hcentral :
      (∫ x, f x ∂μ) ^ 4 ≤
        ∫ g, ∫ h, ∫ u,
          centralHallValue m μ C f g h u ∂m ∂m ∂m := by
    calc
      (∫ x, f x ∂μ) ^ 4 ≤
          ∫ x, fiberFourfold m
            (fiberFamily (orbitFiberMap C f)) x ∂μ :=
        compactCentralAction_fourfold_lower_bound
          m hcube μ C f hf
      _ = ∫ g, ∫ h, ∫ u,
          centralHallValue m μ C f g h u ∂m ∂m ∂m :=
        (integral_centralHallValue_eq_fiberFourfold m μ C f).symm
  have hlim :=
    uniformLiminfAtLeast_centralAverage m μ C f a ha
  intro ε hε
  filter_upwards [hlim ε hε] with N hN
  intro i
  exact lt_of_le_of_lt (sub_le_sub_right hcentral ε) (hN i)

end Chapter02.HostKraHallPetrescoUniformMean
