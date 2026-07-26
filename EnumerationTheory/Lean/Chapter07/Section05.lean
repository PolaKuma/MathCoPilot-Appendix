import Chapter07.Section04

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter07

universe u v w

namespace Section05

/-- Source: Lemma 7.5.1, Chapter 7, Section 5.
Open covers whose diameters tend to zero recover the full topological entropy. -/
theorem smallDiameterCovers_determineTopologicalEntropy
    (S : System.{u}) [PseudoMetricSpace S.X]
    (covers : ℕ -> OpenCover S.X) :
    Chapter05.IsCompactTopologicalSystem S ->
    MetricCompatibleWithTopology S ->
    Tendsto (fun n => openCoverDiameter S (covers n)) atTop (nhds 0) ->
      Tendsto (fun n => topologicalCoverEntropyRate S (covers n)) atTop
        (nhds (topologicalEntropy S)) := by
  sorry

/-- Source: Lemma 7.5.2, Chapter 7, Section 5.
Joining a cover with its first `n` inverse iterates does not change its relative
entropy.  `coverIterateJoin S cover (n+1)` is the book's `cover₀ⁿ`. -/
theorem entropyOfFiniteJoinIterates_sameAsCoverEntropy
    (S : System.{u}) (cover : OpenCover S.X) (n : ℕ) :
    Chapter05.IsCompactTopologicalSystem S ->
      topologicalCoverEntropyRate S (coverIterateJoin S cover (n + 1)) =
        topologicalCoverEntropyRate S cover := by
  sorry

/-- Source: Remark 7.5.3, Chapter 7, Section 5.
For an invertible system the join from time `-n` through time `n` has the same
relative entropy as the original cover. -/
theorem invertibleSystem_twoSidedCoverIterates
    (S : System.{u}) [PseudoMetricSpace S.X] (inv : S.X -> S.X)
    (cover : OpenCover S.X) (n : ℕ)
    (hcompact : Chapter05.IsCompactTopologicalSystem S)
    (hinv : Chapter05.IsContinuousInverse S inv) :
      topologicalCoverEntropyRate S
          (twoSidedCoverIterateJoin S inv hcompact.1 hinv cover n) =
        topologicalCoverEntropyRate S cover := by
  sorry

/-- Source: Proposition 7.5.4 (Abramov theorem), Chapter 7, Section 5. -/
theorem topologicalEntropy_naturalPowers
    (S : System.{u}) (m : ℕ) :
    Chapter05.IsCompactTopologicalSystem S ->
      topologicalEntropy (iterateSystem S m) =
        (m : EReal) * topologicalEntropy S := by
  sorry

/-- Source: Remark 7.5.5, Chapter 7, Section 5.
For an invertible system the entropy of an integer power is scaled by `|m|`. -/
theorem invertibleTopologicalEntropy_integerPowers
    (S : System.{u}) (inv : S.X -> S.X) (m : ℤ) :
    Chapter05.IsCompactTopologicalSystem S ->
    Chapter05.IsContinuousInverse S inv ->
      topologicalEntropy (integerPowerSystem S inv m) =
        (m.natAbs : EReal) * topologicalEntropy S := by
  sorry

/-- Source: Theorem 7.5.6, Chapter 7, Section 5.
Topological entropy is additive under the genuine product system. -/
theorem topologicalEntropy_productAdditivity
    (S : System.{u}) (R : System.{v})
    [PseudoMetricSpace S.X] [PseudoMetricSpace R.X] :
    Chapter05.IsCompactTopologicalSystem S ->
    Chapter05.IsCompactTopologicalSystem R ->
    MetricCompatibleWithTopology S -> MetricCompatibleWithTopology R ->
      topologicalEntropy (productSystem S R) =
        topologicalEntropy S + topologicalEntropy R := by
  sorry

/-- Source: Theorem 7.5.7, Chapter 7, Section 5.
An expansive homeomorphism has both of the book's entropy formulas: a generator
computes entropy, and every scale below one quarter of an expansive constant
computes the spanning and separated versions. -/
theorem expansiveHomeomorphism_entropyFormulas
    (S : System.{u}) [PseudoMetricSpace S.X]
    (inv : S.X -> S.X) (δ : ℝ) :
    Chapter05.IsCompactTopologicalSystem S ->
    MetricCompatibleWithTopology S ->
    Chapter05.IsExpansiveWithConstant S inv δ ->
      (∀ generator : OpenCover S.X,
        Chapter05.IsGeneratorCover S generator.sets ->
          topologicalEntropy S = topologicalCoverEntropyRate S generator) ∧
      (∀ ε : ℝ, 0 < ε -> ε < δ / 4 ->
        topologicalEntropy S = metricSpanningEntropyAtScale S Set.univ ε ∧
        metricSpanningEntropyAtScale S Set.univ ε =
          metricSeparatedEntropyAtScale S Set.univ ε) := by
  sorry

/-- Source: Corollary 7.5.8, Chapter 7, Section 5.
An expansive homeomorphism has finite topological entropy. -/
theorem expansiveHomeomorphism_hasFiniteTopologicalEntropy
    (S : System.{u}) [PseudoMetricSpace S.X] :
    Chapter05.IsCompactTopologicalSystem S ->
    MetricCompatibleWithTopology S -> Chapter05.IsExpansive S ->
      topologicalEntropy S < ⊤ := by
  sorry

/-- Source: Theorem 7.5.9, Chapter 7, Section 5.
A finite measurable partition of diameter below an expansive constant generates
the full Borel sigma algebra under all integer iterates and computes entropy for
every invariant probability measure encoded by `M`. -/
theorem smallMeasurablePartition_isGenerating_andComputesEntropy
    (M : MeasurableSystem.{u}) [PseudoMetricSpace M.X]
    (inv : M.X -> M.X) (δ : ℝ) (ξ : FiniteMeasurablePartition M) :
    Chapter01.IsMeasurePreservingSystem M ->
    M.measurableSpace = borel M.X ->
    Chapter05.IsCompactTopologicalSystem (topologicalSystemOfMeasurable M) ->
    MetricTopologyCompatible M.X ->
    IsExpansiveMapWithConstant M.T inv δ ->
    finitePartitionDiameter M ξ < δ ->
      MeasurableSpace.generateFrom (twoSidedPartitionOrbitSets M inv ξ) =
          M.measurableSpace ∧
        measureEntropy M = (partitionEntropyRate M ξ : EReal) := by
  sorry

/-- Source: Theorem 7.5.10, Chapter 7, Section 5.
Topological entropy can be computed on the nonwandering set. -/
theorem topologicalEntropy_restrictToNonwanderingSet
    (S : System.{u}) (hcompact : Chapter05.IsCompactTopologicalSystem S) :
      topologicalEntropy S =
        topologicalEntropy (nonwanderingRestrictedSystem S hcompact.1) := by
  sorry

/-- Source: Example 7.5.11, Chapter 7, Section 5.
For a nonempty closed invariant subshift, entropy is the limit of normalized
logarithmic word complexity; the full `k`-shift has entropy `log k`. -/
theorem subshiftEntropy_languageGrowth_and_fullShift
    (k : ℕ) (Y : Set (FullShiftSpace k))
    (hY : Set.MapsTo shiftMap Y Y) :
    0 < k -> Y.Nonempty -> IsClosed Y ->
      Tendsto
          (fun n : ℕ =>
            (Real.log (subshiftWordComplexity k Y (n + 1) : ℝ) / (n + 1) : EReal))
          atTop (nhds (topologicalEntropy (subshiftSystem k Y hY))) ∧
        topologicalEntropy (fullShiftSystem k) = (Real.log k : EReal) := by
  sorry

/-- Source: Example 7.5.12, Chapter 7, Section 5.
The entropy of the Markov shift of an irreducible zero-one matrix is the
logarithm of its Perron root. -/
theorem irreducibleMarkovShift_entropyLogPerronRoot
    {k : ℕ} (A : Fin k -> Fin k -> ℕ) (ρ : ℝ) :
    0 < k -> IsZeroOneMatrix A -> IsIrreducibleMatrix A -> IsPerronRoot A ρ ->
      topologicalEntropy (markovShiftSystem A) = (Real.log ρ : EReal) := by
  sorry

/-- Source: Example 7.5.13, Chapter 7, Section 5.
Every homeomorphism of the closed interval has zero topological entropy. -/
theorem intervalHomeomorphism_hasZeroTopologicalEntropy
    (T : Set.Icc (0 : ℝ) 1 ≃ₜ Set.Icc (0 : ℝ) 1) :
    topologicalEntropy
      ({ X := Set.Icc (0 : ℝ) 1, topology := inferInstance, T := T } : System) = 0 := by
  sorry

/-- Source: Example 7.5.14, Chapter 7, Section 5.
Every circle homeomorphism has zero topological entropy. -/
theorem circleHomeomorphism_hasZeroTopologicalEntropy
    (T : Circle ≃ₜ Circle) :
    topologicalEntropy
      ({ X := Circle, topology := inferInstance, T := T } : System) = 0 := by
  sorry

/-- Source: Example 7.5.15, Chapter 7, Section 5.
Every prescribed positive real is realized by the concrete one-sided beta-shift
built from the greedy expansion of `1` in base `exp a`. -/
theorem everyPositiveReal_isTopologicalEntropy_betaShift
    (a : ℝ) :
    0 < a -> ∃ k : ℕ, ∃ digits : ℕ -> Fin k, ∃ remainder : ℕ -> ℝ,
      IsGreedyBetaExpansion (Real.exp a) k digits remainder ∧
        topologicalEntropy (betaShiftSystem digits) = (a : EReal) := by
  sorry

/-- Source: Remark 7.5.16, Chapter 7, Section 5.
The natural two-sided extension of the same beta-shift has identical word
complexity and entropy, and its shift is a homeomorphism. -/
theorem everyPositiveReal_isTopologicalEntropy_twoSidedBetaShift
    (a : ℝ) :
    0 < a -> ∃ k : ℕ, ∃ digits : ℕ -> Fin k, ∃ remainder : ℕ -> ℝ,
      IsGreedyBetaExpansion (Real.exp a) k digits remainder ∧
      (∀ n : ℕ,
        subshiftWordComplexity k (twoSidedBetaShiftSpace digits) n =
          oneSidedWordComplexity k (betaShiftSpace digits) n) ∧
      (∃ inv : (twoSidedBetaShiftSystem digits).X ->
          (twoSidedBetaShiftSystem digits).X,
        Chapter05.IsContinuousInverse (twoSidedBetaShiftSystem digits) inv) ∧
      topologicalEntropy (twoSidedBetaShiftSystem digits) = (a : EReal) := by
  sorry

end Section05
end Chapter07
