import Chapter06.Section03

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter06

universe u v w

namespace Section04


/-- Source: Definition 6.4.1, Chapter 6, Section 4. -/
def uniquelyErgodicSystem (S : System.{u}) : Prop :=
  IsUniquelyErgodic S

/--
Source: Definition 6.4.1, Chapter 6, Section 4.
If the invariant-measure set is a singleton, then its unique measure is ergodic.
-/
def uniqueInvariantMeasureIsErgodicRemark (S : System.{u}) : Prop :=
  IsUniquelyErgodic S -> invariantMeasures S = ergodicMeasures S

/--
Source: Theorem 6.4.2, Chapter 6, Section 4.
Unique ergodicity is equivalent to uniform convergence of all Birkhoff averages
to constants, pointwise convergence of all such averages to constants, and
uniform empirical equidistribution of all orbits toward one invariant measure.
-/
theorem uniqueErgodicityEquivalentCharacterizations (S : System.{u}) :
    IsUniquelyErgodic S ↔
      BirkhoffAveragesConvergeUniformlyToConstant S ∧
        BirkhoffAveragesConvergePointwiseToConstant S ∧
          ∃ μ : MeasureOn S.X, IsInvariantMeasure S μ ∧ EveryOrbitEquidistributesTo S μ := by
  sorry

/--
Source: Theorem 6.4.3, Chapter 6, Section 4.
The support of the unique invariant measure of a uniquely ergodic system is
minimal.
-/
theorem supportOfUniqueInvariantMeasureIsMinimal
    (S : System.{u}) (μ : MeasureOn S.X) :
    IsUniquelyErgodic S -> invariantMeasures S = {μ} ->
      Chapter05.IsMinimalSet S (support μ) := by
  sorry

/--
Source: Proposition 6.4.4, Chapter 6, Section 4.
Unique ergodicity is equivalent to the existence, for every continuous function,
of a pointwise constant-convergent subsequence of Birkhoff averages.
-/
theorem uniqueErgodicityIffSubsequentialConstantPointwiseAverages
    (S : System.{u}) (hS : Chapter05.IsTopologicalSystem S) :
    IsUniquelyErgodic S ↔ ∀ f : S.X -> ℂ, Continuous f -> ∃ n : ℕ -> ℕ, StrictMono n ∧
      ∃ c : ℂ, ∀ x : S.X, Tendsto (fun k : ℕ =>
        if n k = 0 then 0 else ((n k : ℂ)⁻¹ * (Finset.range (n k)).sum (fun i => f ((S.T^[i]) x)))) atTop (nhds c) := by
  sorry

/--
Source: Proposition 6.4.5, Chapter 6, Section 4.
A transitive system whose Birkhoff averages form equicontinuous families for
every continuous observable is uniquely ergodic.
-/
theorem transitiveEquicontinuousAveragesImplyUniqueErgodicity
    (S : System.{u}) :
    Chapter05.IsTopologicalSystem S -> Chapter05.IsTopologicallyTransitive S ->
      (∀ f : S.X -> ℂ, Continuous f -> BirkhoffAverageFamilyEquicontinuous S f) ->
        IsUniquelyErgodic S := by
  sorry

/-- Source: Definition 6.4.6, Chapter 6, Section 4. -/
def strictlyErgodicSystem (S : System.{u}) : Prop :=
  IsStrictlyErgodic S

/--
Source: Example 6.4.7, Chapter 6, Section 4.
Finite cyclic rotations, irrational circle rotations, adding machines, and
rationally independent torus rotations are strictly ergodic.
-/
theorem basicStrictlyErgodicExamples :
    (∀ n : ℕ, ∀ hn : 0 < n, IsStrictlyErgodic (finiteCyclicRotationSystem n hn)) ∧
    (∀ α : ℝ, Irrational α -> IsStrictlyErgodic (circleRotationTopologicalSystem α)) ∧
    IsStrictlyErgodic binaryOdometerTopologicalSystem ∧
    (∀ k : ℕ, 2 ≤ k -> ∀ θ : Fin k → ℝ, IsTotallyIrrationalRotationVector θ ->
      IsStrictlyErgodic (torusRotationTopologicalSystem k θ)) := by
  sorry

/--
Source: Theorem 6.4.8, Chapter 6, Section 4.
A circle homeomorphism with no periodic points is uniquely ergodic and is
semiconjugate to an irrational rotation; if it is minimal, the semiconjugacy is
a conjugacy.
-/
theorem aperiodicCircleHomeomorphismUniquelyErgodicSemiconjugateRotation :
    ∀ T : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ),
      (∀ x, ¬ Chapter05.periodicPoint (circleHomeomorphismSystem T) x) ->
      IsUniquelyErgodic (circleHomeomorphismSystem T) ∧
        ∃ α : ℝ, Irrational α ∧
          ∃ φ : AddCircle (1 : ℝ) → AddCircle (1 : ℝ),
            Chapter05.IsFactorMap (circleHomeomorphismSystem T)
              (circleRotationTopologicalSystem α) φ ∧
            (∀ w, IsPointOrClosedArc (φ ⁻¹' {w})) ∧
            (Chapter05.IsMinimalSystem (circleHomeomorphismSystem T) ->
              Function.Bijective φ) := by
  sorry

/--
Source: Example 6.4.9, Chapter 6, Section 4.
Skew torus maps, minimal nilsystems, horocycle systems, Morse systems, Chacon
systems, and regular almost automorphic systems provide further strictly
ergodic examples.
-/
theorem furtherStrictlyErgodicExamples :
    ∃ S : System.{0}, IsStrictlyErgodic S ∧ Chapter05.IsMSystem S := by
  sorry

/-- Source: Definition 6.4.10, Chapter 6, Section 4. -/
def equidistributedUnitIntervalSequence (x : ℕ -> Set.Icc (0 : ℝ) 1) : Prop :=
  IsEquidistributedInUnitInterval x

/--
Source: Lemma 6.4.11, Chapter 6, Section 4.
Weyl criterion: equidistribution in `[0,1]` is equivalent to vanishing of all
nonzero exponential sums and to correct interval frequencies.
-/
theorem weylCriterionEquivalentForms (x : ℕ -> ℝ)
    (hx : ∀ n, x n ∈ Set.Icc (0 : ℝ) 1) :
    (IsEquidistributedInUnitInterval (unitIntervalSequence x hx) ↔
      WeylCriterionSequence x) ∧
    (WeylCriterionSequence x ↔ IntervalFrequencyCondition x) := by
  sorry

/--
Source: Theorem 6.4.12, Chapter 6, Section 4.
For irrational `α`, the sequence `{n α mod 1}` is equidistributed in `[0,1]`.
-/
theorem weylEquidistributionForIrrationalRotation (α : ℝ) :
    Irrational α -> WeylCriterionSequence fun n : ℕ => (n : ℝ) * α := by
  sorry

/--
Source: Example 6.4.13, Chapter 6, Section 4.
The leading digits of powers of two have Benford frequencies
`log_10((k+1)/k)`.
-/
theorem leadingDigitsOfPowersOfTwoBenford :
    ∀ k : ℕ, 1 ≤ k -> k ≤ 9 ->
      Tendsto (fun n : ℕ =>
        (leadingDigitCountPowersOfTwo k (n + 1) : ℝ) / (n + 1 : ℝ))
        atTop (nhds (Real.log ((k + 1 : ℝ) / (k : ℝ)) / Real.log 10)) := by
  sorry

/-- Source: Definition 6.4.14, Chapter 6, Section 4. -/
def equidistributedForMeasure {X : Type u} [TopologicalSpace X]
    (μ : MeasureOn X) (x : ℕ -> X) : Prop :=
  IsEquidistributedForMeasure X μ x

/--
Source: Remark 6.4.15, Chapter 6, Section 4.
A point is generic for an invariant measure iff its forward orbit is
equidistributed with respect to that measure.
-/
def genericPointIffOrbitEquidistributedRemark
    (S : System.{u}) (μ : MeasureOn S.X) (x : S.X) : Prop :=
  IsGenericPoint S μ x ↔ IsEquidistributedForMeasure S.X μ (fun n : ℕ => (S.T^[n]) x)

/--
Source: Theorem 6.4.16, Chapter 6, Section 4.
Furstenberg's criterion: an ergodic compact-group skew product over a uniquely
ergodic base is uniquely ergodic.
-/
theorem furstenbergSkewProductUniqueErgodicityCriterion :
    IsSkewProductUniquelyErgodicCriterion := by
  sorry

/--
Source: Proposition 6.4.17, Chapter 6, Section 4.
The triangular skew translation on the `k`-torus with irrational base rotation
is strictly ergodic.
-/
theorem triangularTorusSkewTranslationStrictlyErgodic :
    ∀ k : ℕ, 2 ≤ k -> ∀ α : ℝ, Irrational α ->
      IsStrictlyErgodic (triangularTorusTopologicalSystem k α) := by
  sorry

/--
Source: Theorem 6.4.18, Chapter 6, Section 4.
Weyl's polynomial equidistribution theorem: if a real polynomial has at least
one irrational nonconstant coefficient, then `P(n) mod 1` is equidistributed.
-/
theorem weylPolynomialEquidistributionTheorem
    (P : Polynomial ℝ) :
    (∃ k : ℕ, 0 < k ∧ Irrational (P.coeff k)) ->
      WeylCriterionSequence (fun n : ℕ => P.eval (n : ℝ)) := by
  sorry

end Section04
end Chapter06
