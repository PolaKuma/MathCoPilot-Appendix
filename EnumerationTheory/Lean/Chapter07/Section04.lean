import Chapter07.Section03

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter07

universe u v w

namespace Section04

/-- Source: Definition 7.4.1, Chapter 7, Section 4.  The value is `⊤` when
there is no finite subcover. -/
def combinatorialCoverNumber {X : Type u} (𝓤 : SetCover X) : ENNReal :=
  setCoverNumber 𝓤

/-- Source: Definition 7.4.1, Chapter 7, Section 4. -/
def combinatorialCoverEntropy {X : Type u} (𝓤 : SetCover X) : EReal :=
  setCoverEntropy 𝓤

/-- Source: Proposition 7.4.2, Chapter 7, Section 4. -/
theorem openCoverEntropy_basicProperties
    {X : Type u} [Nonempty X] (T : X -> X) (𝓤 𝓥 : SetCover X) :
    0 ≤ setCoverEntropy 𝓤 ∧
      (setCoverRefines 𝓥 𝓤 -> setCoverEntropy 𝓤 ≤ setCoverEntropy 𝓥) ∧
      setCoverEntropy (setCoverJoin 𝓤 𝓥) ≤
        setCoverEntropy 𝓤 + setCoverEntropy 𝓥 ∧
      setCoverEntropy (setCoverPullback T 𝓤) ≤ setCoverEntropy 𝓤 ∧
      (Function.Surjective T ->
        setCoverEntropy 𝓤 = setCoverEntropy (setCoverPullback T 𝓤)) := by
  sorry

/-- Source: Proposition 7.4.3, Chapter 7, Section 4. -/
theorem iteratedOpenCoverEntropy_subadditiveAndLimit
    {X : Type u} [Nonempty X] (T : X -> X) (𝓤 : SetCover X) :
    (∀ m n : ℕ, 0 < m -> 0 < n ->
      setCoverEntropy (setCoverIterateJoin T 𝓤 (m + n)) ≤
        setCoverEntropy (setCoverIterateJoin T 𝓤 m) +
          setCoverEntropy (setCoverIterateJoin T 𝓤 n)) ∧
      Tendsto
        (fun n : ℕ =>
          setCoverEntropy (setCoverIterateJoin T 𝓤 (n + 1)) / (n + 1 : EReal))
        atTop (nhds (combinatorialCoverEntropyRate T 𝓤)) ∧
      combinatorialCoverEntropyRate T 𝓤 =
        sInf {r : EReal | ∃ n : ℕ, 0 < n ∧
          r = setCoverEntropy (setCoverIterateJoin T 𝓤 n) / (n : EReal)} := by
  sorry

/-- Source: Definition 7.4.3, Chapter 7, Section 4. -/
def topologicalEntropyWithOpenCover (S : System.{u}) (𝓤 : OpenCover S.X) : EReal :=
  topologicalCoverEntropyRate S 𝓤

/-- Source: Proposition 7.4.4, Chapter 7, Section 4. -/
theorem openCoverEntropyRate_basicProperties
    {X : Type u} [Nonempty X] (T : X -> X) (𝓤 𝓥 : SetCover X) :
    combinatorialCoverEntropyRate T 𝓤 ≤ setCoverEntropy 𝓤 ∧
      0 ≤ combinatorialCoverEntropyRate T 𝓤 ∧
      (setCoverRefines 𝓥 𝓤 -> combinatorialCoverEntropyRate T 𝓤 ≤
        combinatorialCoverEntropyRate T 𝓥) ∧
      combinatorialCoverEntropyRate T (setCoverJoin 𝓤 𝓥) ≤
        combinatorialCoverEntropyRate T 𝓤 + combinatorialCoverEntropyRate T 𝓥 ∧
      combinatorialCoverEntropyRate T (setCoverPullback T 𝓤) ≤
        combinatorialCoverEntropyRate T 𝓤 ∧
      (Function.Surjective T -> combinatorialCoverEntropyRate T 𝓤 =
        combinatorialCoverEntropyRate T (setCoverPullback T 𝓤)) := by
  sorry

/-- Source: Definition 7.4.5, Chapter 7, Section 4.  This definition genuinely
allows the value `+∞`. -/
def topologicalEntropyOfSystem (S : System.{u}) : EReal :=
  topologicalEntropy S

/-- Source: Proposition 7.4.6, Chapter 7, Section 4. -/
theorem topologicalEntropy_subsystem_factor_and_inverse
    (S : System.{u}) (R : System.{v}) [Nonempty S.X] [Nonempty R.X]
    (π : S.X -> R.X) (hS : Chapter05.IsTopologicalSystem S) :
    (∀ (A : Set S.X) (hA : Set.MapsTo S.T A A), A.Nonempty -> IsClosed A ->
      topologicalEntropy (restrictedSystem S A hA) ≤ topologicalEntropy S) ∧
    (Chapter05.IsFactorMap S R π ->
      topologicalEntropy R ≤ topologicalEntropy S) ∧
    (∀ inv : S.X -> S.X, Chapter05.IsContinuousInverse S inv ->
      topologicalEntropy ({ S with T := inv }) = topologicalEntropy S) := by
  sorry

/-- Source: Remark 7.4.7, Chapter 7, Section 4. -/
theorem topologicalEntropy_conjugacyInvariant
    (S : System.{u}) (R : System.{v}) [Nonempty S.X] [Nonempty R.X] :
    Chapter05.IsTopologicallyConjugate S R ->
      topologicalEntropy S = topologicalEntropy R := by
  sorry

/-- Source: Example 7.4.8, Chapter 7, Section 4. -/
theorem identityMap_hasZeroTopologicalEntropy
    (S : System.{u}) [Nonempty S.X]
    (hS : Chapter05.IsTopologicalSystem S) :
    S.T = id -> topologicalEntropy S = 0 := by
  sorry

/-- Source: Definition 7.4.9(1), Chapter 7, Section 4. -/
def bowenSeparatedFamily (S : System.{u}) [PseudoMetricSpace S.X]
    (n : ℕ) (ε : ℝ) (A : Finset S.X) : Prop :=
  IsMetricSeparatedOn S Set.univ n ε A

/-- Source: Definition 7.4.9(2), Chapter 7, Section 4. -/
def bowenSpanningFamily (S : System.{u}) [PseudoMetricSpace S.X]
    (n : ℕ) (ε : ℝ) (A : Finset S.X) : Prop :=
  IsMetricSpanningFor S Set.univ n ε A

/-- Source: Definition 7.4.9, Chapter 7, Section 4: `sr(n, ε, T)`. -/
def separatedNumber (S : System.{u}) [PseudoMetricSpace S.X]
    (n : ℕ) (ε : ℝ) : ENNReal :=
  metricSeparatedNumber S Set.univ n ε

/-- Source: Definition 7.4.9, Chapter 7, Section 4: `sp(n, ε, T)`. -/
def spanningNumber (S : System.{u}) [PseudoMetricSpace S.X]
    (n : ℕ) (ε : ℝ) : ENNReal :=
  metricSpanningNumber S Set.univ n ε

/-- Source: Definition 7.4.9, Chapter 7, Section 4: the upper exponential
growth rates at scale `ε`. -/
def separatedEntropyAtScale (S : System.{u}) [PseudoMetricSpace S.X]
    (ε : ℝ) : EReal :=
  metricSeparatedEntropyAtScale S Set.univ ε

def spanningEntropyAtScale (S : System.{u}) [PseudoMetricSpace S.X]
    (ε : ℝ) : EReal :=
  metricSpanningEntropyAtScale S Set.univ ε

/-- Source: Definition 7.4.9, Chapter 7, Section 4: limits as `ε ↓ 0`. -/
def separatedMetricEntropy (S : System.{u}) [PseudoMetricSpace S.X] : EReal :=
  metricSeparatedEntropy S Set.univ

def spanningMetricEntropy (S : System.{u}) [PseudoMetricSpace S.X] : EReal :=
  metricSpanningEntropy S Set.univ

/-- Source: Lemma 7.4.10, Chapter 7, Section 4. -/
theorem spanningSeparated_metricBounds
    (S : System.{u}) [Nonempty S.X] [PseudoMetricSpace S.X]
    (hcompact : IsCompact (Set.univ : Set S.X)) (n : ℕ) (hn : 0 < n)
    (ε : ℝ) (hε : 0 < ε) :
    spanningNumber S n ε ≤ separatedNumber S n ε ∧
      separatedNumber S n ε ≤ spanningNumber S n (ε / 2) ∧
      spanningEntropyAtScale S ε ≤ separatedEntropyAtScale S ε ∧
      separatedEntropyAtScale S ε ≤ spanningEntropyAtScale S (ε / 2) ∧
      spanningMetricEntropy S = separatedMetricEntropy S := by
  sorry

/-- Source: Proposition 7.4.11, Chapter 7, Section 4. -/
theorem openCoverAndBowenEntropy_agree
    (S : System.{u}) [Nonempty S.X] [PseudoMetricSpace S.X]
    (hcompat : MetricCompatibleWithTopology S)
    (hcompact : IsCompact (Set.univ : Set S.X)) (hT : Continuous S.T) :
    topologicalEntropy S = spanningMetricEntropy S ∧
      spanningMetricEntropy S = separatedMetricEntropy S := by
  sorry

/-- Lower-limit versions introduced in Corollary 7.4.12. -/
def separatedEntropyAtScaleInf (S : System.{u}) [PseudoMetricSpace S.X]
    (ε : ℝ) : EReal :=
  liminf (fun n : ℕ =>
    ENNReal.log (separatedNumber S (n + 1) ε) / (n + 1 : EReal)) atTop

def spanningEntropyAtScaleInf (S : System.{u}) [PseudoMetricSpace S.X]
    (ε : ℝ) : EReal :=
  liminf (fun n : ℕ =>
    ENNReal.log (spanningNumber S (n + 1) ε) / (n + 1 : EReal)) atTop

def separatedMetricEntropyInf (S : System.{u}) [PseudoMetricSpace S.X] : EReal :=
  sSup {r : EReal | ∃ ε : ℝ, 0 < ε ∧ r = separatedEntropyAtScaleInf S ε}

def spanningMetricEntropyInf (S : System.{u}) [PseudoMetricSpace S.X] : EReal :=
  sSup {r : EReal | ∃ ε : ℝ, 0 < ε ∧ r = spanningEntropyAtScaleInf S ε}

/-- Source: Corollary 7.4.12, Chapter 7, Section 4. -/
theorem lowerLimitBowenEntropy_agreesWithTopologicalEntropy
    (S : System.{u}) [Nonempty S.X] [PseudoMetricSpace S.X]
    (hcompat : MetricCompatibleWithTopology S)
    (hcompact : IsCompact (Set.univ : Set S.X)) (hT : Continuous S.T) :
    topologicalEntropy S = spanningMetricEntropyInf S ∧
      spanningMetricEntropyInf S = separatedMetricEntropyInf S := by
  sorry

/-- Source: Example 7.4.13, Chapter 7, Section 4. -/
theorem isometric_and_equicontinuousSystems_haveZeroEntropy
    (S : System.{u}) [Nonempty S.X] [PseudoMetricSpace S.X]
    (hcompat : MetricCompatibleWithTopology S)
    (hcompact : IsCompact (Set.univ : Set S.X)) (hT : Continuous S.T) :
    ((∀ x y : S.X, dist (S.T x) (S.T y) = dist x y) ->
      topologicalEntropy S = 0) ∧
    (Chapter05.IsEquicontinuous S -> topologicalEntropy S = 0) := by
  sorry

/-- Source: Definition 7.4.14(1), Chapter 7, Section 4. -/
def compactSetSeparatedNumber (S : System.{u}) [PseudoMetricSpace S.X]
    (K : Set S.X) (n : ℕ) (ε : ℝ) : ENNReal :=
  metricSeparatedNumber S K n ε

/-- Source: Definition 7.4.14(2), Chapter 7, Section 4. -/
def compactSetSpanningNumber (S : System.{u}) [PseudoMetricSpace S.X]
    (K : Set S.X) (n : ℕ) (ε : ℝ) : ENNReal :=
  metricSpanningNumber S K n ε

/-- Source: Definition 7.4.14, Chapter 7, Section 4: Bowen entropy on a
possibly noncompact metric space is the supremum over compact subsets. -/
def noncompactBowenEntropy (S : System.{u}) [PseudoMetricSpace S.X] : EReal :=
  bowenMetricEntropy S

/-- The spanning and separated formulations in Definition 7.4.14 agree. -/
theorem noncompactBowenEntropy_spanningSeparatedAgreement
    (S : System.{u}) [PseudoMetricSpace S.X] (hT : UniformContinuous S.T) :
    bowenMetricEntropy S =
      sSup {r : EReal | ∃ K : Set S.X, IsCompact K ∧
        r = metricSeparatedEntropy S K} := by
  sorry

/-- Source: Proposition 7.4.15, Chapter 7, Section 4. -/
theorem uniformlyEquivalentMetrics_giveSameBowenEntropy
    (S : System.{u}) (u₁ u₂ : UniformSpace S.X)
    (hT₁ : @UniformContinuous S.X S.X u₁ u₁ S.T)
    (hT₂ : @UniformContinuous S.X S.X u₂ u₂ S.T)
    (h₁₂ : @UniformContinuous S.X S.X u₁ u₂ id)
    (h₂₁ : @UniformContinuous S.X S.X u₂ u₁ id) :
    bowenEntropyWithUniformity S u₁ = bowenEntropyWithUniformity S u₂ := by
  sorry

/-- The positive half-line used in the example of Remark 7.4.16. -/
abbrev PositiveHalfLine := {x : ℝ // 0 < x}

def positiveDoubling (x : PositiveHalfLine) : PositiveHalfLine :=
  ⟨2 * x.1, mul_pos (by norm_num) x.2⟩

def positiveDoublingSystem : System.{0} where
  X := PositiveHalfLine
  topology := inferInstance
  T := positiveDoubling

/-- Source: Remark 7.4.16, Chapter 7, Section 4.  Topologically equivalent but
not uniformly equivalent metrics can produce different Bowen entropies; the
book's example is doubling on the positive half-line. -/
theorem equivalentMetrics_canGiveDifferentBowenEntropies :
    let S := positiveDoublingSystem
    let u₀ : UniformSpace PositiveHalfLine := inferInstance
    ∃ u₁ : UniformSpace PositiveHalfLine,
      u₁.toTopologicalSpace = u₀.toTopologicalSpace ∧
      ¬ (@UniformContinuous PositiveHalfLine PositiveHalfLine u₀ u₁ id ∧
        @UniformContinuous PositiveHalfLine PositiveHalfLine u₁ u₀ id) ∧
      @UniformContinuous PositiveHalfLine PositiveHalfLine u₁ u₁ S.T ∧
      (Real.log 2 : EReal) ≤ bowenEntropyWithUniformity S u₀ ∧
      bowenEntropyWithUniformity S u₁ = 0 := by
  sorry

end Section04
end Chapter07
