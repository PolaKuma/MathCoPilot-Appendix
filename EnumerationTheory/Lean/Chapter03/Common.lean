import Chapter02.Section06

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter03

structure PartialQuotients where
  a₀ : ℤ
  tail : ℕ -> ℕ

def partialQuotient (a : PartialQuotients) : ℕ -> ℤ
  | 0 => a.a₀
  | n + 1 => a.tail n

def IsRegularPartialQuotients (a : PartialQuotients) : Prop :=
  ∀ n : ℕ, 0 < a.tail n

/-- The exact domain used for the nonnegative continued fractions in Section 3.1. -/
def IsNonnegativeRegularPartialQuotients (a : PartialQuotients) : Prop :=
  0 ≤ a.a₀ ∧ IsRegularPartialQuotients a

/-- Nonnegative integer first term together with a sequence of positive tail terms. -/
abbrev NonnegativeRegularPartialQuotients :=
  {a : PartialQuotients // IsNonnegativeRegularPartialQuotients a}

def finiteContinuedFractionFrom (a : PartialQuotients) : ℕ -> ℕ -> ℚ
  | 0, i => (partialQuotient a i : ℚ)
  | n + 1, i =>
      (partialQuotient a i : ℚ) + (finiteContinuedFractionFrom a n (i + 1))⁻¹

def finiteContinuedFraction (a : PartialQuotients) (n : ℕ) : ℚ :=
  finiteContinuedFractionFrom a n 0

/-- The value assigned to an infinite continued fraction by its convergent limit. -/
noncomputable def continuedFractionValue (a : PartialQuotients) : ℝ :=
  limUnder atTop (fun n : ℕ => ((finiteContinuedFraction a n : ℚ) : ℝ))

def HasContinuedFractionExpansion (u : ℝ) (a : PartialQuotients) : Prop :=
  IsRegularPartialQuotients a ∧
    Tendsto (fun n : ℕ => ((finiteContinuedFraction a n : ℚ) : ℝ)) atTop (nhds u)

def partialQuotientMatrix (m : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![m, 1; 1, 0]

def convergentMatrixProduct (a : PartialQuotients) :
    ℕ -> Matrix (Fin 2) (Fin 2) ℤ
  | 0 => partialQuotientMatrix (partialQuotient a 0)
  | n + 1 =>
      convergentMatrixProduct a n * partialQuotientMatrix (partialQuotient a (n + 1))

def convergentNumerator (a : PartialQuotients) (n : ℕ) : ℤ :=
  (convergentMatrixProduct a n) 0 0

def convergentDenominator (a : PartialQuotients) (n : ℕ) : ℤ :=
  (convergentMatrixProduct a n) 1 0

def previousConvergentNumerator (a : PartialQuotients) (n : ℕ) : ℤ :=
  (convergentMatrixProduct a n) 0 1

def previousConvergentDenominator (a : PartialQuotients) (n : ℕ) : ℤ :=
  (convergentMatrixProduct a n) 1 1

def HasConvergentMatrixFormula (a : PartialQuotients) : Prop :=
  ∀ n : ℕ,
    0 < convergentDenominator a n ∧
    Nat.Coprime (convergentNumerator a n).natAbs
      (convergentDenominator a n).natAbs ∧
    finiteContinuedFraction a n =
      (convergentNumerator a n : ℚ) / (convergentDenominator a n : ℚ) ∧
    (convergentMatrixProduct a n) =
      !![convergentNumerator a n, previousConvergentNumerator a n;
        convergentDenominator a n, previousConvergentDenominator a n] ∧
    Matrix.det (convergentMatrixProduct a n) = (-1 : ℤ) ^ (n + 1)

def HasUniqueNonnegativeIrrationalExpansion (u : ℝ) : Prop :=
  0 ≤ u -> Irrational u ->
    ∃! a : NonnegativeRegularPartialQuotients,
      HasContinuedFractionExpansion u a.1

/-- The map in Proposition 3.1.4 from nonnegative regular partial quotients to `ℝ`. -/
noncomputable def nonnegativeContinuedFractionMap
    (a : NonnegativeRegularPartialQuotients) : ℝ :=
  continuedFractionValue a.1

/-- Proposition 3.1.4: the continued-fraction map is injective and every
nonnegative irrational has a unique expansion in its exact source domain. -/
def NonnegativeContinuedFractionClassification : Prop :=
  Function.Injective nonnegativeContinuedFractionMap ∧
    ∀ u : ℝ, HasUniqueNonnegativeIrrationalExpansion u

def goldenRatioConjugatePartials : PartialQuotients where
  a₀ := 0
  tail := fun _ => 1

def convergentErrorBound (u : ℝ) (a : PartialQuotients) : Prop :=
  HasContinuedFractionExpansion u a ->
    ∀ n : ℕ,
      |u - ((finiteContinuedFraction a n : ℚ) : ℝ)| <
        ((convergentDenominator a n : ℝ) *
          (convergentDenominator a (n + 1) : ℝ))⁻¹

def nearestIntegerDistance (t : ℝ) : ℝ :=
  sInf {d : ℝ | ∃ n : ℤ, d = |t - (n : ℝ)|}

def HasZeroLiminfAtTop (x : ℕ -> ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε -> ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ |x n| < ε

def LittlewoodConjectureStatement : Prop :=
  ∀ u v : ℝ,
    HasZeroLiminfAtTop fun n : ℕ =>
      (n : ℝ) * nearestIntegerDistance ((n : ℝ) * u) *
        nearestIntegerDistance ((n : ℝ) * v)

def littlewoodExceptionalSet : Set (ℝ × ℝ) :=
  {z : ℝ × ℝ |
    ¬ HasZeroLiminfAtTop fun n : ℕ =>
      (n : ℝ) * nearestIntegerDistance ((n : ℝ) * z.1) *
        nearestIntegerDistance ((n : ℝ) * z.2)}

def HasHausdorffDimensionZero (E : Set (ℝ × ℝ)) : Prop :=
  ∀ s : ℝ, 0 < s -> ∀ δ : ℝ, 0 < δ -> ∀ ε : ℝ, 0 < ε ->
    ∃ U : ℕ -> Set (ℝ × ℝ),
      E ⊆ ⋃ n, U n ∧
      (∀ n, Metric.diam (U n) < δ) ∧
      Summable (fun n => (Metric.diam (U n)) ^ s) ∧
      (∑' n, (Metric.diam (U n)) ^ s) < ε

/-- The Gauss-map formula on ambient real numbers. -/
def gaussMapReal (x : ℝ) : ℝ :=
  x⁻¹ - (Int.floor x⁻¹ : ℝ)

/-- The Gauss density, represented first as a measure supported on `[0,1]` in `ℝ`. -/
def gaussMeasureOnReal : MeasureTheory.Measure ℝ :=
  (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity
    (fun x => ENNReal.ofReal ((Real.log 2 * (1 + x))⁻¹))

/-- The actual carrier of the continued-fraction dynamical system in Section 3.2. -/
abbrev GaussSpace := Set.Icc (0 : ℝ) 1

/-- A measurable retraction used to transport the supported real measure to `GaussSpace`. -/
def unitIntervalProjection (x : ℝ) : GaussSpace :=
  ⟨max 0 (min 1 x), by
    constructor
    · exact le_max_left _ _
    · exact max_le zero_le_one (min_le_left _ _)⟩

/-- The Gauss measure as a measure on the exact carrier `[0,1]`. -/
noncomputable def gaussMeasure : MeasureTheory.Measure GaussSpace :=
  MeasureTheory.Measure.map unitIntervalProjection gaussMeasureOnReal

/-- The fractional-part formula for the Gauss map stays in `[0,1]`. -/
theorem gaussMapReal_mem_gaussSpace (x : ℝ) :
    gaussMapReal x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Int.fract_nonneg x⁻¹
  · exact (Int.fract_lt_one x⁻¹).le

/-- The Gauss transformation as the self-map `T : [0,1] → [0,1]` of the book. -/
def gaussMap (x : GaussSpace) : GaussSpace :=
  ⟨gaussMapReal x.1, gaussMapReal_mem_gaussSpace x.1⟩

structure GaussSystemData where
  μ : MeasureTheory.Measure GaussSpace
  T : GaussSpace -> GaussSpace

def IsGaussMeasure (μ : MeasureTheory.Measure GaussSpace) : Prop :=
  μ = gaussMeasure

def IsGaussTransformation (T : GaussSpace -> GaussSpace) : Prop :=
  T = gaussMap

def IsMeasurePreservingGaussSystem (G : GaussSystemData) : Prop :=
  IsGaussMeasure G.μ ∧ IsGaussTransformation G.T ∧
    MeasureTheory.IsProbabilityMeasure G.μ ∧
    MeasureTheory.MeasurePreserving G.T G.μ G.μ

def IsErgodicGaussSystem (G : GaussSystemData) : Prop :=
  IsMeasurePreservingGaussSystem G ∧
    ∀ A : Set GaussSpace, MeasurableSet A ->
      G.μ (Chapter00.symmDiff (G.T ⁻¹' A) A) = 0 ->
        G.μ A = 0 ∨ G.μ A = 1

def shiftPartials (a : PartialQuotients) : PartialQuotients where
  a₀ := a.tail 0
  tail := fun n => a.tail (n + 1)

def ShiftSemiconjugatesContinuedFractionMap : Prop :=
  ∀ x : ℝ, ∀ a : PartialQuotients,
    x ∈ Set.Ioo 0 1 -> HasContinuedFractionExpansion x a ->
      HasContinuedFractionExpansion (gaussMapReal x) (shiftPartials a)

def gaussDigit (x : ℝ) (n : ℕ) : ℕ :=
  Int.toNat (Int.floor (((gaussMapReal^[n]) x)⁻¹))

def gaussPartialQuotients (x : ℝ) : PartialQuotients where
  a₀ := 0
  tail := gaussDigit x

def completeQuotient (u : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then u else ((gaussMapReal^[n - 1]) u)⁻¹

def CompleteQuotientRelations : Prop :=
  ∀ u : ℝ, ∀ a : PartialQuotients,
    HasContinuedFractionExpansion u a -> ∀ n : ℕ, 1 ≤ n ->
      completeQuotient u n =
        (partialQuotient a n : ℝ) + (completeQuotient u (n + 1))⁻¹

def AlmostEveryOnUnitInterval (P : ℝ -> Prop) : Prop :=
  ∀ᵐ x ∂gaussMeasure, P x.1

def digitFrequency (a : PartialQuotients) (j n : ℕ) : ℝ :=
  (((Finset.range n).filter fun k => a.tail k = j).card : ℝ) / (n : ℝ)

def geometricMeanPartialQuotients (a : PartialQuotients) (n : ℕ) : ℝ :=
  Real.exp (((n : ℝ)⁻¹) *
    (Finset.range n).sum (fun k => Real.log (a.tail k : ℝ)))

noncomputable def khinchinConstant : ℝ :=
  ∏' a : ℕ,
    Real.rpow (((a + 2 : ℝ) ^ 2) / ((a + 1 : ℝ) * (a + 3 : ℝ)))
      (Real.log (a + 1 : ℝ) / Real.log 2)

def levyConstant : ℝ :=
  Real.pi ^ 2 / (12 * Real.log 2)

def continuedFractionErrorExponent : ℝ :=
  -Real.pi ^ 2 / (6 * Real.log 2)

def IsBadlyApproximable (u : ℝ) : Prop :=
  ∃ a : PartialQuotients, ∃ M : ℕ,
    HasContinuedFractionExpansion u a ∧ 0 < M ∧ ∀ n : ℕ, a.tail n ≤ M

/-- Definition 3.3.1 as stated on `[0,1]`, where the integer part is zero. -/
def IsUnitIntervalBadlyApproximable (u : ℝ) : Prop :=
  u ∈ Set.Icc (0 : ℝ) 1 ∧
    ∃ a : PartialQuotients, ∃ M : ℕ,
      a.a₀ = 0 ∧ HasContinuedFractionExpansion u a ∧
        0 < M ∧ ∀ n : ℕ, a.tail n ≤ M

def HasDiophantineBadApproximationBound (u : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ p : ℤ, ∀ q : ℕ, 0 < q ->
      ε / (q : ℝ) ^ 2 ≤ |u - (p : ℝ) / (q : ℝ)|

def IsQuadraticIrrational (u : ℝ) : Prop :=
  Irrational u ∧ ∃ a b c : ℤ,
    a ≠ 0 ∧ (a : ℝ) * u ^ 2 + (b : ℝ) * u + (c : ℝ) = 0

def IsEventuallyPeriodic (a : PartialQuotients) : Prop :=
  ∃ N k : ℕ, 0 < k ∧ ∀ n : ℕ, N ≤ n ->
    partialQuotient a (n + k) = partialQuotient a n

def HasEventuallyPeriodicContinuedFraction (u : ℝ) : Prop :=
  ∃ a : PartialQuotients, HasContinuedFractionExpansion u a ∧ IsEventuallyPeriodic a

end Chapter03
