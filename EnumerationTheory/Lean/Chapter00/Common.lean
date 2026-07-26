import Mathlib

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter00

universe u v

abbrev SetFamily (X : Type u) := Set (Set X)

def PairwiseDisjoint {X : Type u} {n : ℕ} (A : Fin n -> Set X) : Prop :=
  ∀ i j : Fin n, i ≠ j -> Disjoint (A i) (A j)

/-!
The book's notion of a semialgebra includes a finite disjoint decomposition of
the complement of each member.  A Mathlib set semiring supplies the relative
difference decompositions; the additional finite disjoint cover of the whole
space recovers exactly the book's complement condition.
-/
def IsSemiAlgebra {X : Type u} (S : SetFamily X) : Prop :=
  MeasureTheory.IsSetSemiring S ∧
    ∃ n : ℕ, ∃ B : Fin n → Set X,
      PairwiseDisjoint B ∧ (∀ i, B i ∈ S) ∧ (⋃ i, B i) = Set.univ

def IsAlgebra {X : Type u} (A : SetFamily X) : Prop :=
  (∅ : Set X) ∈ A ∧
    (∀ E ∈ A, ∀ F ∈ A, E \ F ∈ A) ∧
    ∀ E ∈ A, Eᶜ ∈ A

def generatedAlgebra {X : Type u} (S : SetFamily X) : SetFamily X :=
  sInf {A : SetFamily X | IsAlgebra A ∧ S ⊆ A}

def IsSigmaAlgebraFamily {X : Type u} (𝓧 : SetFamily X) : Prop :=
  Set.univ ∈ 𝓧 ∧
    (∀ A ∈ 𝓧, Aᶜ ∈ 𝓧) ∧
    (∀ A : ℕ -> Set X, (∀ n : ℕ, A n ∈ 𝓧) -> (⋃ n : ℕ, A n) ∈ 𝓧)

def generatedSigmaAlgebra {X : Type u} (S : SetFamily X) : SetFamily X :=
  {A : Set X | @MeasurableSet X (MeasurableSpace.generateFrom S) A}

def IsMeasureOn {X : Type u} (𝓧 : SetFamily X) (μ : Set X -> ENNReal) : Prop :=
  IsSigmaAlgebraFamily 𝓧 ∧ μ ∅ = 0 ∧
    ∀ A : ℕ -> Set X, (∀ n, A n ∈ 𝓧) ->
      (∀ i j : ℕ, i ≠ j -> Disjoint (A i) (A j)) ->
        μ (⋃ n, A n) = ∑' n, μ (A n)

def IsProbabilityMeasureOn {X : Type u} (𝓧 : SetFamily X) (μ : Set X -> ENNReal) : Prop :=
  IsMeasureOn 𝓧 μ ∧ μ Set.univ = 1

def CountablyGeneratedFamily {X : Type u} (𝓧 : SetFamily X) : Prop :=
  ∃ A : ℕ -> Set X, generatedSigmaAlgebra (Set.range A) = 𝓧

abbrev ExtendedReal := EReal

def MeasurableExtendedRealFunction {X : Type u} (𝓧 : SetFamily X)
    (f : X -> ExtendedReal) : Prop :=
  ∀ c : ℝ, {x : X | (c : ExtendedReal) < f x} ∈ 𝓧

def symmDiff {X : Type u} (A B : Set X) : Set X :=
  (A \ B) ∪ (B \ A)

def almostEverywhereApproximation {X : Type u} (𝓧 : SetFamily X)
    (μ : Set X -> ENNReal) (A : SetFamily X) : Prop :=
  ∀ ε : ℝ, 0 < ε -> ∀ B ∈ 𝓧, ∃ C ∈ A, μ (symmDiff C B) < ENNReal.ofReal ε

abbrev LpMember {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (p : ENNReal) (f : X -> ℂ) : Prop :=
  MeasureTheory.MemLp f p μ

def IsLpInclusionStatement {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X)
    (p q : ENNReal) : Prop :=
  1 ≤ p ∧ p < q -> ∀ f : X -> ℂ, LpMember μ q f -> LpMember μ p f

def IsSeparableBanachLpStatement {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) : Prop :=
  MeasurableSpace.CountablyGenerated X ->
    ∀ p : ENNReal, 1 ≤ p -> p < ⊤ ->
      ∃ D : Set (X -> ℂ), D.Countable ∧
        ∀ f : X -> ℂ, MeasureTheory.MemLp f p μ -> ∀ ε : ℝ, 0 < ε ->
          ∃ g ∈ D, MeasureTheory.MemLp g p μ ∧
            MeasureTheory.eLpNorm (fun x => f x - g x) p μ < ENNReal.ofReal ε

structure BasicProbabilitySpaceData where
  X : Type u
  measurableSpace : MeasurableSpace X
  μ : @MeasureTheory.Measure X measurableSpace
  isProbability : @MeasureTheory.IsProbabilityMeasure X measurableSpace μ

attribute [instance] BasicProbabilitySpaceData.measurableSpace
  BasicProbabilitySpaceData.isProbability

namespace BasicProbabilitySpaceData

def 𝓧 (P : BasicProbabilitySpaceData) : SetFamily P.X :=
  {A | MeasurableSet A}

def integral (P : BasicProbabilitySpaceData) (f : P.X -> ℂ) : ℂ :=
  ∫ x, f x ∂P.μ

def lpMember (P : BasicProbabilitySpaceData) (p : ENNReal) (f : P.X -> ℂ) : Prop :=
  MeasureTheory.MemLp f p P.μ

def lpNorm (P : BasicProbabilitySpaceData) (p : ENNReal) (f : P.X -> ℂ) : ℝ :=
  (MeasureTheory.eLpNorm f p P.μ).toReal

end BasicProbabilitySpaceData

abbrev SignedMeasureData (X : Type u) [MeasurableSpace X] :=
  MeasureTheory.SignedMeasure X

def IsMeasureExtension {X : Type u} (S T : SetFamily X)
    (μ ν : Set X -> ENNReal) : Prop :=
  S ⊆ T ∧ ∀ A ∈ S, ν A = μ A

def EqualOnFamily {X : Type u} (T : SetFamily X)
    (μ ν : Set X -> ENNReal) : Prop :=
  ∀ A ∈ T, μ A = ν A

def IsFinitelyAdditiveOn {X : Type u} (S : SetFamily X) (μ : Set X -> ENNReal) : Prop :=
  μ ∅ = 0 ∧
    ∀ n : ℕ, ∀ A : Fin n -> Set X,
      (∀ i, A i ∈ S) -> PairwiseDisjoint A -> (⋃ i, A i) ∈ S ->
        μ (⋃ i, A i) = ∑ i, μ (A i)

def IsCountablyAdditiveOn {X : Type u} (S : SetFamily X) (μ : Set X -> ENNReal) : Prop :=
  IsFinitelyAdditiveOn S μ ∧
    ∀ A : ℕ -> Set X, (∀ n, A n ∈ S) -> (∀ i j : ℕ, i ≠ j -> Disjoint (A i) (A j)) ->
      (⋃ n, A n) ∈ S -> μ (⋃ n, A n) = ∑' n, μ (A n)

def IsMonotoneClass {X : Type u} (M : SetFamily X) : Prop :=
  (∀ A : ℕ -> Set X, (∀ n, A n ∈ M) -> (∀ n, A n ⊆ A (n + 1)) ->
    (⋃ n, A n) ∈ M) ∧
    ∀ A : ℕ -> Set X, (∀ n, A n ∈ M) -> (∀ n, A (n + 1) ⊆ A n) ->
      (⋂ n, A n) ∈ M

def generatedMonotoneClass {X : Type u} (A : SetFamily X) : SetFamily X :=
  sInf {M : SetFamily X | IsMonotoneClass M ∧ A ⊆ M}

/-- A finite consecutive-coordinate cylinder in a two-sided sequence space. -/
def twoSidedCylinder {Y : Type u} (h : ℤ) (word : List Y) : Set (ℤ -> Y) :=
  {x | ∀ i : Fin word.length, word[i]? = some (x (h + (i : ℕ)))}

def HasDaniellKolmogorovMeasure (k : ℕ)
    (p : ℕ -> List (Fin k) -> ℝ) : Prop :=
  2 ≤ k ->
  (∀ n : ℕ, ∀ word : List (Fin k), word.length = n + 1 -> 0 ≤ p n word) ->
  (Finset.univ.sum fun a : Fin k => p 0 [a]) = 1 ->
  (∀ n : ℕ, ∀ word : List (Fin k), word.length = n + 1 ->
    p n word = Finset.univ.sum fun a : Fin k => p (n + 1) (word ++ [a])) ->
  (∀ n : ℕ, ∀ word : List (Fin k), word.length = n + 1 ->
    p n word = Finset.univ.sum fun a : Fin k => p (n + 1) (a :: word)) ->
    ∃ m : MeasurableSpace (ℤ -> Fin k),
      m = MeasurableSpace.generateFrom
        {C : Set (ℤ -> Fin k) | ∃ h : ℤ, ∃ word : List (Fin k),
          C = twoSidedCylinder h word} ∧
      ∃ μ : @MeasureTheory.Measure (ℤ -> Fin k) m,
        @MeasureTheory.IsProbabilityMeasure (ℤ -> Fin k) m μ ∧
        (∀ h : ℤ, ∀ n : ℕ, ∀ word : List (Fin k), word.length = n + 1 ->
          μ (twoSidedCylinder h word) = ENNReal.ofReal (p n word)) ∧
        ∀ ν : @MeasureTheory.Measure (ℤ -> Fin k) m,
          @MeasureTheory.IsProbabilityMeasure (ℤ -> Fin k) m ν ->
          (∀ h : ℤ, ∀ n : ℕ, ∀ word : List (Fin k), word.length = n + 1 ->
            ν (twoSidedCylinder h word) = ENNReal.ofReal (p n word)) ->
          ν = μ

def MonotoneConvergenceStatement (P : BasicProbabilitySpaceData) : Prop :=
  ∀ f : ℕ -> P.X -> ℝ,
    (∀ n, MeasureTheory.Integrable (f n) P.μ) ->
    (∀ n, ∀ᵐ x ∂P.μ, f n x ≤ f (n + 1) x) ->
    BddAbove (Set.range fun n => ∫ x, f n x ∂P.μ) ->
      ∃ g : P.X -> ℝ, MeasureTheory.Integrable g P.μ ∧
        (∀ᵐ x ∂P.μ, Tendsto (fun n => f n x) atTop (nhds (g x))) ∧
        Tendsto (fun n => ∫ x, f n x ∂P.μ) atTop (nhds (∫ x, g x ∂P.μ))

def lowerShiftedExtendedIntegral (P : BasicProbabilitySpaceData)
    (f lower : P.X -> ℝ) : EReal :=
  ((∫ x, lower x ∂P.μ : ℝ) : EReal) +
    ((∫⁻ x, ENNReal.ofReal (f x - lower x) ∂P.μ : ENNReal) : EReal)

def FatouLemmaStatement (P : BasicProbabilitySpaceData) : Prop :=
  ∀ f : ℕ -> P.X -> ℝ, ∀ lower : P.X -> ℝ,
    (∀ n, MeasureTheory.AEStronglyMeasurable (f n) P.μ) ->
    MeasureTheory.Integrable lower P.μ ->
    (∀ n, ∀ᵐ x ∂P.μ, lower x ≤ f n x) ->
    Filter.liminf (fun n => lowerShiftedExtendedIntegral P (f n) lower) atTop < ⊤ ->
      MeasureTheory.Integrable (fun x => Filter.liminf (fun n => f n x) atTop) P.μ ∧
      ((∫ x, Filter.liminf (fun n => f n x) atTop ∂P.μ : ℝ) : EReal) ≤
        Filter.liminf (fun n => lowerShiftedExtendedIntegral P (f n) lower) atTop

def DominatedConvergenceStatement (P : BasicProbabilitySpaceData) : Prop :=
  ∀ f : ℕ -> P.X -> ℝ, ∀ g limit : P.X -> ℝ,
    (∀ n, MeasureTheory.AEStronglyMeasurable (f n) P.μ) ->
    MeasureTheory.Integrable g P.μ ->
    (∀ n, ∀ᵐ x ∂P.μ, |f n x| ≤ g x) ->
    (∀ᵐ x ∂P.μ, Tendsto (fun n => f n x) atTop (nhds (limit x))) ->
      MeasureTheory.Integrable limit P.μ ∧
      Tendsto (fun n => ∫ x, f n x ∂P.μ) atTop (nhds (∫ x, limit x ∂P.μ))

def NormConvergentLpSequenceHasAeSubsequence (P : BasicProbabilitySpaceData) : Prop :=
  ∀ p : ENNReal, 1 ≤ p -> ∀ f : ℕ -> P.X -> ℂ, ∀ limit : P.X -> ℂ,
    (∀ n, MeasureTheory.MemLp (f n) p P.μ) -> MeasureTheory.MemLp limit p P.μ ->
    Tendsto (fun n => MeasureTheory.eLpNorm (fun x => f n x - limit x) p P.μ)
      atTop (nhds 0) ->
      ∃ nseq : ℕ -> ℕ, StrictMono nseq ∧
        ∀ᵐ x ∂P.μ, Tendsto (fun k => f (nseq k) x) atTop (nhds (limit x))

def IsTopologicalSubbasis {X : Type u} (C : Set (Set X)) (T : TopologicalSpace X) : Prop :=
  T = TopologicalSpace.generateFrom C

def IsNowhereDenseSubset {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  interior (closure A) = ∅

def IsFirstCategorySubset {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ N : ℕ -> Set X, (∀ n, IsNowhereDenseSubset (N n)) ∧ A = ⋃ n, N n

def IsBaireSpaceProperty (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ U : Set X, IsOpen U -> U.Nonempty -> ¬ IsFirstCategorySubset U

def HasLebesgueNumber {X : Type u} [PseudoMetricSpace X] (α : Set (Set X)) (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ A : Set X, (∀ x ∈ A, ∀ y ∈ A, dist x y ≤ δ) ->
    ∃ U ∈ α, A ⊆ U

def derivedSet {X : Type u} [TopologicalSpace X] (A : Set X) : Set X :=
  {x : X | x ∈ closure (A \ {x})}

abbrev IsConnectedSubset {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  IsConnected A

def IsHomeomorphism {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X -> Y) : Prop :=
  ∃ e : X ≃ₜ Y, ∀ x : X, e x = f x

def HasCountableBasisSpace (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ B : ℕ -> Set X, (∀ n, IsOpen (B n)) ∧
    ∀ U : Set X, IsOpen U -> ∀ x ∈ U, ∃ n, x ∈ B n ∧ B n ⊆ U

def IsZeroDimensionalCompactSpace (X : Type u) [TopologicalSpace X] : Prop :=
  IsCompact (Set.univ : Set X) ∧ ∀ x : X, ∀ U : Set X, IsOpen U -> x ∈ U ->
    ∃ V : Set X, IsOpen V ∧ IsClosed V ∧ x ∈ V ∧ V ⊆ U

/-- A Hausdorff space with a clopen neighbourhood basis (Definition 0.2.28). -/
def IsZeroDimensionalSpace (X : Type u) [TopologicalSpace X] : Prop :=
  T2Space X ∧ ∀ x : X, ∀ U : Set X, IsOpen U -> x ∈ U ->
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U

def IsTotallyDisconnectedSpace (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ C : Set X, IsPreconnected C -> ∀ x ∈ C, ∀ y ∈ C, x = y

def SeparatesPoints {X : Type u} (A : Set (X -> ℝ)) : Prop :=
  ∀ x y : X, x ≠ y -> ∃ f ∈ A, f x ≠ f y

/-- The real continuous-function subalgebras used in Stone--Weierstrass. -/
def IsRealContinuousSubalgebra {X : Type u} [TopologicalSpace X]
    (A : Set C(X, ℝ)) : Prop :=
  (1 : C(X, ℝ)) ∈ A ∧
    (∀ c : ℝ, ∀ f ∈ A, c • f ∈ A) ∧
    (∀ f ∈ A, ∀ g ∈ A, f + g ∈ A ∧ f * g ∈ A)

/-- The complex continuous-function subalgebras used in Stone--Weierstrass. -/
def IsStarClosedComplexContinuousSubalgebra {X : Type u} [TopologicalSpace X]
    (A : Set C(X, ℂ)) : Prop :=
  (1 : C(X, ℂ)) ∈ A ∧
    (∀ c : ℂ, ∀ f ∈ A, c • f ∈ A ∧ star f ∈ A) ∧
    (∀ f ∈ A, ∀ g ∈ A, f + g ∈ A ∧ f * g ∈ A)

def SeparatesPointsContinuous {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (A : Set C(X, Y)) : Prop :=
  ∀ x y : X, x ≠ y -> ∃ f ∈ A, f x ≠ f y

def IsEquicontinuousFamily {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PseudoMetricSpace Y] (A : Set (X -> Y)) : Prop :=
  ∀ x : X, ∀ ε : ℝ, 0 < ε -> ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ y ∈ U, ∀ f ∈ A, dist (f y) (f x) < ε

def IsPointwiseRelativelyCompact {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (A : Set (X -> Y)) : Prop :=
  ∀ x : X, IsCompact (closure ((fun f : X -> Y => f x) '' A))

def IsEquicontinuousContinuousMapFamily {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PseudoMetricSpace Y] (A : Set C(X, Y)) : Prop :=
  ∀ x : X, ∀ ε : ℝ, 0 < ε -> ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ y ∈ U, ∀ f ∈ A, dist (f y) (f x) < ε

def IsUniformlyEquicontinuousContinuousMapFamily {X : Type u} {Y : Type v}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (A : Set C(X, Y)) : Prop :=
  ∀ ε : ℝ, 0 < ε -> ∃ δ : ℝ, 0 < δ ∧
    ∀ f ∈ A, ∀ x y : X, dist x y < δ -> dist (f x) (f y) < ε

def IsUniformlyBoundedContinuousMapFamily {X : Type u}
    [TopologicalSpace X] (A : Set C(X, ℂ)) : Prop :=
  ∃ M : ℝ, 0 < M ∧ ∀ f ∈ A, ∀ x : X, ‖f x‖ ≤ M

def IsPointwiseRelativelyCompactContinuousMapFamily {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (A : Set C(X, Y)) : Prop :=
  ∀ x : X, IsCompact (closure ((fun f : C(X, Y) => f x) '' A))

/-- The equivalence relation whose classes are connected components. -/
def ConnectedRelation {X : Type u} [TopologicalSpace X] (x y : X) : Prop :=
  ∃ C : Set X, IsConnected C ∧ x ∈ C ∧ y ∈ C

/-- The quotient topology on the quotient by a setoid. -/
def quotientTopologicalSpace {X : Type u} [TopologicalSpace X] (s : Setoid X) :
    TopologicalSpace (Quotient s) :=
  TopologicalSpace.coinduced (@Quotient.mk' X s) inferInstance

/-- A Cantor subset: nonempty, compact, metrizable, zero-dimensional, and without isolated points. -/
def IsCantorSubset {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  A.Nonempty ∧ IsCompact A ∧ TopologicalSpace.MetrizableSpace A ∧
    IsZeroDimensionalSpace A ∧ ∀ x : A, ¬ IsOpen ({x} : Set A)

structure ConditionalExpectationData (P : BasicProbabilitySpaceData) (A : SetFamily P.X) where
  op : (P.X -> ℂ) -> P.X -> ℂ

def IsMeasurableForFamily {X : Type u} {Y : Type v} [TopologicalSpace Y]
    (A : SetFamily X) (f : X -> Y) : Prop :=
  ∀ C : Set Y, IsClosed C -> f ⁻¹' C ∈ A

def IsConditionalExpectation (P : BasicProbabilitySpaceData) (A : SetFamily P.X)
    (E : ConditionalExpectationData P A) : Prop :=
  ∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
    IsMeasurableForFamily A (E.op f) ∧
    MeasureTheory.Integrable (E.op f) P.μ ∧
    ∀ B ∈ A, ∫ x in B, E.op f x ∂P.μ = ∫ x in B, f x ∂P.μ

structure ConditionalMeasureFamily (P : BasicProbabilitySpaceData) (A : SetFamily P.X) where
  fullSet : Set P.X
  measureAt : P.X -> MeasureTheory.Measure P.X

def IsConditionalMeasureFamily (P : BasicProbabilitySpaceData) (A : SetFamily P.X)
    (E : ConditionalExpectationData P A) (D : ConditionalMeasureFamily P A) : Prop :=
  D.fullSet ∈ A ∧ P.μ D.fullSet = 1 ∧
    (∀ x ∈ D.fullSet, MeasureTheory.IsProbabilityMeasure (D.measureAt x)) ∧
    (∀ B : Set P.X, MeasurableSet B ->
      IsMeasurableForFamily A (fun x => D.measureAt x B)) ∧
    ∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
      ∀ᵐ x ∂P.μ, E.op f x = ∫ y, f y ∂(D.measureAt x)

def HasMeasureDisintegration {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    (φ : X -> Y) (μ : MeasureTheory.Measure X) (ν : MeasureTheory.Measure Y) : Prop :=
  Measurable φ ∧ ν = MeasureTheory.Measure.map φ μ ∧
    ∃ μy : Y -> MeasureTheory.Measure X,
      (∀ᵐ y ∂ν, MeasureTheory.IsProbabilityMeasure (μy y) ∧
        μy y (φ ⁻¹' {y}) = 1) ∧
      (∀ B : Set X, MeasurableSet B -> Measurable fun y => μy y B) ∧
      (∀ B : Set X, MeasurableSet B -> μ B = ∫⁻ y, μy y B ∂ν) ∧
      ∀ μy' : Y -> MeasureTheory.Measure X,
        (∀ᵐ y ∂ν, MeasureTheory.IsProbabilityMeasure (μy' y) ∧
          μy' y (φ ⁻¹' {y}) = 1) ->
        (∀ B : Set X, MeasurableSet B -> Measurable fun y => μy' y B) ->
        (∀ B : Set X, MeasurableSet B -> μ B = ∫⁻ y, μy' y B ∂ν) ->
        ∀ᵐ y ∂ν, μy y = μy' y

def HasHaarMeasure (G : Type u) [Group G] [TopologicalSpace G]
    [MeasurableSpace G] : Prop :=
  ∃ μ : MeasureTheory.Measure G, μ.IsHaarMeasure

def HasLeftInvariantMetric (G : Type u) [Group G] [PseudoMetricSpace G] : Prop :=
  ∀ z x y : G, dist (z * x) (z * y) = dist x y

abbrev CharacterGroup (G : Type u) [TopologicalSpace G] [Monoid G] : Type u :=
  ContinuousMonoidHom G Circle

def IsCircleClosedSubgroupClassification : Prop :=
  ∀ H : Subgroup Circle, IsClosed (H : Set Circle) ->
    H = ⊤ ∨ ∃ p : ℕ, 0 < p ∧
      (H : Set Circle) = {z : Circle | z ^ p = 1}

def complexIntPower (z : ℂ) (m : ℤ) : ℂ :=
  if 0 ≤ m then z ^ m.toNat else z⁻¹ ^ (-m).toNat

def IsNonnegativeMatrix (k : ℕ) (A : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ i j, 0 ≤ A i j

def IsIrreducibleNonnegativeMatrix (k : ℕ)
    (A : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  IsNonnegativeMatrix k A ∧ ∀ i j, ∃ n : ℕ, 0 < n ∧ 0 < (A ^ n) i j

def IsAperiodicNonnegativeMatrix (k : ℕ)
    (A : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  IsNonnegativeMatrix k A ∧ ∃ n : ℕ, 0 < n ∧ ∀ i j, 0 < (A ^ n) i j

def IsComplexEigenvalueOfRealMatrix (k : ℕ)
    (A : Matrix (Fin k) (Fin k) ℝ) (z : ℂ) : Prop :=
  ∃ w : Fin k -> ℂ, w ≠ 0 ∧
    ∀ i, (Finset.univ.sum fun j : Fin k => (A i j : ℂ) * w j) = z * w i

def IsPerronFrobeniusMatrixStatement (k : ℕ)
    (A : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  0 < k -> IsNonnegativeMatrix k A ->
    ∃ lam : ℝ, 0 ≤ lam ∧
      (∀ z : ℂ, IsComplexEigenvalueOfRealMatrix k A z -> ‖z‖ ≤ lam) ∧
      (∃ imin imax : Fin k,
        (Finset.univ.sum fun j : Fin k => A imin j) ≤ lam ∧
        lam ≤ Finset.univ.sum fun j : Fin k => A imax j) ∧
      ∃ u v : Fin k -> ℝ,
        u ≠ 0 ∧ v ≠ 0 ∧ (∀ i, 0 ≤ u i ∧ 0 ≤ v i) ∧
        (∀ j, (Finset.univ.sum fun i : Fin k => u i * A i j) = lam * u j) ∧
        (∀ i, (Finset.univ.sum fun j : Fin k => A i j * v j) = lam * v i) ∧
        (IsIrreducibleNonnegativeMatrix k A ->
          (∀ i, 0 < u i ∧ 0 < v i) ∧
          (∀ w : Fin k -> ℝ,
            (∀ i, (Finset.univ.sum fun j : Fin k => A i j * w j) = lam * w i) ->
              ∃ c : ℝ, w = fun i => c * v i) ∧
          (¬ ∃ w : Fin k -> ℝ,
            ∀ i, (Finset.univ.sum fun j : Fin k => A i j * w j) - lam * w i = v i) ∧
          (∀ z : ℝ, (∃ w : Fin k -> ℝ, (∀ i, 0 ≤ w i) ∧ w ≠ 0 ∧
            ∀ i, (Finset.univ.sum fun j : Fin k => A i j * w j) = z * w i) ->
            z = lam))

def RenewalEquationStatement (c d u : ℕ -> ℝ) : Prop :=
  Bornology.IsBounded (Set.range c) -> Bornology.IsBounded (Set.range d) ->
  (∀ n, 0 ≤ c n ∧ c n ≤ 1 ∧ 0 ≤ d n) ->
  (∀ q : ℕ, (∀ n, 0 < c n -> q ∣ n) -> q = 1) ->
  (∀ n, u n = d n + (Finset.range (n + 1)).sum fun j => c j * u (n - j)) ->
  (∑' n : ℕ, ENNReal.ofReal (c n)) = 1 ->
  (∑' n : ℕ, ENNReal.ofReal (d n)) < (⊤ : ENNReal) ->
    Tendsto u atTop (nhds
      (ENNReal.toReal ((∑' n : ℕ, ENNReal.ofReal (d n)) /
        (∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * c n)))))

abbrev StandardCantorSet : Type := cantorSet

def IsHomeomorphicToCantor (X : Type u) [TopologicalSpace X] : Prop :=
  Nonempty (X ≃ₜ StandardCantorSet)

abbrev FurstenbergFamily (X : Type u) := SetFamily X

def IsFurstenbergFamily {X : Type u} (F : FurstenbergFamily X) : Prop :=
  ∀ ⦃A B : Set X⦄, A ∈ F -> A ⊆ B -> B ∈ F

def ProperFamily {X : Type u} (F : FurstenbergFamily X) : Prop :=
  IsFurstenbergFamily F ∧ (∅ : Set X) ∉ F ∧ Set.univ ∈ F

def generatedFurstenbergFamily {X : Type u} (A : Set (Set X)) : FurstenbergFamily X :=
  {F : Set X | ∃ A₀ ∈ A, A₀ ⊆ F}

def familyDual {X : Type u} (F : FurstenbergFamily X) : FurstenbergFamily X :=
  {A : Set X | Aᶜ ∉ F}

def familyProduct {X : Type u} (F G : FurstenbergFamily X) : FurstenbergFamily X :=
  {A : Set X | ∃ F₀ ∈ F, ∃ G₀ ∈ G, A = F₀ ∩ G₀}

def IsFilterFamily {X : Type u} (F : FurstenbergFamily X) : Prop :=
  ProperFamily F ∧ ∀ A ∈ F, ∀ B ∈ F, A ∩ B ∈ F

def IsFilterDual {X : Type u} (F : FurstenbergFamily X) : Prop :=
  IsFilterFamily (familyDual F)

def HasRamseyProperty {X : Type u} (F : FurstenbergFamily X) : Prop :=
  ∀ A B : Set X, A ∪ B ∈ F -> A ∈ F ∨ B ∈ F

def infiniteSetFamily : FurstenbergFamily ℕ :=
  {A : Set ℕ | A.Infinite}

def cofiniteSetFamily : FurstenbergFamily ℕ :=
  {A : Set ℕ | Aᶜ.Finite}

def natInterval (a n : ℕ) : Finset ℕ :=
  Finset.Ico a (a + n)

def natIntervalDensity (A : Set ℕ) (a n : ℕ) : ℝ :=
  (((natInterval a n).filter fun k => k ∈ A).card : ℝ) / (n : ℝ)

def natInitialDensity (A : Set ℕ) (n : ℕ) : ℝ :=
  natIntervalDensity A 0 n

def lowerBanachDensity (A : Set ℕ) : ℝ :=
  sSup {r : ℝ | ∃ N : ℕ, ∀ a n : ℕ, N ≤ n -> r ≤ natIntervalDensity A a n}

def upperBanachDensity (A : Set ℕ) : ℝ :=
  sInf {r : ℝ | ∃ N : ℕ, ∀ a n : ℕ, N ≤ n -> natIntervalDensity A a n ≤ r}

def lowerAsymptoticDensity (A : Set ℕ) : ℝ :=
  sSup {r : ℝ | ∃ N : ℕ, ∀ n : ℕ, N ≤ n -> r ≤ natInitialDensity A n}

def upperAsymptoticDensity (A : Set ℕ) : ℝ :=
  sInf {r : ℝ | ∃ N : ℕ, ∀ n : ℕ, N ≤ n -> natInitialDensity A n ≤ r}

def intInterval (a : ℤ) (n : ℕ) : Finset ℤ :=
  (Finset.range n).image fun k : ℕ => a + (k : ℤ)

def intIntervalDensity (A : Set ℤ) (a : ℤ) (n : ℕ) : ℝ :=
  (((intInterval a n).filter fun k => k ∈ A).card : ℝ) / (n : ℝ)

def intSymmetricDensity (A : Set ℤ) (n : ℕ) : ℝ :=
  intIntervalDensity A (-(n : ℤ)) (2 * n + 1)

def lowerBanachDensityInt (A : Set ℤ) : ℝ :=
  sSup {r : ℝ | ∃ N : ℕ, ∀ a : ℤ, ∀ n : ℕ, N ≤ n -> r ≤ intIntervalDensity A a n}

def upperBanachDensityInt (A : Set ℤ) : ℝ :=
  sInf {r : ℝ | ∃ N : ℕ, ∀ a : ℤ, ∀ n : ℕ, N ≤ n -> intIntervalDensity A a n ≤ r}

def lowerAsymptoticDensityInt (A : Set ℤ) : ℝ :=
  sSup {r : ℝ | ∃ N : ℕ, ∀ n : ℕ, N ≤ n -> r ≤ intSymmetricDensity A n}

def upperAsymptoticDensityInt (A : Set ℤ) : ℝ :=
  sInf {r : ℝ | ∃ N : ℕ, ∀ n : ℕ, N ≤ n -> intSymmetricDensity A n ≤ r}

def densityOneFamily : FurstenbergFamily ℕ :=
  {A : Set ℕ | lowerAsymptoticDensity A = 1}

def lowerBanachDensityOneFamily : FurstenbergFamily ℕ :=
  {A : Set ℕ | lowerBanachDensity A = 1}

def densityOneFamilyInt : FurstenbergFamily ℤ :=
  {A : Set ℤ | lowerAsymptoticDensityInt A = 1}

def lowerBanachDensityOneFamilyInt : FurstenbergFamily ℤ :=
  {A : Set ℤ | lowerBanachDensityInt A = 1}

end Chapter00
