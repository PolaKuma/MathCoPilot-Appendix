import Chapter07.Section11

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter07

universe u v

namespace Section12

def topologicallyCompletelyPositiveEntropy (S : System.{u}) : Prop :=
  ∀ R : System.{u}, (∃ π : S.X -> R.X, Chapter05.IsFactorMap S R π) ->
    (¬ Subsingleton R.X) -> 0 < topologicalEntropy R

def uniformlyPositiveEntropyOfOrder (S : System.{u}) (n : ℕ) : Prop :=
  2 ≤ n ∧ ∀ cover : OpenCover S.X, cover.sets.ncard = n ->
    IsNontrivialOpenCover cover -> 0 < topologicalCoverEntropyRate S cover

def diagonalSet (X : Type u) (n : ℕ) : Set (Fin n -> X) :=
  {x | ∀ i j, x i = x j}

def IsGDelta {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ U : ℕ -> Set X, (∀ n, IsOpen (U n)) ∧ A = ⋂ n, U n

def isAlmostOneToOneExtension (S : System.{u}) (R : System.{v})
    (π : S.X -> R.X) : Prop :=
  Chapter05.IsFactorMap S R π ∧
    Dense {x : S.X | ∀ y : S.X, π y = π x -> y = x} ∧
    IsGDelta {x : S.X | ∀ y : S.X, π y = π x -> y = x}

def IsTopologicalMeasureModel (S : System.{u}) (μ : MeasureOn S.X)
    (M : MeasurableSystem.{u}) : Prop :=
  ∃ e : S.X ≃ M.X,
    @Measurable S.X M.X (borel S.X) M.measurableSpace e ∧
    @Measurable M.X S.X M.measurableSpace (borel S.X) e.symm ∧
    (∀ x, e (S.T x) = M.T (e x)) ∧
    ∀ B : Set M.X, @MeasurableSet M.X M.measurableSpace B ->
      μ.measure (e ⁻¹' B) = M.μ B

def IsMaximalEquicontinuousFactor (S : System.{u}) (R : System.{v})
    (π : S.X -> R.X) : Prop :=
  Chapter05.IsFactorMap S R π ∧
    (∃ _ : PseudoMetricSpace R.X, Chapter05.IsEquicontinuous R) ∧
    ∀ Z : System.{v}, (∃ _ : PseudoMetricSpace Z.X, Chapter05.IsEquicontinuous Z) ->
      ∀ ρ : S.X -> Z.X, Chapter05.IsFactorMap S Z ρ ->
        ∃ σ : R.X -> Z.X, Chapter05.IsFactorMap R Z σ ∧ ρ = σ ∘ π

/-- Source: Definition 7.12.1. -/
def topologicalCpeAndUpe (S : System.{u}) : Prop :=
  topologicallyCompletelyPositiveEntropy S ∧ hasUniformlyPositiveEntropy S

/-- Blanchard's implications stated immediately after Definition 7.12.1. -/
theorem upe_isWeakMixing_and_cpeHasFullSupportMeasure
    (S : System.{u}) (hS : Chapter05.IsTopologicalSystem S) :
    (hasUniformlyPositiveEntropy S -> Chapter05.IsWeakMixing S) ∧
    (topologicallyCompletelyPositiveEntropy S ->
      ∃ μ : MeasureOn S.X, Chapter06.IsInvariantMeasure S μ ∧
        Chapter06.support μ = Set.univ) := by
  sorry

/-- Source: Definition 7.12.2. -/
def uniformlyPositiveEntropyOfOrderDefinition (S : System.{u}) (n : ℕ) : Prop :=
  uniformlyPositiveEntropyOfOrder S n

def topologicalKSystemDefinition (S : System.{u}) : Prop :=
  ∀ n : ℕ, 2 ≤ n -> uniformlyPositiveEntropyOfOrder S n

/-- Source: Definition 7.12.3. -/
def topologicalEntropyTupleSet (S : System.{u}) (n : ℕ) : Set (Fin n -> S.X) :=
  {x | topologicalEntropyTuple S n x}

/-- The four basic properties following Definition 7.12.3. -/
theorem topologicalEntropyTuple_basicProperties
    (S : System.{u}) (n : ℕ) (hn : 2 ≤ n)
    (hS : Chapter05.IsTopologicalSystem S) :
    (∀ cover : OpenCover S.X, cover.sets.ncard = n ->
      0 < topologicalCoverEntropyRate S cover ->
        ∃ U : Fin n -> Set S.X, Set.range U = cover.sets ∧
          ∃ x : Fin n -> S.X, (∀ i, x i ∉ U i) ∧
            x ∈ topologicalEntropyTupleSet S n) ∧
    IsClosed (topologicalEntropyTupleSet S n ∪ diagonalSet S.X n) ∧
    (∀ R : System.{u}, ∀ π : S.X -> R.X, Chapter05.IsFactorMap S R π ->
      Set.MapsTo (fun x i => π (x i))
        (topologicalEntropyTupleSet S n ∪ diagonalSet S.X n)
        (topologicalEntropyTupleSet R n ∪ diagonalSet R.X n)) ∧
    (∀ A : Set S.X, ∀ hA : Set.MapsTo S.T A A,
      ∀ x : Fin n -> (restrictedSystem S A hA).X,
        topologicalEntropyTuple (restrictedSystem S A hA) n x ->
          topologicalEntropyTuple S n (fun i => (x i).1)) := by
  sorry

theorem entropyTuples_characterizePositiveEntropyAndUpe
    (S : System.{u}) (n : ℕ) (hn : 2 ≤ n)
    (hS : Chapter05.IsTopologicalSystem S) :
    (0 < topologicalEntropy S ↔ (topologicalEntropyTupleSet S 2).Nonempty) ∧
    (uniformlyPositiveEntropyOfOrder S n ↔
      ∀ x : Fin n -> S.X, x ∉ diagonalSet S.X n ->
        x ∈ topologicalEntropyTupleSet S n) := by
  sorry

/-- Source: Definition 7.12.4. -/
def topologicalPinskerFactorDefinition (S : System.{u}) : Prop :=
  topologicalPinskerFactor S

def IsClosedInvariantEquivalenceRelation (S : System.{u})
    (R : Set (S.X × S.X)) : Prop :=
  IsClosed R ∧ Equivalence fun x y => (x, y) ∈ R ∧
    ∀ x y, (x, y) ∈ R -> (S.T x, S.T y) ∈ R

/-- Blanchard--Lacroix characterization following Definition 7.12.4. -/
theorem entropyPairGeneratedRelation_givesTopologicalPinskerFactor
    (S : System.{u}) (hS : Chapter05.IsTopologicalSystem S) :
    ∃ R : Set (S.X × S.X), IsClosedInvariantEquivalenceRelation S R ∧
      (∀ x, x ∈ topologicalEntropyTupleSet S 2 -> (x 0, x 1) ∈ R) ∧
      ∀ Q : Set (S.X × S.X), IsClosedInvariantEquivalenceRelation S Q ->
        (∀ x, x ∈ topologicalEntropyTupleSet S 2 -> (x 0, x 1) ∈ Q) -> R ⊆ Q := by
  sorry

/-- Source: Definition 7.12.5. -/
def measureEntropyTupleSet (S : System.{u}) (μ : MeasureOn S.X) (n : ℕ) :
    Set (Fin n -> S.X) := {x | measureEntropyTuple S μ n x}

/-- The Borel measurable system associated to a topological system and a Borel
measure on it.  This supplies the measurable system on which the Pinsker
sigma-algebra and conditional probabilities in Theorem 7.12.6 are evaluated. -/
def borelMeasureSystem (S : System.{u}) (μ : MeasureOn S.X) : MeasurableSystem.{u} where
  X := S.X
  measurableSpace := borel S.X
  μ := μ.toMeasure
  T := S.T

structure PinskerSelfJoiningData (S : System.{u}) (μ : MeasureOn S.X) (n : ℕ) where
  joining : MeasureOn (Fin n -> S.X)
  probability : Chapter06.IsProbabilityBorelMeasure joining
  invariant : Chapter06.pushForwardMeasure (fun x i => S.T (x i)) joining = joining
  marginals : ∀ i : Fin n,
    Chapter06.pushForwardMeasure (fun x => x i) joining = μ
  rectangles : ∀ A : Fin n -> Set S.X,
    (∀ i, @MeasurableSet S.X (borel S.X) (A i)) ->
    joining.measure {x | ∀ i, x i ∈ A i} =
      ENNReal.ofReal
        (∫ x, ∏ i,
          conditionalProbability (borelMeasureSystem S μ) (A i)
            (pinskerSigmaAlgebra (borelMeasureSystem S μ)) x ∂μ.toMeasure)

/-- Source: Theorem 7.12.6, including its two stated consequences. -/
theorem measureEntropyTuples_areSupportOfPinskerSelfJoining
    (S : System.{u}) (μ : MeasureOn S.X) (n : ℕ) (hn : 2 ≤ n)
    (hS : Chapter05.IsTopologicalSystem S)
    (hμ : Chapter06.IsInvariantMeasure S μ) :
    ∃ D : PinskerSelfJoiningData S μ n,
      measureEntropyTupleSet S μ n =
        Chapter06.support D.joining \ diagonalSet S.X n ∧
      (entropyMap S μ = 0 ↔ measureEntropyTupleSet S μ 2 = ∅) ∧
      IsClosed (measureEntropyTupleSet S μ n ∪ diagonalSet S.X n) := by
  sorry

structure FiniteBorelCover (S : System.{u}) where
  sets : Finset (Set S.X)
  measurable_sets : ∀ A ∈ sets, @MeasurableSet S.X (borel S.X) A
  covers_univ : ⋃₀ (sets : Set (Set S.X)) = Set.univ

def openCoverAsSetCover {S : System.{u}} (cover : OpenCover S.X) : SetCover S.X where
  sets := cover.sets
  covers_univ := cover.covers_univ

def finiteBorelCoverAsSetCover {S : System.{u}}
    (cover : FiniteBorelCover S) : SetCover S.X where
  sets := cover.sets
  covers_univ := cover.covers_univ

def AlmostEveryForMeasureOn {S : System.{u}} (μ : MeasureOn S.X)
    (P : S.X -> Prop) : Prop :=
  ∃ N : Set S.X, μ.measure N = 0 ∧ ∀ x ∉ N, P x

def borelPartitionRefinesCover (S : System.{u})
    (α : FiniteBorelPartition S) (cover : Set (Set S.X)) : Prop :=
  ∀ A ∈ α.atoms, ∃ U ∈ cover, A ⊆ U

def upperMeasureCoverEntropy (S : System.{u}) (μ : MeasureOn S.X)
    (cover : SetCover S.X) : EReal :=
  sInf {r : EReal | ∃ α : FiniteBorelPartition S,
    borelPartitionRefinesCover S α cover.sets ∧
      r = (borelPartitionEntropyRate S μ α : EReal)}

def lowerMeasureCoverEntropy (S : System.{u}) (μ : MeasureOn S.X)
    (cover : SetCover S.X) : EReal :=
  limsup (fun n : ℕ => sInf {r : EReal | ∃ α : FiniteBorelPartition S,
    borelPartitionRefinesCover S α
      (setCoverIterateJoin S.T cover (n + 1)).sets ∧
      r = (borelPartitionEntropy S μ α : EReal) / (n + 1 : EReal)}) atTop

/-- Source: Theorem 7.12.7. -/
theorem localVariationalPrinciple_measureExistence
    (S : System.{u}) [Nonempty S.X] (cover : OpenCover S.X)
    (hS : Chapter05.IsTopologicalSystem S) :
    ∃ μ : MeasureOn S.X, Chapter06.IsInvariantMeasure S μ ∧
      topologicalCoverEntropyRate S cover ≤
        upperMeasureCoverEntropy S μ (openCoverAsSetCover cover) := by
  sorry

/-- Source: Theorem 7.12.8. -/
theorem localVariationalPrinciple
    (S : System.{u}) [Nonempty S.X] (cover : OpenCover S.X)
    (hS : Chapter05.IsTopologicalSystem S) :
    (∀ μ : MeasureOn S.X, Chapter06.IsInvariantMeasure S μ ->
      upperMeasureCoverEntropy S μ (openCoverAsSetCover cover) =
        lowerMeasureCoverEntropy S μ (openCoverAsSetCover cover)) ∧
    (∃ μ : MeasureOn S.X, Chapter06.IsInvariantMeasure S μ ∧
      upperMeasureCoverEntropy S μ (openCoverAsSetCover cover) =
        topologicalCoverEntropyRate S cover) ∧
    (∃ μ : MeasureOn S.X, Chapter06.IsInvariantMeasure S μ ∧
      lowerMeasureCoverEntropy S μ (openCoverAsSetCover cover) =
        topologicalCoverEntropyRate S cover) := by
  sorry

/-- Source: Theorem 7.12.9. -/
theorem entropyTupleVariationalPrinciple
    (S : System.{u}) (hS : Chapter05.IsTopologicalSystem S) :
    (∀ μ : MeasureOn S.X, Chapter06.IsInvariantMeasure S μ -> ∀ n : ℕ, 2 ≤ n ->
      measureEntropyTupleSet S μ n ⊆ topologicalEntropyTupleSet S n) ∧
    (∀ n : ℕ, 2 ≤ n -> ∃ μ : MeasureOn S.X,
      Chapter06.IsInvariantMeasure S μ ∧
        topologicalEntropyTupleSet S n = measureEntropyTupleSet S μ n) := by
  sorry

/-- Source: Theorem 7.12.10 and its two consequences stated in the text. -/
theorem borelCoverEntropy_ergodicDecomposition
    (S : System.{u}) (μ : MeasureOn S.X) (cover : FiniteBorelCover S)
    (D : EntropyErgodicDecompositionData S μ)
    (hμ : Chapter06.IsInvariantMeasure S μ) :
    upperMeasureCoverEntropy S μ (finiteBorelCoverAsSetCover cover) =
      D.averageEReal (fun ν =>
        upperMeasureCoverEntropy S ν (finiteBorelCoverAsSetCover cover)) ∧
    (∃ ν : MeasureOn S.X, Chapter06.IsErgodicMeasure S ν ∧
      upperMeasureCoverEntropy S ν (finiteBorelCoverAsSetCover cover) =
        sSup {r : EReal | ∃ m : MeasureOn S.X,
          Chapter06.IsInvariantMeasure S m ∧
            r = upperMeasureCoverEntropy S m (finiteBorelCoverAsSetCover cover)}) := by
  sorry

/-- A point-indexed realization of the ergodic decomposition of `μ`: almost
every component is ergodic and continuous observables satisfy the barycenter
identity. -/
def IsPointwiseErgodicDecomposition
    (S : System.{u}) (μ : MeasureOn S.X)
    (components : S.X -> MeasureOn S.X) : Prop :=
  Chapter06.IsInvariantMeasure S μ ∧
  (∀ᵐ x ∂μ.toMeasure, Chapter06.IsErgodicMeasure S (components x)) ∧
  ∀ f : S.X -> ℂ, Continuous f ->
    @Measurable S.X ℂ (borel S.X) inferInstance
      (fun x => (components x).integral f) ∧
    μ.integral f = μ.integral (fun x => (components x).integral f)

/-- Source: Theorem 7.12.11. -/
theorem entropyTuplesAlongErgodicComponents
    (S : System.{u}) (μ : MeasureOn S.X) (n : ℕ) (hn : 2 ≤ n)
    (components : S.X -> MeasureOn S.X)
    (hS : Chapter05.IsTopologicalSystem S)
    (hμ : Chapter06.IsInvariantMeasure S μ)
    (hD : IsPointwiseErgodicDecomposition S μ components) :
    AlmostEveryForMeasureOn μ (fun x =>
      measureEntropyTupleSet S (components x) n ⊆ measureEntropyTupleSet S μ n) ∧
    (∀ tuple ∈ measureEntropyTupleSet S μ n, ∀ V : Set (Fin n -> S.X),
      IsOpen V -> tuple ∈ V ->
        0 < μ.measure {x | (V ∩ measureEntropyTupleSet S (components x) n).Nonempty}) ∧
    ∃ X₀ : Set S.X, @MeasurableSet S.X (borel S.X) X₀ ∧ μ.measure X₀ = 1 ∧
      (⋃ x ∈ X₀, measureEntropyTupleSet S (components x) n) \ diagonalSet S.X n =
        measureEntropyTupleSet S μ n := by
  sorry

/-- Source: Theorem 7.12.12. -/
theorem positiveEntropy_iffWeakHorseshoe
    (S : System.{u}) (hS : Chapter05.IsTopologicalSystem S) :
    0 < topologicalEntropy S ↔ hasWeakHorseshoe S := by
  sorry

def isIPSet (A : Set ℕ) : Prop :=
  ∃ p : ℕ -> ℕ, StrictMono p ∧
    ∀ F : Finset ℕ, F.Nonempty -> F.sum p ∈ A

def IsNontrivialFinitePartition (M : MeasurableSystem.{u})
    (α : FiniteMeasurablePartition M) : Prop :=
  ∀ A ∈ α.atoms, M.μ A ≠ 0 ∧ M.μ A ≠ 1

/-- Source: Theorem 7.12.13. -/
theorem measureMildMixing_sequenceEntropyCharacterization
    (M : MeasurableSystem.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter02.IsMildMixing M ↔
      (∀ α : FiniteMeasurablePartition M, α.atoms.card = 2 ->
        IsNontrivialFinitePartition M α -> ∀ F : Set ℕ, isIPSet F ->
          ∃ A ⊆ F, A.Infinite ∧ 0 < sequenceMeasureEntropy M A α) ∧
      (∀ α : FiniteMeasurablePartition M, IsNontrivialFinitePartition M α ->
        ∀ F : Set ℕ, isIPSet F ->
          ∃ A ⊆ F, A.Infinite ∧ 0 < sequenceMeasureEntropy M A α) := by
  sorry

/-- Source: Theorem 7.12.14. -/
theorem topologicalMildMixing_sequenceEntropyCharacterization
    (S : System.{u}) (hS : Chapter05.IsTopologicalSystem S) :
    Chapter05.IsMildMixing S ↔
      (∀ cover : OpenCover S.X, cover.sets.ncard = 2 -> IsNontrivialOpenCover cover ->
        ∀ F : Set ℕ, isIPSet F -> ∃ A ⊆ F, A.Infinite ∧
          0 < sequenceTopologicalEntropy S A cover) ∧
      (∀ cover : OpenCover S.X, IsNontrivialOpenCover cover ->
        ∀ F : Set ℕ, isIPSet F -> ∃ A ⊆ F, A.Infinite ∧
          0 < sequenceTopologicalEntropy S A cover) := by
  sorry

/-- Source: Theorem 7.12.15 (Kushnirenko). -/
theorem kushnirenkoNullTheorem
    (M : MeasurableSystem.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    hasDiscreteSpectrum M ↔ IsNullMeasureSystem M := by
  sorry

/-- Source: Theorem 7.12.16. -/
theorem minimalNullSystems_areAlmostOneToOneOverMaximalEquicontinuousFactor
    (S : System.{u}) (hS : Chapter05.IsTopologicalSystem S) :
    Chapter05.IsMinimalSystem S -> isNullSystem S ->
      ∃ R : System.{u}, ∃ π : S.X -> R.X,
        IsMaximalEquicontinuousFactor S R π ∧ isAlmostOneToOneExtension S R π ∧
        Chapter06.IsUniquelyErgodic S ∧
        ∀ μ : MeasureOn S.X, Chapter06.IsInvariantMeasure S μ ->
          ∃ M : MeasurableSystem.{u}, IsTopologicalMeasureModel S μ M ∧
            hasDiscreteSpectrum M := by
  sorry

def maximalPatternMeasureEntropy (M : MeasurableSystem.{u}) : EReal :=
  sSup {r : EReal | ∃ A : Set ℕ, A.Infinite ∧
    r = sequenceMeasureEntropyOfSystem M A}

/-- Source: Theorem 7.12.17. -/
theorem maximalPatternEntropy_sequenceEntropyCharacterization
    (S : System.{u}) (M : MeasurableSystem.{v})
    (hS : Chapter05.IsTopologicalSystem S)
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    maximalPatternEntropy S =
      sSup {r : EReal | ∃ A : Set ℕ, A.Infinite ∧
        r = sequenceTopologicalEntropyOfSystem S A} ∧
    maximalPatternMeasureEntropy M =
      sSup {r : EReal | ∃ A : Set ℕ, A.Infinite ∧
        r = sequenceMeasureEntropyOfSystem M A} ∧
    (isNullSystem S ↔ maximalPatternEntropy S = 0) ∧
    (hasDiscreteSpectrum M ↔ maximalPatternMeasureEntropy M = 0) := by
  sorry

/-- Source: Theorem 7.12.18. -/
theorem maximalPatternEntropy_hasDiscreteValues
    (S : System.{u}) (M : MeasurableSystem.{v})
    (hS : Chapter05.IsTopologicalSystem S) :
    maximalPatternEntropy S ∈ Set.range (fun k : ℕ => (Real.log k : EReal)) ∪ {⊤} ∧
    (Chapter02.IsErgodic M ->
      maximalPatternMeasureEntropy M ∈
        Set.range (fun k : ℕ => (Real.log k : EReal)) ∪ {⊤}) := by
  sorry

def maximalPatternEntropySpectrum (X : Type u) [TopologicalSpace X] : Set EReal :=
  {h | ∃ T : X -> X, Continuous T ∧ h = maximalPatternEntropy
    { X := X, topology := inferInstance, T := T }}

/-- Source: Theorem 7.12.19. -/
theorem prescribedMaximalPatternEntropySpectrum
    (A : Set EReal)
    (hA : {0} ⊆ A ∧ A ⊆ Set.range (fun k : ℕ => (Real.log k : EReal)) ∪ {⊤}) :
    ∃ X : Set (Fin 3 -> ℝ), IsCompact X ∧
      maximalPatternEntropySpectrum X = A := by
  sorry

end Section12
end Chapter07
