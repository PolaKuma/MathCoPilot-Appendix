import Chapter05.Section07

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter06

universe u v w

abbrev System := Chapter05.System
abbrev MeasurableSystem := Chapter01.MeasurePreservingSystemData

/-!
`BorelMeasureData X` is the ambient real cone of Borel measures used in the
book.  The probability measures `M(X)` are selected by
`IsProbabilityBorelMeasure`; keeping the ambient cone is necessary for the
convex structure while ensuring that set evaluation and integration come from
one and the same genuine Mathlib measure.
-/
structure BorelMeasureData (X : Type u) [TopologicalSpace X] where
  toMeasure : @MeasureTheory.Measure X (borel X)

abbrev BorelProbabilityMeasureData := BorelMeasureData

abbrev MeasureOn (X : Type u) [TopologicalSpace X] := BorelMeasureData X

namespace BorelMeasureData

def measure {X : Type u} [TopologicalSpace X] (μ : MeasureOn X) : Set X → ENNReal :=
  μ.toMeasure

def integral {X : Type u} [TopologicalSpace X] (μ : MeasureOn X) (f : X → ℂ) : ℂ :=
  @MeasureTheory.integral X ℂ _ _ (borel X) μ.toMeasure f

def realIntegral {X : Type u} [TopologicalSpace X] (μ : MeasureOn X) (f : X → ℝ) : ℝ :=
  @MeasureTheory.integral X ℝ _ _ (borel X) μ.toMeasure f

def eRealLIntegral {X : Type u} [TopologicalSpace X]
    (μ : MeasureOn X) (f : X → EReal) : EReal :=
  ((@MeasureTheory.lintegral X (borel X) μ.toMeasure
    (fun x => (f x).toENNReal) : ENNReal) : EReal)

end BorelMeasureData

instance measureOnZero (X : Type u) [TopologicalSpace X] : Zero (MeasureOn X) where
  zero := ⟨0⟩

instance measureOnAdd (X : Type u) [TopologicalSpace X] : Add (MeasureOn X) where
  add μ ν := ⟨μ.toMeasure + ν.toMeasure⟩

instance measureOnSMul (X : Type u) [TopologicalSpace X] : SMul ℝ (MeasureOn X) where
  smul a μ := ⟨ENNReal.ofReal a • μ.toMeasure⟩

def weakStarTopology (X : Type u) [TopologicalSpace X] : TopologicalSpace (MeasureOn X) :=
  TopologicalSpace.induced
    (fun μ : MeasureOn X => fun f : C(X, ℂ) => μ.integral f)
    inferInstance

instance measureOnTopologicalSpace (X : Type u) [TopologicalSpace X] :
    TopologicalSpace (MeasureOn X) :=
  weakStarTopology X

def IsProbabilityBorelMeasure {X : Type u} [TopologicalSpace X] (μ : MeasureOn X) : Prop :=
  @MeasureTheory.IsProbabilityMeasure X (borel X) μ.toMeasure

def IsRegularMeasure {X : Type u} [TopologicalSpace X] (μ : MeasureOn X) : Prop :=
  ∀ B : Set X, @MeasurableSet X (borel X) B → ∀ ε : ℝ, 0 < ε -> ∃ U C : Set X,
    IsOpen U ∧ IsClosed C ∧ C ⊆ B ∧ B ⊆ U ∧ μ.measure (U \ C) < ENNReal.ofReal ε

def innerRegularValue {X : Type u} [TopologicalSpace X] (μ : MeasureOn X) (B : Set X) : ENNReal :=
  sSup {r : ENNReal | ∃ C : Set X, IsClosed C ∧ C ⊆ B ∧ r = μ.measure C}

def outerRegularValue {X : Type u} [TopologicalSpace X] (μ : MeasureOn X) (B : Set X) : ENNReal :=
  sInf {r : ENNReal | ∃ U : Set X, IsOpen U ∧ B ⊆ U ∧ r = μ.measure U}

def MeasuresAgreeOnContinuousFunctions {X : Type u} [TopologicalSpace X]
    (μ ν : MeasureOn X) : Prop :=
  ∀ f : X -> ℂ, Continuous f -> μ.integral f = ν.integral f

structure ContinuousLinearFunctionalData (X : Type u) [TopologicalSpace X] where
  eval : C(X, ℂ) -> ℂ

def IsPositiveNormalizedContinuousLinearFunctional
    {X : Type u} [TopologicalSpace X] (F : ContinuousLinearFunctionalData X) : Prop :=
  (∀ f g : C(X, ℂ), F.eval (f + g) = F.eval f + F.eval g) ∧
    (∀ c : ℂ, ∀ f : C(X, ℂ), F.eval (c • f) = c * F.eval f) ∧
    Continuous F.eval ∧
    (∀ f : C(X, ℂ), (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ->
      0 ≤ (F.eval f).re ∧ (F.eval f).im = 0) ∧
    F.eval (1 : C(X, ℂ)) = 1

instance continuousLinearFunctionalZero (X : Type u) [TopologicalSpace X] :
    Zero (ContinuousLinearFunctionalData X) where
  zero := { eval := fun _ => 0 }

instance continuousLinearFunctionalAdd (X : Type u) [TopologicalSpace X] :
    Add (ContinuousLinearFunctionalData X) where
  add F G := { eval := fun f => F.eval f + G.eval f }

instance continuousLinearFunctionalSMul (X : Type u) [TopologicalSpace X] :
    SMul ℝ (ContinuousLinearFunctionalData X) where
  smul a F := { eval := fun f => (a : ℂ) * F.eval f }

def rieszFunctional {X : Type u} [TopologicalSpace X] (μ : MeasureOn X) :
    ContinuousLinearFunctionalData X where
  eval := fun f => μ.integral f

def IsRieszCorrespondence {X : Type u} [TopologicalSpace X] : Prop :=
  (∀ μ : MeasureOn X, IsProbabilityBorelMeasure μ ->
    IsPositiveNormalizedContinuousLinearFunctional (rieszFunctional μ)) ∧
  (∀ μ ν : MeasureOn X, IsProbabilityBorelMeasure μ -> IsProbabilityBorelMeasure ν ->
    rieszFunctional μ = rieszFunctional ν -> μ = ν) ∧
  (∀ F : ContinuousLinearFunctionalData X,
    IsPositiveNormalizedContinuousLinearFunctional F ->
      ∃ μ : MeasureOn X, IsProbabilityBorelMeasure μ ∧ rieszFunctional μ = F) ∧
  ∀ μ ν : MeasureOn X, IsProbabilityBorelMeasure μ -> IsProbabilityBorelMeasure ν ->
    ∀ a : ℝ, 0 ≤ a -> a ≤ 1 ->
      rieszFunctional (a • μ + (1 - a) • ν) =
        a • rieszFunctional μ + (1 - a) • rieszFunctional ν

def IsAffineMap {A : Type u} {B : Type v} [Add A] [SMul ℝ A]
    [Add B] [SMul ℝ B] (φ : A -> B) : Prop :=
  ∀ x y : A, ∀ a : ℝ, 0 ≤ a -> a ≤ 1 ->
    φ (a • x + (1 - a) • y) = a • φ x + (1 - a) • φ y

def IsWeakStarTopologyForMeasures {X : Type u} [TopologicalSpace X]
    (τ : TopologicalSpace (MeasureOn X)) : Prop :=
  τ = weakStarTopology X

def weakStarConverges {X : Type u} [TopologicalSpace X]
    (μn : ℕ -> MeasureOn X) (μ : MeasureOn X) : Prop :=
  ∀ f : X -> ℂ, Continuous f -> Tendsto (fun n : ℕ => (μn n).integral f) atTop (nhds (μ.integral f))

def weakStarNeighborhood {X : Type u} [TopologicalSpace X]
    (μ : MeasureOn X) (f : Finset (X -> ℂ)) (ε : ℝ) : Set (MeasureOn X) :=
  {ν : MeasureOn X | ∀ g ∈ f, ‖μ.integral g - ν.integral g‖ < ε}

def CompatibleMeasureMetric {X : Type u} [TopologicalSpace X]
    (_P : MeasureOn X -> MeasureOn X -> ℝ) : Prop :=
  (∀ μ ν : MeasureOn X, IsProbabilityBorelMeasure μ -> IsProbabilityBorelMeasure ν ->
    0 ≤ _P μ ν ∧ (_P μ ν = 0 ↔ μ = ν) ∧ _P μ ν = _P ν μ) ∧
  (∀ μ ν ρ : MeasureOn X,
    IsProbabilityBorelMeasure μ -> IsProbabilityBorelMeasure ν ->
    IsProbabilityBorelMeasure ρ -> _P μ ρ ≤ _P μ ν + _P ν ρ) ∧
  ∀ μn : ℕ -> MeasureOn X, ∀ μ : MeasureOn X,
    (∀ n, IsProbabilityBorelMeasure (μn n)) -> IsProbabilityBorelMeasure μ ->
      (weakStarConverges μn μ ↔
        Tendsto (fun n => _P (μn n) μ) atTop (nhds 0))

def diracMeasure {X : Type u} [TopologicalSpace X] (x : X) : MeasureOn X :=
  ⟨@MeasureTheory.Measure.dirac X (borel X) x⟩

def diracEmbedding {X : Type u} [TopologicalSpace X] : X -> MeasureOn X :=
  diracMeasure

def IsTopologicalEmbedding {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X -> Y) : Prop :=
  TopologicalSpace.induced φ (inferInstance : TopologicalSpace Y) =
      (inferInstance : TopologicalSpace X) ∧
    Function.Injective φ

def PortmanteauEquivalent {X : Type u} [TopologicalSpace X]
    (μn : ℕ -> MeasureOn X) (μ : MeasureOn X) : Prop :=
  weakStarConverges μn μ ↔
    ((∀ E : Set X, IsClosed E -> Filter.limsup (fun n : ℕ => μn n |>.measure E) atTop ≤ μ.measure E) ∧
      (∀ U : Set X, IsOpen U -> μ.measure U ≤ Filter.liminf (fun n : ℕ => μn n |>.measure U) atTop) ∧
        ∀ A : Set X, @MeasurableSet X (borel X) A → μ.measure (frontier A) = 0 ->
          Tendsto (fun n : ℕ => μn n |>.measure A) atTop (nhds (μ.measure A)))

def pushForwardMeasure {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X -> Y) (μ : MeasureOn X) : MeasureOn Y :=
  ⟨@MeasureTheory.Measure.map X Y (borel X) (borel Y) φ μ.toMeasure⟩

def IsInvariantMeasure (S : System.{u}) (μ : MeasureOn S.X) : Prop :=
  Chapter05.IsTopologicalSystem S ∧ IsProbabilityBorelMeasure μ ∧
    pushForwardMeasure S.T μ = μ

def invariantMeasures (S : System.{u}) : Set (MeasureOn S.X) :=
  {μ : MeasureOn S.X | IsInvariantMeasure S μ}

def orbitAverageMeasure (S : System.{u}) (x : S.X) (n : ℕ) : MeasureOn S.X :=
  if n = 0 then 0 else
    ⟨(n : ENNReal)⁻¹ • (Finset.range n).sum
      (fun i => @MeasureTheory.Measure.dirac S.X (borel S.X) ((S.T^[i]) x))⟩

def averagedPushForwardMeasure (S : System.{u}) (σ : ℕ -> MeasureOn S.X) (n : ℕ) : MeasureOn S.X :=
  if n = 0 then 0 else
    ⟨(n : ENNReal)⁻¹ • (Finset.range n).sum
      (fun i => (pushForwardMeasure (S.T^[i]) (σ n)).toMeasure)⟩

def IsConvexSet {E : Type u} [Add E] [SMul ℝ E] (K : Set E) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, ∀ a : ℝ, 0 ≤ a -> a ≤ 1 ->
    a • x + (1 - a) • y ∈ K

def IsCompactConvexSet {E : Type u} [TopologicalSpace E] [Add E] [SMul ℝ E]
    (K : Set E) : Prop :=
  IsCompact K ∧ IsConvexSet K

def convexHullSet {E : Type u} [Add E] [SMul ℝ E] (A : Set E) : Set E :=
  ⋂₀ {C : Set E | A ⊆ C ∧ IsConvexSet C}

def IsGDeltaSet {E : Type u} [TopologicalSpace E] (K : Set E) : Prop :=
  ∃ U : ℕ → Set E, (∀ n, IsOpen (U n)) ∧ K = ⋂ n, U n

def IsExtremePoint {E : Type u} [Add E] [SMul ℝ E] (K : Set E) (x : E) : Prop :=
  x ∈ K ∧ ∀ y z : E, y ∈ K -> z ∈ K -> ∀ a : ℝ, 0 < a -> a < 1 ->
    x = a • y + (1 - a) • z -> y = x ∧ z = x

def extremePoints {E : Type u} [Add E] [SMul ℝ E] (K : Set E) : Set E :=
  {x : E | IsExtremePoint K x}

def IsErgodicMeasure (S : System.{u}) (μ : MeasureOn S.X) : Prop :=
  IsInvariantMeasure S μ ∧ ∀ A : Set S.X,
    @MeasurableSet S.X (borel S.X) A ->
      μ.measure (Chapter00.symmDiff (S.T ⁻¹' A) A) = 0 ->
      μ.measure A = 0 ∨ μ.measure A = 1

def ergodicMeasures (S : System.{u}) : Set (MeasureOn S.X) :=
  {μ : MeasureOn S.X | IsErgodicMeasure S μ}

def MutuallySingular {X : Type u} [TopologicalSpace X] (μ ν : MeasureOn X) : Prop :=
  μ.toMeasure.MutuallySingular ν.toMeasure

def AbsolutelyContinuous {X : Type u} [TopologicalSpace X] (μ ν : MeasureOn X) : Prop :=
  μ.toMeasure.AbsolutelyContinuous ν.toMeasure

structure ChoquetMeasureData {E : Type u} [TopologicalSpace E] [Add E] [SMul ℝ E]
    (K : Set E) where
  barycenter : E
  weight : MeasureOn E
  probability : IsProbabilityBorelMeasure weight
  supported_on_extreme_points : weight.measure (extremePoints K)ᶜ = 0
  barycenter_property : ∀ f : E → ℂ, Continuous f ->
    (∀ x y, f (x + y) = f x + f y) ->
    (∀ a : ℝ, ∀ x, f (a • x) = (a : ℂ) * f x) ->
      f barycenter = weight.integral f

def HasChoquetRepresentation {E : Type u} [TopologicalSpace E] [Add E] [SMul ℝ E]
    (K : Set E) (m : E) : Prop :=
  ∃ τ : ChoquetMeasureData K, τ.barycenter = m

structure ErgodicDecompositionData (S : System.{u}) where
  weight : MeasureOn (MeasureOn S.X)
  probability : IsProbabilityBorelMeasure weight
  supported_on_ergodic : weight.measure (ergodicMeasures S)ᶜ = 0

def HasErgodicDecomposition (S : System.{u}) (μ : MeasureOn S.X) : Prop :=
  ∃ D : ErgodicDecompositionData S, ∀ f : S.X -> ℂ, Continuous f ->
    μ.integral f = D.weight.integral (fun ν => ν.integral f)

def factorPushForwardMap (S : System.{u}) (R : System.{v}) (π : S.X -> R.X)
    (μ : MeasureOn S.X) : MeasureOn R.X :=
  pushForwardMeasure π μ

def IsGenericPoint (S : System.{u}) (μ : MeasureOn S.X) (x : S.X) : Prop :=
  IsInvariantMeasure S μ ∧ weakStarConverges (fun n : ℕ => orbitAverageMeasure S x (n + 1)) μ

def genericPointSet (S : System.{u}) (μ : MeasureOn S.X) : Set S.X :=
  {x : S.X | IsGenericPoint S μ x}

def IsBorelSet {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  @MeasurableSet X (borel X) A

def support {X : Type u} [TopologicalSpace X] (μ : MeasureOn X) : Set X :=
  {x : X | ∀ U : Set X, IsOpen U -> x ∈ U -> 0 < μ.measure U}

def supportSystem (S : System.{u}) (μ : MeasureOn S.X)
    (hforward : S.T '' support μ ⊆ support μ) : System.{u} where
  X := {x : S.X // x ∈ support μ}
  topology := inferInstance
  T := fun x => ⟨S.T x, hforward ⟨x, x.property, rfl⟩⟩

def IsUniquelyErgodic (S : System.{u}) : Prop :=
  ∃ μ : MeasureOn S.X, invariantMeasures S = {μ}

def uniqueInvariantMeasure (S : System.{u}) : Prop :=
  ∃ μ : MeasureOn S.X, invariantMeasures S = {μ}

def BirkhoffAveragesConvergeUniformlyToConstant (S : System.{u}) : Prop :=
  ∀ f : S.X -> ℂ, Continuous f -> ∃ c : ℂ,
    TendstoUniformly (fun (n : ℕ) (x : S.X) =>
      if n = 0 then 0 else (n : ℂ)⁻¹ * (Finset.range n).sum (fun i => f ((S.T^[i]) x)))
      (fun _ => c) atTop

def BirkhoffAveragesConvergePointwiseToConstant (S : System.{u}) : Prop :=
  ∀ f : S.X -> ℂ, Continuous f -> ∃ c : ℂ, ∀ x : S.X,
    Tendsto (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹ * (Finset.range n).sum (fun i => f ((S.T^[i]) x))) atTop (nhds c)

def birkhoffAverage (S : System.{u}) (f : S.X → ℂ) (n : ℕ) (x : S.X) : ℂ :=
  if n = 0 then 0 else
    (n : ℂ)⁻¹ * (Finset.range n).sum (fun i => f ((S.T^[i]) x))

def BirkhoffAverageFamilyEquicontinuous (S : System.{u}) (f : S.X → ℂ) : Prop :=
  ∀ x : S.X, ∀ ε : ℝ, 0 < ε -> ∃ U : Set S.X,
    IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, ∀ n : ℕ, 0 < n ->
      ‖birkhoffAverage S f n y - birkhoffAverage S f n x‖ < ε

def EveryOrbitEquidistributesTo (S : System.{u}) (μ : MeasureOn S.X) : Prop :=
  ∀ x : S.X, weakStarConverges (fun n : ℕ => orbitAverageMeasure S x (n + 1)) μ

def IsStrictlyErgodic (S : System.{u}) : Prop :=
  Chapter05.IsMinimalSystem S ∧ IsUniquelyErgodic S

def finiteCyclicRotationSystem (n : ℕ) (hn : 0 < n) : System.{0} where
  X := Fin n
  topology := inferInstance
  T := fun i => ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

def circleRotationTopologicalSystem (α : ℝ) : System.{0} where
  X := AddCircle (1 : ℝ)
  topology := inferInstance
  T := fun x => x + (α : AddCircle (1 : ℝ))

def binaryOdometerTopologicalSystem : System.{0} where
  X := Chapter01.BinarySequence
  topology := inferInstance
  T := Chapter01.addingOne

def torusRotationTopologicalSystem (k : ℕ) (θ : Fin k → ℝ) : System.{0} where
  X := Chapter01.Torus k
  topology := inferInstance
  T := Chapter01.torusRotation k θ

def IsTotallyIrrationalRotationVector {k : ℕ} (θ : Fin k → ℝ) : Prop :=
  ∀ z : Fin k → ℤ, z ≠ 0 ->
    ¬ ∃ m : ℤ, ∑ i, (z i : ℝ) * θ i = (m : ℝ)

def triangularTorusTopologicalSystem (k : ℕ) (α : ℝ) : System.{0} where
  X := Chapter01.Torus k
  topology := inferInstance
  T := Chapter01.triangularTorusMap k α

def circleHomeomorphismSystem
    (T : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) : System.{0} where
  X := AddCircle (1 : ℝ)
  topology := inferInstance
  T := T

def IsPointOrClosedArc (A : Set (AddCircle (1 : ℝ))) : Prop :=
  A.Subsingleton ∨ (IsClosed A ∧ IsConnected A ∧ A ≠ Set.univ)

def unitIntervalGridPoint (m : ℕ) (k : Fin m) : Set.Icc (0 : ℝ) 1 :=
  ⟨k.val / (m : ℝ), by
    have hm : 0 < (m : ℝ) := by
      exact_mod_cast Nat.zero_lt_of_lt k.isLt
    constructor
    · exact div_nonneg (by positivity) (le_of_lt hm)
    · exact (div_le_one hm).2 (by exact_mod_cast Nat.le_of_lt k.isLt)⟩

def IsEquidistributedInUnitInterval (x : ℕ -> Set.Icc (0 : ℝ) 1) : Prop :=
  ∀ f : Set.Icc (0 : ℝ) 1 -> ℂ, Continuous f -> ∃ I : ℂ,
    Tendsto (fun n : ℕ => if n = 0 then 0 else
      (n : ℂ)⁻¹ * (Finset.range n).sum (fun k => f (x k))) atTop (nhds I) ∧
    Tendsto (fun m : ℕ => if m = 0 then 0 else
      (m : ℂ)⁻¹ * Finset.univ.sum (fun k : Fin m => f (unitIntervalGridPoint m k)))
      atTop (nhds I)

def WeylCriterionSequence (x : ℕ -> ℝ) : Prop :=
  ∀ k : ℤ, k ≠ 0 -> Tendsto (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹ * (Finset.range n).sum (fun j => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x j : ℂ)))) atTop (nhds 0)

def IntervalFrequencyCondition (x : ℕ -> ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a -> a < b -> b ≤ 1 ->
    Tendsto (fun n : ℕ => if n = 0 then 0 else ((Finset.range n).filter (fun j => a ≤ x j ∧ x j ≤ b)).card / (n : ℝ)) atTop (nhds (b - a))

def unitIntervalSequence (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Set.Icc (0 : ℝ) 1) :
    ℕ → Set.Icc (0 : ℝ) 1 :=
  fun n => ⟨x n, hx n⟩

def leadingDigitCountPowersOfTwo (k n : ℕ) : ℕ :=
  ((Finset.range n).filter fun i =>
    ∃ r : ℕ, k * 10 ^ r ≤ 2 ^ i ∧ 2 ^ i < (k + 1) * 10 ^ r).card

def IsEquidistributedForMeasure (X : Type u) [TopologicalSpace X]
    (μ : MeasureOn X) (x : ℕ -> X) : Prop :=
  weakStarConverges (fun n : ℕ =>
    if n = 0 then 0 else
      ⟨(n : ENNReal)⁻¹ • (Finset.range n).sum
        (fun j => @MeasureTheory.Measure.dirac X (borel X) (x j))⟩) μ

def IsSkewProductUniquelyErgodicCriterion : Prop :=
  ∀ Y : System.{u}, IsUniquelyErgodic Y ->
    ∀ G : Type u, ∀ _ : CommGroup G, ∀ _ : TopologicalSpace G,
    ∀ _ : IsTopologicalGroup G, ∀ _ : CompactSpace G,
    ∀ ξ : Y.X -> G, Continuous ξ ->
    ∀ ν : MeasureOn Y.X, IsInvariantMeasure Y ν ->
    ∀ m : MeasureOn G,
      IsProbabilityBorelMeasure m ->
      (∀ g : G, ∀ f : G -> ℂ, Continuous f ->
        m.integral (fun h => f (g * h)) = m.integral f) ->
    ∀ productMeasure : MeasureOn (Y.X × G),
      (∀ A : Set Y.X, ∀ B : Set G,
        productMeasure.measure (A ×ˢ B) = ν.measure A * m.measure B) ->
      let X : System.{u} :=
        { X := Y.X × G
          topology := inferInstance
          T := fun p => (Y.T p.1, ξ p.1 * p.2) }
      IsErgodicMeasure X productMeasure -> IsUniquelyErgodic X

structure TopologicalModelData (M : MeasurableSystem.{u}) where
  sourceSet : Set M.X
  topologicalSystem : System.{u}
  invariantMeasure : MeasureOn topologicalSystem.X
  modelMeasurableSpace : MeasurableSpace topologicalSystem.X
  borel_measurable_space : modelMeasurableSpace = borel topologicalSystem.X
  modelMeasure : @MeasureTheory.Measure topologicalSystem.X modelMeasurableSpace
  measure_agrees : ∀ A : Set topologicalSystem.X,
    modelMeasure A = invariantMeasure.measure A
  integral_agrees : ∀ f : topologicalSystem.X -> ℂ,
    (∫ x, f x ∂modelMeasure) = invariantMeasure.integral f

def TopologicalModelData.modelSystem {M : MeasurableSystem.{u}}
    (D : TopologicalModelData M) : MeasurableSystem.{u} :=
  { X := D.topologicalSystem.X,
    measurableSpace := D.modelMeasurableSpace,
    μ := D.modelMeasure,
    T := D.topologicalSystem.T }

def IsTopologicalModel (M : MeasurableSystem.{u}) (D : TopologicalModelData M) : Prop :=
  Chapter05.IsTopologicalSystem D.topologicalSystem ∧
    D.modelMeasurableSpace = borel D.topologicalSystem.X ∧
    IsInvariantMeasure D.topologicalSystem D.invariantMeasure ∧
    Chapter01.IsIsomorphicSystems M D.modelSystem

def HasTopologicalModel (M : MeasurableSystem.{u}) : Prop :=
  ∃ D : TopologicalModelData M, IsTopologicalModel M D

def IsNonatomicSystem (M : MeasurableSystem.{u}) : Prop :=
  ∀ A : Set M.X, MeasurableSet A -> 0 < M.μ A ->
    ∃ B : Set M.X, MeasurableSet B ∧ B ⊆ A ∧ 0 < M.μ B ∧ M.μ B < M.μ A

def IsInvertibleTopologicalSystem (S : System.{u}) : Prop :=
  Chapter05.IsTopologicalSystem S ∧ ∃ R : S.X → S.X,
    Continuous R ∧ Function.LeftInverse R S.T ∧ Function.RightInverse R S.T

def HasMinimalUniversalTopologicalModel : Prop :=
  ∃ S : System.{0}, IsInvertibleTopologicalSystem S ∧ Chapter05.IsMinimalSystem S ∧
    ∀ M : MeasurableSystem.{0}, Chapter01.IsMeasurePreservingSystem M ->
      Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace ->
      Chapter01.IsInvertibleMeasurePreservingMap M.𝓧 M.μ M.𝓧 M.μ M.T ->
      IsNonatomicSystem M -> Chapter02.IsErgodic M ->
        ∃ D : TopologicalModelData M,
          D.topologicalSystem = S ∧ IsTopologicalModel M D

def HasUniquelyErgodicMinimalTopologicalModel (M : MeasurableSystem.{u}) : Prop :=
  ∃ D : TopologicalModelData M, IsTopologicalModel M D ∧ Chapter05.IsMinimalSystem D.topologicalSystem ∧ IsUniquelyErgodic D.topologicalSystem

def HasStrongMixingUniquelyErgodicTopologicalModel (M : MeasurableSystem.{u}) : Prop :=
  ∃ D : TopologicalModelData M, IsTopologicalModel M D ∧ Chapter05.IsMinimalSystem D.topologicalSystem ∧
    IsUniquelyErgodic D.topologicalSystem ∧ Chapter05.IsStrongMixing D.topologicalSystem

def IsTopologicalModelOfFactor
    (M N : MeasurableSystem.{u}) (D : TopologicalModelData M) (E : TopologicalModelData N)
    (πm : M.X → N.X) (πt : D.topologicalSystem.X -> E.topologicalSystem.X) : Prop :=
  IsTopologicalModel M D ∧ IsTopologicalModel N E ∧
    Chapter01.IsFactorMap M N πm ∧
    Chapter05.IsFactorMap D.topologicalSystem E.topologicalSystem πt ∧
    ∃ φM : M.X → D.modelSystem.X, ∃ ψM : D.modelSystem.X → M.X,
    ∃ φN : N.X → E.modelSystem.X, ∃ ψN : E.modelSystem.X → N.X,
      Chapter01.IsFactorMap M D.modelSystem φM ∧
      Chapter01.IsFactorMap D.modelSystem M ψM ∧
      Function.LeftInverse ψM φM ∧ Function.RightInverse ψM φM ∧
      Chapter01.IsFactorMap N E.modelSystem φN ∧
      Chapter01.IsFactorMap E.modelSystem N ψN ∧
      Function.LeftInverse ψN φN ∧ Function.RightInverse ψN φN ∧
      ∀ x : M.X, φN (πm x) = πt (φM x)

end Chapter06
