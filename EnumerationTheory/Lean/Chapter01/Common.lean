import Chapter00.Common

noncomputable section

open Classical
open scoped BigOperators

namespace Chapter01

universe u v w

abbrev SetFamily (X : Type u) := Chapter00.SetFamily X

structure ProbabilitySpaceData where
  X : Type u
  measurableSpace : MeasurableSpace X
  μ : @MeasureTheory.Measure X measurableSpace

structure MeasurePreservingSystemData where
  X : Type u
  measurableSpace : MeasurableSpace X
  μ : @MeasureTheory.Measure X measurableSpace
  T : X -> X

attribute [instance] ProbabilitySpaceData.measurableSpace
  MeasurePreservingSystemData.measurableSpace

namespace ProbabilitySpaceData

def 𝓧 (P : ProbabilitySpaceData) : SetFamily P.X :=
  {A | MeasurableSet A}

def integral (P : ProbabilitySpaceData) (f : P.X -> ℂ) : ℂ :=
  ∫ x, f x ∂P.μ

def lpMember (P : ProbabilitySpaceData) (p : ENNReal) (f : P.X -> ℂ) : Prop :=
  MeasureTheory.MemLp f p P.μ

def lpNorm (P : ProbabilitySpaceData) (p : ENNReal) (f : P.X -> ℂ) : ℝ :=
  (MeasureTheory.eLpNorm f p P.μ).toReal

end ProbabilitySpaceData

namespace MeasurePreservingSystemData

def 𝓧 (S : MeasurePreservingSystemData) : SetFamily S.X :=
  {A | MeasurableSet A}

def integral (S : MeasurePreservingSystemData) (f : S.X -> ℂ) : ℂ :=
  ∫ x, f x ∂S.μ

def lpMember (S : MeasurePreservingSystemData) (p : ENNReal) (f : S.X -> ℂ) : Prop :=
  MeasureTheory.MemLp f p S.μ

def lpNorm (S : MeasurePreservingSystemData) (p : ENNReal) (f : S.X -> ℂ) : ℝ :=
  (MeasureTheory.eLpNorm f p S.μ).toReal

end MeasurePreservingSystemData

def MeasurePreservingSystemData.toProbabilitySpace (S : MeasurePreservingSystemData.{u}) :
    ProbabilitySpaceData.{u} where
  X := S.X
  measurableSpace := S.measurableSpace
  μ := S.μ

def IsProbabilitySpace (P : ProbabilitySpaceData.{u}) : Prop :=
  MeasureTheory.IsProbabilityMeasure P.μ

/-- Source: Definition 1.1.1(a), measurable transformation. -/
def IsMeasurableMap {X : Type u} {Y : Type v}
    (𝓧 : SetFamily X) (𝓨 : SetFamily Y) (T : X -> Y) : Prop :=
  ∀ B : Set Y, B ∈ 𝓨 -> T ⁻¹' B ∈ 𝓧

/-- Source: Definition 1.1.1(b), measure-preserving transformation. -/
def IsMeasurePreservingMap {X : Type u} {Y : Type v}
    (𝓧 : SetFamily X) (μ : Set X -> ENNReal)
    (𝓨 : SetFamily Y) (ν : Set Y -> ENNReal) (T : X -> Y) : Prop :=
  IsMeasurableMap 𝓧 𝓨 T ∧ ∀ B : Set Y, B ∈ 𝓨 -> μ (T ⁻¹' B) = ν B

/-- Source: Definition 1.1.1(c), invertible measure-preserving transformation. -/
def IsInvertibleMeasurePreservingMap {X : Type u} {Y : Type v}
    (𝓧 : SetFamily X) (μ : Set X -> ENNReal)
    (𝓨 : SetFamily Y) (ν : Set Y -> ENNReal) (T : X -> Y) : Prop :=
  ∃ S : Y -> X,
    IsMeasurePreservingMap 𝓧 μ 𝓨 ν T ∧
      IsMeasurePreservingMap 𝓨 ν 𝓧 μ S ∧
      Function.LeftInverse S T ∧ Function.RightInverse S T

/-- Source: Definition 1.1.2, measure-preserving system. -/
def IsMeasurePreservingSystem (S : MeasurePreservingSystemData.{u}) : Prop :=
  IsProbabilitySpace S.toProbabilitySpace ∧
    MeasureTheory.MeasurePreserving S.T S.μ S.μ

def IsMeasurePreservingOnFullSets (S₁ : MeasurePreservingSystemData.{u})
    (S₂ : MeasurePreservingSystemData.{v}) (M₁ : Set S₁.X) (M₂ : Set S₂.X)
    (φ : S₁.X -> S₂.X) : Prop :=
  M₁ ∈ S₁.𝓧 ∧ M₂ ∈ S₂.𝓧 ∧ S₁.μ M₁ = 1 ∧ S₂.μ M₂ = 1 ∧
    (∀ x ∈ M₁, φ x ∈ M₂) ∧
    ∀ B : Set S₂.X, B ∈ S₂.𝓧 ->
      M₁ ∩ φ ⁻¹' (B ∩ M₂) ∈ S₁.𝓧 ∧
        S₁.μ (M₁ ∩ φ ⁻¹' (B ∩ M₂)) = S₂.μ (B ∩ M₂)

/-- Source: Definition 1.1.3, factor map up to invariant full-measure subsets. -/
def IsFactorMap (S₁ : MeasurePreservingSystemData.{u})
    (S₂ : MeasurePreservingSystemData.{v}) (φ : S₁.X -> S₂.X) : Prop :=
  IsMeasurePreservingSystem S₁ ∧ IsMeasurePreservingSystem S₂ ∧
    ∃ M₁ : Set S₁.X, ∃ M₂ : Set S₂.X,
      S₁.μ M₁ = 1 ∧ S₂.μ M₂ = 1 ∧
        (∀ x ∈ M₁, S₁.T x ∈ M₁) ∧
        (∀ y ∈ M₂, S₂.T y ∈ M₂) ∧
        IsMeasurePreservingOnFullSets S₁ S₂ M₁ M₂ φ ∧
        ∀ x ∈ M₁, φ (S₁.T x) = S₂.T (φ x)

/-- Source: Definition 1.1.3, isomorphism of measure-preserving systems. -/
def IsIsomorphicSystems (S₁ : MeasurePreservingSystemData.{u})
    (S₂ : MeasurePreservingSystemData.{v}) : Prop :=
  IsMeasurePreservingSystem S₁ ∧ IsMeasurePreservingSystem S₂ ∧
  ∃ M₁ : Set S₁.X, ∃ M₂ : Set S₂.X,
  ∃ φ : S₁.X -> S₂.X, ∃ ψ : S₂.X -> S₁.X,
    S₁.μ M₁ = 1 ∧ S₂.μ M₂ = 1 ∧
    (∀ x ∈ M₁, S₁.T x ∈ M₁) ∧ (∀ y ∈ M₂, S₂.T y ∈ M₂) ∧
    IsMeasurePreservingOnFullSets S₁ S₂ M₁ M₂ φ ∧
    IsMeasurePreservingOnFullSets S₂ S₁ M₂ M₁ ψ ∧
    (∀ x ∈ M₁, φ x ∈ M₂ ∧ ψ (φ x) = x ∧
      φ (S₁.T x) = S₂.T (φ x)) ∧
    ∀ y ∈ M₂, ψ y ∈ M₁ ∧ φ (ψ y) = y ∧
      ψ (S₂.T y) = S₁.T (ψ y)

/-- Source: Definition 1.1.5, Koopman operator. -/
def koopman {X : Type u} {Y : Type v} (T : X -> Y) (f : Y -> ℂ) : X -> ℂ :=
  fun x => f (T x)

def IsRealValuedFunction {X : Type u} (f : X -> ℂ) : Prop :=
  ∀ x : X, f x = ((f x).re : ℂ)

def IsNonnegativeFunction {X : Type u} (f : X -> ℂ) : Prop :=
  IsRealValuedFunction f ∧ ∀ x : X, 0 ≤ (f x).re

def IsKoopmanOperatorFor {X : Type u} {Y : Type v}
    (T : X -> Y) (U : (Y -> ℂ) -> X -> ℂ) : Prop :=
  ∀ f : Y -> ℂ, U f = koopman T f

def KoopmanBasicProperties {X : Type u} {Y : Type v} {Z : Type w}
    (T : X -> Y) (S : Y -> Z) : Prop :=
  (∀ f g : Y -> ℂ, ∀ a b : ℂ,
      koopman T (fun y => a * f y + b * g y) =
        fun x => a * koopman T f x + b * koopman T g x) ∧
    (∀ f g : Y -> ℂ,
      koopman T (fun y => f y * g y) =
        fun x => koopman T f x * koopman T g x) ∧
    (∀ c : ℂ, koopman T (fun _ : Y => c) = fun _ : X => c) ∧
    (∀ f : Y -> ℂ, IsNonnegativeFunction f -> IsNonnegativeFunction (koopman T f)) ∧
    (∀ B : Set Y, koopman T (fun y => if y ∈ B then 1 else 0) =
      fun x => if x ∈ T ⁻¹' B then 1 else 0) ∧
    (∀ f : Z -> ℂ, koopman (S ∘ T) f = koopman T (koopman S f))

def PreservesIntegrals (P : ProbabilitySpaceData.{u}) (Q : ProbabilitySpaceData.{v})
    (T : P.X -> Q.X) : Prop :=
  ∀ f : Q.X -> ℂ, Measurable f ->
    (MeasureTheory.Integrable (koopman T f) P.μ ↔
      MeasureTheory.Integrable f Q.μ) ∧
    (MeasureTheory.Integrable f Q.μ ->
      P.integral (koopman T f) = Q.integral f)

def KoopmanIsLpIsometry (P : ProbabilitySpaceData.{u}) (Q : ProbabilitySpaceData.{v})
    (T : P.X -> Q.X) : Prop :=
  ∀ p : ENNReal, 1 ≤ p ->
    (∀ f : Q.X -> ℂ, Q.lpMember p f -> P.lpMember p (koopman T f)) ∧
      ∀ f : Q.X -> ℂ, Q.lpMember p f -> P.lpNorm p (koopman T f) = Q.lpNorm p f

def KoopmanPreservesRealLp (P : ProbabilitySpaceData.{u}) (Q : ProbabilitySpaceData.{v})
    (T : P.X -> Q.X) : Prop :=
  ∀ p : ENNReal, 1 ≤ p -> ∀ f : Q.X -> ℂ,
    Q.lpMember p f -> IsRealValuedFunction f -> IsRealValuedFunction (koopman T f)

structure InverseSequenceData where
  system : ℕ -> MeasurePreservingSystemData.{u}
  factorMap : ∀ i j : ℕ, j ≤ i -> (system i).X -> (system j).X

def IsCoherentInverseSequence (D : InverseSequenceData.{u}) : Prop :=
  (∀ i : ℕ, ∀ h : i ≤ i, D.factorMap i i h = id) ∧
    ∀ i j k : ℕ, ∀ hij : j ≤ i, ∀ hjk : k ≤ j, ∀ hik : k ≤ i,
      D.factorMap j k hjk ∘ D.factorMap i j hij = D.factorMap i k hik

/-- Source: Definition 1.1.9, inverse limit system. -/
def IsInverseLimitSystem (D : InverseSequenceData.{u})
    (L : MeasurePreservingSystemData.{u}) (π : ∀ i : ℕ, L.X -> (D.system i).X) : Prop :=
  IsCoherentInverseSequence D ∧ IsMeasurePreservingSystem L ∧
    (∀ i j : ℕ, ∀ h : j ≤ i, D.factorMap i j h ∘ π i = π j) ∧
    (∀ i : ℕ, IsFactorMap L (D.system i) (π i)) ∧
    L.𝓧 = Chapter00.generatedSigmaAlgebra
      {A : Set L.X | ∃ i : ℕ, ∃ B : Set (D.system i).X,
        B ∈ (D.system i).𝓧 ∧ A = (π i) ⁻¹' B}

/-- Source: Definition 1.1.10, natural extension. -/
def IsNaturalExtension (S : MeasurePreservingSystemData.{u})
    (Stilde : MeasurePreservingSystemData.{v}) (φ : Stilde.X -> S.X) : Prop :=
  IsMeasurePreservingSystem S ∧ IsMeasurePreservingSystem Stilde ∧
    IsInvertibleMeasurePreservingMap Stilde.𝓧 Stilde.μ Stilde.𝓧 Stilde.μ Stilde.T ∧
    IsFactorMap Stilde S φ ∧
    Stilde.𝓧 = Chapter00.generatedSigmaAlgebra
      {C : Set Stilde.X | ∃ n : ℕ, ∃ A : Set S.X,
        A ∈ S.𝓧 ∧ C = (Stilde.T^[n]) '' (φ ⁻¹' A)}

def IsTrivialSystem (S : MeasurePreservingSystemData.{u}) : Prop :=
  IsMeasurePreservingSystem S ∧ S.𝓧 = ({Set.univ, ∅} : Set (Set S.X)) ∧ S.T = id

def IsNPeriodicSystem (S : MeasurePreservingSystemData.{u}) (n : ℕ) : Prop :=
  IsMeasurePreservingSystem S ∧
    ∃ e : S.X ≃ Fin n,
      ∀ x : S.X, (e (S.T x)).val = ((e x).val + 1) % n

def IsRotationSystem (S : MeasurePreservingSystemData.{u}) (rotationParameter : ℝ) : Prop :=
  IsMeasurePreservingSystem S ∧
    ∃ e : S.X ≃ AddCircle (1 : ℝ),
      Measurable e ∧ Measurable e.symm ∧
      MeasureTheory.Measure.map e S.μ = AddCircle.haarAddCircle ∧
      ∀ x : S.X,
        e (S.T x) = e x + (rotationParameter : AddCircle (1 : ℝ))

/-- The `k`-dimensional torus `𝕋ᵏ` used in Example 1.2.7. -/
abbrev Torus (k : ℕ) := Fin k -> AddCircle (1 : ℝ)

/-- Normalized Lebesgue (Haar) probability measure on `𝕋ᵏ`. -/
noncomputable def torusHaarMeasure (k : ℕ) : MeasureTheory.Measure (Torus k) :=
  MeasureTheory.Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)

/-- Translation by `θ` on `𝕋ᵏ`. -/
def torusRotation (k : ℕ) (θ : Fin k -> ℝ) : Torus k -> Torus k :=
  fun x => x + fun i => (θ i : AddCircle (1 : ℝ))

/-- The concrete probability-preserving torus rotation from Example 1.2.7. -/
noncomputable def torusRotationSystem (k : ℕ) (θ : Fin k -> ℝ) :
    MeasurePreservingSystemData where
  X := Torus k
  measurableSpace := inferInstance
  μ := torusHaarMeasure k
  T := torusRotation k θ

/-- The triangular torus map from Example 1.2.13. -/
def triangularTorusMap : (k : ℕ) -> ℝ -> Torus k -> Torus k
  | 0, _, x => x
  | _n + 1, α, x => fun i =>
      Fin.cases (x 0 + (α : AddCircle (1 : ℝ)))
        (fun j => x j.succ + x j.castSucc) i

/-- The concrete triangular torus system from Example 1.2.13. -/
noncomputable def triangularTorusSystem (k : ℕ) (α : ℝ) :
    MeasurePreservingSystemData where
  X := Torus k
  measurableSpace := inferInstance
  μ := torusHaarMeasure k
  T := triangularTorusMap k α

/-- The binary sequence space `Σ₂ = {0,1}^{ℤ₊}` from Example 1.2.8. -/
abbrev BinarySequence := ℕ -> Fin 2

/-- The Bernoulli `(1/2,1/2)` product probability measure on `Σ₂`. -/
noncomputable def binaryProductMeasure : MeasureTheory.Measure BinarySequence :=
  MeasureTheory.Measure.infinitePi
    (fun _ : ℕ => ProbabilityTheory.uniformOn (Set.univ : Set (Fin 2)))

/-- Addition of `1 = (1,0,0,...)` with binary carry. -/
def addingOne (x : BinarySequence) : BinarySequence :=
  fun n => if ∀ j < n, x j = 1 then x n + 1 else x n

/-- The concrete adding-machine probability system from Example 1.2.8. -/
noncomputable def addingMachineSystem : MeasurePreservingSystemData where
  X := BinarySequence
  measurableSpace := inferInstance
  μ := binaryProductMeasure
  T := addingOne

/-- Left rotation by `a` on a group. -/
def groupRotation {G : Type u} [Mul G] (a : G) : G -> G :=
  fun x => a * x

/-- The concrete Haar system associated to a group rotation. -/
noncomputable def groupRotationSystem {G : Type u} [MeasurableSpace G] [Mul G]
    (m : MeasureTheory.Measure G) (a : G) : MeasurePreservingSystemData where
  X := G
  measurableSpace := inferInstance
  μ := m
  T := groupRotation a

/-- The concrete Haar system associated to a continuous group endomorphism. -/
noncomputable def groupEndomorphismSystem {G : Type u} [MeasurableSpace G] [MulOneClass G]
    (m : MeasureTheory.Measure G) (A : G →* G) : MeasurePreservingSystemData where
  X := G
  measurableSpace := inferInstance
  μ := m
  T := A

/-- The affine map `x ↦ a * A x` from Example 1.2.11. -/
def affineGroupMap {G : Type u} [MulOneClass G] (a : G) (A : G →* G) : G -> G :=
  fun x => a * A x

/-- The concrete Haar system associated to an affine group map. -/
noncomputable def affineGroupSystem {G : Type u} [MeasurableSpace G] [MulOneClass G]
    (m : MeasureTheory.Measure G) (a : G) (A : G →* G) :
    MeasurePreservingSystemData where
  X := G
  measurableSpace := inferInstance
  μ := m
  T := affineGroupMap a A

def IsEndomorphismSystem (S : MeasurePreservingSystemData.{u}) : Prop :=
  IsMeasurePreservingSystem S ∧ ∃ mul : S.X -> S.X -> S.X, ∀ x y : S.X, S.T (mul x y) = mul (S.T x) (S.T y)

def IsAffineSystem (S : MeasurePreservingSystemData.{u}) : Prop :=
  IsMeasurePreservingSystem S ∧
    ∃ mul : S.X -> S.X -> S.X, ∃ a : S.X, ∃ A : S.X -> S.X,
      (∀ x : S.X, S.T x = mul a (A x)) ∧
        ∀ x y : S.X, A (mul x y) = mul (A x) (A y)

def IsSkewProductSystem (X : Type u) (Y : Type v) (Z : Type w)
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
    (S : Y -> Y) (φ : Y -> Z -> Z) (T : X -> X) : Prop :=
  Continuous S ∧ (∀ y, Continuous (φ y)) ∧
    Continuous (fun p : Y × Z => φ p.1 p.2) ∧ Continuous T ∧
    ∃ e : X ≃ₜ Y × Z, ∀ x : X,
      e (T x) = (S (e x).1, φ (e x).1 (e x).2)

def IsGroupExtensionSystem (X : Type u) (Y : Type v) (G : Type w)
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TopologicalSpace.MetrizableSpace G]
    (S : Y -> Y) (φ : Y -> G) (T : X -> X) : Prop :=
  Continuous S ∧ Continuous φ ∧ Continuous T ∧
    ∃ e : X ≃ₜ Y × G, ∀ x : X,
      e (T x) = (S (e x).1, φ (e x).1 * (e x).2)

/-! ## One-sided symbolic systems from Example 1.2.14 -/

/-- The one-sided full shift space `A^{ℤ₊}` on the alphabet `Fin k`. -/
abbrev OneSidedSymbolicSpace (k : ℕ) := ℕ -> Fin k

/-- The left shift `σ(x₀x₁x₂⋯) = x₁x₂x₃⋯`. -/
def oneSidedShift {k : ℕ} (x : OneSidedSymbolicSpace k) :
    OneSidedSymbolicSpace k :=
  fun n => x (n + 1)

/-- Concatenation of two finite words. -/
def oneSidedWordConcat {k : ℕ} (u v : List (Fin k)) : List (Fin k) :=
  u ++ v

/-- A finite word occurs in a one-sided infinite word at coordinate `start`. -/
def OneSidedWordOccursAt {k : ℕ} (word : List (Fin k))
    (x : OneSidedSymbolicSpace k) (start : ℕ) : Prop :=
  ∀ i : Fin word.length, x (start + i) = word.get i

/-- The initial cylinder `[word]`. -/
def oneSidedCylinder {k : ℕ} (word : List (Fin k)) :
    Set (OneSidedSymbolicSpace k) :=
  {x | OneSidedWordOccursAt word x 0}

/-- The family of all initial cylinders, including the empty-word cylinder. -/
def oneSidedCylinderFamily (k : ℕ) : Set (Set (OneSidedSymbolicSpace k)) :=
  {C | ∃ word : List (Fin k), C = oneSidedCylinder word}

/-- A nonempty closed forward-invariant subset of the one-sided full shift. -/
def IsOneSidedSubshift (k : ℕ) (X : Set (OneSidedSymbolicSpace k)) : Prop :=
  X.Nonempty ∧ IsClosed X ∧ Set.MapsTo oneSidedShift X X

/-- The atomic probability measure on the finite alphabet with weights `p`. -/
noncomputable def alphabetProbabilityMeasure (k : ℕ) (p : Fin k -> ℝ) :
    MeasureTheory.Measure (Fin k) :=
  ∑ i : Fin k, ENNReal.ofReal (p i) • MeasureTheory.Measure.dirac i

/-- The Bernoulli product measure on the one-sided sequence space. -/
noncomputable def oneSidedBernoulliMeasure (k : ℕ) (p : Fin k -> ℝ) :
    MeasureTheory.Measure (OneSidedSymbolicSpace k) :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => alphabetProbabilityMeasure k p)

/-- The concrete one-sided Bernoulli shift used in Example 1.2.14. -/
noncomputable def oneSidedBernoulliSystem (k : ℕ) (p : Fin k -> ℝ) :
    MeasurePreservingSystemData where
  X := OneSidedSymbolicSpace k
  measurableSpace := inferInstance
  μ := oneSidedBernoulliMeasure k p
  T := oneSidedShift

/-- Binary expansion `Σ₂ → ℝ/ℤ` from Example 1.2.14. -/
noncomputable def binaryCoding (x : OneSidedSymbolicSpace 2) :
    AddCircle (1 : ℝ) :=
  ((∑' n : ℕ, ((x n).val : ℝ) / (2 : ℝ) ^ (n + 1)) : AddCircle (1 : ℝ))

def IsOneSidedFullShiftSystem (S : MeasurePreservingSystemData.{u}) (k : ℕ) : Prop :=
  IsMeasurePreservingSystem S ∧
    ∃ e : S.X ≃ (ℕ -> Fin k),
      Measurable e ∧ Measurable e.symm ∧
      ∀ x : S.X, ∀ n : ℕ, e (S.T x) n = e x (n + 1)

def IsTwoSidedFullShiftSystem (S : MeasurePreservingSystemData.{u}) (k : ℕ) : Prop :=
  IsMeasurePreservingSystem S ∧
    ∃ e : S.X ≃ (ℤ -> Fin k),
      Measurable e ∧ Measurable e.symm ∧
      ∀ x : S.X, ∀ n : ℤ, e (S.T x) n = e x (n + 1)

def IsOneSidedMarkovShiftWith (S : MeasurePreservingSystemData.{u}) (k : ℕ)
    (initial : Fin k -> ℝ) (transition : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  IsMeasurePreservingSystem S ∧
    ∃ e : S.X ≃ (ℕ -> Fin k),
      Measurable e ∧ Measurable e.symm ∧
      (∀ x : S.X, ∀ n : ℕ, e (S.T x) n = e x (n + 1)) ∧
      (∀ i, 0 ≤ initial i) ∧
      (∑ i, initial i) = 1 ∧
      (∀ i j, 0 ≤ transition i j) ∧
      (∀ i, (∑ j, transition i j) = 1) ∧
      (∀ j, (∑ i, initial i * transition i j) = initial j) ∧
      ∀ n : ℕ, ∀ a : Fin (n + 1) -> Fin k,
        S.μ {x | ∀ i : Fin (n + 1), e x i = a i} =
          ENNReal.ofReal
            (initial (a 0) * ∏ i : Fin n, transition (a i.castSucc) (a i.succ))

def IsTwoSidedMarkovShiftWith (S : MeasurePreservingSystemData.{u}) (k : ℕ)
    (initial : Fin k -> ℝ) (transition : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  IsMeasurePreservingSystem S ∧
    ∃ e : S.X ≃ (ℤ -> Fin k),
      Measurable e ∧ Measurable e.symm ∧
      (∀ x : S.X, ∀ n : ℤ, e (S.T x) n = e x (n + 1)) ∧
      (∀ i, 0 ≤ initial i) ∧
      (∑ i, initial i) = 1 ∧
      (∀ i j, 0 ≤ transition i j) ∧
      (∀ i, (∑ j, transition i j) = 1) ∧
      (∀ j, (∑ i, initial i * transition i j) = initial j) ∧
      ∀ n : ℕ, ∀ a : Fin (n + 1) -> Fin k,
        S.μ {x | ∀ i : Fin (n + 1), e x (i : ℤ) = a i} =
          ENNReal.ofReal
            (initial (a 0) * ∏ i : Fin n, transition (a i.castSucc) (a i.succ))

def IsMarkovShiftWith (S : MeasurePreservingSystemData.{u}) (k : ℕ)
    (initial : Fin k -> ℝ) (transition : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  IsOneSidedMarkovShiftWith S k initial transition ∨
    IsTwoSidedMarkovShiftWith S k initial transition

def IsMarkovShiftSystem (S : MeasurePreservingSystemData.{u}) (k : ℕ) : Prop :=
  ∃ initial : Fin k -> ℝ, ∃ transition : Matrix (Fin k) (Fin k) ℝ,
    IsMarkovShiftWith S k initial transition

def IsOneSidedBernoulliShiftWith
    (S : MeasurePreservingSystemData.{u}) (k : ℕ) (p : Fin k -> ℝ) : Prop :=
  IsMeasurePreservingSystem S ∧
    ∃ e : S.X ≃ (ℕ -> Fin k),
      Measurable e ∧ Measurable e.symm ∧
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      (∀ x : S.X, ∀ n : ℕ, e (S.T x) n = e x (n + 1)) ∧
      ∀ n : ℕ, ∀ a : Fin (n + 1) -> Fin k,
        S.μ {x | ∀ i : Fin (n + 1), e x i = a i} =
          ENNReal.ofReal (∏ i, p (a i))

def IsOneSidedBernoulliShiftSystem
    (S : MeasurePreservingSystemData.{u}) (k : ℕ) : Prop :=
  ∃ p : Fin k -> ℝ, IsOneSidedBernoulliShiftWith S k p

def IsTwoSidedBernoulliShiftWith
    (S : MeasurePreservingSystemData.{u}) (k : ℕ) (p : Fin k -> ℝ) : Prop :=
  IsMeasurePreservingSystem S ∧
    ∃ e : S.X ≃ (ℤ -> Fin k),
      Measurable e ∧ Measurable e.symm ∧
      MeasureTheory.Measure.map e S.μ =
        MeasureTheory.Measure.infinitePi
          (fun _ : ℤ ↦ alphabetProbabilityMeasure k p) ∧
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      (∀ x : S.X, ∀ n : ℤ, e (S.T x) n = e x (n + 1)) ∧
      ∀ n : ℕ, ∀ a : Fin (n + 1) -> Fin k,
        S.μ {x | ∀ i : Fin (n + 1), e x (i : ℤ) = a i} =
          ENNReal.ofReal (∏ i, p (a i))

def IsTwoSidedBernoulliShiftSystem
    (S : MeasurePreservingSystemData.{u}) (k : ℕ) : Prop :=
  ∃ p : Fin k -> ℝ, IsTwoSidedBernoulliShiftWith S k p

def IsBernoulliShiftSystem (S : MeasurePreservingSystemData.{u}) (k : ℕ) : Prop :=
  IsOneSidedBernoulliShiftSystem S k ∨ IsTwoSidedBernoulliShiftSystem S k

/-- The Cauchy probability measure from Example 1.2.15. -/
noncomputable def cauchyMeasure : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.withDensity
    (fun x => ENNReal.ofReal ((Real.pi * (1 + x ^ 2))⁻¹))

/-- The real-line model `x ↦ (x - 1/x)/2`, with the displayed value at zero. -/
def cauchyDoublingMap (x : ℝ) : ℝ :=
  if x = 0 then 0 else (x - x⁻¹) / 2

noncomputable def cauchyDoublingSystem : MeasurePreservingSystemData where
  X := ℝ
  measurableSpace := inferInstance
  μ := cauchyMeasure
  T := cauchyDoublingMap

def IsStationaryProcess (P : ProbabilitySpaceData.{u}) (f : ℤ -> P.X -> ℝ) : Prop :=
  IsProbabilitySpace P ∧ (∀ n : ℤ, Measurable (f n)) ∧
    ∀ r : ℕ, ∀ n : Fin r -> ℤ, ∀ B : Fin r -> Set ℝ,
      (∀ i, MeasurableSet (B i)) -> ∀ shift : ℤ,
        P.μ {ω | ∀ i, f (n i) ω ∈ B i} =
          P.μ {ω | ∀ i, f (n i + shift) ω ∈ B i}

def IsStationaryProcessShiftModel (P : ProbabilitySpaceData.{u})
    (f : ℤ -> P.X -> ℝ) (S : MeasurePreservingSystemData.{v}) : Prop :=
  IsStationaryProcess P f ∧ IsMeasurePreservingSystem S ∧
    ∃ e : S.X ≃ (ℤ -> ℝ),
      Measurable e ∧ Measurable e.symm ∧
      MeasureTheory.Measure.map e S.μ =
        MeasureTheory.Measure.map (fun ω n => f n ω) P.μ ∧
      ∀ x : S.X, ∀ n : ℤ, e (S.T x) n = e x (n + 1)

def IsTopologicallyMinimal {X : Type u} [TopologicalSpace X] (T : X -> X) : Prop :=
  ∀ x : X, Dense (Set.range fun n : ℕ => (T^[n]) x)

def circleTimes (n : ℕ) (x : AddCircle (1 : ℝ)) : AddCircle (1 : ℝ) :=
  n • x

/-- The concrete Haar probability system for `x ↦ n x (mod 1)`. -/
noncomputable def circleTimesSystem (n : ℕ) : MeasurePreservingSystemData where
  X := AddCircle (1 : ℝ)
  measurableSpace := inferInstance
  μ := AddCircle.haarAddCircle
  T := circleTimes n

/-- All mathematical clauses stated in Example 1.2.14, on the concrete
standard product model rather than an unstructured type-equivalent carrier. -/
def OneSidedShiftExampleSemantics (k : ℕ) (p : Fin k -> ℝ) : Prop :=
  IsOneSidedBernoulliShiftWith (oneSidedBernoulliSystem k p) k p ∧
  Nonempty (CompactSpace (OneSidedSymbolicSpace k)) ∧
  Nonempty (TopologicalSpace.MetrizableSpace (OneSidedSymbolicSpace k)) ∧
  Continuous (@oneSidedShift k) ∧ Function.Surjective (@oneSidedShift k) ∧
  (∀ X : Set (OneSidedSymbolicSpace k),
    IsOneSidedSubshift k X ↔
      X.Nonempty ∧ IsClosed X ∧ Set.MapsTo oneSidedShift X X) ∧
  (∀ u v : List (Fin k),
    oneSidedWordConcat u v = u ++ v ∧
      (oneSidedWordConcat u v).length = u.length + v.length) ∧
  (∀ word : List (Fin k), IsClopen (oneSidedCylinder word)) ∧
  TopologicalSpace.IsTopologicalBasis (oneSidedCylinderFamily k) ∧
  (∀ x : OneSidedSymbolicSpace 2,
    binaryCoding (oneSidedShift x) = circleTimes 2 (binaryCoding x)) ∧
  IsFactorMap
    (oneSidedBernoulliSystem 2 (fun _ => (1 / 2 : ℝ)))
    (circleTimesSystem 2) binaryCoding ∧
  IsIsomorphicSystems
    (oneSidedBernoulliSystem 2 (fun _ => (1 / 2 : ℝ)))
    (circleTimesSystem 2)

/-- The interval representative of the doubling map in Example 1.2.4. -/
def doublingIntervalValue (x : Set.Icc (0 : ℝ) 1) : ℝ :=
  if (x : ℝ) < 1 / 2 then 2 * (x : ℝ) else 2 * (x : ℝ) - 1

/-- The doubling map on the fundamental-domain model `(0,1]` of the circle.
The endpoint convention is the one induced by `AddCircle.equivIoc`; it removes
the duplicate representatives `0` and `1` present in the closed interval. -/
noncomputable def doublingIocMap :
    Set.Ioc (0 : ℝ) (0 + 1) → Set.Ioc (0 : ℝ) (0 + 1) :=
  fun x => AddCircle.measurableEquivIoc 1 0
    (circleTimes 2 ((x : ℝ) : AddCircle (1 : ℝ)))

/-- A system is the textbook interval doubling system, in the standard
fundamental-domain coordinates `(0,1]`. -/
def IsDoublingIntervalSystem (S : MeasurePreservingSystemData.{u}) : Prop :=
  IsMeasurePreservingSystem S ∧
    ∃ e : S.X ≃ Set.Ioc (0 : ℝ) (0 + 1),
      Measurable e ∧ Measurable e.symm ∧
      MeasureTheory.Measure.map e S.μ =
        MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume ∧
      ∀ x : S.X, e (S.T x) = doublingIocMap (e x)

/-- A system is the circle power model `z ↦ zⁿ`, expressed in `ℝ/ℤ` coordinates. -/
def IsCirclePowerSystem (S : MeasurePreservingSystemData.{u}) (n : ℕ) : Prop :=
  IsMeasurePreservingSystem S ∧
    ∃ e : S.X ≃ AddCircle (1 : ℝ),
      Measurable e ∧ Measurable e.symm ∧
      MeasureTheory.Measure.map e S.μ = AddCircle.haarAddCircle ∧
      ∀ x : S.X, e (S.T x) = circleTimes n (e x)

def IsInvariantUnderCircleTimes
    (μ : MeasureTheory.Measure (AddCircle (1 : ℝ))) (n : ℕ) : Prop :=
  MeasureTheory.MeasurePreserving (circleTimes n) μ μ

def IsJointlyErgodicForCircleTimes
    (μ : MeasureTheory.Measure (AddCircle (1 : ℝ))) (n m : ℕ) : Prop :=
  ∀ A : Set (AddCircle (1 : ℝ)), MeasurableSet A ->
    μ (Chapter00.symmDiff A ((circleTimes n) ⁻¹' A)) = 0 ->
    μ (Chapter00.symmDiff A ((circleTimes m) ⁻¹' A)) = 0 ->
      μ A = 0 ∨ μ A = 1

def IsUniformMeasureOnFiniteCircleSet
    (μ : MeasureTheory.Measure (AddCircle (1 : ℝ))) : Prop :=
  ∃ F : Finset (AddCircle (1 : ℝ)), F.Nonempty ∧
    μ = (F.card : ENNReal)⁻¹ • ∑ x ∈ F, MeasureTheory.Measure.dirac x

def iterateMap {X : Type u} (T : X -> X) (n : ℕ) : X -> X :=
  T^[n]

def IsPoincareSequence (S : Set ℕ) : Prop :=
  ∀ M : MeasurePreservingSystemData.{u}, ∀ A : Set M.X,
    IsMeasurePreservingSystem M -> A ∈ M.𝓧 -> 0 < M.μ A ->
      ∃ n : ℕ, n ∈ S ∧ 0 < n ∧ 0 < M.μ (A ∩ (iterateMap M.T n) ⁻¹' A)

def differenceSet (F : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ a ∈ F, ∃ b ∈ F, b < a ∧ n = a - b}

def IsDeltaStarSet (H : Set ℕ) : Prop :=
  ∀ F : Set ℕ, Set.Infinite F -> (H ∩ differenceSet F).Nonempty

def returnTimes (M : MeasurePreservingSystemData.{u}) (A B : Set M.X) : Set ℕ :=
  {n : ℕ | 0 < n ∧ 0 < M.μ (A ∩ (iterateMap M.T n) ⁻¹' B)}

def AlmostEveryPointReturnsInfinitelyOften (M : MeasurePreservingSystemData.{u})
    (A : Set M.X) : Prop :=
  ∃ B : Set M.X, B ⊆ A ∧ M.μ B = M.μ A ∧
    ∀ x ∈ B, ∃ n : ℕ -> ℕ,
      StrictMono n ∧ ∀ i : ℕ, iterateMap M.T (n i) x ∈ B

end Chapter01
