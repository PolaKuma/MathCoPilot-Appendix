import Chapter07.Section13

noncomputable section

open Classical Filter MeasureTheory
open scoped BigOperators ENNReal

set_option linter.unusedVariables false

namespace Chapter08

universe u v w

abbrev SetFamily (X : Type u) := Chapter00.SetFamily X
abbrev MeasurableSystem := Chapter02.System
abbrev TopologicalSystem := Chapter07.System
abbrev MeasureOn := Chapter06.MeasureOn

def IsInvariantMeasure (S : TopologicalSystem.{u}) (μ : MeasureOn S.X) : Prop :=
  Chapter06.IsInvariantMeasure S μ

def topologicalEntropy (S : TopologicalSystem.{u}) : EReal :=
  Chapter07.topologicalEntropy S

def measureEntropy (M : MeasurableSystem.{u}) : EReal :=
  Chapter07.measureEntropy M

/-! ## Joinings and multiple joinings -/

/-- A joining datum is an actual countably additive measure on the product space. -/
structure JoiningData (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) where
  measure : Measure (M.X × N.X)

noncomputable instance joiningDataAdd (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) :
    Add (JoiningData M N) where
  add J K := ⟨J.measure + K.measure⟩

noncomputable instance joiningDataSMul (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) :
    SMul ℝ (JoiningData M N) where
  smul a J := ⟨ENNReal.ofReal a • J.measure⟩

def JoiningData.integral (J : JoiningData M N) (f : M.X × N.X → ℂ) : ℂ :=
  ∫ p, f p ∂J.measure

def flipJoining (J : JoiningData M N) : JoiningData N M :=
  ⟨J.measure.map fun p => (p.2, p.1)⟩

def productTransformation (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) :
    M.X × N.X → M.X × N.X :=
  fun p => (M.T p.1, N.T p.2)

def joiningSystem (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (J : JoiningData M N) : MeasurableSystem.{max u v} :=
  { X := M.X × N.X
    measurableSpace := inferInstance
    μ := J.measure
    T := productTransformation M N }

def IsJoining (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (J : JoiningData M N) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧ Chapter01.IsMeasurePreservingSystem N ∧
    J.measure Set.univ = 1 ∧
    MeasurePreserving Prod.fst J.measure M.μ ∧
    MeasurePreserving Prod.snd J.measure N.μ ∧
    MeasurePreserving (productTransformation M N) J.measure J.measure

/-- A joining of the underlying probability spaces, with no dynamics imposed. -/
def IsMeasureSpaceJoining (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (J : JoiningData M N) : Prop :=
  MeasureTheory.IsProbabilityMeasure M.μ ∧ MeasureTheory.IsProbabilityMeasure N.μ ∧
    J.measure Set.univ = 1 ∧
    MeasurePreserving Prod.fst J.measure M.μ ∧
    MeasurePreserving Prod.snd J.measure N.μ

def IsErgodicJoining (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (J : JoiningData M N) : Prop :=
  IsJoining M N J ∧ Chapter02.IsErgodic (joiningSystem M N J)

def Joinings (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) :
    Set (JoiningData M N) :=
  {J | IsJoining M N J}

def ErgodicJoinings (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) :
    Set (JoiningData M N) :=
  {J | IsErgodicJoining M N J}

abbrev JoiningSpace (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) :=
  {J : JoiningData M N // IsJoining M N J}

def IsExtremePoint {E : Type u} [Add E] [SMul ℝ E] (K : Set E) (x : E) : Prop :=
  Chapter06.IsExtremePoint K x

def IsSelfJoining (M : MeasurableSystem.{u}) (J : JoiningData M M) : Prop :=
  IsJoining M M J

def IsProductJoining (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (J : JoiningData M N) : Prop :=
  IsJoining M N J ∧ J.measure = M.μ.prod N.μ

def JoiningSpaceTopologyProperties (M : MeasurableSystem.{u})
    (N : MeasurableSystem.{v}) : Prop :=
  Chapter00.CountablyGeneratedFamily M.𝓧 ∧
  Chapter00.CountablyGeneratedFamily N.𝓧 ∧
  Nonempty (JoiningSpace M N) ∧
  Chapter06.IsConvexSet (Joinings M N) ∧
  ∃ τ : TopologicalSpace (JoiningSpace M N),
    Nonempty (@CompactSpace (JoiningSpace M N) τ) ∧
      Nonempty (@TopologicalSpace.MetrizableSpace (JoiningSpace M N) τ) ∧
      (letI := τ
       ∀ Jseq : ℕ → JoiningSpace M N, ∀ J : JoiningSpace M N,
         Tendsto Jseq atTop (nhds J) ↔
           ∀ A : Set M.X, MeasurableSet A →
           ∀ B : Set N.X, MeasurableSet B →
             Tendsto (fun n => (Jseq n).1.measure (A ×ˢ B)) atTop
               (nhds (J.1.measure (A ×ˢ B))))

abbrev MultipleJoiningData {ι : Type w} (M : ι → MeasurableSystem.{u}) :=
  Measure ((i : ι) → (M i).X)

def multipleTransformation {ι : Type w} (M : ι → MeasurableSystem.{u}) :
    ((i : ι) → (M i).X) → ((i : ι) → (M i).X) :=
  fun x i => (M i).T (x i)

def IsMultipleJoining {ι : Type w} (M : ι → MeasurableSystem.{u})
    (J : MultipleJoiningData M) : Prop :=
  (∀ i, Chapter01.IsMeasurePreservingSystem (M i)) ∧
    J Set.univ = 1 ∧
    (∀ i : ι, MeasurePreserving (fun x => x i) J (M i).μ) ∧
    MeasurePreserving (multipleTransformation M) J J

def multipleJoiningSystem {ι : Type w} (M : ι → MeasurableSystem.{u})
    (J : MultipleJoiningData M) : MeasurableSystem.{max u w} :=
  { X := (i : ι) → (M i).X
    measurableSpace := inferInstance
    μ := J
    T := multipleTransformation M }

def IsErgodicMultipleSelfJoining (M : MeasurableSystem.{u}) (k : ℕ)
    (J : MultipleJoiningData (fun _ : Fin k => M)) : Prop :=
  IsMultipleJoining (fun _ : Fin k => M) J ∧
    Chapter02.IsErgodic (multipleJoiningSystem (fun _ : Fin k => M) J)

def IsAutomorphism (M : MeasurableSystem.{u}) (φ : M.X → M.X) : Prop :=
  ∃ ψ : M.X → M.X, Chapter01.IsFactorMap M M φ ∧ Chapter01.IsFactorMap M M ψ ∧
    Function.LeftInverse ψ φ ∧ Function.RightInverse ψ φ

def IsIntegerPowerTransformation (M : MeasurableSystem.{u}) (φ : M.X → M.X) : Prop :=
  ∃ inv : M.X → M.X, Function.LeftInverse inv M.T ∧ Function.RightInverse inv M.T ∧
    ((∃ n : ℕ, φ = M.T^[n]) ∨ ∃ n : ℕ, φ = inv^[n])

def IsGraphJoining (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (J : JoiningData M N) : Prop :=
  IsJoining M N J ∧ ∃ φ : M.X → N.X, Chapter01.IsFactorMap M N φ ∧
    J.measure {p | p.2 ≠ φ p.1} = 0

def IsIsomorphismGraphJoining (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (J : JoiningData M N) : Prop :=
  IsJoining M N J ∧ ∃ φ : M.X → N.X, ∃ ψ : N.X → M.X,
    Chapter01.IsFactorMap M N φ ∧ Chapter01.IsFactorMap N M ψ ∧
      Function.LeftInverse ψ φ ∧ Function.RightInverse ψ φ ∧
      J.measure {p | p.2 ≠ φ p.1} = 0

def IsOffDiagonalJoining (M : MeasurableSystem.{u}) (k : ℕ)
    (J : MultipleJoiningData (fun _ : Fin (k + 1) => M)) : Prop :=
  IsMultipleJoining (fun _ : Fin (k + 1) => M) J ∧
    ∃ φ : Fin (k + 1) → M.X → M.X, (∀ i, IsAutomorphism M (φ i)) ∧
      φ 0 = id ∧
      ∀ A : Fin (k + 1) → Set M.X, (∀ i, MeasurableSet (A i)) →
        J {x | ∀ i, x i ∈ A i} = M.μ (⋂ i, (φ i) ⁻¹' A i)

def IsPOODJoining (M : MeasurableSystem.{u}) (k : ℕ)
    (J : MultipleJoiningData (fun _ : Fin k => M)) : Prop :=
  IsMultipleJoining (fun _ : Fin k => M) J ∧
    ∃ blocks : Finset (Set (Fin k)), blocks.Nonempty ∧
      ⋃₀ (blocks : Set (Set (Fin k))) = Set.univ ∧
      (∀ b ∈ blocks, ∀ c ∈ blocks, b ≠ c → Disjoint b c) ∧
      (∀ b ∈ blocks, b.Nonempty) ∧
      ∃ φ : Fin k → M.X → M.X, (∀ i, IsAutomorphism M (φ i)) ∧
        ∀ A : Fin k → Set M.X, (∀ i, MeasurableSet (A i)) →
          J {x | ∀ i, x i ∈ A i} =
            blocks.prod (fun b => M.μ (⋂ i : Fin k,
              if i ∈ b then (φ i) ⁻¹' A i else Set.univ))

def IsKSimple (M : MeasurableSystem.{u}) (k : ℕ) : Prop :=
  Chapter02.IsErgodic M ∧ 2 ≤ k ∧ ∀ J : MultipleJoiningData (fun _ : Fin k => M),
    IsErgodicMultipleSelfJoining M k J → IsPOODJoining M k J

def IsSimpleSystem (M : MeasurableSystem.{u}) : Prop :=
  ∀ k : ℕ, 2 ≤ k → IsKSimple M k

def HasMinimalSelfJoiningsOfOrder (M : MeasurableSystem.{u}) (k : ℕ) : Prop :=
  IsKSimple M k ∧
    ∀ φ : M.X → M.X, IsAutomorphism M φ → IsIntegerPowerTransformation M φ

def IsRelativelyIndependentJoining
  (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (Z : MeasurableSystem.{w})
    (π : M.X → Z.X) (φ : N.X → Z.X) (J : JoiningData M N) : Prop :=
    Chapter01.IsFactorMap M Z π ∧ Chapter01.IsFactorMap N Z φ ∧ IsJoining M N J ∧
    ∃ μz : Z.X → Measure M.X, ∃ νz : Z.X → Measure N.X,
      (∀ A : Set M.X, MeasurableSet A → Measurable fun z => μz z A) ∧
      (∀ B : Set N.X, MeasurableSet B → Measurable fun z => νz z B) ∧
      (∀ᵐ z ∂Z.μ, MeasureTheory.IsProbabilityMeasure (μz z) ∧
        MeasureTheory.IsProbabilityMeasure (νz z)) ∧
      (∀ A : Set M.X, MeasurableSet A → M.μ A = ∫⁻ z, μz z A ∂Z.μ) ∧
      (∀ B : Set N.X, MeasurableSet B → N.μ B = ∫⁻ z, νz z B ∂Z.μ) ∧
      (∀ᵐ z ∂Z.μ, μz z (π ⁻¹' {z}) = 1 ∧ νz z (φ ⁻¹' {z}) = 1) ∧
      ∀ A : Set M.X, ∀ B : Set N.X, MeasurableSet A → MeasurableSet B →
        J.measure {p | p.1 ∈ A ∧ p.2 ∈ B} = ∫⁻ z, μz z A * νz z B ∂Z.μ

def IsConditionalProductMeasure {ι : Type w} [Fintype ι]
    (M : ι → MeasurableSystem.{u}) (Y : ι → MeasurableSystem.{v})
    (π : ∀ i : ι, (M i).X → (Y i).X)
    (ξ : MultipleJoiningData Y) (J : MultipleJoiningData M) : Prop :=
  (∀ i, Chapter01.IsFactorMap (M i) (Y i) (π i)) ∧
    IsMultipleJoining Y ξ ∧ IsMultipleJoining M J ∧
    ∃ K : ∀ i : ι, (Y i).X → Measure (M i).X,
      (∀ i, ∀ A : Set (M i).X, MeasurableSet A →
        Measurable fun y => K i y A) ∧
      (∀ i, ∀ᵐ y ∂(Y i).μ,
        MeasureTheory.IsProbabilityMeasure (K i y) ∧
          K i y ((π i) ⁻¹' {y}) = 1) ∧
      (∀ i, ∀ A : Set (M i).X, MeasurableSet A →
        (M i).μ A = ∫⁻ y, K i y A ∂(Y i).μ) ∧
      ∀ A : (i : ι) → Set (M i).X, (∀ i, MeasurableSet (A i)) →
        J {x | ∀ i, x i ∈ A i} = ∫⁻ y, ∏ i, K i (y i) (A i) ∂ξ

/-- The relatively independent self-product `J ×_N J` used in Lemma 8.3.1. -/
def IsRelativelyIndependentSelfProductOverRight
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (J : JoiningData M N) (K : Measure ((M.X × N.X) × M.X)) : Prop :=
  IsJoining M N J ∧ K Set.univ = 1 ∧
    MeasurePreserving (fun p : (M.X × N.X) × M.X => p.1) K J.measure ∧
    MeasurePreserving (fun p : (M.X × N.X) × M.X => (p.2, p.1.2)) K
      J.measure ∧
    ∃ μy : N.X → Measure M.X,
      (∀ A : Set M.X, MeasurableSet A → Measurable fun y => μy y A) ∧
      (∀ᵐ y ∂N.μ, MeasureTheory.IsProbabilityMeasure (μy y)) ∧
      (∀ A : Set M.X, ∀ B : Set N.X, MeasurableSet A → MeasurableSet B →
        J.measure {p | p.1 ∈ A ∧ p.2 ∈ B} = ∫⁻ y in B, μy y A ∂N.μ) ∧
      ∀ A C : Set M.X, ∀ B : Set N.X,
        MeasurableSet A → MeasurableSet B → MeasurableSet C →
        K {p | p.1.1 ∈ A ∧ p.1.2 ∈ B ∧ p.2 ∈ C} =
          ∫⁻ y in B, μy y A * μy y C ∂N.μ

def HasPairwiseIndependentNonproductTripleSelfJoining
    (M : MeasurableSystem.{u}) : Prop :=
  measureEntropy M = 0 ∧
    ∃ J : MultipleJoiningData (fun _ : Fin 3 => M),
      IsMultipleJoining (fun _ : Fin 3 => M) J ∧
      (∀ i j : Fin 3, i ≠ j →
        MeasurePreserving (fun x => (x i, x j)) J (M.μ.prod M.μ)) ∧
      ∃ A : Fin 3 → Set M.X, (∀ i, MeasurableSet (A i)) ∧
        J {x | ∀ i, x i ∈ A i} ≠ ∏ i, M.μ (A i)

/-! ## The common factor determined by a joining -/

abbrev SubSigmaAlgebra (M : MeasurableSystem.{u}) := Set (Set M.X)

def IsInvariantSubSigmaAlgebra (M : MeasurableSystem.{u})
    (𝒜 : SubSigmaAlgebra M) : Prop :=
  Chapter00.IsSigmaAlgebraFamily 𝒜 ∧ 𝒜 ⊆ M.𝓧 ∧
    (∀ A ∈ 𝒜, M.T ⁻¹' A ∈ 𝒜)

def cylinderLeft {M : MeasurableSystem.{u}} {N : MeasurableSystem.{v}}
    (A : Set M.X) : Set (M.X × N.X) := {p | p.1 ∈ A}
def cylinderRight {M : MeasurableSystem.{u}} {N : MeasurableSystem.{v}}
    (B : Set N.X) : Set (M.X × N.X) := {p | p.2 ∈ B}

def ModEqUnderJoining (J : JoiningData M N) (A : Set M.X) (B : Set N.X) : Prop :=
  J.measure ((cylinderLeft A \ cylinderRight B) ∪
    (cylinderRight B \ cylinderLeft A)) = 0

def ModEqUnderMeasure {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (A B : Set α) : Prop :=
  μ ((A \ B) ∪ (B \ A)) = 0

def IsCommonFactorDeterminedByJoining
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (J : JoiningData M N) (𝒜 : SubSigmaAlgebra M) (𝒝 : SubSigmaAlgebra N) : Prop :=
  IsJoining M N J ∧
    𝒜 = {A | MeasurableSet A ∧ ∃ B : Set N.X, MeasurableSet B ∧ ModEqUnderJoining J A B} ∧
    𝒝 = {B | MeasurableSet B ∧ ∃ A : Set M.X, MeasurableSet A ∧ ModEqUnderJoining J A B} ∧
    IsInvariantSubSigmaAlgebra M 𝒜 ∧ IsInvariantSubSigmaAlgebra N 𝒝 ∧
    ∃ Z : MeasurableSystem.{max u v}, ∃ π : M.X → Z.X, ∃ φ : N.X → Z.X,
      Chapter01.IsFactorMap M Z π ∧ Chapter01.IsFactorMap N Z φ ∧
      (∀ A ∈ 𝒜, ∃ C : Set Z.X, MeasurableSet C ∧ ModEqUnderMeasure M.μ A (π ⁻¹' C)) ∧
      (∀ B ∈ 𝒝, ∃ C : Set Z.X, MeasurableSet C ∧ ModEqUnderMeasure N.μ B (φ ⁻¹' C))

abbrev HasDiscreteSpectrumMeasureSystem (M : MeasurableSystem.{u}) : Prop :=
  Chapter07.hasDiscreteSpectrum M

def SpectrallyIsomorphic (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧ Chapter01.IsMeasurePreservingSystem N ∧
    ∃ Φ : (M.X → ℂ) → (N.X → ℂ), ∃ Ψ : (N.X → ℂ) → (M.X → ℂ),
      (∀ f, M.lpMember 2 f → N.lpMember 2 (Φ f)) ∧
      (∀ g, N.lpMember 2 g → M.lpMember 2 (Ψ g)) ∧
      (∀ f f', M.lpMember 2 f → M.lpMember 2 f' → f =ᵐ[M.μ] f' →
        Φ f =ᵐ[N.μ] Φ f') ∧
      (∀ g g', N.lpMember 2 g → N.lpMember 2 g' → g =ᵐ[N.μ] g' →
        Ψ g =ᵐ[M.μ] Ψ g') ∧
      (∀ f g, M.lpMember 2 f → M.lpMember 2 g → ∀ a b : ℂ,
        Φ (fun x => a * f x + b * g x) =ᵐ[N.μ]
          fun y => a * Φ f y + b * Φ g y) ∧
      (∀ f g, M.lpMember 2 f → M.lpMember 2 g →
        M.integral (fun x => f x * starRingEnd ℂ (g x)) =
          N.integral (fun y => Φ f y * starRingEnd ℂ (Φ g y))) ∧
      (∀ f, M.lpMember 2 f →
        Φ (fun x => f (M.T x)) =ᵐ[N.μ] fun y => Φ f (N.T y)) ∧
      (∀ f, M.lpMember 2 f → Ψ (Φ f) =ᵐ[M.μ] f) ∧
      ∀ g, N.lpMember 2 g → Φ (Ψ g) =ᵐ[N.μ] g

/-! ## Disjointness -/

def IsDisjoint (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
    Chapter01.IsMeasurePreservingSystem N ∧
    ∀ J : JoiningData M N, IsJoining M N J → IsProductJoining M N J

def IsJoiningOver
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (Z : MeasurableSystem.{w})
    (π : M.X → Z.X) (φ : N.X → Z.X) (J : JoiningData M N) : Prop :=
  IsJoining M N J ∧ J.measure {p | π p.1 ≠ φ p.2} = 0

def IsRelativelyDisjointOver
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (Z : MeasurableSystem.{w})
    (π : M.X → Z.X) (φ : N.X → Z.X) : Prop :=
  Chapter01.IsFactorMap M Z π ∧ Chapter01.IsFactorMap N Z φ ∧
    ∀ J : JoiningData M N, IsJoiningOver M N Z π φ J →
      IsRelativelyIndependentJoining M N Z π φ J

def IsNontrivialSystem (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
    ∃ A : Set M.X, MeasurableSet A ∧ M.μ A ≠ 0 ∧ M.μ A ≠ 1

def IsIdentitySystem (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧ ∀ x : M.X, M.T x = x

def IsErgodicExtension (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (π : M.X → N.X) : Prop :=
  Chapter01.IsFactorMap M N π ∧
    ∀ f : M.X → ℂ, MeasureTheory.AEStronglyMeasurable f M.μ →
      (fun x => f (M.T x)) =ᵐ[M.μ] f →
      ∃ g : N.X → ℂ, MeasureTheory.AEStronglyMeasurable g N.μ ∧
        f =ᵐ[M.μ] g ∘ π

def measureZIterate (M : MeasurableSystem.{u}) (inv : M.X -> M.X)
    (n : ℤ) : M.X -> M.X :=
  if 0 ≤ n then M.T^[n.toNat] else inv^[n.natAbs]

def IsFactorDisintegrationKernel
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (π : M.X -> N.X) (μy : N.X -> Measure M.X) : Prop :=
  (∀ A : Set M.X, MeasurableSet A -> Measurable fun y => μy y A) ∧
  (∀ᵐ y ∂N.μ, MeasureTheory.IsProbabilityMeasure (μy y) ∧
    μy y (π ⁻¹' {y}) = 1) ∧
  ∀ A : Set M.X, MeasurableSet A -> M.μ A = ∫⁻ y, μy y A ∂N.μ

def IsRelativelyAlmostPeriodicFunction
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (π : M.X -> N.X) (inv : M.X -> M.X)
    (μy : N.X -> Measure M.X) (f : M.X -> ℂ) : Prop :=
  M.lpMember 2 f ∧ ∀ ε : ℝ, 0 < ε ->
    ∃ r : ℕ, 0 < r ∧ ∃ g : Fin r -> M.X -> ℂ,
      (∀ i, M.lpMember 2 (g i)) ∧
      ∀ n : ℤ, ∀ᵐ y ∂N.μ, ∃ i : Fin r,
        MeasureTheory.eLpNorm
          (fun x => f (measureZIterate M inv n x) - g i x) 2 (μy y) <
            ENNReal.ofReal ε

def IsCompactMeasureExtension (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (π : M.X → N.X) : Prop :=
  Chapter01.IsFactorMap M N π ∧
    ∃ inv : M.X -> M.X,
      Chapter01.IsMeasurePreservingMap M.𝓧 M.μ M.𝓧 M.μ inv ∧
      Function.LeftInverse inv M.T ∧ Function.RightInverse inv M.T ∧
    ∃ μy : N.X -> Measure M.X, IsFactorDisintegrationKernel M N π μy ∧
      ∀ f : M.X -> ℂ, M.lpMember 2 f -> ∀ ε : ℝ, 0 < ε ->
        ∃ g : M.X -> ℂ,
          IsRelativelyAlmostPeriodicFunction M N π inv μy g ∧
          MeasureTheory.eLpNorm (fun x => f x - g x) 2 M.μ < ENNReal.ofReal ε

def IsMeasureSpaceFactorMap (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (π : M.X → N.X) : Prop :=
  MeasureTheory.IsProbabilityMeasure M.μ ∧ MeasureTheory.IsProbabilityMeasure N.μ ∧
    MeasurePreserving π M.μ N.μ

def IsRelativelyIndependentMeasureSpaceJoining
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (Z : MeasurableSystem.{w}) (π : M.X → Z.X) (φ : N.X → Z.X)
    (J : JoiningData M N) : Prop :=
  IsMeasureSpaceFactorMap M Z π ∧ IsMeasureSpaceFactorMap N Z φ ∧
    IsMeasureSpaceJoining M N J ∧
    ∃ μz : Z.X → Measure M.X, ∃ νz : Z.X → Measure N.X,
      (∀ A : Set M.X, MeasurableSet A → Measurable fun z => μz z A) ∧
      (∀ B : Set N.X, MeasurableSet B → Measurable fun z => νz z B) ∧
      (∀ᵐ z ∂Z.μ, MeasureTheory.IsProbabilityMeasure (μz z) ∧
        MeasureTheory.IsProbabilityMeasure (νz z) ∧
        μz z (π ⁻¹' {z}) = 1 ∧ νz z (φ ⁻¹' {z}) = 1) ∧
      (∀ A : Set M.X, MeasurableSet A → M.μ A = ∫⁻ z, μz z A ∂Z.μ) ∧
      (∀ B : Set N.X, MeasurableSet B → N.μ B = ∫⁻ z, νz z B ∂Z.μ) ∧
      ∀ A : Set M.X, ∀ B : Set N.X, MeasurableSet A → MeasurableSet B →
        J.measure {p | p.1 ∈ A ∧ p.2 ∈ B} = ∫⁻ z, μz z A * νz z B ∂Z.μ

def IsMaximalCommonMeasureFactorDeterminedByJoining
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (J : JoiningData M N) (Z : MeasurableSystem.{w})
    (π : M.X → Z.X) (φ : N.X → Z.X) : Prop :=
  Chapter04.IsLebesgueProbabilitySpace Z.toProbabilitySpace ∧
    IsMeasureSpaceFactorMap M Z π ∧ IsMeasureSpaceFactorMap N Z φ ∧
    (∀ A : Set M.X, MeasurableSet A →
      ((∃ B : Set N.X, MeasurableSet B ∧ ModEqUnderJoining J A B) ↔
        ∃ C : Set Z.X, MeasurableSet C ∧
          ModEqUnderMeasure M.μ A (π ⁻¹' C))) ∧
    ∀ B : Set N.X, MeasurableSet B →
      ((∃ A : Set M.X, MeasurableSet A ∧ ModEqUnderJoining J A B) ↔
        ∃ C : Set Z.X, MeasurableSet C ∧
          ModEqUnderMeasure N.μ B (φ ⁻¹' C))

/-- Exact content of Theorem 8.4.8, including its measure-space statement and
the final specialization to a joining of measure-preserving systems. -/
def IsRelativeIndependentTowerStatement : Prop :=
  ∀ M : MeasurableSystem.{u}, ∀ N : MeasurableSystem.{v}, ∀ J : JoiningData M N,
    Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace →
    Chapter04.IsLebesgueProbabilitySpace N.toProbabilitySpace →
    IsMeasureSpaceJoining M N J →
      ∃ μinf : Measure (ℤ → M.X), ∃ Jinf : JoiningData
        { X := ℤ → M.X, measurableSpace := inferInstance, μ := μinf,
          T := fun x n => x (n + 1) } N,
      ∃ Z : MeasurableSystem.{max u v},
      ∃ π : (ℤ → M.X) → Z.X, ∃ φ : N.X → Z.X,
      ∃ μy : N.X → Measure M.X,
        (∀ A : Set M.X, ∀ B : Set N.X, MeasurableSet A → MeasurableSet B →
          J.measure {p | p.1 ∈ A ∧ p.2 ∈ B} = ∫⁻ y in B, μy y A ∂N.μ) ∧
        (∀ F : Finset ℤ, ∀ A : ℤ → Set M.X, (∀ i ∈ F, MeasurableSet (A i)) →
          μinf {x | ∀ i ∈ F, x i ∈ A i} = ∫⁻ y, ∏ i ∈ F, μy y (A i) ∂N.μ) ∧
        (∀ F : Finset ℤ, ∀ A : ℤ → Set M.X, ∀ B : Set N.X,
          (∀ i ∈ F, MeasurableSet (A i)) → MeasurableSet B →
          Jinf.measure {p | (∀ i ∈ F, p.1 i ∈ A i) ∧ p.2 ∈ B} =
            ∫⁻ y in B, ∏ i ∈ F, μy y (A i) ∂N.μ) ∧
        MeasurePreserving (fun x : ℤ → M.X => x 0) μinf M.μ ∧
        IsMeasureSpaceJoining
          { X := ℤ → M.X, measurableSpace := inferInstance, μ := μinf,
            T := fun x n => x (n + 1) } N Jinf ∧
        MeasurePreserving (fun p : (ℤ → M.X) × N.X => (p.1 0, p.2))
          Jinf.measure J.measure ∧
        IsMaximalCommonMeasureFactorDeterminedByJoining
          { X := ℤ → M.X, measurableSpace := inferInstance, μ := μinf,
            T := fun x n => x (n + 1) } N Jinf Z π φ ∧
        IsRelativelyIndependentMeasureSpaceJoining
          { X := ℤ → M.X, measurableSpace := inferInstance, μ := μinf,
            T := fun x n => x (n + 1) } N Z π φ Jinf ∧
        (IsJoining M N J →
          IsJoining
            { X := ℤ → M.X, measurableSpace := inferInstance, μ := μinf,
              T := fun x n => x (n + 1) } N Jinf ∧
          Chapter01.IsFactorMap
            { X := ℤ → M.X, measurableSpace := inferInstance, μ := μinf,
              T := fun x n => x (n + 1) } Z π ∧
          Chapter01.IsFactorMap N Z φ ∧
          IsRelativelyIndependentJoining
            { X := ℤ → M.X, measurableSpace := inferInstance, μ := μinf,
              T := fun x n => x (n + 1) } N Z π φ Jinf)

def IsDistalMeasureSystem (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
  ∃ α : Ordinal.{0}, ∃ tower : Ordinal.{0} → MeasurableSystem.{u},
  ∃ factorMap : ∀ β γ, (tower γ).X → (tower β).X,
    {β : Ordinal.{0} | β < α}.Countable ∧
    Subsingleton (tower 0).X ∧ Chapter01.IsIsomorphicSystems M (tower α) ∧
    (∀ β γ, β ≤ γ -> γ ≤ α ->
      Chapter01.IsFactorMap (tower γ) (tower β) (factorMap β γ)) ∧
    (∀ β, β ≤ α -> factorMap β β = id) ∧
    (∀ β γ δ, β ≤ γ -> γ ≤ δ -> δ ≤ α ->
      factorMap β δ = factorMap β γ ∘ factorMap γ δ) ∧
    (∀ β : Ordinal.{0}, β < α →
      IsCompactMeasureExtension (tower (β + 1)) (tower β)
        (factorMap β (β + 1)) ∧
      ¬ Chapter01.IsIsomorphicSystems (tower (β + 1)) (tower β)) ∧
    ∀ limitOrd : Ordinal.{0}, limitOrd ≤ α → limitOrd ≠ 0 →
      (∀ γ : Ordinal.{0}, γ < limitOrd → γ + 1 < limitOrd) →
      MeasurableSpace.generateFrom
        {A : Set (tower limitOrd).X | ∃ β, β < limitOrd ∧
          ∃ B : Set (tower β).X,
            MeasurableSet B ∧ A = (factorMap β limitOrd) ⁻¹' B} =
        (tower limitOrd).measurableSpace

def IsRigidMeasureSystem (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
  ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ A : Set M.X, MeasurableSet A →
    Tendsto (fun k : ℕ => (M.μ (A ∩ (M.T^[n k]) ⁻¹' A)).toReal)
      atTop (nhds (M.μ A).toReal)

def IsMildMixingMeasureSystem (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧ Chapter02.IsMildMixing M

def IsZeroEntropyMeasureSystem (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧ measureEntropy M = 0

abbrev IsKMeasureSystem (M : MeasurableSystem.{u}) : Prop :=
  Chapter07.isMeasureKSystem M

def multipleRecurrenceAverage (M : MeasurableSystem.{u}) (k : ℕ)
    (A : Fin (k + 1) → Set M.X) (N : ℕ) : ℝ :=
  if N = 0 then 0 else (N : ℝ)⁻¹ * (Finset.range N).sum fun n : ℕ =>
    (M.μ (⋂ i : Fin (k + 1), (M.T^[n * i.val]) ⁻¹' A i)).toReal

def multipleMeasureProduct (M : MeasurableSystem.{u}) (k : ℕ)
    (A : Fin (k + 1) → Set M.X) : ℝ :=
  Finset.univ.prod fun i : Fin (k + 1) => (M.μ (A i)).toReal

/-! ## Möbius, Chowla and Sarnak -/

def mobiusFunction : ℕ → ℤ := ArithmeticFunction.moebius

def liouvilleFunction (n : ℕ) : ℤ :=
  if n = 0 then 0 else (-1 : ℤ) ^ n.primeFactorsList.length

def IsMobiusFunction (μ : ℕ → ℤ) : Prop :=
  μ = mobiusFunction

def IsLiouvilleFunction (liouville : ℕ → ℤ) : Prop :=
  liouville = liouvilleFunction

def IsSignedOneSidedSequence (z : ℕ → ℤ) : Prop :=
  ∀ n, z n = -1 ∨ z n = 0 ∨ z n = 1

def sequenceAverage (a : ℕ → ℂ) : ℕ → ℂ :=
  fun N => if N = 0 then 0 else (N : ℂ)⁻¹ *
    (Finset.range N).sum fun n => a (n + 1)

def asymptoticallyOrthogonal (a b : ℕ → ℂ) : Prop :=
  Tendsto (fun N : ℕ => sequenceAverage (fun n => a n * b n) N) atTop (nhds 0)

def IsSequenceRealizedBy (S : TopologicalSystem.{u}) (ξ : ℕ → ℂ) : Prop :=
  Chapter05.IsCompactTopologicalSystem S ∧ Nonempty (PseudoMetricSpace S.X) ∧
    ∃ x : S.X, ∃ f : S.X → ℂ, Continuous f ∧
      ∀ n : ℕ, ξ n = f ((S.T^[n]) x)

def IsZeroEntropySequence (ξ : ℕ → ℂ) : Prop :=
  ∃ S : TopologicalSystem.{0}, topologicalEntropy S = 0 ∧ IsSequenceRealizedBy S ξ

def ChowlaCondition (z : ℕ → ℤ) : Prop :=
  IsSignedOneSidedSequence z ∧
    ∀ r : ℕ, ∀ a : Fin r → ℕ, ∀ k : Fin (r + 1) → ℕ,
      (∀ i, k i = 1 ∨ k i = 2) → (∃ i, k i = 1) →
      (∀ i, 1 ≤ a i) → StrictMono a →
        Tendsto
          (fun N : ℕ => if N = 0 then 0 else (N : ℝ)⁻¹ *
            (Finset.range N).sum fun n : ℕ =>
              (((z (n + 1) ^ k 0) *
                (∏ i : Fin r, z (n + 1 + a i) ^ k i.succ) : ℤ) : ℝ))
          atTop (nhds 0)

def SarnakCondition (z : ℕ → ℤ) : Prop :=
  IsSignedOneSidedSequence z ∧
    ∀ ξ : ℕ → ℂ, IsZeroEntropySequence ξ →
      asymptoticallyOrthogonal (fun n => (z n : ℂ)) ξ

def ChowlaConjecture : Prop := ChowlaCondition mobiusFunction
def SarnakConjecture : Prop := SarnakCondition mobiusFunction

def PrimeNumberTheoremOrthogonality : Prop :=
  asymptoticallyOrthogonal (fun n => (mobiusFunction n : ℂ)) (fun _ => 1) ∧
    asymptoticallyOrthogonal (fun n => (liouvilleFunction n : ℂ)) (fun _ => 1)

def mobiusOrbitClosure : Set (ℕ → ℤ) :=
  closure (Set.range fun k : ℕ => fun n : ℕ => mobiusFunction (n + k + 1))

def IsMobiusOrbitClosureSystem (S : TopologicalSystem.{u}) : Prop :=
  Chapter05.IsCompactTopologicalSystem S ∧
    ∃ e : S.X ≃ₜ {x : ℕ → ℤ // x ∈ mobiusOrbitClosure},
      (∀ x : S.X, ∀ n : ℕ, (e (S.T x)).val n = (e x).val (n + 1)) ∧
      ∃ z0 : S.X, (∀ n : ℕ, (e z0).val n = 0) ∧ S.T z0 = z0

def IsProximalTopologicalSystem (S : TopologicalSystem.{u}) : Prop :=
  ∀ x y : S.X, ∃ z : S.X, (z, z) ∈ closure (Set.range fun n : ℕ =>
    ((S.T^[n]) x, (S.T^[n]) y))

def HasUniqueFixedMinimalSubset (S : TopologicalSystem.{u}) : Prop :=
  ∃ z : S.X, S.T z = z ∧ ∀ K : Set S.X, Chapter05.IsMinimalSet S K → K = {z}

def HasNontrivialKroneckerJoiningForInvariantMeasure
    (S : TopologicalSystem.{u}) (μ : MeasureOn S.X) : Prop :=
  ∃ M : MeasurableSystem.{u},
    Chapter01.IsMeasurePreservingSystem M ∧
    Chapter07.Section12.IsTopologicalMeasureModel S μ M ∧
    ¬ Chapter02.IsWeakMixing M ∧
    ∃ K : MeasurableSystem.{u}, HasDiscreteSpectrumMeasureSystem K ∧
      IsNontrivialSystem K ∧ ¬ IsDisjoint M K

def MobiusOrbitSystemEntropyStatement (Xμ : TopologicalSystem.{u}) : Prop :=
  IsMobiusOrbitClosureSystem Xμ →
    ((6 / Real.pi ^ 2 * Real.log 2 : ℝ) : EReal) ≤ topologicalEntropy Xμ ∧
      topologicalEntropy Xμ ≤ ((6 / Real.pi ^ 2 * Real.log 3 : ℝ) : EReal) ∧
      IsProximalTopologicalSystem Xμ ∧ HasUniqueFixedMinimalSubset Xμ ∧
      ∀ μ : MeasureOn Xμ.X, IsInvariantMeasure Xμ μ →
        (∀ z : Xμ.X, Xμ.T z = z -> μ ≠ Chapter06.diracMeasure z) ->
        HasNontrivialKroneckerJoiningForInvariantMeasure Xμ μ

def DavenportEstimate : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
    ∀ z : ℂ, ‖z‖ = 1 →
      ‖(Finset.range N).sum fun n : ℕ => z ^ (n + 1) * (mobiusFunction (n + 1) : ℂ)‖ ≤
        C * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) A

def SarnakMeasureTheoremStatement (M : MeasurableSystem.{u}) (f : M.X → ℂ) : Prop :=
  Chapter01.IsMeasurePreservingSystem M →
    Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace →
    M.lpMember 1 f → ∃ E : Set M.X, M.μ Eᶜ = 0 ∧ ∀ x ∈ E,
      Tendsto
        (fun N : ℕ => if N = 0 then 0 else (N : ℂ)⁻¹ *
          (Finset.range N).sum fun n : ℕ =>
            f ((M.T^[n + 1]) x) * (mobiusFunction (n + 1) : ℂ))
        atTop (nhds 0)

abbrev SymbolicSequence := ℤ → ℤ
abbrev SupportSequence := ℤ → Bool

def IsSignedSymbolicSequence (z : SymbolicSequence) : Prop :=
  ∀ n, z n = -1 ∨ z n = 0 ∨ z n = 1

def squareProjection (z : SymbolicSequence) : SymbolicSequence := fun n => z n ^ 2
def squareSupportProjection (z : SymbolicSequence) : SupportSequence :=
  fun n => decide (z n ≠ 0)
def symbolicShift (z : ℤ → α) (n : ℕ) : ℤ → α :=
  fun i => z (i + n)

def IsShiftInvariantProbabilityMeasure {A : Type u} [MeasurableSpace A]
    (μ : Measure (ℤ → A)) : Prop :=
  μ Set.univ = 1 ∧
    MeasurePreserving (fun z => symbolicShift z 1) μ μ

def IsCylinderSet {A : Type u} (C : Set (ℤ → A)) : Prop :=
  ∃ F : Finset ℤ, ∃ pattern : ℤ → A, C = {x | ∀ i ∈ F, x i = pattern i}

def IsQuasiGenericFor {A : Type u} [DecidableEq A] [MeasurableSpace A]
    (z : ℤ → A) (μ : Measure (ℤ → A)) (N : ℕ → ℕ) : Prop :=
  StrictMono N ∧ IsShiftInvariantProbabilityMeasure μ ∧
    ∀ C : Set (ℤ → A), IsCylinderSet C →
      Tendsto (fun k : ℕ => if N k = 0 then 0 else
        (N k : ENNReal)⁻¹ * ((Finset.range (N k)).filter
          (fun n => symbolicShift z (n + 1) ∈ C)).card) atTop (nhds (μ C))

def IsRelativelyIndependentLift (ν : Measure SupportSequence)
    (νhat : Measure SymbolicSequence) : Prop :=
  IsShiftInvariantProbabilityMeasure ν ∧
    IsShiftInvariantProbabilityMeasure νhat ∧
    νhat {z | IsSignedSymbolicSequence z} = 1 ∧
    MeasurePreserving squareSupportProjection νhat ν ∧
    ∀ F : Finset ℤ, ∀ pattern : ℤ → ℤ,
      (∀ i ∈ F, pattern i = -1 ∨ pattern i = 0 ∨ pattern i = 1) →
      νhat {z | ∀ i ∈ F, z i = pattern i} =
        (2 : ENNReal)⁻¹ ^ (F.filter fun i => pattern i ≠ 0).card *
          ν {b | ∀ i ∈ F, b i = decide (pattern i ≠ 0)}

theorem exists_relativelyIndependentLift (ν : Measure SupportSequence)
    (hν : IsShiftInvariantProbabilityMeasure ν) :
    ∃ νhat : Measure SymbolicSequence, IsRelativelyIndependentLift ν νhat := by
  sorry

noncomputable def RelativelyIndependentLift (ν : Measure SupportSequence) :
    Measure SymbolicSequence :=
  if hν : IsShiftInvariantProbabilityMeasure ν then
    Classical.choose (exists_relativelyIndependentLift ν hν)
  else 0

theorem relativelyIndependentLift_specification (ν : Measure SupportSequence)
    (hν : IsShiftInvariantProbabilityMeasure ν) :
    IsRelativelyIndependentLift ν (RelativelyIndependentLift ν) :=
  by
    rw [RelativelyIndependentLift, dif_pos hν]
    exact Classical.choose_spec (exists_relativelyIndependentLift ν hν)

def CoordinateFunction (z : SymbolicSequence) : ℤ := z 0

def symbolicMoment (ρ : Measure SymbolicSequence) (r : ℕ)
    (a : Fin r → ℕ) (k : Fin (r + 1) → ℕ) : ℝ :=
  ∫ z, (((z 0 ^ k 0) * ∏ i : Fin r, z (a i) ^ k i.succ : ℤ) : ℝ) ∂ρ

def supportMoment (ν : Measure SupportSequence) (r : ℕ) (a : Fin r → ℕ) : ℝ :=
  ∫ z, ((if z 0 then 1 else 0) * ∏ i : Fin r, if z (a i) then 1 else 0 : ℝ) ∂ν

def ChowlaConditionTwoSided (z : SymbolicSequence) : Prop :=
  IsSignedSymbolicSequence z ∧ ChowlaCondition (fun n => z n)

def ChowlaQuasiGenericEquivalence (z : SymbolicSequence) : Prop :=
  IsSignedSymbolicSequence z → ∀ N : ℕ → ℕ, ∀ ν : Measure SupportSequence,
    IsQuasiGenericFor (squareSupportProjection z) ν N →
      (IsQuasiGenericFor z (RelativelyIndependentLift ν) N ↔
        ∀ r : ℕ, ∀ a : Fin r → ℕ, ∀ k : Fin (r + 1) → ℕ,
          (∀ i, k i = 1 ∨ k i = 2) → (∃ i, k i = 1) →
          (∀ i, 1 ≤ a i) → StrictMono a →
          Tendsto
            (fun j : ℕ => if N j = 0 then 0 else (N j : ℝ)⁻¹ *
              (Finset.range (N j)).sum fun n : ℕ =>
                (((z (n + 1) ^ k 0) *
                  ∏ i : Fin r, z (n + 1 + a i) ^ k i.succ : ℤ) : ℝ))
            atTop (nhds 0))

def QuasiGenericMeasures {A : Type u} [DecidableEq A] [MeasurableSpace A] (z : ℤ → A) :
    Set (Measure (ℤ → A)) :=
  {ν | ∃ N : ℕ → ℕ, IsQuasiGenericFor z ν N}

def ChowlaQuasiGenericRemark (z : SymbolicSequence) : Prop :=
  ChowlaConditionTwoSided z ↔
    QuasiGenericMeasures z =
      { νhat | ∃ ν ∈ QuasiGenericMeasures (squareSupportProjection z),
        νhat = RelativelyIndependentLift ν }

abbrev SignSequence := ℤ → Bool

def IsFairBernoulliSignMeasure (β : Measure SignSequence) : Prop :=
  IsShiftInvariantProbabilityMeasure β ∧ ∀ F : Finset ℤ, ∀ pattern : ℤ → Bool,
    β {s | ∀ i ∈ F, s i = pattern i} = (2 : ENNReal)⁻¹ ^ F.card

def supportTimesSign (w : SupportSequence × SignSequence) : SymbolicSequence :=
  fun i => if w.1 i then if w.2 i then 1 else -1 else 0

def RelativeIndependentLiftFactorStatement (ν : Measure SupportSequence) : Prop :=
  IsShiftInvariantProbabilityMeasure ν →
    ∃ β : Measure SignSequence, IsFairBernoulliSignMeasure β ∧
      MeasurePreserving supportTimesSign (ν.prod β) (RelativelyIndependentLift ν) ∧
      ∀ w, supportTimesSign (symbolicShift w.1 1, symbolicShift w.2 1) =
        symbolicShift (supportTimesSign w) 1

def IsRelativelyKExtension (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (π : M.X → N.X) : Prop :=
  Chapter01.IsFactorMap M N π ∧ ∀ P : MeasurableSystem.{u}, ∀ ρ : M.X → P.X,
    ∀ σ : P.X → N.X, Chapter01.IsFactorMap M P ρ →
      Chapter01.IsFactorMap P N σ → π = σ ∘ ρ →
      IsNontrivialSystem P → measureEntropy N < measureEntropy P

def RelativeKOrTrivialExtensionStatement (ν : Measure SupportSequence) : Prop :=
  IsShiftInvariantProbabilityMeasure ν →
    let νhat := RelativelyIndependentLift ν
    (∃ E : Set SymbolicSequence, νhat Eᶜ = 0 ∧
      ∀ z w : SymbolicSequence, z ∈ E → w ∈ E →
        squareSupportProjection z = squareSupportProjection w → z = w) ∨
    (∃ M N : MeasurableSystem.{0}, ∃ eM : M.X ≃ SymbolicSequence,
      ∃ eN : N.X ≃ SupportSequence, ∃ π : M.X → N.X,
        @Measurable M.X SymbolicSequence M.measurableSpace inferInstance eM ∧
        @Measurable SymbolicSequence M.X inferInstance M.measurableSpace eM.symm ∧
        @Measurable N.X SupportSequence N.measurableSpace inferInstance eN ∧
        @Measurable SupportSequence N.X inferInstance N.measurableSpace eN.symm ∧
        (∀ x, eM (M.T x) = symbolicShift (eM x) 1) ∧
        (∀ y, eN (N.T y) = symbolicShift (eN y) 1) ∧
        π = (fun x => eN.symm (squareSupportProjection (eM x))) ∧
        (∀ A : Set SymbolicSequence, M.μ (eM ⁻¹' A) = νhat A) ∧
        (∀ B : Set SupportSequence, N.μ (eN ⁻¹' B) = ν B) ∧
        IsRelativelyKExtension M N π)

def ConditionalExpectationCoordinateZeroStatement (ν : Measure SupportSequence) : Prop :=
  IsShiftInvariantProbabilityMeasure ν →
    let νhat := RelativelyIndependentLift ν
    ∀ B : Set SupportSequence, MeasurableSet B →
      νhat {z | squareSupportProjection z ∈ B ∧ z 0 = 1} =
        νhat {z | squareSupportProjection z ∈ B ∧ z 0 = -1}

def IsTopologicallyQuasiGenericFor (S : TopologicalSystem.{u}) (x : S.X)
    (κ : MeasureOn S.X) (N : ℕ → ℕ) : Prop :=
  IsInvariantMeasure S κ ∧ StrictMono N ∧
    ∀ f : S.X → ℂ, Continuous f →
      Tendsto (fun j => if N j = 0 then 0 else (N j : ℂ)⁻¹ *
        (Finset.range (N j)).sum fun n => f ((S.T^[n + 1]) x)) atTop
          (nhds (κ.integral f))

def IsJointOrbitQuasiGenericFor (S : TopologicalSystem.{u}) (x : S.X)
    (z : SymbolicSequence) (ρ : MeasureOn (S.X × SymbolicSequence))
    (N : ℕ → ℕ) : Prop :=
  Chapter05.IsTopologicalSystem S ∧ Chapter06.IsProbabilityBorelMeasure ρ ∧
    Chapter06.pushForwardMeasure
      (fun p : S.X × SymbolicSequence => (S.T p.1, symbolicShift p.2 1)) ρ = ρ ∧
    StrictMono N ∧ ∀ f : S.X × SymbolicSequence → ℂ, Continuous f →
      Tendsto (fun j => if N j = 0 then 0 else (N j : ℂ)⁻¹ *
        (Finset.range (N j)).sum fun n =>
          f ((S.T^[n + 1]) x, symbolicShift z (n + 1)))
        atTop (nhds (ρ.integral f))

def ZeroEntropyJoiningRelativeIndependenceStatement : Prop :=
  ∀ S : TopologicalSystem.{u}, Chapter05.IsCompactTopologicalSystem S →
  topologicalEntropy S = 0 → ∀ x : S.X,
  ∀ ν : Measure SupportSequence, ∀ z : SymbolicSequence, ∀ N : ℕ → ℕ,
    IsShiftInvariantProbabilityMeasure ν → IsSignedSymbolicSequence z →
    IsQuasiGenericFor z (RelativelyIndependentLift ν) N →
    ∀ ρ : MeasureOn (S.X × SymbolicSequence),
      IsJointOrbitQuasiGenericFor S x z ρ N →
      ∃ κ : MeasureOn S.X, IsTopologicallyQuasiGenericFor S x κ N ∧
        (∀ A : Set S.X, @MeasurableSet S.X (borel S.X) A →
          ρ.measure {p | p.1 ∈ A} = κ.measure A) ∧
        (∀ B : Set SymbolicSequence, MeasurableSet B →
          ρ.measure {p | p.2 ∈ B} = RelativelyIndependentLift ν B) ∧
        ∃ κu : SupportSequence → @Measure S.X (borel S.X),
        ∃ Lu : SupportSequence → Measure SymbolicSequence,
          (∀ A : Set S.X, @MeasurableSet S.X (borel S.X) A →
            Measurable fun u => κu u A) ∧
          (∀ B : Set SymbolicSequence, MeasurableSet B → Measurable fun u => Lu u B) ∧
          (∀ᵐ u ∂ν, MeasureTheory.IsProbabilityMeasure (κu u) ∧
            MeasureTheory.IsProbabilityMeasure (Lu u) ∧
            Lu u {z | squareSupportProjection z = u} = 1) ∧
          (∀ A : Set S.X, @MeasurableSet S.X (borel S.X) A →
            κ.measure A = ∫⁻ u, κu u A ∂ν) ∧
          (∀ B : Set SymbolicSequence, MeasurableSet B →
            RelativelyIndependentLift ν B = ∫⁻ u, Lu u B ∂ν) ∧
          ∀ A : Set S.X, ∀ B : Set SymbolicSequence,
            @MeasurableSet S.X (borel S.X) A → MeasurableSet B →
              ρ.measure {p | p.1 ∈ A ∧ p.2 ∈ B} =
                ∫⁻ u, κu u A * Lu u B ∂ν

def ZeroEntropyJoiningOrthogonalityStatement (z : SymbolicSequence) : Prop :=
  IsSignedSymbolicSequence z ∧
    ∀ ξ : ℕ → ℂ, IsZeroEntropySequence ξ →
      asymptoticallyOrthogonal (fun n => (z n : ℂ)) ξ

end Chapter08
