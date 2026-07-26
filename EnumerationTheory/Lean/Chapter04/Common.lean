import Chapter03.Common

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter04

universe u v w

abbrev SetFamily (X : Type u) := Chapter00.SetFamily X
abbrev ProbabilitySpace := Chapter01.ProbabilitySpaceData
abbrev System := Chapter01.MeasurePreservingSystemData

structure MeasurableSpaceData where
  X : Type u
  measurableSpace : MeasurableSpace X

attribute [instance] MeasurableSpaceData.measurableSpace

def MeasurableSpaceData.sets (M : MeasurableSpaceData.{u}) : SetFamily M.X :=
  {A | MeasurableSet A}

def IsMeasurableSpaceData (M : MeasurableSpaceData.{u}) : Prop :=
  M.sets = {A | MeasurableSet A}

def IsMeasurableMap (M : MeasurableSpaceData.{u}) (N : MeasurableSpaceData.{v})
    (f : M.X -> N.X) : Prop :=
  ∀ A : Set N.X, A ∈ N.sets -> f ⁻¹' A ∈ M.sets

def IsMeasurableIsomorphism (M : MeasurableSpaceData.{u}) (N : MeasurableSpaceData.{v}) : Prop :=
  ∃ f : M.X -> N.X, ∃ g : N.X -> M.X,
    Function.LeftInverse g f ∧ Function.RightInverse g f ∧
      IsMeasurableMap M N f ∧ IsMeasurableMap N M g

def SeparatesPoints {X : Type u} (𝓧 : SetFamily X) : Prop :=
  ∀ x y : X, x ≠ y -> ∃ A : Set X, A ∈ 𝓧 ∧ x ∈ A ∧ y ∉ A

def HasCountableGeneratingFamily {X : Type u} (𝓧 : SetFamily X) : Prop :=
  ∃ A : ℕ -> Set X, Chapter00.generatedSigmaAlgebra (Set.range A) = 𝓧

def HasSeparableMetricBorelModel (M : MeasurableSpaceData.{u}) : Prop :=
  ∃ Y : Type u, ∃ _t : TopologicalSpace Y, ∃ _m : MeasurableSpace Y,
    ∃ _metrizable : TopologicalSpace.MetrizableSpace Y,
    ∃ _sep : TopologicalSpace.SeparableSpace Y,
    @BorelSpace Y _t _m ∧
      IsMeasurableIsomorphism M { X := Y, measurableSpace := _m }

def HasCantorSubsetBorelModel (M : MeasurableSpaceData.{u}) : Prop :=
  ∃ C : Set (ℕ -> Bool), ∃ mC : MeasurableSpace C,
    mC = MeasurableSpace.comap Subtype.val (borel (ℕ -> Bool)) ∧
    IsMeasurableIsomorphism M { X := C, measurableSpace := mC }

def IsBorelSpace (M : MeasurableSpaceData.{u}) : Prop :=
  HasSeparableMetricBorelModel M

def IsStandardBorelSpaceData (M : MeasurableSpaceData.{u}) : Prop :=
  ∃ Y : Type u, ∃ _m : MeasurableSpace Y, ∃ _s : StandardBorelSpace Y,
    IsMeasurableIsomorphism M { X := Y, measurableSpace := _m }

def subspaceMeasurableSpace (M : MeasurableSpaceData.{u}) (A : Set M.X) : MeasurableSpaceData.{u} where
  X := A
  measurableSpace := MeasurableSpace.comap Subtype.val M.measurableSpace

def IsAnalyticSet (M : MeasurableSpaceData.{u}) (A : Set M.X) : Prop :=
  ∃ Y : MeasurableSpaceData.{u}, IsStandardBorelSpaceData Y ∧
    ∃ B : Set Y.X, B ∈ Y.sets ∧
    ∃ f : Y.X -> M.X, IsMeasurableMap Y M f ∧ A = f '' B

def analyticSigmaAlgebra (M : MeasurableSpaceData.{u}) : SetFamily M.X :=
  Chapter00.generatedSigmaAlgebra {A : Set M.X | IsAnalyticSet M A}

def IsNullSet (P : ProbabilitySpace.{u}) (A : Set P.X) : Prop :=
  ∃ B : Set P.X, B ∈ P.𝓧 ∧ A ⊆ B ∧ P.μ B = 0

def completionSigmaAlgebra (P : ProbabilitySpace.{u}) : SetFamily P.X :=
  {A : Set P.X | ∃ B C : Set P.X, B ∈ P.𝓧 ∧ IsNullSet P C ∧ A = B ∪ C}

def IsUniversallyMeasurable (M : MeasurableSpaceData.{u}) (A : Set M.X) : Prop :=
  ∀ μ : MeasureTheory.Measure M.X,
    μ Set.univ < ⊤ ->
    ∃ B N : Set M.X, MeasurableSet B ∧ MeasurableSet N ∧
      μ N = 0 ∧ Chapter00.symmDiff A B ⊆ N

def IsLebesgueProbabilitySpace (P : ProbabilitySpace.{u}) : Prop :=
  Chapter01.IsProbabilitySpace P ∧
    IsStandardBorelSpaceData { X := P.X, measurableSpace := P.measurableSpace }

def IsContinuousProbabilityMeasure (P : ProbabilitySpace.{u}) : Prop :=
  Chapter01.IsProbabilitySpace P ∧ ∀ x : P.X, P.μ {x} = 0

def IsLebesgueUnitIntervalModel (P : ProbabilitySpace.{u}) : Prop :=
  ∃ e : P.X -> Set.Icc (0 : ℝ) 1, ∃ inv : Set.Icc (0 : ℝ) 1 -> P.X,
    Measurable e ∧ Measurable inv ∧
    (fun x => inv (e x)) =ᵐ[P.μ] id ∧
    (∀ x, e (inv x) = x) ∧
    ∀ B : Set (Set.Icc (0 : ℝ) 1), MeasurableSet B ->
      P.μ (e ⁻¹' B) = MeasureTheory.volume (Subtype.val '' B)

def HasLebesgueCanonicalDecomposition (P : ProbabilitySpace.{u}) : Prop :=
  ∃ continuousPart : Set P.X, MeasurableSet continuousPart ∧
    ∃ atoms : Set (Set P.X), atoms.Countable ∧
      (∀ B ∈ atoms, MeasurableSet B ∧ 0 < P.μ B ∧
        ∀ A : Set P.X, MeasurableSet A -> A ⊆ B ->
          P.μ A = 0 ∨ P.μ A = P.μ B) ∧
      (∀ A ∈ atoms, ∀ B ∈ atoms, A ≠ B -> Disjoint A B) ∧
      P.μ (continuousPart ∪ ⋃₀ atoms) = 1 ∧
      (∀ x ∈ continuousPart, P.μ {x} = 0)

def IsIsomorphicProbabilitySpaces (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v}) : Prop :=
  ∃ X₀ : Set P.X, ∃ Y₀ : Set Q.X,
    MeasurableSet X₀ ∧ MeasurableSet Y₀ ∧ P.μ X₀ = 1 ∧ Q.μ Y₀ = 1 ∧
    ∃ φ : X₀ -> Y₀, ∃ ψ : Y₀ -> X₀,
      Function.LeftInverse ψ φ ∧ Function.RightInverse ψ φ ∧
      @Measurable X₀ Y₀ (MeasurableSpace.comap Subtype.val P.measurableSpace)
        (MeasurableSpace.comap Subtype.val Q.measurableSpace) φ ∧
      @Measurable Y₀ X₀ (MeasurableSpace.comap Subtype.val Q.measurableSpace)
        (MeasurableSpace.comap Subtype.val P.measurableSpace) ψ ∧
      ∀ B : Set Y₀,
        @MeasurableSet Y₀ (MeasurableSpace.comap Subtype.val Q.measurableSpace) B ->
        P.μ (Subtype.val '' (φ ⁻¹' B)) = Q.μ (Subtype.val '' B)

def IsIdeal {X : Type u} (𝓘 : Set (Set X)) : Prop :=
  ∅ ∈ 𝓘 ∧ (∀ A B : Set X, A ⊆ B -> B ∈ 𝓘 -> A ∈ 𝓘) ∧
    ∀ A B : Set X, A ∈ 𝓘 -> B ∈ 𝓘 -> A ∪ B ∈ 𝓘

def IsSigmaIdeal {X : Type u} (𝓘 : Set (Set X)) : Prop :=
  IsIdeal 𝓘 ∧ ∀ A : ℕ -> Set X, (∀ n : ℕ, A n ∈ 𝓘) -> (⋃ n : ℕ, A n) ∈ 𝓘

def quotientEquivalentByIdeal {X : Type u} (𝓘 : Set (Set X)) (A B : Set X) : Prop :=
  Chapter00.symmDiff A B ∈ 𝓘

structure QuotientBooleanHomData (M : MeasurableSpaceData.{u})
    (N : MeasurableSpaceData.{v}) (𝓨 : Set (Set M.X)) (𝓩 : Set (Set N.X)) where
  map : Set N.X -> Set M.X

def IsQuotientBooleanHom {M : MeasurableSpaceData.{u}}
    {N : MeasurableSpaceData.{v}} {𝓨 : Set (Set M.X)} {𝓩 : Set (Set N.X)}
  (Φ : QuotientBooleanHomData M N 𝓨 𝓩) : Prop :=
  (∀ A, A ∈ N.sets -> Φ.map A ∈ M.sets) ∧
  (∀ A B, A ∈ N.sets -> B ∈ N.sets -> quotientEquivalentByIdeal 𝓩 A B ->
    quotientEquivalentByIdeal 𝓨 (Φ.map A) (Φ.map B)) ∧
  (∀ A B, A ∈ N.sets -> B ∈ N.sets ->
    quotientEquivalentByIdeal 𝓨 (Φ.map (A ∪ B))
    (Φ.map A ∪ Φ.map B)) ∧
  (∀ A, A ∈ N.sets ->
    quotientEquivalentByIdeal 𝓨 (Φ.map Aᶜ) (Φ.map A)ᶜ) ∧
  ∀ A : ℕ -> Set N.X, (∀ n, A n ∈ N.sets) ->
    quotientEquivalentByIdeal 𝓨 (Φ.map (⋃ n, A n)) (⋃ n, Φ.map (A n))

def IsQuotientBooleanIso {M : MeasurableSpaceData.{u}}
    {N : MeasurableSpaceData.{v}} {𝓨 : Set (Set M.X)} {𝓩 : Set (Set N.X)}
  (Φ : QuotientBooleanHomData M N 𝓨 𝓩) : Prop :=
  IsQuotientBooleanHom Φ ∧
  (∀ A B, A ∈ N.sets -> B ∈ N.sets ->
    quotientEquivalentByIdeal 𝓨 (Φ.map A) (Φ.map B) ->
    quotientEquivalentByIdeal 𝓩 A B) ∧
  ∀ C ∈ M.sets, ∃ A ∈ N.sets,
    quotientEquivalentByIdeal 𝓨 (Φ.map A) C

structure MeasureAlgebraData where
  carrier : Type u
  equiv : carrier -> carrier -> Prop
  top : carrier
  bot : carrier
  compl : carrier -> carrier
  union : carrier -> carrier -> carrier
  inter : carrier -> carrier -> carrier
  iUnion : (ℕ -> carrier) -> carrier
  measure : carrier -> ℝ

def IsMeasureAlgebra (A : MeasureAlgebraData.{u}) : Prop :=
  Equivalence A.equiv ∧
  (∀ a b a' b', A.equiv a a' -> A.equiv b b' ->
    A.equiv (A.union a b) (A.union a' b') ∧
    A.equiv (A.inter a b) (A.inter a' b')) ∧
  (∀ a b, A.equiv a b -> A.equiv (A.compl a) (A.compl b)) ∧
  (∀ a b, A.equiv a b -> A.measure a = A.measure b) ∧
  (∀ a, A.equiv (A.union a A.bot) a ∧ A.equiv (A.inter a A.top) a) ∧
  (∀ a, A.equiv (A.inter a A.bot) A.bot ∧ A.equiv (A.union a A.top) A.top) ∧
  (∀ a, A.equiv (A.union a (A.compl a)) A.top) ∧
  (∀ a, A.equiv (A.inter a (A.compl a)) A.bot) ∧
  (∀ a, A.equiv (A.compl (A.compl a)) a) ∧
  (∀ a b, A.equiv (A.union a b) (A.union b a) ∧
    A.equiv (A.inter a b) (A.inter b a)) ∧
  (∀ a b c, A.equiv (A.union (A.union a b) c) (A.union a (A.union b c)) ∧
    A.equiv (A.inter (A.inter a b) c) (A.inter a (A.inter b c))) ∧
  (∀ a b c,
    A.equiv (A.inter a (A.union b c))
      (A.union (A.inter a b) (A.inter a c)) ∧
    A.equiv (A.union a (A.inter b c))
      (A.inter (A.union a b) (A.union a c))) ∧
  (∀ f : ℕ -> A.carrier, ∀ n,
    A.equiv (A.inter (f n) (A.iUnion f)) (f n)) ∧
  (∀ f : ℕ -> A.carrier, ∀ b : A.carrier,
    (∀ n, A.equiv (A.inter (f n) b) (f n)) ->
      A.equiv (A.inter (A.iUnion f) b) (A.iUnion f)) ∧
  A.measure A.bot = 0 ∧
  (∀ a, 0 ≤ A.measure a) ∧
  (∀ a, A.measure a = 0 ↔ A.equiv a A.bot) ∧
  ∀ f : ℕ -> A.carrier,
    (∀ i j, i ≠ j -> A.equiv (A.inter (f i) (f j)) A.bot) ->
      A.measure (A.iUnion f) = ∑' n, A.measure (f n)

structure MeasureAlgebraHomData (B : MeasureAlgebraData.{u}) (A : MeasureAlgebraData.{v}) where
  map : B.carrier -> A.carrier

def measureAlgebraDistance (A : MeasureAlgebraData.{u})
    (a b : A.carrier) : ℝ :=
  A.measure (A.union (A.inter a (A.compl b)) (A.inter b (A.compl a)))

def IsMeasureAlgebraHom {B : MeasureAlgebraData.{u}} {A : MeasureAlgebraData.{v}}
    (Φ : MeasureAlgebraHomData B A) : Prop :=
  (∀ b c, B.equiv b c -> A.equiv (Φ.map b) (Φ.map c)) ∧
  (∀ b c : B.carrier,
    A.equiv (Φ.map (B.union b c)) (A.union (Φ.map b) (Φ.map c))) ∧
    (∀ b : B.carrier, A.equiv (Φ.map (B.compl b)) (A.compl (Φ.map b))) ∧
    (∀ f : ℕ -> B.carrier,
      A.equiv (Φ.map (B.iUnion f)) (A.iUnion (fun n => Φ.map (f n)))) ∧
      ∀ b : B.carrier, A.measure (Φ.map b) = B.measure b

def IsMeasureAlgebraIsomorphism {B : MeasureAlgebraData.{u}} {A : MeasureAlgebraData.{v}}
    (Φ : MeasureAlgebraHomData B A) : Prop :=
  IsMeasureAlgebraHom Φ ∧
    (∀ b c, A.equiv (Φ.map b) (Φ.map c) -> B.equiv b c) ∧
    ∀ a : A.carrier, ∃ b : B.carrier, A.equiv (Φ.map b) a

def IsSeparableMeasureAlgebra (A : MeasureAlgebraData.{u}) : Prop :=
  ∃ d : ℕ -> A.carrier, ∀ a : A.carrier, ∀ ε : ℝ, 0 < ε ->
    ∃ n, A.measure (A.union (A.inter a (A.compl (d n)))
      (A.inter (d n) (A.compl a))) < ε

def inducedMeasureAlgebra (P : ProbabilitySpace.{u}) : MeasureAlgebraData.{u} where
  carrier := {A : Set P.X // MeasurableSet A}
  equiv := fun A B => P.μ (Chapter00.symmDiff A.1 B.1) = 0
  top := ⟨Set.univ, MeasurableSet.univ⟩
  bot := ⟨∅, MeasurableSet.empty⟩
  compl := fun A => ⟨A.1ᶜ, A.2.compl⟩
  union := fun A B => ⟨A.1 ∪ B.1, A.2.union B.2⟩
  inter := fun A B => ⟨A.1 ∩ B.1, A.2.inter B.2⟩
  iUnion := fun A => ⟨⋃ n, (A n).1, MeasurableSet.iUnion fun n => (A n).2⟩
  measure := fun A => (P.μ A.1).toReal

def AreConjugateProbabilitySpaces (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v}) : Prop :=
  ∃ Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q) (inducedMeasureAlgebra P),
    IsMeasureAlgebraIsomorphism Φ

def IsLtwoAlgebraUnitaryFor (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (W : (Q.X -> ℂ) -> (P.X -> ℂ)) : Prop :=
    (∀ f g, Q.lpMember 2 f -> Q.lpMember 2 g ->
      f =ᵐ[Q.μ] g -> W f =ᵐ[P.μ] W g) ∧
    (∀ f g, Q.lpMember 2 f -> Q.lpMember 2 g ->
      W (fun y => f y + g y) =ᵐ[P.μ] fun x => W f x + W g x) ∧
    (∀ c : ℂ, ∀ f, Q.lpMember 2 f ->
      W (fun y => c * f y) =ᵐ[P.μ] fun x => c * W f x) ∧
    (∀ f, Q.lpMember 2 f -> P.lpMember 2 (W f) ∧
      MeasureTheory.eLpNorm (W f) 2 P.μ = MeasureTheory.eLpNorm f 2 Q.μ) ∧
    (∀ h : P.X -> ℂ, P.lpMember 2 h -> ∀ ε : ℝ, 0 < ε ->
      ∃ f : Q.X -> ℂ, Q.lpMember 2 f ∧
        MeasureTheory.eLpNorm (fun x => h x - W f x) 2 P.μ < ENNReal.ofReal ε) ∧
    (∀ f : Q.X -> ℂ, Q.lpMember ⊤ f -> P.lpMember ⊤ (W f)) ∧
    (∀ h : P.X -> ℂ, P.lpMember ⊤ h ->
      ∃ f : Q.X -> ℂ, Q.lpMember ⊤ f ∧ W f =ᵐ[P.μ] h) ∧
    (W (fun _ => 1) =ᵐ[P.μ] fun _ => 1) ∧
    ∀ f g : Q.X -> ℂ, Q.lpMember ⊤ f -> Q.lpMember ⊤ g ->
      W (fun y => f y * g y) =ᵐ[P.μ] fun x => W f x * W g x

def HasLtwoAlgebraUnitary (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v}) : Prop :=
  ∃ W : (Q.X -> ℂ) -> (P.X -> ℂ), IsLtwoAlgebraUnitaryFor P Q W

structure MeasureAlgebraSystemData extends MeasureAlgebraData where
  transform : carrier -> carrier

/-- A genuine measure-algebra dynamical system: its transformation is an
automorphism of the underlying measure algebra.  This is the structure implicit
in the textbook's notation `(X, μ*, T*)`. -/
def IsMeasureAlgebraSystem (A : MeasureAlgebraSystemData.{u}) : Prop :=
  IsMeasureAlgebra A.toMeasureAlgebraData ∧
    ∃ Θ : MeasureAlgebraHomData A.toMeasureAlgebraData A.toMeasureAlgebraData,
      IsMeasureAlgebraIsomorphism Θ ∧
        ∀ a : A.carrier, A.equiv (Θ.map a) (A.transform a)

def inducedMeasureAlgebraSystem (M : System.{u}) : MeasureAlgebraSystemData.{u} where
  toMeasureAlgebraData := inducedMeasureAlgebra M.toProbabilitySpace
  transform := if hT : Measurable M.T then
    fun A => ⟨M.T ⁻¹' A.1, A.2.preimage hT⟩
  else fun _ => ⟨∅, MeasurableSet.empty⟩

def IsMeasureAlgebraSystemIsomorphism (B : MeasureAlgebraSystemData.{u})
    (A : MeasureAlgebraSystemData.{v}) : Prop :=
  ∃ Φ : MeasureAlgebraHomData B.toMeasureAlgebraData A.toMeasureAlgebraData,
    IsMeasureAlgebraIsomorphism Φ ∧ ∀ b : B.carrier,
      A.equiv (Φ.map (B.transform b)) (A.transform (Φ.map b))

def IsSystemConjugate (M : System.{u}) (N : System.{v}) : Prop :=
  IsMeasureAlgebraSystemIsomorphism
    (inducedMeasureAlgebraSystem N) (inducedMeasureAlgebraSystem M)

def IsSpatialModelOfMeasureAlgebraSystem
    (A : MeasureAlgebraSystemData.{u}) (M : System.{u}) : Prop :=
  IsMeasureAlgebraSystemIsomorphism A (inducedMeasureAlgebraSystem M)

def IsSemiConjugateSystem (factor extension : System.{u}) : Prop :=
  ∃ π : extension.X -> factor.X, Chapter01.IsFactorMap extension factor π

def IsInvertibleModNull (M : System.{u}) : Prop :=
  ∃ S : M.X -> M.X, Measurable S ∧
    MeasureTheory.MeasurePreserving S M.μ M.μ ∧
    (fun x => S (M.T x)) =ᵐ[M.μ] id ∧
    (fun x => M.T (S x)) =ᵐ[M.μ] id

def IsModNullInverseFor (M : System.{u}) (S : M.X → M.X) : Prop :=
  Measurable S ∧ MeasureTheory.MeasurePreserving S M.μ M.μ ∧
    (fun x => S (M.T x)) =ᵐ[M.μ] id ∧
    (fun x => M.T (S x)) =ᵐ[M.μ] id

structure MeasureIntegerActionData (M : System.{u}) where
  act : ℤ -> M.X -> M.X
  zero_act : act 0 = id
  add_act : ∀ m n, act (m + n) = act m ∘ act n
  one_act : act 1 = M.T
  measure_preserving : ∀ n, MeasureTheory.MeasurePreserving (act n) M.μ M.μ

def IsInducedSigmaAlgebraSurjective (M : System.{u}) : Prop :=
  Measurable M.T ∧ ∀ A : Set M.X, MeasurableSet A ->
    ∃ B : Set M.X, MeasurableSet B ∧
      M.μ (Chapter00.symmDiff (M.T ⁻¹' B) A) = 0

def IsSpectralIntertwinerFor (M : System.{u}) (N : System.{v})
    (W : (N.X -> ℂ) -> (M.X -> ℂ)) : Prop :=
    (∀ f g, N.lpMember 2 f -> N.lpMember 2 g ->
      f =ᵐ[N.μ] g -> W f =ᵐ[M.μ] W g) ∧
    (∀ f g, N.lpMember 2 f -> N.lpMember 2 g ->
      W (fun y => f y + g y) =ᵐ[M.μ] fun x => W f x + W g x) ∧
    (∀ c : ℂ, ∀ f, N.lpMember 2 f ->
      W (fun y => c * f y) =ᵐ[M.μ] fun x => c * W f x) ∧
    (∀ f, N.lpMember 2 f -> M.lpMember 2 (W f) ∧
      MeasureTheory.eLpNorm (W f) 2 M.μ = MeasureTheory.eLpNorm f 2 N.μ) ∧
    (∀ h : M.X -> ℂ, M.lpMember 2 h -> ∀ ε : ℝ, 0 < ε ->
      ∃ f : N.X -> ℂ, N.lpMember 2 f ∧
        MeasureTheory.eLpNorm (fun x => h x - W f x) 2 M.μ < ENNReal.ofReal ε) ∧
    ∀ f : N.X -> ℂ, N.lpMember 2 f ->
      W (Chapter01.koopman N.T f) =ᵐ[M.μ] Chapter01.koopman M.T (W f)

def IsSpectrallyIsomorphic (M : System.{u}) (N : System.{v}) : Prop :=
  ∃ W : (N.X -> ℂ) -> (M.X -> ℂ), IsSpectralIntertwinerFor M N W

/-- The exact same-operator form of Theorem 4.2.11. -/
def IsAlgebraicSpectralIsomorphism (M : System.{u}) (N : System.{v}) : Prop :=
  ∃ W : (N.X -> ℂ) -> (M.X -> ℂ),
    IsSpectralIntertwinerFor M N W ∧
      IsLtwoAlgebraUnitaryFor M.toProbabilitySpace N.toProbabilitySpace W

def IsSubSigmaAlgebra (M : System.{u}) (A : SetFamily M.X) : Prop :=
  Chapter00.IsSigmaAlgebraFamily A ∧ A ⊆ M.𝓧

def EqualModuloMeasure (M : System.{u})
    (A B : SetFamily M.X) : Prop :=
  (∀ U ∈ A, ∃ V ∈ B, M.μ (Chapter00.symmDiff U V) = 0) ∧
    ∀ V ∈ B, ∃ U ∈ A, M.μ (Chapter00.symmDiff U V) = 0

def FamilySubsetModuloMeasure (M : System.{u})
    (A B : SetFamily M.X) : Prop :=
  ∀ U ∈ A, ∃ V ∈ B, M.μ (Chapter00.symmDiff U V) = 0

def imageSetFamily {X : Type u} (T : X → X)
    (A : SetFamily X) : SetFamily X :=
  {B | ∃ C ∈ A, B = T '' C}

def preimageSetFamily {X : Type u} (T : X → X)
    (A : SetFamily X) : SetFamily X :=
  {B | ∃ C ∈ A, B = T ⁻¹' C}

def kolmogorovForwardJoin (M : System.{u}) (S : M.X → M.X)
    (A : SetFamily M.X) : SetFamily M.X :=
  Chapter00.generatedSigmaAlgebra
    {B | ∃ n : ℕ, B ∈ preimageSetFamily (S^[n]) A}

def kolmogorovBackwardTail (M : System.{u})
    (A : SetFamily M.X) : SetFamily M.X :=
  ⋂ n : ℕ, preimageSetFamily (M.T^[n]) A

/-- The Kolmogorov property in the measure-algebra sense of Definition 4.3.1.
The generating join and the backward tail are compared modulo null sets, as
they must be for a transformation which is invertible only modulo null sets. -/
def IsKolmogorovSystem (M : System.{u}) : Prop :=
  IsLebesgueProbabilitySpace M.toProbabilitySpace ∧
  Chapter01.IsMeasurePreservingSystem M ∧ IsInvertibleModNull M ∧
  (∃ B : Set M.X, MeasurableSet B ∧ 0 < M.μ B ∧ M.μ B < 1) ∧
  ∃ S : M.X → M.X, IsModNullInverseFor M S ∧
    ∃ A : SetFamily M.X, IsSubSigmaAlgebra M A ∧
      FamilySubsetModuloMeasure M A (preimageSetFamily S A) ∧
      EqualModuloMeasure M (kolmogorovForwardJoin M S A) M.𝓧 ∧
      EqualModuloMeasure M (kolmogorovBackwardTail M A) {∅, Set.univ}

/-- The nontrivial invertible Lebesgue ambient class in which 4.3.10 is stated. -/
def IsKolmogorovAmbientSystem (M : System.{u}) : Prop :=
  IsLebesgueProbabilitySpace M.toProbabilitySpace ∧
    Chapter01.IsMeasurePreservingSystem M ∧ IsInvertibleModNull M ∧
    ∃ B : Set M.X, MeasurableSet B ∧ 0 < M.μ B ∧ M.μ B < 1

def LegacyIsBernoulliSystem (M : System.{u}) : Prop :=
  ∃ Ω : Type u, ∃ mΩ : MeasurableSpace Ω,
    ∃ ρ : @MeasureTheory.Measure Ω mΩ,
    MeasureTheory.IsProbabilityMeasure ρ ∧
    ∃ ν : @MeasureTheory.Measure (ℤ -> Ω) (MeasurableSpace.pi),
    MeasureTheory.IsProbabilityMeasure ν ∧
    ∃ e : M.X -> (ℤ -> Ω), ∃ inv : (ℤ -> Ω) -> M.X,
      @Measurable M.X (ℤ -> Ω) M.measurableSpace MeasurableSpace.pi e ∧
      @Measurable (ℤ -> Ω) M.X MeasurableSpace.pi M.measurableSpace inv ∧
      (fun x => inv (e x)) =ᵐ[M.μ] id ∧
      (fun x => e (inv x)) =ᵐ[ν] id ∧
      MeasureTheory.Measure.map e M.μ = ν ∧
      (∀ᵐ x ∂M.μ, ∀ n : ℤ, e (M.T x) n = e x (n + 1)) ∧
      ∀ I : Finset ℤ, ∀ C : ℤ -> Set Ω,
        (∀ i ∈ I, @MeasurableSet Ω mΩ (C i)) ->
        ν {x | ∀ i ∈ I, x i ∈ C i} = ∏ i ∈ I, ρ (C i)

/-- A Bernoulli system in the nontrivial convention required by Theorem 4.3.4:
the base probability space has an event of measure strictly between zero and
one.  The remaining fields are exactly the two-sided product-shift model. -/
def IsBernoulliSystem (M : System.{u}) : Prop :=
  IsLebesgueProbabilitySpace M.toProbabilitySpace ∧
  Chapter01.IsMeasurePreservingSystem M ∧ IsInvertibleModNull M ∧
  ∃ Ω : Type u, ∃ mΩ : MeasurableSpace Ω,
    ∃ ρ : @MeasureTheory.Measure Ω mΩ,
    MeasureTheory.IsProbabilityMeasure ρ ∧
    (∃ C : Set Ω, @MeasurableSet Ω mΩ C ∧ 0 < ρ C ∧ ρ C < 1) ∧
    ∃ ν : @MeasureTheory.Measure (ℤ -> Ω) (MeasurableSpace.pi),
    MeasureTheory.IsProbabilityMeasure ν ∧
    ∃ e : M.X -> (ℤ -> Ω), ∃ inv : (ℤ -> Ω) -> M.X,
      @Measurable M.X (ℤ -> Ω) M.measurableSpace MeasurableSpace.pi e ∧
      @Measurable (ℤ -> Ω) M.X MeasurableSpace.pi M.measurableSpace inv ∧
      (fun x => inv (e x)) =ᵐ[M.μ] id ∧
      (fun x => e (inv x)) =ᵐ[ν] id ∧
      MeasureTheory.Measure.map e M.μ = ν ∧
      (∀ᵐ x ∂M.μ, ∀ n : ℤ, e (M.T x) n = e x (n + 1)) ∧
      ∀ I : Finset ℤ, ∀ C : ℤ -> Set Ω,
        (∀ i ∈ I, @MeasurableSet Ω mΩ (C i)) ->
        ν {x | ∀ i ∈ I, x i ∈ C i} = ∏ i ∈ I, ρ (C i)

def measureProductSystem (M : System.{u}) (N : System.{v}) :
    System.{max u v} where
  X := M.X × N.X
  measurableSpace := inferInstance
  μ := M.μ.prod N.μ
  T := fun p => (M.T p.1, N.T p.2)

def l2Inner (M : System.{u}) (f g : M.X -> ℂ) : ℂ :=
  ∫ x, f x * star (g x) ∂M.μ

def IsTotalInZeroMeanL2 (M : System.{u}) (V : Set (M.X -> ℂ)) : Prop :=
  ∀ f : M.X -> ℂ, M.lpMember 2 f -> ∫ x, f x ∂M.μ = 0 ->
    ∀ ε : ℝ, 0 < ε ->
      ∃ s : Finset (M.X -> ℂ), (↑s : Set (M.X -> ℂ)) ⊆ V ∧
        ∃ c : (M.X -> ℂ) -> ℂ,
        MeasureTheory.eLpNorm (fun x => f x - ∑ g ∈ s, c g * g x) 2 M.μ <
          ENNReal.ofReal ε

def HasCountableLebesgueSpectrum (M : System.{u}) : Prop :=
  IsLebesgueProbabilitySpace M.toProbabilitySpace ∧ IsInvertibleModNull M ∧
  ∃ U : MeasureIntegerActionData M, ∃ f : ℕ -> M.X -> ℂ,
    (∀ i, M.lpMember 2 (f i) ∧ ∫ x, f i x ∂M.μ = 0) ∧
    (∀ i j m n, l2Inner M
      (Chapter01.koopman (U.act m) (f i))
      (Chapter01.koopman (U.act n) (f j)) =
        if i = j ∧ m = n then 1 else 0) ∧
    IsTotalInZeroMeanL2 M
      {g | ∃ i n, g = Chapter01.koopman (U.act n) (f i)}

def HasDiscreteSpectrum (M : System.{u}) : Prop :=
  ∃ basis : Set (M.X -> ℂ),
    (∀ f ∈ basis, ∃ lam : ℂ, Chapter02.Eigenfunction M lam f) ∧
    (∀ f ∈ basis, ∀ g ∈ basis, f ≠ g -> l2Inner M f g = 0) ∧
    ∀ h : M.X -> ℂ, M.lpMember 2 h -> ∀ ε : ℝ, 0 < ε ->
      ∃ s : Finset (M.X -> ℂ), (↑s : Set (M.X -> ℂ)) ⊆ basis ∧
        ∃ c : (M.X -> ℂ) -> ℂ,
        MeasureTheory.eLpNorm (fun x => h x - ∑ f ∈ s, c f * f x) 2 M.μ <
          ENNReal.ofReal ε

def eigenvalueSet (M : System.{u}) : Set ℂ :=
  {lam : ℂ | Chapter02.Eigenvalue M lam}

def HasEigenfunctionMultiplicativeChoice (M : System.{u}) : Prop :=
  ∃ f : ℂ -> M.X -> ℂ,
    (∀ lam ∈ eigenvalueSet M, Chapter02.Eigenfunction M lam (f lam) ∧
      (fun x => ‖f lam x‖) =ᵐ[M.μ] fun _ => 1) ∧
    (f (1 : ℂ) =ᵐ[M.μ] fun _ => (1 : ℂ)) ∧
    ∀ lam ∈ eigenvalueSet M, ∀ xi ∈ eigenvalueSet M,
      f (lam * xi) =ᵐ[M.μ] fun x => f lam x * f xi x

def IsCompactAbelianRotationModel (M : System.{u}) (G : Type v)
    [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (η : MeasureTheory.Measure G) (e : M.X -> G) (inv : G -> M.X) (a : G) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
    MeasureTheory.Measure.IsAddHaarMeasure η ∧
    MeasureTheory.IsProbabilityMeasure η ∧
    Measurable e ∧ Measurable inv ∧
    Function.LeftInverse inv e ∧ Function.RightInverse inv e ∧
    MeasureTheory.Measure.map e M.μ = η ∧
    ∀ x : M.X, e (M.T x) = a + e x

def IsCompactAbelianRotationSystem (M : System.{u}) : Prop :=
  ∃ G : Type u, ∃ _ : AddCommGroup G, ∃ _ : TopologicalSpace G,
  ∃ _ : IsTopologicalAddGroup G, ∃ _ : CompactSpace G,
  ∃ _ : MeasurableSpace G, ∃ _ : BorelSpace G,
  ∃ η : MeasureTheory.Measure G, ∃ e : M.X -> G, ∃ inv : G -> M.X, ∃ a : G,
    IsCompactAbelianRotationModel M G η e inv a

def IsMetrizableCompactAbelianRotationSystem (M : System.{u}) : Prop :=
  ∃ G : Type u, ∃ _ : AddCommGroup G, ∃ _ : TopologicalSpace G,
  ∃ _ : IsTopologicalAddGroup G, ∃ _ : CompactSpace G,
  ∃ _ : TopologicalSpace.MetrizableSpace G,
  ∃ _ : MeasurableSpace G, ∃ _ : BorelSpace G,
  ∃ η : MeasureTheory.Measure G, ∃ e : M.X -> G, ∃ inv : G -> M.X, ∃ a : G,
    IsCompactAbelianRotationModel M G η e inv a

def IsCircleSubgroup (H : Set ℂ) : Prop :=
  (1 : ℂ) ∈ H ∧ (∀ z ∈ H, ‖z‖ = 1) ∧
  (∀ z w, z ∈ H -> w ∈ H -> z * w ∈ H) ∧
  ∀ z, z ∈ H -> z⁻¹ ∈ H

def HasDivisibleRetraction (H : Type u) [CommGroup H] (K : Subgroup H) : Prop :=
  RootableBy K ℕ → ∃ θ : H →* K, ∀ k : K, θ k = k

def IsRotationCharacter {G : Type v} [AddCommGroup G] [TopologicalSpace G]
    (χ : G -> ℂ) : Prop :=
  Continuous χ ∧ χ 0 = 1 ∧
    (∀ x y, χ (x + y) = χ x * χ y) ∧
    ∀ x, ‖χ x‖ = 1

def RotationCharacterEigenvalueForModel {G : Type v}
    [AddCommGroup G] [TopologicalSpace G] (a : G) (lam : ℂ) : Prop :=
  ∃ χ : G -> ℂ, IsRotationCharacter χ ∧ lam = χ a

def RotationCharacterEigenfunctionForModel
    {M : System.{u}} {G : Type v} [AddCommGroup G] [TopologicalSpace G]
    (e : M.X -> G) (a : G) (lam : ℂ) (f : M.X -> ℂ) : Prop :=
  ∃ χ : G -> ℂ, ∃ c : ℂ,
    IsRotationCharacter χ ∧ lam = χ a ∧ c ≠ 0 ∧
      f =ᵐ[M.μ] fun x => c * χ (e x)

def RotationCharacterEigenvalue (M : System.{u}) (lam : ℂ) : Prop :=
  ∃ G : Type u, ∃ _ : AddCommGroup G, ∃ _ : TopologicalSpace G,
  ∃ _ : IsTopologicalAddGroup G, ∃ _ : CompactSpace G,
  ∃ _ : MeasurableSpace G, ∃ _ : BorelSpace G,
  ∃ η : MeasureTheory.Measure G, ∃ e : M.X -> G, ∃ inv : G -> M.X, ∃ a : G,
    IsCompactAbelianRotationModel M G η e inv a ∧
      RotationCharacterEigenvalueForModel a lam

def IsConjugateToInverseSystem (M : System.{u}) : Prop :=
  ∃ S : M.X -> M.X, Measurable S ∧
    MeasureTheory.MeasurePreserving S M.μ M.μ ∧
    (fun x => S (M.T x)) =ᵐ[M.μ] id ∧
    (fun x => M.T (S x)) =ᵐ[M.μ] id ∧
    IsSystemConjugate M
      { X := M.X, measurableSpace := M.measurableSpace, μ := M.μ, T := S }

def IsGroupExtension (extension factor : System.{u}) : Prop :=
  ∃ K : Type u, ∃ _ : Group K, ∃ _ : TopologicalSpace K,
  ∃ _ : IsTopologicalGroup K, ∃ _ : CompactSpace K,
  ∃ π : extension.X -> factor.X, ∃ act : K -> extension.X -> extension.X,
    Chapter01.IsFactorMap extension factor π ∧
    (∀ k, Measurable (act k) ∧
      MeasureTheory.MeasurePreserving (act k) extension.μ extension.μ) ∧
    (∀ x, act 1 x = x) ∧
    (∀ k l x, act (k * l) x = act k (act l x)) ∧
    (∀ k x, π (act k x) = π x) ∧
    ∀ x y, π x = π y -> ∃ k, act k x = y

def IsSkewProductExtension (extension factor : System.{u}) : Prop :=
  ∃ K : Type u, ∃ mK : MeasurableSpace K,
  ∃ ρ : @MeasureTheory.Measure K mK, MeasureTheory.IsProbabilityMeasure ρ ∧
  ∃ cocycle : factor.X -> K -> K,
  Measurable (fun p : factor.X × K => cocycle p.1 p.2) ∧
  (∀ᵐ y ∂factor.μ, MeasureTheory.MeasurePreserving (cocycle y) ρ ρ) ∧
  ∃ e : extension.X -> factor.X × K,
  ∃ inv : factor.X × K -> extension.X,
    Measurable e ∧ Measurable inv ∧
    (fun x => inv (e x)) =ᵐ[extension.μ] id ∧
    (fun x => e (inv x)) =ᵐ[factor.μ.prod ρ] id ∧
    MeasureTheory.Measure.map e extension.μ = factor.μ.prod ρ ∧
    ∀ᵐ x ∂extension.μ,
      e (extension.T x) = (factor.T (e x).1, cocycle (e x).1 (e x).2)

def IsHereditaryFamily {X : Type u} (𝓗 : Set (Set X)) : Prop :=
  𝓗.Nonempty ∧ ∀ A B : Set X, A ⊆ B -> B ∈ 𝓗 -> A ∈ 𝓗

def Saturates {X : Type u} (𝓗 : Set (Set X)) (𝓧 : SetFamily X)
    (μ : Set X -> ENNReal) : Prop :=
  ∀ A : Set X, A ∈ 𝓧 -> 0 < μ A ->
    ∃ B ∈ 𝓗, B ⊆ A ∧ 0 < μ B

def HasMeasurableUnion {X : Type u} (𝓗 : Set (Set X))
    (𝓧 : SetFamily X) (μ : Set X -> ENNReal) (U : Set X) : Prop :=
  U ∈ 𝓧 ∧
  ∃ A : ℕ -> Set X, (∀ n : ℕ, A n ∈ 𝓗) ∧
    (∀ i j : ℕ, i ≠ j -> Disjoint (A i) (A j)) ∧ U = ⋃ n : ℕ, A n ∧
    ∀ B ∈ 𝓗, μ (B \ U) = 0

def IsMeasurablyInvertibleOn
    (P Q : ProbabilitySpace.{u}) (π : P.X → Q.X) (A : Set P.X) : Prop :=
  MeasurableSet A ∧ MeasurableSet (π '' A) ∧
    ∃ σ : Q.X → P.X, Measurable σ ∧
      (∀ x ∈ A, σ (π x) = x) ∧
      ∀ y ∈ π '' A, π (σ y) = y

def LocalInversionForCountableFibers : Prop :=
  ∀ P Q : ProbabilitySpace.{u}, ∀ π : P.X -> Q.X,
    IsLebesgueProbabilitySpace P -> IsLebesgueProbabilitySpace Q ->
    MeasureTheory.MeasurePreserving π P.μ Q.μ ->
    (∀ y : Q.X, Set.Countable {x : P.X | π x = y}) ->
      ∃ A : ℕ -> Set P.X,
        (∀ n, IsMeasurablyInvertibleOn P Q π (A n)) ∧
        (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
        (⋃ n, A n) = Set.univ

def RohlinSkewProductTheoremStatement : Prop :=
  ∀ extension factor : System.{u}, IsSemiConjugateSystem factor extension ->
    IsLebesgueProbabilitySpace extension.toProbabilitySpace ->
    IsLebesgueProbabilitySpace factor.toProbabilitySpace ->
    IsInvertibleModNull extension -> IsInvertibleModNull factor ->
    Chapter02.IsErgodic extension -> Chapter02.IsErgodic factor ->
      IsSkewProductExtension extension factor

def GroupSkewProductRepresentationStatement : Prop :=
  ∀ extension factor : System.{u}, Chapter02.IsErgodic extension ->
    IsLebesgueProbabilitySpace extension.toProbabilitySpace ->
    IsLebesgueProbabilitySpace factor.toProbabilitySpace ->
    IsInvertibleModNull extension -> IsInvertibleModNull factor ->
    IsGroupExtension extension factor -> IsSkewProductExtension extension factor

structure ErgodicDecompositionData (M : System.{u}) where
  Y : Type u
  measurableSpace : MeasurableSpace Y
  ν : @MeasureTheory.Measure Y measurableSpace
  component : Y -> MeasureTheory.Measure M.X

attribute [instance] ErgodicDecompositionData.measurableSpace

def IsErgodicMeasureComponent (M : System.{u})
    (μy : MeasureTheory.Measure M.X) : Prop :=
  MeasureTheory.IsProbabilityMeasure μy ∧
  MeasureTheory.MeasurePreserving M.T μy μy ∧
  ∀ A : Set M.X, MeasurableSet A ->
    μy (Chapter00.symmDiff (M.T ⁻¹' A) A) = 0 ->
      μy A = 0 ∨ μy A = 1

def IsErgodicDecomposition (M : System.{u}) (D : ErgodicDecompositionData M) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
    MeasureTheory.IsProbabilityMeasure D.ν ∧
    (∀ᵐ y ∂D.ν, IsErgodicMeasureComponent M (D.component y)) ∧
    (∀ A : Set M.X, MeasurableSet A ->
      Measurable fun y => D.component y A) ∧
    ∀ A : Set M.X, MeasurableSet A ->
      M.μ A = ∫⁻ y, D.component y A ∂D.ν

def HasFactorErgodicDecomposition (M : System.{u}) : Prop :=
  ∃ Ysys : System.{u}, ∃ φ : M.X -> Ysys.X,
    Chapter01.IsFactorMap M Ysys φ ∧
    Ysys.T = id ∧
    EqualModuloMeasure M
      {A | ∃ B : Set Ysys.X, MeasurableSet B ∧ A = φ ⁻¹' B}
      (Chapter02.invariantSigmaAlgebra M) ∧
    ∃ D : ErgodicDecompositionData M,
      IsErgodicDecomposition M D ∧
      ∃ e : D.Y -> Ysys.X, Function.Bijective e ∧ Measurable e ∧
      ∀ᵐ y ∂D.ν, D.component y (φ ⁻¹' {e y}) = 1

end Chapter04
