import Chapter01.Section03
import Mathlib.MeasureTheory.Measure.NullMeasurable

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter02

universe u v

abbrev System := Chapter01.MeasurePreservingSystemData
abbrev SetFamily (X : Type u) := Chapter00.SetFamily X

def realMeasure (M : System.{u}) (A : Set M.X) : ℝ :=
  (M.μ A).toReal

def preimageIter (M : System.{u}) (n : ℕ) (A : Set M.X) : Set M.X :=
  (Chapter01.iterateMap M.T n) ⁻¹' A

def correlation (M : System.{u}) (A B : Set M.X) (n : ℕ) : ℝ :=
  realMeasure M (A ∩ preimageIter M n B)

def productMeasureValue (M : System.{u}) (A B : Set M.X) : ℝ :=
  realMeasure M A * realMeasure M B

def cesaroAverage (a : ℕ -> ℝ) (N : ℕ) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ * (Finset.range (N + 1)).sum a

def seqTendsTo (a : ℕ -> ℝ) (l : ℝ) : Prop :=
  Tendsto a atTop (nhds l)

def cesaroTendsTo (a : ℕ -> ℝ) (l : ℝ) : Prop :=
  seqTendsTo (fun N => cesaroAverage a N) l

def IsErgodic (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
    ∀ A : Set M.X, MeasurableSet A ->
      M.μ (Chapter00.symmDiff (M.T ⁻¹' A) A) = 0 ->
        M.μ A = 0 ∨ M.μ A = 1

def IsErgodicNonProbability (M : System.{u}) : Prop :=
  ∀ A : Set M.X, MeasurableSet A ->
    M.μ (Chapter00.symmDiff (M.T ⁻¹' A) A) = 0 ->
      M.μ A = 0 ∨ M.μ Aᶜ = 0

def IsAlmostInvariantSet (M : System.{u}) (A : Set M.X) : Prop :=
  A ∈ M.𝓧 ∧ M.μ (Chapter00.symmDiff (M.T ⁻¹' A) A) = 0

def HasErgodicEquivalentCharacterizations (M : System.{u}) : Prop :=
  IsErgodic M ↔
    ((∀ B : Set M.X, IsAlmostInvariantSet M B -> M.μ B = 0 ∨ M.μ B = 1) ∧
      (∀ A : Set M.X, A ∈ M.𝓧 -> 0 < M.μ A ->
        M.μ (⋃ n : ℕ, preimageIter M (n + 1) A) = 1) ∧
      (∀ A B : Set M.X, A ∈ M.𝓧 -> B ∈ M.𝓧 -> 0 < M.μ A -> 0 < M.μ B ->
        (Chapter01.returnTimes M A B).Nonempty))

def IsSyndetic (A : Set ℕ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ i : ℕ, ∃ a ∈ A, i ≤ a ∧ a < i + N

def syndeticFamily : Set (Set ℕ) :=
  {A : Set ℕ | IsSyndetic A}

def Eigenvalue (M : System.{u}) (lam : ℂ) : Prop :=
  ∃ f : M.X -> ℂ, MeasureTheory.MemLp f 2 M.μ ∧
    ¬ f =ᵐ[M.μ] 0 ∧ Chapter01.koopman M.T f =ᵐ[M.μ] fun x => lam * f x

def Eigenfunction (M : System.{u}) (lam : ℂ) (f : M.X -> ℂ) : Prop :=
  MeasureTheory.MemLp f 2 M.μ ∧ ¬ f =ᵐ[M.μ] 0 ∧
    Chapter01.koopman M.T f =ᵐ[M.μ] fun x => lam * f x

def IsInvariantFunction (M : System.{u}) (f : M.X -> ℂ) : Prop :=
  Chapter01.koopman M.T f =ᵐ[M.μ] f

def IsAEEqConstant (M : System.{u}) (f : M.X -> ℂ) : Prop :=
  ∃ c : ℂ, f =ᵐ[M.μ] fun _ => c

def HasInvariantFunctionCharacterizations (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    (IsErgodic M ↔ ∀ f : M.X -> ℂ, MeasureTheory.MemLp f 2 M.μ ->
      IsInvariantFunction M f -> IsAEEqConstant M f)

def invariantSigmaAlgebra (M : System.{u}) : SetFamily M.X :=
  {A : Set M.X | IsAlmostInvariantSet M A}

def ConditionalExpectationInvariant (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    ∀ f : M.X -> ℂ, MeasureTheory.Integrable f M.μ ->
      MeasureTheory.condExp (MeasurableSpace.generateFrom (invariantSigmaAlgebra M))
          M.μ (Chapter01.koopman M.T f) =ᵐ[M.μ]
        MeasureTheory.condExp (MeasurableSpace.generateFrom (invariantSigmaAlgebra M)) M.μ f

def IsInvariantSigmaMeasurable (M : System.{u}) (f : M.X -> ℂ) : Prop :=
  @Measurable M.X ℂ
    (MeasurableSpace.generateFrom (invariantSigmaAlgebra M)) inferInstance f

def HasInvariantSigmaMeasurableRepresentative
    (M : System.{u}) (f : M.X -> ℂ) : Prop :=
  ∃ g : M.X -> ℂ, IsInvariantSigmaMeasurable M g ∧ f =ᵐ[M.μ] g

structure HilbertOperatorData where
  H : Type u
  normedAddCommGroup : NormedAddCommGroup H
  innerProductSpace : InnerProductSpace ℂ H
  completeSpace : CompleteSpace H
  U : H →L[ℂ] H

attribute [instance] HilbertOperatorData.normedAddCommGroup
  HilbertOperatorData.innerProductSpace HilbertOperatorData.completeSpace

def IsContraction (D : HilbertOperatorData.{u}) : Prop :=
  ∀ x : D.H, ‖D.U x‖ ≤ ‖x‖

def IsUnitary (D : HilbertOperatorData.{u}) : Prop :=
  Function.Surjective D.U ∧ ∀ x : D.H, ‖D.U x‖ = ‖x‖

def fixedVectors (D : HilbertOperatorData.{u}) : Set D.H :=
  {x : D.H | D.U x = x}

def MeanErgodicHilbertStatement (D : HilbertOperatorData.{u}) : Prop :=
  IsContraction D ->
    ∃ P : D.H →L[ℂ] D.H,
      (∀ x, P x ∈ fixedVectors D) ∧
      (∀ x ∈ fixedVectors D, P x = x) ∧
      ∀ x : D.H,
        Tendsto
          (fun n : ℕ => if n = 0 then 0 else
            ((n : ℂ)⁻¹) • ∑ i ∈ Finset.range n, (D.U^[i]) x)
          atTop (nhds (P x))

/-- The fixed-space/closed-coboundary orthogonality used in Remark 2.2.2. -/
def IsometryFixedSpaceOrthogonalityStatement (D : HilbertOperatorData.{u}) : Prop :=
  (∀ x : D.H, ‖D.U x‖ = ‖x‖) ->
    ∀ u : D.H,
      (D.U u = u ↔ ∀ v : D.H,
        @inner ℂ D.H _ u (v - D.U v) = 0)

def ergodicAverage (M : System.{u}) (f : M.X -> ℂ) (n : ℕ) (x : M.X) : ℂ :=
  if n = 0 then 0 else
    ((n : ℂ)⁻¹) * ∑ i ∈ Finset.range n, f ((M.T^[i]) x)

def realErgodicAverage (M : System.{u}) (f : M.X -> ℝ) (n : ℕ) (x : M.X) : ℝ :=
  if n = 0 then 0 else
    ((n : ℝ)⁻¹) * ∑ i ∈ Finset.range n, f ((M.T^[i]) x)

def MeanErgodicSystemStatement (M : System.{u}) (p : ENNReal) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    ∀ f : M.X -> ℂ, M.lpMember p f ->
      ∃ fstar : M.X -> ℂ, M.lpMember p fstar ∧ IsInvariantFunction M fstar ∧
        Tendsto (fun n => MeasureTheory.eLpNorm
          (fun x => ergodicAverage M f n x - fstar x) p M.μ) atTop (nhds 0) ∧
        MeasureTheory.condExp
            (MeasurableSpace.generateFrom (invariantSigmaAlgebra M)) M.μ f =ᵐ[M.μ] fstar ∧
        ∫ x, fstar x ∂M.μ = ∫ x, f x ∂M.μ ∧
        (IsErgodic M -> fstar =ᵐ[M.μ] fun _ => ∫ x, f x ∂M.μ)

def LpInclusionFiniteMeasureStatement (P : Chapter01.ProbabilitySpaceData.{u}) : Prop :=
  P.μ Set.univ < ⊤ ->
    ∀ p q : ENNReal, 0 < p -> p < q -> q ≤ ⊤ ->
      ∀ f : P.X -> ℂ, P.lpMember q f ->
        P.lpMember p f ∧
        MeasureTheory.eLpNorm f p P.μ ≤
          MeasureTheory.eLpNorm f q P.μ *
            ENNReal.rpow (P.μ Set.univ) (p.toReal⁻¹ - q.toReal⁻¹)

def KhintchineRecurrenceStatement (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    ∀ A : Set M.X, A ∈ M.𝓧 -> 0 < M.μ A -> ∀ ε : ℝ, 0 < ε ->
      IsSyndetic {n : ℕ | realMeasure M (A ∩ preimageIter M n A) >
        realMeasure M A * realMeasure M A - ε}

def MultipleKhintchineStatement (M : System.{u}) : Prop :=
  (IsErgodic M -> ∀ A : Set M.X, MeasurableSet A -> 0 < M.μ A ->
    ∀ ε : ℝ, 0 < ε ->
      IsSyndetic {n : ℕ |
        realMeasure M (A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A) >
          (realMeasure M A) ^ 3 - ε} ∧
      IsSyndetic {n : ℕ |
        realMeasure M
          (A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A ∩
            preimageIter M (3 * n) A) >
          (realMeasure M A) ^ 4 - ε}) ∧
  (∃ N : System.{u}, IsErgodic N ∧ ∀ l : ℕ, ∃ A : Set N.X,
    MeasurableSet A ∧ 0 < N.μ A ∧
    ∀ n : ℕ, 0 < n →
      realMeasure N
        (A ∩ preimageIter N n A ∩ preimageIter N (2 * n) A ∩
          preimageIter N (3 * n) A ∩ preimageIter N (4 * n) A) ≤
        (realMeasure N A) ^ l)

def ErgodicAverageAETends (M : System.{u}) (f fstar : M.X -> ℂ) : Prop :=
  ∀ᵐ x ∂M.μ, Tendsto (fun n => ergodicAverage M f n x) atTop (nhds (fstar x))

def BirkhoffPointwiseErgodicStatement (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    ∀ f : M.X -> ℂ, M.lpMember 1 f -> ∃ fstar : M.X -> ℂ,
      M.lpMember 1 fstar ∧ IsInvariantFunction M fstar ∧
      ErgodicAverageAETends M f fstar ∧
      ∫ x, fstar x ∂M.μ = ∫ x, f x ∂M.μ

def LOneMeanErgodicIdentifiesPointwiseLimitStatement (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    MeanErgodicSystemStatement M 1 ->
    ∀ f fstar : M.X -> ℂ, M.lpMember 1 f ->
      ErgodicAverageAETends M f fstar ->
        M.lpMember 1 fstar ∧ ∫ x, fstar x ∂M.μ = ∫ x, f x ∂M.μ

def ErgodicTimeAverageEqualsSpaceAverage (M : System.{u}) : Prop :=
  IsErgodic M -> ∀ f : M.X -> ℂ, M.lpMember 1 f ->
    ∀ᵐ x ∂M.μ,
      Tendsto (fun n => ergodicAverage M f n x) atTop
        (nhds (∫ y, f y ∂M.μ))

def MeanErgodicLimitPreservesLinfty (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    ∀ f fstar : M.X -> ℂ,
      M.lpMember ⊤ f ->
      M.lpMember 1 fstar ->
      Tendsto (fun n => MeasureTheory.eLpNorm
        (fun x => ergodicAverage M f n x - fstar x) 1 M.μ) atTop (nhds 0) ->
        M.lpMember ⊤ fstar ∧
        MeasureTheory.eLpNorm fstar ⊤ M.μ ≤ MeasureTheory.eLpNorm f ⊤ M.μ

def MaximalErgodicStatement (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    ∀ f : M.X -> ℝ, MeasureTheory.Integrable f M.μ -> ∀ α : ℝ,
      let B := {x | ∃ n : ℕ, 0 < n ∧ α < realErgodicAverage M f n x}
      MeasureTheory.NullMeasurableSet B M.μ ∧
        α * realMeasure M B ≤ ∫ x in B, f x ∂M.μ

def IsPositiveL1Contraction (M : System.{u})
    (U : (M.X -> ℝ) -> M.X -> ℝ) : Prop :=
  (∀ f g : M.X -> ℝ, ∀ a b : ℝ,
    U (fun x => a * f x + b * g x) = fun x => a * U f x + b * U g x) ∧
  (∀ f, (∀ᵐ x ∂M.μ, 0 ≤ f x) -> ∀ᵐ x ∂M.μ, 0 ≤ U f x) ∧
  ∀ f, MeasureTheory.Integrable f M.μ ->
    MeasureTheory.Integrable (U f) M.μ ∧
    MeasureTheory.eLpNorm (U f) 1 M.μ ≤ MeasureTheory.eLpNorm f 1 M.μ

def maximalRec {X : Type u} (U : (X -> ℝ) -> X -> ℝ) (f : X -> ℝ) :
    ℕ -> X -> ℝ
  | 0 => f
  | n + 1 => fun x => f x + U (fun y => max (maximalRec U f n y) 0) x

def PositiveContractionMaximalStatement (M : System.{u}) : Prop :=
  ∀ U : (M.X -> ℝ) -> M.X -> ℝ, IsPositiveL1Contraction M U ->
    ∀ f : M.X -> ℝ, MeasureTheory.Integrable f M.μ -> ∀ N : ℕ,
      let A := {x | 0 < maximalRec U f N x}
      MeasureTheory.NullMeasurableSet A M.μ ∧ 0 ≤ ∫ x in A, f x ∂M.μ

def WeakTypeMaximalInequalityStatement (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    ∀ f : M.X -> ℂ, M.lpMember 1 f -> ∀ α : ℝ, 0 < α ->
      M.μ {x | ∃ n : ℕ, 0 < n ∧ α < ‖ergodicAverage M f n x‖} ≤
        ENNReal.ofReal (MeasureTheory.eLpNorm f 1 M.μ).toReal /
          ENNReal.ofReal α

def DenseCoboundariesStatement (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    ∀ f : M.X -> ℂ, M.lpMember 1 f ->
      MeasureTheory.condExp (MeasurableSpace.generateFrom (invariantSigmaAlgebra M))
        M.μ f =ᵐ[M.μ] 0 ->
      ∀ ε : ℝ, 0 < ε -> ∃ g : M.X -> ℂ, M.lpMember 1 g ∧
        MeasureTheory.eLpNorm
          (fun x => f x - (g (M.T x) - g x)) 1 M.μ < ENNReal.ofReal ε

def OrbitVisitDensityStatement (M : System.{u}) : Prop :=
  IsErgodic M -> ∀ A : Set M.X, MeasurableSet A ->
    ∀ᵐ x ∂M.μ, Tendsto
      (fun n : ℕ => if n = 0 then 0 else
        ((n : ℝ)⁻¹) * ((Finset.range n).filter
          (fun i => (M.T^[i]) x ∈ A)).card)
      atTop (nhds (realMeasure M A))

def binaryDigit (x : ℝ) (n : ℕ) : ℤ :=
  ⌊(2 : ℝ) ^ (n + 1) * x⌋ - 2 * ⌊(2 : ℝ) ^ n * x⌋

def BorelNormalNumberTheoremStatement : Prop :=
  ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)),
    ∀ d : ℤ, d = 0 ∨ d = 1 ->
      Tendsto
        (fun n : ℕ => if n = 0 then 0 else
          (((Finset.range n).filter (fun i => binaryDigit x i = d)).card : ℝ) / n)
        atTop (nhds (1 / 2 : ℝ))

def ErgodicIffCesaroCorrelations (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    (IsErgodic M ↔ ∀ A B : Set M.X, A ∈ M.𝓧 -> B ∈ M.𝓧 ->
      cesaroTendsTo (fun n => correlation M A B n) (productMeasureValue M A B))

def ErgodicIffOnGeneratingSemiAlgebra (M : System.{u}) (S : SetFamily M.X) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    Chapter00.IsSemiAlgebra S ->
      Chapter00.generatedSigmaAlgebra S = M.𝓧 ->
        (IsErgodic M ↔ ∀ A B : Set M.X, A ∈ S -> B ∈ S ->
          cesaroTendsTo (fun n => correlation M A B n) (productMeasureValue M A B))

def StrongLawStatement : Prop :=
  ∀ P : Chapter01.ProbabilitySpaceData.{u}, ∀ X : ℕ -> P.X -> ℝ,
    Chapter01.IsProbabilitySpace P ->
    (∀ n, MeasureTheory.Integrable (X n) P.μ) ->
    (∀ n, MeasureTheory.Measure.map (X n) P.μ =
      MeasureTheory.Measure.map (X 0) P.μ) ->
    (∀ I : Finset ℕ, ∀ B : ℕ -> Set ℝ, (∀ i ∈ I, MeasurableSet (B i)) ->
      P.μ {ω | ∀ i ∈ I, X i ω ∈ B i} =
        ∏ i ∈ I, P.μ {ω | X i ω ∈ B i}) ->
      ∀ᵐ ω ∂P.μ, Tendsto
        (fun n : ℕ => if n = 0 then 0 else
          ((n : ℝ)⁻¹) * ∑ i ∈ Finset.range n, X i ω)
        atTop (nhds (∫ ω, X 0 ω ∂P.μ))

def StochasticMatrixLimitStatement : Prop :=
  ∀ k : ℕ, ∀ P : Matrix (Fin k) (Fin k) ℝ,
    (∀ i j, 0 ≤ P i j) -> (∀ i, ∑ j, P i j = 1) ->
    ∃ Q : Matrix (Fin k) (Fin k) ℝ,
      (∀ i j, Tendsto
        (fun N : ℕ => if N = 0 then 0 else
          ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N, (P ^ n) i j)
        atTop (nhds (Q i j))) ∧
      P * Q = Q ∧ Q * P = Q ∧ Q * Q = Q

def IsStochasticCesaroLimit {k : ℕ}
    (P Q : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  (∀ i j, Tendsto
      (fun N : ℕ => if N = 0 then 0 else
        ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N, (P ^ n) i j)
      atTop (nhds (Q i j))) ∧
    P * Q = Q ∧ Q * P = Q ∧ Q * Q = Q

def IsIrreducibleStochasticMatrix {k : ℕ}
    (P : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ (∀ i, ∑ j, P i j = 1) ∧
    ∀ i j, ∃ n : ℕ, 0 < (P ^ n) i j

def StochasticMatrixRowsEqual {k : ℕ}
    (Q : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ i i' j, Q i j = Q i' j

def StochasticMatrixStrictlyPositive {k : ℕ}
    (Q : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ i j, 0 < Q i j

/-- The characteristic polynomial has `1` as a root of algebraic multiplicity one. -/
def HasSimpleEigenvalueOne {k : ℕ}
    (P : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∃ q : Polynomial ℝ,
    Matrix.charpoly P = (Polynomial.X - Polynomial.C 1) * q ∧
      q.eval 1 ≠ 0

noncomputable def compactGroupRotationSystem {G : Type u} [MeasurableSpace G]
    [Group G] (m : MeasureTheory.Measure G) (a : G) : System.{u} where
  X := G
  measurableSpace := inferInstance
  μ := m
  T := fun x => a * x

def CompactGroupRotationErgodicityStatement : Prop :=
  ∀ G : Type u, ∀ _ : Group G, ∀ _ : MetricSpace G,
  ∀ _ : CompactSpace G, ∀ _ : MeasurableSpace G, ∀ _ : BorelSpace G,
  ∀ _ : IsTopologicalGroup G, ∀ m : MeasureTheory.Measure G,
    MeasureTheory.IsProbabilityMeasure m ->
    (∀ g : G, MeasureTheory.MeasurePreserving (fun x : G => g * x) m m) -> ∀ a : G,
      (IsErgodic (compactGroupRotationSystem m a) ↔
        closure (Set.range fun n : ℤ => a ^ n) = Set.univ) ∧
      (IsErgodic (compactGroupRotationSystem m a) ->
        ∀ x y : G, x * y = y * x)

noncomputable def circleEndomorphismSystem (n : ℕ) : System.{0} where
  X := AddCircle (1 : ℝ)
  measurableSpace := inferInstance
  μ := AddCircle.haarAddCircle
  T := fun x => n • x

def CircleEndomorphismErgodicityStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n -> IsErgodic (circleEndomorphismSystem n)

structure ContinuousCircleCharacter (G : Type u) [AddCommGroup G]
    [TopologicalSpace G] where
  toFun : G -> ℂ
  map_zero : toFun 0 = 1
  map_add : ∀ x y, toFun (x + y) = toFun x * toFun y
  continuous : Continuous toFun
  unit_norm : ∀ x, ‖toFun x‖ = 1

structure ContinuousMultiplicativeCircleCharacter (G : Type u) [CommGroup G]
    [TopologicalSpace G] where
  toFun : G → ℂ
  map_one : toFun 1 = 1
  map_mul : ∀ x y, toFun (x * y) = toFun x * toFun y
  continuous : Continuous toFun
  unit_norm : ∀ x, ‖toFun x‖ = 1

noncomputable def compactGroupEndomorphismSystem {G : Type u}
    [MeasurableSpace G] [AddCommGroup G] (m : MeasureTheory.Measure G) (A : G →+ G) :
    System.{u} where
  X := G
  measurableSpace := inferInstance
  μ := m
  T := A

/- The following two legacy forms record the earlier, overly general
formalizations.  They are retained only so that `Counterexamples.lean` can
document why the Haar hypothesis below is necessary. -/
def LegacyCompactGroupEndomorphismErgodicityStatement : Prop :=
  ∀ G : Type u, ∀ _ : AddCommGroup G, ∀ _ : MetricSpace G,
  ∀ _ : CompactSpace G, ∀ _ : MeasurableSpace G, ∀ _ : BorelSpace G,
  ∀ m : MeasureTheory.Measure G, MeasureTheory.IsProbabilityMeasure m ->
  ∀ A : G →+ G, Continuous A -> Function.Surjective A ->
    MeasureTheory.MeasurePreserving A m m ->
    (IsErgodic (compactGroupEndomorphismSystem m A) ↔
      ∀ χ : ContinuousCircleCharacter G,
        (∃ n : ℕ, 0 < n ∧
          (fun x => χ.toFun ((A : G -> G)^[n] x)) = χ.toFun) ->
        ∀ x, χ.toFun x = 1)

/-- The system in Example 2.1.15, written in the multiplicative language of
continuous circle characters. -/
noncomputable def compactGroupHaarEndomorphismSystem {G : Type u}
    [MeasurableSpace G] [CommGroup G] (m : MeasureTheory.Measure G)
    (A : G →* G) : System.{u} where
  X := G
  measurableSpace := inferInstance
  μ := m
  T := A

/-- Source: Example 2.1.15.  The measure is the normalized Haar measure, as
in the textbook; the topological-group hypothesis makes this meaningful. -/
def CompactGroupEndomorphismErgodicityStatement : Prop :=
  ∀ G : Type u, ∀ _ : CommGroup G, ∀ _ : MetricSpace G,
  ∀ _ : CompactSpace G, ∀ _ : IsTopologicalGroup G,
  ∀ _ : MeasurableSpace G, ∀ _ : BorelSpace G,
  ∀ m : MeasureTheory.Measure G, MeasureTheory.IsProbabilityMeasure m ->
    m.IsHaarMeasure ->
  ∀ A : G →* G, Continuous A -> Function.Surjective A ->
    (IsErgodic (compactGroupHaarEndomorphismSystem m A) ↔
      ∀ χ : ContinuousMultiplicativeCircleCharacter G,
        (∃ n : ℕ, 0 < n ∧
          (fun x => ContinuousMultiplicativeCircleCharacter.toFun χ
            ((A : G -> G)^[n] x)) =
            ContinuousMultiplicativeCircleCharacter.toFun χ) ->
        ∀ x, ContinuousMultiplicativeCircleCharacter.toFun χ x = 1)

def torusMatrixMap (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) :
    Chapter01.Torus n -> Chapter01.Torus n :=
  fun x i => ∑ j, A i j • x j

noncomputable def torusEndomorphismSystem (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) : System.{0} where
  X := Chapter01.Torus n
  measurableSpace := inferInstance
  μ := Chapter01.torusHaarMeasure n
  T := torusMatrixMap n A

def HasRootOfUnityEigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ lam : ℂ, (∃ q : ℕ, 0 < q ∧ lam ^ q = 1) ∧
    ∃ v : Fin n -> ℂ, v ≠ 0 ∧
      ∀ i, ∑ j, (A i j : ℂ) * v j = lam * v i

def TorusEndomorphismErgodicityStatement : Prop :=
  ∀ n : ℕ, ∀ A : Matrix (Fin n) (Fin n) ℤ,
    Function.Surjective (torusMatrixMap n A) ->
      (IsErgodic (torusEndomorphismSystem n A) ↔
        ¬ HasRootOfUnityEigenvalue A)

def BernoulliShiftErgodicityStatement : Prop :=
  ∀ M : System.{0},
    (∃ k : ℕ, Chapter01.IsBernoulliShiftSystem M k) -> IsErgodic M

def MarkovShiftErgodicCharacterization : Prop :=
  ∀ M : System.{u}, ∀ k : ℕ, ∀ p : Fin k -> ℝ,
    ∀ P : Matrix (Fin k) (Fin k) ℝ,
    Chapter01.IsMarkovShiftWith M k p P ->
      (∀ i, 0 < p i) ->
      (IsErgodic M ↔ IsIrreducibleStochasticMatrix P)

def MarkovShiftErgodicEquivalentConditionsStatement : Prop :=
  ∀ M : System.{u}, ∀ k : ℕ, ∀ p : Fin k -> ℝ,
  ∀ P Q : Matrix (Fin k) (Fin k) ℝ,
    Chapter01.IsMarkovShiftWith M k p P ->
    (∀ i, 0 < p i) -> IsStochasticCesaroLimit P Q ->
      (IsErgodic M ↔ StochasticMatrixRowsEqual Q) ∧
      (StochasticMatrixRowsEqual Q ↔ StochasticMatrixStrictlyPositive Q) ∧
      (StochasticMatrixStrictlyPositive Q ↔ IsIrreducibleStochasticMatrix P) ∧
      (IsIrreducibleStochasticMatrix P ↔ HasSimpleEigenvalueOne P)

def IsWeakMixing (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
    ∀ A B : Set M.X, A ∈ M.𝓧 -> B ∈ M.𝓧 ->
      cesaroTendsTo (fun n => |correlation M A B n - productMeasureValue M A B|) 0

def IsStrongMixing (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
    ∀ A B : Set M.X, A ∈ M.𝓧 -> B ∈ M.𝓧 ->
      seqTendsTo (fun n => correlation M A B n) (productMeasureValue M A B)

def IsKMixing (M : System.{u}) (k : ℕ) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
    ∀ A : Fin (k + 1) -> Set M.X, (∀ i, MeasurableSet (A i)) ->
    ∀ gaps : ℕ -> Fin k -> ℕ, (∀ i, Tendsto (fun r => gaps r i) atTop atTop) ->
      Tendsto
        (fun r => realMeasure M
          (A 0 ∩ ⋂ i : Fin k,
            preimageIter M (∑ j ∈ Finset.Iic i, gaps r j) (A i.succ)))
        atTop (nhds (∏ i, realMeasure M (A i)))

def IsUniformMixing (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
    ∀ A : Set M.X, MeasurableSet A ->
    ∀ k : ℕ, ∀ B : Fin k -> Set M.X, (∀ i, MeasurableSet (B i)) ->
    ∀ ε : ℝ, 0 < ε -> ∃ N : ℕ, ∀ n : ℕ, N ≤ n ->
      ∀ C : Set M.X,
        C ∈ Chapter00.generatedSigmaAlgebra
          {C | ∃ j : ℕ, n ≤ j ∧ ∃ i : Fin k, C = preimageIter M j (B i)} ->
        |realMeasure M (A ∩ C) - realMeasure M A * realMeasure M C| < ε

def HasMixingImplications (M : System.{u}) : Prop :=
  IsStrongMixing M -> IsWeakMixing M ∧ IsErgodic M

def RohlinMixingProblem : Prop :=
  ∀ M : System.{u}, IsStrongMixing M -> ∀ k : ℕ, IsKMixing M k

structure MeasurePreservingZ2ActionData where
  X : Type u
  measurableSpace : MeasurableSpace X
  μ : @MeasureTheory.Measure X measurableSpace
  action : (ℤ × ℤ) -> X -> X

attribute [instance] MeasurePreservingZ2ActionData.measurableSpace

def IsMeasurePreservingZ2Action (A : MeasurePreservingZ2ActionData.{u}) : Prop :=
  MeasureTheory.IsProbabilityMeasure A.μ ∧
    (∀ x, A.action (0, 0) x = x) ∧
    (∀ g h x, A.action (g.1 + h.1, g.2 + h.2) x =
      A.action g (A.action h x)) ∧
    ∀ g, MeasureTheory.MeasurePreserving (A.action g) A.μ A.μ

def z2EscapeSize (g : ℤ × ℤ) : ℕ :=
  g.1.natAbs + g.2.natAbs

def z2Correlation (A : MeasurePreservingZ2ActionData.{u})
    (E F : Set A.X) (g : ℤ × ℤ) : ℝ :=
  (A.μ (E ∩ (A.action g) ⁻¹' F)).toReal

def IsOneMixingZ2Action (A : MeasurePreservingZ2ActionData.{u}) : Prop :=
  ∀ E F : Set A.X, MeasurableSet E -> MeasurableSet F ->
    ∀ g : ℕ -> ℤ × ℤ,
      Tendsto (fun n => z2EscapeSize (g n)) atTop atTop ->
      Tendsto (fun n => z2Correlation A E F (g n)) atTop
        (nhds ((A.μ E).toReal * (A.μ F).toReal))

def IsTwoMixingZ2Action (A : MeasurePreservingZ2ActionData.{u}) : Prop :=
  ∀ E₀ E₁ E₂ : Set A.X,
    MeasurableSet E₀ -> MeasurableSet E₁ -> MeasurableSet E₂ ->
    ∀ g h : ℕ -> ℤ × ℤ,
      Tendsto (fun n => z2EscapeSize (g n)) atTop atTop ->
      Tendsto (fun n => z2EscapeSize (h n)) atTop atTop ->
      Tendsto (fun n => z2EscapeSize
        ((g n).1 - (h n).1, (g n).2 - (h n).2)) atTop atTop ->
      Tendsto
        (fun n => (A.μ
          (E₀ ∩ (A.action (g n)) ⁻¹' E₁ ∩ (A.action (h n)) ⁻¹' E₂)).toReal)
        atTop (nhds ((A.μ E₀).toReal * (A.μ E₁).toReal * (A.μ E₂).toReal))

def relativeSigmaAlgebra (M N : System.{u}) (π : M.X -> N.X) : SetFamily M.X :=
  {A | ∃ B : Set N.X, MeasurableSet B ∧ A = π ⁻¹' B}

def relativeCondExp (M N : System.{u}) (π : M.X -> N.X)
    (f : M.X -> ℂ) : M.X -> ℂ :=
  MeasureTheory.condExp
    (MeasurableSpace.generateFrom (relativeSigmaAlgebra M N π)) M.μ f

def IsRelativelyStrongMixingOver (M N : System.{u}) (π : M.X -> N.X) : Prop :=
  Chapter01.IsFactorMap M N π ∧
    ∀ f g : M.X -> ℂ, M.lpMember 2 f -> M.lpMember 2 g ->
      relativeCondExp M N π f =ᵐ[M.μ] 0 ->
      Tendsto
        (fun n => MeasureTheory.eLpNorm
          (relativeCondExp M N π
            (fun x => f ((M.T^[n]) x) * star (g x))) 2 M.μ)
        atTop (nhds 0)

def IsRelativelyTwoMixingOver (M N : System.{u}) (π : M.X -> N.X) : Prop :=
  Chapter01.IsFactorMap M N π ∧
    ∀ f₀ f₁ f₂ : M.X -> ℂ,
      M.lpMember ⊤ f₀ -> M.lpMember ⊤ f₁ -> M.lpMember ⊤ f₂ ->
      relativeCondExp M N π f₀ =ᵐ[M.μ] 0 ->
      ∀ a b : ℕ -> ℕ,
        Tendsto a atTop atTop -> Tendsto b atTop atTop ->
        Tendsto (fun n => ((a n : ℤ) - (b n : ℤ)).natAbs) atTop atTop ->
        Tendsto
          (fun n => MeasureTheory.eLpNorm
            (relativeCondExp M N π
              (fun x => f₀ x * f₁ ((M.T^[a n]) x) * f₂ ((M.T^[b n]) x)))
            2 M.μ) atTop (nhds 0)

def LedrappierAndRelativeRohlinCounterexamples : Prop :=
  (∃ A : MeasurePreservingZ2ActionData.{u},
    IsMeasurePreservingZ2Action A ∧ IsOneMixingZ2Action A ∧
      ¬ IsTwoMixingZ2Action A) ∧
  (∃ M N : System.{u}, ∃ π : M.X -> N.X,
    IsRelativelyStrongMixingOver M N π ∧
      ¬ IsRelativelyTwoMixingOver M N π)

def MixingCriteriaOnSemiAlgebra (M : System.{u}) (S : SetFamily M.X) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    Chapter00.IsSemiAlgebra S ->
    Chapter00.generatedSigmaAlgebra S = M.𝓧 ->
      (IsWeakMixing M ↔ ∀ A B : Set M.X, A ∈ S -> B ∈ S ->
        cesaroTendsTo (fun n => |correlation M A B n - productMeasureValue M A B|) 0) ∧
      (IsStrongMixing M ↔ ∀ A B : Set M.X, A ∈ S -> B ∈ S ->
        seqTendsTo (fun n => correlation M A B n) (productMeasureValue M A B))

def KoopmanVonNeumannZeroDensityLemma : Prop :=
  ∀ a : ℕ -> ℂ, BddAbove (Set.range fun n => ‖a n‖) ->
    (cesaroTendsTo (fun n => ‖a n‖) 0 ↔
      (∃ J : Set ℕ,
        Chapter00.lowerAsymptoticDensity J = 0 ∧
        Chapter00.upperAsymptoticDensity J = 0 ∧
        Tendsto a (Filter.principal Jᶜ ⊓ atTop) (nhds 0)) ∧
      cesaroTendsTo (fun n => ‖a n‖ ^ 2) 0)

def WeakMixingEquivalentCharacterizations (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    (IsWeakMixing M ↔
      ((∀ A B : Set M.X, MeasurableSet A -> MeasurableSet B ->
        ∃ J : Set ℕ, Chapter00.densityOneFamily J ∧
          Tendsto (fun n => correlation M A B n)
            (Filter.principal J ⊓ atTop) (nhds (productMeasureValue M A B))) ∧
      ∀ A B : Set M.X, MeasurableSet A -> MeasurableSet B ->
        cesaroTendsTo
          (fun n => (correlation M A B n - productMeasureValue M A B) ^ 2) 0))

def functionCorrelation (M : System.{u})
    (f g : M.X -> ℂ) (n : ℕ) : ℂ :=
  ∫ x, f ((M.T^[n]) x) * star (g x) ∂M.μ

def productOfMeans (M : System.{u}) (f g : M.X -> ℂ) : ℂ :=
  (∫ x, f x ∂M.μ) * star (∫ x, g x ∂M.μ)

def SpectralErgodicWeakStrongCharacterizations (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    ((IsErgodic M ↔
      ∀ f g : M.X -> ℂ, M.lpMember 2 f -> M.lpMember 2 g ->
        Tendsto (fun N : ℕ => if N = 0 then 0 else
          ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N, functionCorrelation M f g n)
          atTop (nhds (productOfMeans M f g))) ∧
    (IsWeakMixing M ↔
      ∀ f g : M.X -> ℂ, M.lpMember 2 f -> M.lpMember 2 g ->
        cesaroTendsTo
          (fun n => ‖functionCorrelation M f g n - productOfMeans M f g‖) 0) ∧
    (IsStrongMixing M ↔
      ∀ f g : M.X -> ℂ, M.lpMember 2 f -> M.lpMember 2 g ->
        Tendsto (fun n => functionCorrelation M f g n) atTop
          (nhds (productOfMeans M f g))))

def AreWeaklyDisjoint (M : System.{u}) (N : System.{v}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
  Chapter01.IsMeasurePreservingSystem N ∧
  ∀ A : Set (M.X × N.X), MeasurableSet A ->
    (M.μ.prod N.μ)
      (Chapter00.symmDiff
        ((fun p => (M.T p.1, N.T p.2)) ⁻¹' A) A) = 0 ->
      (M.μ.prod N.μ) A = 0 ∨ (M.μ.prod N.μ) A = 1

def ProductWeakMixingCharacterization (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    (IsWeakMixing M ↔ AreWeaklyDisjoint M M) ∧
      (IsWeakMixing M ↔ ∀ N : System.{u}, IsErgodic N -> AreWeaklyDisjoint M N)

def HasContinuousSpectrum (M : System.{u}) : Prop :=
  (∀ lam : ℂ, Eigenvalue M lam -> lam = 1) ∧
    ∀ f : M.X -> ℂ, Eigenfunction M 1 f -> IsAEEqConstant M f

def WeakMixingIffContinuousSpectrum (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    Chapter01.IsInvertibleMeasurePreservingMap M.𝓧 M.μ M.𝓧 M.μ M.T ->
    (IsWeakMixing M ↔ HasContinuousSpectrum M)

def RotationNotWeakMixingStatement : Prop :=
  ∀ G : Type u, ∀ _ : CommGroup G, ∀ _ : MetricSpace G,
  ∀ _ : CompactSpace G, ∀ _ : MeasurableSpace G, ∀ _ : BorelSpace G,
  ∀ _ : IsTopologicalGroup G, ∀ _ : Nontrivial G,
  ∀ m : MeasureTheory.Measure G, MeasureTheory.IsProbabilityMeasure m ->
    (∀ g : G, MeasureTheory.MeasurePreserving (fun x : G => g * x) m m) -> ∀ a : G,
      (∃ χ : ContinuousMultiplicativeCircleCharacter G,
        ¬ IsAEEqConstant (compactGroupRotationSystem m a)
          (ContinuousMultiplicativeCircleCharacter.toFun χ : G → ℂ)) ->
      ¬ IsWeakMixing (compactGroupRotationSystem m a)

def LegacyCompactGroupEndomorphismMixingEquivalence : Prop :=
  ∀ G : Type u, ∀ _ : AddCommGroup G, ∀ _ : MetricSpace G,
  ∀ _ : CompactSpace G, ∀ _ : MeasurableSpace G, ∀ _ : BorelSpace G,
  ∀ m : MeasureTheory.Measure G, MeasureTheory.IsProbabilityMeasure m ->
  ∀ A : G →+ G, Continuous A -> Function.Surjective A ->
    MeasureTheory.MeasurePreserving A m m ->
    let M := compactGroupEndomorphismSystem m A
    (IsErgodic M ↔ IsWeakMixing M) ∧ (IsWeakMixing M ↔ IsStrongMixing M)

/-- Source: Theorem 2.4.15.  This is the compact abelian topological-group
endomorphism statement for normalized Haar measure from the textbook. -/
def CompactGroupEndomorphismMixingEquivalence : Prop :=
  ∀ G : Type u, ∀ _ : CommGroup G, ∀ _ : MetricSpace G,
  ∀ _ : CompactSpace G, ∀ _ : IsTopologicalGroup G,
  ∀ _ : MeasurableSpace G, ∀ _ : BorelSpace G,
  ∀ m : MeasureTheory.Measure G, MeasureTheory.IsProbabilityMeasure m ->
    m.IsHaarMeasure ->
  ∀ A : G →* G, Continuous A -> Function.Surjective A ->
    let M := compactGroupHaarEndomorphismSystem m A
    (IsErgodic M ↔ IsWeakMixing M) ∧ (IsWeakMixing M ↔ IsStrongMixing M)

def BernoulliShiftStrongMixingStatement : Prop :=
  ∀ M : System.{0},
    (∃ k : ℕ, Chapter01.IsBernoulliShiftSystem M k) ->
      IsStrongMixing M

def MarkovShiftMixingCharacterization : Prop :=
  ∀ M : System.{0}, ∀ k : ℕ, ∀ p : Fin k -> ℝ,
    ∀ P : Matrix (Fin k) (Fin k) ℝ,
    Chapter01.IsMarkovShiftWith M k p P ->
      (∀ i, 0 < p i) ->
      (IsWeakMixing M ↔ IsStrongMixing M) ∧
      (IsStrongMixing M ↔
        (IsIrreducibleStochasticMatrix P ∧
          Chapter00.IsAperiodicNonnegativeMatrix k P)) ∧
      ((IsIrreducibleStochasticMatrix P ∧
          Chapter00.IsAperiodicNonnegativeMatrix k P) ↔
        ∀ i j, Tendsto (fun n => (P ^ n) i j) atTop (nhds (p j)))

def FamilyConvergesTo {α : Type u} [TopologicalSpace α]
    (F : Set (Set ℕ)) (x : ℕ -> α) (a : α) : Prop :=
  ∀ U : Set α, IsOpen U -> a ∈ U -> {n : ℕ | x n ∈ U} ∈ F

def IsIPSet (A : Set ℕ) : Prop :=
  ∃ p : ℕ -> ℕ, (∀ i, 0 < p i) ∧
    A = {n | ∃ s : Finset ℕ, s.Nonempty ∧ s.sum p = n}

def IsIPStarSet (A : Set ℕ) : Prop :=
  ∀ B : Set ℕ, IsIPSet B -> (A ∩ B).Nonempty

def IsRigidFunction (M : System.{u}) (f : M.X -> ℂ) : Prop :=
  M.lpMember 2 f ∧ ∃ n : ℕ -> ℕ, StrictMono n ∧
    Tendsto
      (fun k => MeasureTheory.eLpNorm
        (fun x => f ((M.T^[n k]) x) - f x) 2 M.μ)
      atTop (nhds 0)

def IsMildMixing (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
    ∀ A B : Set M.X, A ∈ M.𝓧 -> B ∈ M.𝓧 ->
      FamilyConvergesTo {E : Set ℕ | IsIPStarSet E}
        (fun n => correlation M A B n) (productMeasureValue M A B)

def MildMixingCharacterizations (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    (IsMildMixing M ↔ ∀ f : M.X -> ℂ, IsRigidFunction M f -> IsAEEqConstant M f)

def HasEigenvalueProperties (M : System.{u}) : Prop :=
  IsErgodic M ->
    (∀ lam : ℂ, ∀ f : M.X -> ℂ, Eigenfunction M lam f ->
      ‖lam‖ = 1 ∧ ∃ c : ℝ, 0 < c ∧
        (fun x => ‖f x‖) =ᵐ[M.μ] fun _ => c) ∧
    (∀ lam ξ : ℂ, lam ≠ ξ ->
      ∀ f g : M.X -> ℂ, Eigenfunction M lam f -> Eigenfunction M ξ g ->
        ∫ x, f x * star (g x) ∂M.μ = 0) ∧
    (∀ lam : ℂ, ∀ f g : M.X -> ℂ,
      Eigenfunction M lam f -> Eigenfunction M lam g ->
        ∃ c : ℂ, f =ᵐ[M.μ] fun x => c * g x) ∧
    (1 ∈ {lam : ℂ | Eigenvalue M lam} ∧
      ∀ lam ξ : ℂ, Eigenvalue M lam -> Eigenvalue M ξ ->
        Eigenvalue M (lam * ξ⁻¹))

def IsL2Separable (M : System.{u}) : Prop :=
  ∃ d : ℕ -> (M.X -> ℂ),
    (∀ n, M.lpMember 2 (d n)) ∧
    ∀ f : M.X -> ℂ, M.lpMember 2 f -> ∀ ε : ℝ, 0 < ε ->
      ∃ n, MeasureTheory.eLpNorm (fun x => f x - d n x) 2 M.μ < ENNReal.ofReal ε

def EigenspacesAndCountabilityStatement (M : System.{u}) : Prop :=
  IsErgodic M ->
    (∀ lam : ℂ, ∀ f g : M.X -> ℂ,
      Eigenfunction M lam f -> Eigenfunction M lam g ->
        ∃ c : ℂ, f =ᵐ[M.μ] fun x => c * g x) ∧
    (IsL2Separable M -> Set.Countable {lam : ℂ | Eigenvalue M lam})

def IsAlmostPeriodicFunction (M : System.{u}) (f : M.X -> ℂ) : Prop :=
  M.lpMember 2 f ∧ ∃ inv : M.X -> M.X,
    Function.LeftInverse inv M.T ∧ Function.RightInverse inv M.T ∧
    ∀ ε : ℝ, 0 < ε -> ∃ F : Finset (M.X -> ℂ),
      (∀ g ∈ F, M.lpMember 2 g) ∧
      ∀ n : ℤ, ∃ g ∈ F,
        MeasureTheory.eLpNorm
          (fun x => f ((if 0 ≤ n then M.T^[n.toNat] else inv^[n.natAbs]) x) - g x)
          2 M.μ < ENNReal.ofReal ε

def IsBoundedAlmostPeriodicFunction (M : System.{u}) (f : M.X -> ℂ) : Prop :=
  M.lpMember ⊤ f ∧ IsAlmostPeriodicFunction M f

def BoundedAlmostPeriodicFunctionsFormAlgebra (M : System.{u}) : Prop :=
  (∀ f g : M.X -> ℂ,
    IsBoundedAlmostPeriodicFunction M f -> IsBoundedAlmostPeriodicFunction M g ->
      IsBoundedAlmostPeriodicFunction M (fun x => f x + g x) ∧
      IsBoundedAlmostPeriodicFunction M (fun x => f x * g x)) ∧
  (∀ f : M.X -> ℂ, IsBoundedAlmostPeriodicFunction M f ->
    ∀ c : ℂ,
      IsBoundedAlmostPeriodicFunction M (fun x => c * f x) ∧
      IsBoundedAlmostPeriodicFunction M (fun x => star (f x)) ∧
      IsBoundedAlmostPeriodicFunction M (Chapter01.koopman M.T f))

def KoopmanVonNeumannSpectralMixingStatement (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    Chapter01.IsInvertibleMeasurePreservingMap M.𝓧 M.μ M.𝓧 M.μ M.T ->
    (HasContinuousSpectrum M ↔ IsWeakMixing M)

def IsPositiveDefinite (φ : ℤ -> ℂ) : Prop :=
  ∀ N : ℕ, ∀ a : Fin (N + 1) -> ℂ,
    let q := ∑ m : Fin (N + 1), ∑ n : Fin (N + 1),
      a m * star (a n) * φ (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ))
    q.im = 0 ∧ 0 ≤ q.re

def HasMeasurableRepresentativeForFamily (M : System.{u})
    (A : SetFamily M.X) (f : M.X -> ℂ) : Prop :=
  ∃ g : M.X -> ℂ,
    @Measurable M.X ℂ (MeasurableSpace.generateFrom A) inferInstance g ∧
      f =ᵐ[M.μ] g

abbrev Circle := _root_.Circle

instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩
instance circleOpensMeasurableSpace : OpensMeasurableSpace Circle := ⟨le_rfl⟩

structure CircleMeasureData where
  μ : MeasureTheory.Measure Circle
  isFinite : MeasureTheory.IsFiniteMeasure μ

attribute [instance] CircleMeasureData.isFinite

def circleFourierCoefficient (μ : CircleMeasureData) (n : ℤ) : ℂ :=
  ∫ z, (z : ℂ) ^ n ∂μ.μ

def HasSpectralMeasure (D : HilbertOperatorData.{u})
    (x : D.H) (μ : CircleMeasureData) : Prop :=
  ∀ n : ℕ, circleFourierCoefficient μ n =
    @inner ℂ D.H inferInstance x ((D.U^[n]) x)

def HerglotzStatement : Prop :=
  ∀ φ : ℤ -> ℂ, IsPositiveDefinite φ ->
    ∃! μ : CircleMeasureData,
      ∀ n : ℤ, circleFourierCoefficient μ n = φ n

def SpectralMeasureStatement (D : HilbertOperatorData.{u}) : Prop :=
  IsUnitary D -> ∀ x : D.H, ∃! μ : CircleMeasureData,
    HasSpectralMeasure D x μ

def IsEigenvector (D : HilbertOperatorData.{u}) (x : D.H) : Prop :=
  x ≠ 0 ∧ ∃ lam : ℂ, D.U x = lam • x

def InDiscreteSpectralSubspace (D : HilbertOperatorData.{u}) (x : D.H) : Prop :=
  ∀ ε : ℝ, 0 < ε -> ∃ s : Finset D.H, (∀ y ∈ s, IsEigenvector D y) ∧
    ∃ c : D.H -> ℂ, ‖x - ∑ y ∈ s, c y • y‖ < ε

def InContinuousSpectralSubspace (D : HilbertOperatorData.{u}) (x : D.H) : Prop :=
  ∀ y : D.H, IsEigenvector D y ->
    @inner ℂ D.H inferInstance x y = 0

def DiscreteContinuousSpectralSubspacesStatement (D : HilbertOperatorData.{u}) : Prop :=
  IsUnitary D -> ∀ x : D.H, ∃! p : D.H × D.H,
    x = p.1 + p.2 ∧
    InDiscreteSpectralSubspace D p.1 ∧
    InContinuousSpectralSubspace D p.2

def WienerTheoremStatement (D : HilbertOperatorData.{u}) : Prop :=
  IsUnitary D -> ∀ x : D.H,
    (InContinuousSpectralSubspace D x ↔
      Tendsto
        (fun N : ℕ => if N = 0 then 0 else
          ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
            ‖@inner ℂ D.H inferInstance ((D.U^[n]) x) x‖ ^ 2)
        atTop (nhds 0))

def IsAlmostPeriodicVector (D : HilbertOperatorData.{u}) (x : D.H) : Prop :=
  ∀ ε : ℝ, 0 < ε -> ∃ F : Finset D.H,
    ∀ n : ℕ, ∃ y ∈ F, ‖(D.U^[n]) x - y‖ < ε

def AlmostPeriodicVectorStatement (D : HilbertOperatorData.{u}) : Prop :=
  IsUnitary D -> ∀ x : D.H,
    IsAlmostPeriodicVector D x ↔ InDiscreteSpectralSubspace D x

/-- A representative-level closed linear subspace of `L²`, saturated under a.e. equality. -/
def IsClosedL2FunctionSubspace (M : System.{u}) (H : Set (M.X -> ℂ)) : Prop :=
  (fun _ : M.X => (0 : ℂ)) ∈ H ∧
  (∀ f ∈ H, M.lpMember 2 f) ∧
  (∀ f ∈ H, ∀ g ∈ H, ∀ a b : ℂ,
    (fun x => a * f x + b * g x) ∈ H) ∧
  (∀ f ∈ H, ∀ g : M.X -> ℂ, f =ᵐ[M.μ] g -> g ∈ H) ∧
  ∀ fseq : ℕ -> M.X -> ℂ, (∀ n, fseq n ∈ H) ->
    ∀ f : M.X -> ℂ, M.lpMember 2 f ->
      Tendsto (fun n => MeasureTheory.eLpNorm
        (fun x => fseq n x - f x) 2 M.μ) atTop (nhds 0) -> f ∈ H

def AlgebraOfBoundedFunctionsStatement (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
  ∀ H : Set (M.X -> ℂ), IsClosedL2FunctionSubspace M H ->
    (fun _ : M.X => (1 : ℂ)) ∈ H ->
    (∀ f ∈ H, M.lpMember ⊤ f) ->
    (∀ f ∈ H, (fun x => star (f x)) ∈ H) ->
    (∀ f ∈ H, ∀ g ∈ H, (fun x => f x * g x) ∈ H) ->
      ∃ A : SetFamily M.X, Chapter00.IsSigmaAlgebraFamily A ∧ A ⊆ M.𝓧 ∧
        (∀ f : M.X -> ℂ, f ∈ H ↔
          M.lpMember 2 f ∧
          HasMeasurableRepresentativeForFamily M A f) ∧
        ((Chapter01.IsInvertibleMeasurePreservingMap
            M.𝓧 M.μ M.𝓧 M.μ M.T ∧
          ∀ f : M.X -> ℂ,
            f ∈ H ↔ (fun x => f (M.T x)) ∈ H) ->
          ∀ B : Set M.X,
            B ∈ Chapter00.generatedSigmaAlgebra A ↔
              M.T ⁻¹' B ∈ Chapter00.generatedSigmaAlgebra A)

def IsInvariantSubSigmaAlgebraFamily (M : System.{u}) (K : SetFamily M.X) : Prop :=
  Chapter00.IsSigmaAlgebraFamily K ∧ K ⊆ M.𝓧 ∧
    ∀ A : Set M.X, A ∈ K ↔ M.T ⁻¹' A ∈ K

def KroneckerFactorStatement (M : System.{u}) : Prop :=
  ∃ K : SetFamily M.X, IsInvariantSubSigmaAlgebraFamily M K ∧
    ∀ f : M.X -> ℂ,
      IsAlmostPeriodicFunction M f ↔
        M.lpMember 2 f ∧
        HasMeasurableRepresentativeForFamily M K f

def productTransformation (M : System.{u}) (p : M.X × M.X) : M.X × M.X :=
  (M.T p.1, M.T p.2)

def IsInvariantL2Kernel (M : System.{u}) (H : M.X × M.X -> ℂ) : Prop :=
  MeasureTheory.MemLp H 2 (M.μ.prod M.μ) ∧
    H ∘ productTransformation M =ᵐ[M.μ.prod M.μ] H

/-- A kernel is essentially constant when it agrees almost everywhere with
one scalar on the product probability space. -/
def IsAEEqConstantKernel (M : System.{u}) (H : M.X × M.X -> ℂ) : Prop :=
  ∃ c : ℂ, H =ᵐ[M.μ.prod M.μ] fun _ => c

def kernelAction (M : System.{u})
    (H : M.X × M.X -> ℂ) (f : M.X -> ℂ) (x : M.X) : ℂ :=
  ∫ y, H (x, y) * f y ∂M.μ

def InKernelRange (M : System.{u})
    (H : M.X × M.X -> ℂ) (g : M.X -> ℂ) : Prop :=
  ∃ f : M.X -> ℂ, M.lpMember 2 f ∧ g =ᵐ[M.μ] kernelAction M H f

def KernelRangeSpannedByEigenfunctions (M : System.{u})
    (H : M.X × M.X -> ℂ) : Prop :=
  ∀ g : M.X -> ℂ, InKernelRange M H g -> ∀ ε : ℝ, 0 < ε ->
    ∃ s : Finset (M.X -> ℂ),
      (∀ h ∈ s, ∃ lam : ℂ, Eigenfunction M lam h) ∧
      ∃ c : (M.X -> ℂ) -> ℂ,
        MeasureTheory.eLpNorm
          (fun x => g x - ∑ h ∈ s, c h * h x) 2 M.μ < ENNReal.ofReal ε

def productInvariantSigmaAlgebra (M : System.{u}) : SetFamily (M.X × M.X) :=
  {A | MeasurableSet A ∧
    (M.μ.prod M.μ)
      (Chapter00.symmDiff ((productTransformation M) ⁻¹' A) A) = 0}

def TensorSquare (M : System.{u}) (f : M.X -> ℂ) (p : M.X × M.X) : ℂ :=
  f p.1 * star (f p.2)

def HasDenseCompactFunctions (M : System.{u}) : Prop :=
  ∀ f : M.X -> ℂ, M.lpMember 2 f -> ∀ ε : ℝ, 0 < ε ->
    ∃ g : M.X -> ℂ, IsAlmostPeriodicFunction M g ∧
      MeasureTheory.eLpNorm (fun x => f x - g x) 2 M.μ < ENNReal.ofReal ε

def IsIntegrableKernelRangeFunction (M : System.{u}) (g : M.X -> ℂ) : Prop :=
  ∃ H : M.X × M.X -> ℂ, ∃ f : M.X -> ℂ,
    MeasureTheory.Integrable H (M.μ.prod M.μ) ∧
    MeasureTheory.Integrable f M.μ ∧
    g =ᵐ[M.μ] kernelAction M H f

def HilbertSchmidtConsequencesStatement (M : System.{u}) : Prop :=
  IsErgodic M ->
    (∀ H : M.X × M.X -> ℂ, IsInvariantL2Kernel M H ->
      ¬ IsAEEqConstantKernel M H ->
        KernelRangeSpannedByEigenfunctions M H ∧
        ∃ g : M.X -> ℂ, InKernelRange M H g ∧
          ∃ lam : ℂ, Eigenfunction M lam g ∧ ¬ IsAEEqConstant M g) ∧
    (∀ f : M.X -> ℂ, IsAlmostPeriodicFunction M f ->
      ¬ f =ᵐ[M.μ] 0 ->
      MeasureTheory.MemLp (TensorSquare M f) 2 (M.μ.prod M.μ) ->
      ¬ MeasureTheory.condExp
        (MeasurableSpace.generateFrom (productInvariantSigmaAlgebra M))
        (M.μ.prod M.μ) (TensorSquare M f) =ᵐ[M.μ.prod M.μ] 0) ∧
    (HasDenseCompactFunctions M ->
      ∀ f : M.X -> ℂ, M.lpMember 2 f -> ∀ ε : ℝ, 0 < ε ->
        ∃ g : M.X -> ℂ, IsIntegrableKernelRangeFunction M g ∧
          MeasureTheory.eLpNorm (fun x => f x - g x) 2 M.μ < ENNReal.ofReal ε)

def HasDenseEigenfunctionSpan (M : System.{u}) : Prop :=
  ∀ f : M.X -> ℂ, M.lpMember 2 f -> ∀ ε : ℝ, 0 < ε ->
    ∃ s : Finset (M.X -> ℂ),
      (∀ g ∈ s, ∃ lam : ℂ, Eigenfunction M lam g) ∧
      ∃ c : (M.X -> ℂ) -> ℂ,
        MeasureTheory.eLpNorm
          (fun x => f x - ∑ g ∈ s, c g * g x) 2 M.μ < ENNReal.ofReal ε

def HasDiscreteSpectrum (M : System.{u}) : Prop :=
  HasDenseEigenfunctionSpan M

def IsCompactSystem (M : System.{u}) : Prop :=
  HasDenseCompactFunctions M

def CompactIffDiscreteSpectrumStatement (M : System.{u}) : Prop :=
  IsErgodic M ->
    Chapter01.IsInvertibleMeasurePreservingMap M.𝓧 M.μ M.𝓧 M.μ M.T ->
    (IsCompactSystem M ↔ HasDiscreteSpectrum M) ∧
    (IsWeakMixing M ↔ HasContinuousSpectrum M)

def circleConvolution (μ ν : CircleMeasureData) : MeasureTheory.Measure Circle :=
  MeasureTheory.Measure.map (fun p : Circle × Circle => p.1 * p.2) (μ.μ.prod ν.μ)

def circleConvolutionPower (μ : CircleMeasureData) : ℕ -> MeasureTheory.Measure Circle
  | 0 => MeasureTheory.Measure.dirac 1
  | n + 1 => MeasureTheory.Measure.map
      (fun p : Circle × Circle => p.1 * p.2)
      ((circleConvolutionPower μ n).prod μ.μ)

def IsSingularCircleMeasure (μ : CircleMeasureData) : Prop :=
  MeasureTheory.Measure.MutuallySingular μ.μ MeasureTheory.Measure.haar

def IsAbsolutelyContinuousCircleMeasure (μ : CircleMeasureData) : Prop :=
  MeasureTheory.Measure.AbsolutelyContinuous μ.μ MeasureTheory.Measure.haar

def HasIndependentPowers (μ : CircleMeasureData) : Prop :=
  ∀ n m : ℕ, 0 < n -> 0 < m -> n ≠ m ->
    MeasureTheory.Measure.MutuallySingular
      (circleConvolutionPower μ n) (circleConvolutionPower μ m)

def RiemannLebesgueStatement : Prop :=
  ∀ μ : CircleMeasureData,
    MeasureTheory.Measure.AbsolutelyContinuous μ.μ MeasureTheory.Measure.haar ->
    Tendsto (fun n : ℕ => circleFourierCoefficient μ n) atTop (nhds 0)

def IsClosedCircleL2Subspace (μ : CircleMeasureData)
    (H : Set (Circle -> ℂ)) : Prop :=
  (fun _ : Circle => (0 : ℂ)) ∈ H ∧
  (∀ f ∈ H, MeasureTheory.MemLp f 2 μ.μ) ∧
  (∀ f ∈ H, ∀ g ∈ H, ∀ a b : ℂ,
    (fun z => a * f z + b * g z) ∈ H) ∧
  (∀ f ∈ H, ∀ g : Circle -> ℂ, f =ᵐ[μ.μ] g -> g ∈ H) ∧
  ∀ fseq : ℕ -> Circle -> ℂ, (∀ n, fseq n ∈ H) ->
    ∀ f : Circle -> ℂ, MeasureTheory.MemLp f 2 μ.μ ->
      Tendsto (fun n => MeasureTheory.eLpNorm
        (fun z => fseq n z - f z) 2 μ.μ) atTop (nhds 0) -> f ∈ H

def WienerInvariantSubspaceStatement : Prop :=
  ∀ μ : CircleMeasureData, ∀ H : Set (Circle -> ℂ),
    IsClosedCircleL2Subspace μ H ->
    (∀ f ∈ H, (fun z : Circle => (z : ℂ) * f z) ∈ H) ->
    (∀ f, (fun z : Circle => (z : ℂ) * f z) ∈ H -> f ∈ H) ->
      ∃ B : Set Circle, MeasurableSet B ∧
        H = {f | MeasureTheory.MemLp f 2 μ.μ ∧
          f =ᵐ[μ.μ] fun z => if z ∈ B then f z else 0}

def UnitarilyEquivalent (D E : HilbertOperatorData.{u}) : Prop :=
  ∃ W : D.H -> E.H,
    Function.Bijective W ∧
    (∀ x y, W (x + y) = W x + W y) ∧
    (∀ c : ℂ, ∀ x, W (c • x) = c • W x) ∧
    (∀ x, ‖W x‖ = ‖x‖) ∧
    ∀ x : D.H, W (D.U x) = E.U (W x)

/-- A closed linear subspace invariant in both directions under `D.U`. -/
def IsClosedReducingSubspace (D : HilbertOperatorData.{u}) (K : Set D.H) : Prop :=
  0 ∈ K ∧
  (∀ x ∈ K, ∀ y ∈ K, ∀ a b : ℂ, a • x + b • y ∈ K) ∧
  (∀ xseq : ℕ -> D.H, (∀ n, xseq n ∈ K) -> ∀ x : D.H,
    Tendsto xseq atTop (nhds x) -> x ∈ K) ∧
  ∀ x : D.H, x ∈ K ↔ D.U x ∈ K

/-- Membership in the two-sided cyclic subspace generated by `x`. -/
def InCyclicSubspace (D : HilbertOperatorData.{u}) (x y : D.H) : Prop :=
  ∀ K : Set D.H, IsClosedReducingSubspace D K -> x ∈ K -> y ∈ K

def CyclicSubspaceMultiplicationModelStatement
    (D : HilbertOperatorData.{u}) : Prop :=
  IsUnitary D -> ∀ x : D.H, x ≠ 0 ->
    ∃ μ : CircleMeasureData, HasSpectralMeasure D x μ ∧
    ∃ W : (Circle -> ℂ) -> D.H,
      (∀ f g, f =ᵐ[μ.μ] g -> W f = W g) ∧
      (∀ f g, W (fun z => f z + g z) = W f + W g) ∧
      (∀ c : ℂ, ∀ f, W (fun z => c * f z) = c • W f) ∧
      (∀ f, MeasureTheory.MemLp f 2 μ.μ ->
        ‖W f‖ = (MeasureTheory.eLpNorm f 2 μ.μ).toReal) ∧
      (∀ y, InCyclicSubspace D x y ↔
        ∃ f, MeasureTheory.MemLp f 2 μ.μ ∧ W f = y) ∧
      W (fun _ => (1 : ℂ)) = x ∧
      ∀ f, MeasureTheory.MemLp f 2 μ.μ ->
        W (fun z => (z : ℂ) * f z) = D.U (W f)

def OrthogonalCyclicSubspaces (D : HilbertOperatorData.{u}) (x y : D.H) : Prop :=
  ∀ a b : D.H, InCyclicSubspace D x a -> InCyclicSubspace D y b ->
    @inner ℂ D.H inferInstance a b = 0

def SpectralMeasureAbsoluteContinuityAndOrthogonality
    (D : HilbertOperatorData.{u}) : Prop :=
  IsUnitary D ->
    (∀ x : D.H, ∀ μ ν : CircleMeasureData,
      HasSpectralMeasure D x μ ->
      MeasureTheory.Measure.AbsolutelyContinuous ν.μ μ.μ ->
      ∃ y : D.H, InCyclicSubspace D x y ∧ HasSpectralMeasure D y ν) ∧
    (∀ x y : D.H, ∀ μx μy μsum : CircleMeasureData,
      OrthogonalCyclicSubspaces D x y ->
      HasSpectralMeasure D x μx -> HasSpectralMeasure D y μy ->
      HasSpectralMeasure D (x + y) μsum -> μsum.μ = μx.μ + μy.μ) ∧
    ∀ x y : D.H, ∀ μx μy : CircleMeasureData,
      HasSpectralMeasure D x μx -> HasSpectralMeasure D y μy ->
      MeasureTheory.Measure.MutuallySingular μx.μ μy.μ ->
        OrthogonalCyclicSubspaces D x y

def IsDiscreteCircleMeasure (μ : CircleMeasureData) : Prop :=
  ∃ z : ℕ -> Circle, ∃ a : ℕ -> ENNReal, (∑' n, a n) < ⊤ ∧
    ∀ A : Set Circle, MeasurableSet A ->
      μ.μ A = ∑' n, if z n ∈ A then a n else 0

def IsContinuousCircleMeasure (μ : CircleMeasureData) : Prop :=
  ∀ z : Circle, μ.μ {z} = 0

def SpectralSubspaceMeasureTypeStatement (D : HilbertOperatorData.{u}) : Prop :=
  IsUnitary D -> ∀ x : D.H, x ≠ 0 -> ∀ μ : CircleMeasureData,
    HasSpectralMeasure D x μ ->
      (InDiscreteSpectralSubspace D x ↔ IsDiscreteCircleMeasure μ) ∧
      (InContinuousSpectralSubspace D x ↔ IsContinuousCircleMeasure μ)

def EigenvectorSpectralMeasurePointMassStatement
    (D : HilbertOperatorData.{u}) : Prop :=
  IsUnitary D -> ∀ x : D.H, ∀ lam : Circle, x ≠ 0 ->
    D.U x = (lam : ℂ) • x -> ∀ μ : CircleMeasureData,
      HasSpectralMeasure D x μ ->
        μ.μ = ENNReal.ofReal (‖x‖ ^ 2) • MeasureTheory.Measure.dirac lam

def CyclicSubspaceSpectralProperties (D : HilbertOperatorData.{u}) : Prop :=
  IsUnitary D -> ∀ x y : D.H,
    (InCyclicSubspace D x y ->
      ∃ μx μy : CircleMeasureData,
        (∀ n : ℕ, circleFourierCoefficient μx n =
          @inner ℂ D.H inferInstance x ((D.U^[n]) x)) ∧
        (∀ n : ℕ, circleFourierCoefficient μy n =
          @inner ℂ D.H inferInstance y ((D.U^[n]) y)) ∧
        MeasureTheory.Measure.AbsolutelyContinuous μy.μ μx.μ)

def OrthogonalCyclicSubspacesCounterexample : Prop :=
  ∃ D : HilbertOperatorData.{u}, ∃ x y : D.H,
    IsUnitary D ∧ OrthogonalCyclicSubspaces D x y ∧
    ∃ μx μy : CircleMeasureData,
      HasSpectralMeasure D x μx ∧ HasSpectralMeasure D y μy ∧
      ¬ MeasureTheory.Measure.MutuallySingular μx.μ μy.μ

def SpectralTypeDefinition (μ : CircleMeasureData) : Set CircleMeasureData :=
  {ν | MeasureTheory.Measure.AbsolutelyContinuous ν.μ μ.μ ∧
    MeasureTheory.Measure.AbsolutelyContinuous μ.μ ν.μ}

/-- A countable orthogonal cyclic decomposition with dense algebraic sum. -/
def IsOrthogonalCyclicDecomposition (D : HilbertOperatorData.{u})
    (x : ℕ -> D.H) : Prop :=
  (∀ i j, i ≠ j -> OrthogonalCyclicSubspaces D (x i) (x j)) ∧
  ∀ y : D.H, ∀ ε : ℝ, 0 < ε -> ∃ s : Finset ℕ, ∃ z : ℕ -> D.H,
    (∀ n ∈ s, InCyclicSubspace D (x n) (z n)) ∧
    ‖y - ∑ n ∈ s, z n‖ < ε

def SpectralMeasureDominatesVector (D : HilbertOperatorData.{u})
    (x y : D.H) : Prop :=
  ∀ μx μy : CircleMeasureData, HasSpectralMeasure D x μx ->
    HasSpectralMeasure D y μy ->
      MeasureTheory.Measure.AbsolutelyContinuous μy.μ μx.μ

def SpectralMeasureEquivalentVectors (D : HilbertOperatorData.{u})
    (x y : D.H) : Prop :=
  SpectralMeasureDominatesVector D x y ∧ SpectralMeasureDominatesVector D y x

def SpectralMeasureEquivalentAcross
    (D : HilbertOperatorData.{u}) (x : D.H)
    (E : HilbertOperatorData.{u}) (y : E.H) : Prop :=
  ∀ μx μy : CircleMeasureData, HasSpectralMeasure D x μx ->
    HasSpectralMeasure E y μy ->
      MeasureTheory.Measure.AbsolutelyContinuous μx.μ μy.μ ∧
      MeasureTheory.Measure.AbsolutelyContinuous μy.μ μx.μ

/-- An orthogonal cyclic decomposition whose spectral types decrease in order. -/
def IsOrderedSpectralDecomposition (D : HilbertOperatorData.{u})
    (x : ℕ -> D.H) : Prop :=
  IsOrthogonalCyclicDecomposition D x ∧
    ∀ n, SpectralMeasureDominatesVector D (x n) (x (n + 1))

def SpectralDecompositionFormOne (D : HilbertOperatorData.{u}) : Prop :=
  TopologicalSpace.SeparableSpace D.H -> IsUnitary D ->
    ∃ x : ℕ -> D.H, IsOrderedSpectralDecomposition D x ∧
      ∀ y : ℕ -> D.H, IsOrderedSpectralDecomposition D y ->
        ∀ n, SpectralMeasureEquivalentVectors D (x n) (y n)

/-- Membership in the Hilbert direct sum of the spaces `L²(S¹, μ n)`. -/
def InCircleL2DirectSum (μ : ℕ -> CircleMeasureData)
    (f : ℕ -> Circle -> ℂ) : Prop :=
  (∀ n, MeasureTheory.MemLp (f n) 2 (μ n).μ) ∧
    Summable (fun n =>
      (MeasureTheory.eLpNorm (f n) 2 (μ n).μ).toReal ^ 2)

/-- A concrete unitary model from a direct sum of circle `L²` spaces. -/
def IsDirectSumMultiplicationModel (D : HilbertOperatorData.{u})
    (μ : ℕ -> CircleMeasureData)
    (W : (ℕ -> Circle -> ℂ) -> D.H) : Prop :=
  (∀ f g, (∀ n, f n =ᵐ[(μ n).μ] g n) -> W f = W g) ∧
  (∀ f g, InCircleL2DirectSum μ f -> InCircleL2DirectSum μ g ->
    W (fun n z => f n z + g n z) = W f + W g) ∧
  (∀ c : ℂ, ∀ f, InCircleL2DirectSum μ f ->
    W (fun n z => c * f n z) = c • W f) ∧
  (∀ f, InCircleL2DirectSum μ f ->
    ‖W f‖ ^ 2 = ∑' n,
      (MeasureTheory.eLpNorm (f n) 2 (μ n).μ).toReal ^ 2) ∧
  (∀ y : D.H, ∃ f : ℕ -> Circle -> ℂ,
    InCircleL2DirectSum μ f ∧ W f = y) ∧
  ∀ f, InCircleL2DirectSum μ f ->
    W (fun n z => (z : ℂ) * f n z) = D.U (W f)

def DirectSumOfCyclicMultiplicationModelsStatement
    (D : HilbertOperatorData.{u}) : Prop :=
  TopologicalSpace.SeparableSpace D.H -> IsUnitary D ->
    ∃ x : ℕ -> D.H, ∃ μ : ℕ -> CircleMeasureData,
      ∃ W : (ℕ -> Circle -> ℂ) -> D.H,
        IsOrderedSpectralDecomposition D x ∧
        (∀ n, HasSpectralMeasure D (x n) (μ n)) ∧
        IsDirectSumMultiplicationModel D μ W ∧
        ∀ n, W (fun j _ => if j = n then (1 : ℂ) else 0) = x n

def IsMaximalSpectralMeasure (D : HilbertOperatorData.{u})
    (μ : CircleMeasureData) : Prop :=
  IsUnitary D ∧
    (∃ x : D.H, HasSpectralMeasure D x μ) ∧
    ∀ x : D.H, ∃ μx : CircleMeasureData,
      HasSpectralMeasure D x μx ∧
      MeasureTheory.Measure.AbsolutelyContinuous μx.μ μ.μ

/-- `n = 0` denotes infinite multiplicity; positive `n` has indices `k < n`. -/
def IsActiveMultiplicityIndex (n k : ℕ) : Prop := n = 0 ∨ k < n

/-- A homogeneous-stratum cyclic decomposition realizing spectral multiplicity. -/
def IsMultiplicityDecomposition (D : HilbertOperatorData.{u})
    (B : ℕ -> Set Circle) (x : ℕ -> ℕ -> D.H)
    (μ : ℕ -> ℕ -> CircleMeasureData) : Prop :=
  (∀ n, MeasurableSet (B n)) ∧
  (∀ n m, n ≠ m -> Disjoint (B n) (B m)) ∧
  (⋃ n, B n) = Set.univ ∧
  (∀ n k, ¬ IsActiveMultiplicityIndex n k -> x n k = 0) ∧
  (∀ n k, IsActiveMultiplicityIndex n k ->
    HasSpectralMeasure D (x n k) (μ n k) ∧ (μ n k).μ (B n)ᶜ = 0) ∧
  (∀ n i j, IsActiveMultiplicityIndex n i -> IsActiveMultiplicityIndex n j ->
    SpectralTypeDefinition (μ n i) = SpectralTypeDefinition (μ n j)) ∧
  (∀ n i m j, (n, i) ≠ (m, j) ->
    IsActiveMultiplicityIndex n i -> IsActiveMultiplicityIndex m j ->
    OrthogonalCyclicSubspaces D (x n i) (x m j)) ∧
  ∀ y : D.H, ∀ ε : ℝ, 0 < ε ->
    ∃ s : Finset (ℕ × ℕ), ∃ z : ℕ × ℕ -> D.H,
      (∀ p ∈ s, IsActiveMultiplicityIndex p.1 p.2 ∧
        InCyclicSubspace D (x p.1 p.2) (z p)) ∧
      ‖y - ∑ p ∈ s, z p‖ < ε

/-- A maximal spectral measure together with its operator-linked multiplicity function. -/
def HasSpectralMultiplicityData (D : HilbertOperatorData.{u})
    (μmax : CircleMeasureData) (multiplicity : Circle -> ENNReal) : Prop :=
  IsMaximalSpectralMeasure D μmax ∧ Measurable multiplicity ∧
    ∃ B : ℕ -> Set Circle, ∃ x : ℕ -> ℕ -> D.H,
    ∃ μ : ℕ -> ℕ -> CircleMeasureData,
      IsMultiplicityDecomposition D B x μ ∧
      ∀ n, ∀ᵐ z ∂μmax.μ, z ∈ B n ->
        multiplicity z = if n = 0 then ⊤ else (n : ENNReal)

def MaximalSpectralTypeAndMultiplicityDefinitions (D : HilbertOperatorData.{u}) : Prop :=
  IsUnitary D -> ∃ μ : CircleMeasureData, ∃ multiplicity : Circle -> ENNReal,
    HasSpectralMultiplicityData D μ multiplicity

def SpectralClassificationByMaximalTypeAndMultiplicity (D : HilbertOperatorData.{u}) : Prop :=
  TopologicalSpace.SeparableSpace D.H -> IsUnitary D ->
  ∀ E : HilbertOperatorData.{u}, TopologicalSpace.SeparableSpace E.H -> IsUnitary E ->
    (UnitarilyEquivalent D E ↔
      ∃ μD μE : CircleMeasureData,
      ∃ multiplicityD multiplicityE : Circle -> ENNReal,
        HasSpectralMultiplicityData D μD multiplicityD ∧
        HasSpectralMultiplicityData E μE multiplicityE ∧
        MeasureTheory.Measure.AbsolutelyContinuous μD.μ μE.μ ∧
        MeasureTheory.Measure.AbsolutelyContinuous μE.μ μD.μ ∧
        multiplicityD =ᵐ[μD.μ] multiplicityE)

def HasDiscreteSpectrumOperator (D : HilbertOperatorData.{u}) : Prop :=
  ∃ μ : CircleMeasureData,
    IsMaximalSpectralMeasure D μ ∧ IsDiscreteCircleMeasure μ

def HasContinuousSpectrumOperator (D : HilbertOperatorData.{u}) : Prop :=
  ∃ μ : CircleMeasureData,
    IsMaximalSpectralMeasure D μ ∧ IsContinuousCircleMeasure μ

def HasSingularSpectrumOperator (D : HilbertOperatorData.{u}) : Prop :=
  ∃ μ : CircleMeasureData,
    IsMaximalSpectralMeasure D μ ∧ IsSingularCircleMeasure μ

def HasAbsolutelyContinuousSpectrumOperator (D : HilbertOperatorData.{u}) : Prop :=
  ∃ μ : CircleMeasureData,
    IsMaximalSpectralMeasure D μ ∧ IsAbsolutelyContinuousCircleMeasure μ

def HasLebesgueSpectrumOperator (D : HilbertOperatorData.{u}) : Prop :=
  ∃ μ : CircleMeasureData, IsMaximalSpectralMeasure D μ ∧
    MeasureTheory.Measure.AbsolutelyContinuous μ.μ MeasureTheory.Measure.haar ∧
    MeasureTheory.Measure.AbsolutelyContinuous MeasureTheory.Measure.haar μ.μ

def SpectralKindDefinitions (D : HilbertOperatorData.{u}) :
    Prop × Prop × Prop × Prop × Prop :=
  (HasDiscreteSpectrumOperator D, HasContinuousSpectrumOperator D,
    HasSingularSpectrumOperator D, HasAbsolutelyContinuousSpectrumOperator D,
    HasLebesgueSpectrumOperator D)

def HomogeneousSpectrumDefinitions (D : HilbertOperatorData.{u}) : Prop :=
  ∃ μ : CircleMeasureData, ∃ multiplicity : Circle -> ENNReal,
    HasSpectralMultiplicityData D μ multiplicity ∧
    ∃ N : ENNReal, 1 ≤ N ∧ multiplicity =ᵐ[μ.μ] fun _ => N

def SpectralDecompositionFormTwo (D : HilbertOperatorData.{u}) : Prop :=
  TopologicalSpace.SeparableSpace D.H -> IsUnitary D ->
    ∃ B : ℕ -> Set Circle, ∃ x : ℕ -> ℕ -> D.H,
    ∃ μ : ℕ -> ℕ -> CircleMeasureData,
      IsMultiplicityDecomposition D B x μ ∧
      ∀ C : ℕ -> Set Circle, ∀ y : ℕ -> ℕ -> D.H,
      ∀ ν : ℕ -> ℕ -> CircleMeasureData,
        IsMultiplicityDecomposition D C y ν ->
        ∀ n k, IsActiveMultiplicityIndex n k ->
          SpectralMeasureEquivalentVectors D (x n k) (y n k)

def IsZeroMeanFunction (M : System.{u}) (f : M.X -> ℂ) : Prop :=
  M.lpMember 2 f ∧ ∫ x, f x ∂M.μ = 0

def HasFunctionSpectralMeasure (M : System.{u})
    (f : M.X -> ℂ) (μ : CircleMeasureData) : Prop :=
  ∀ n : ℕ, circleFourierCoefficient μ n = functionCorrelation M f f n

def HasSimpleTrivialEigenvalue (M : System.{u}) : Prop :=
  Eigenvalue M 1 ∧
    ∀ f : M.X -> ℂ, Eigenfunction M 1 f -> IsAEEqConstant M f

def spectralSquareCesaro (M : System.{u}) (f : M.X -> ℂ) (N : ℕ) : ℝ :=
  if N = 0 then 0 else
    (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖functionCorrelation M f f n‖ ^ 2

def spectralAbsoluteCesaro (M : System.{u}) (f : M.X -> ℂ) (N : ℕ) : ℝ :=
  if N = 0 then 0 else
    (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖functionCorrelation M f f n‖

def SpectralCharacterizationsOfMixing (M : System.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
    ((IsErgodic M ↔
      HasSimpleTrivialEigenvalue M ∧
      ∀ f : M.X -> ℂ, IsZeroMeanFunction M f ->
        ∀ μ : CircleMeasureData, HasFunctionSpectralMeasure M f μ -> μ.μ {1} = 0) ∧
    (IsWeakMixing M ↔
      ∀ f : M.X -> ℂ, IsZeroMeanFunction M f ->
        (∀ μ : CircleMeasureData, HasFunctionSpectralMeasure M f μ ->
          IsContinuousCircleMeasure μ) ∧
        Tendsto (spectralAbsoluteCesaro M f) atTop (nhds 0)) ∧
    (IsStrongMixing M ↔
      ∀ f : M.X -> ℂ, IsZeroMeanFunction M f ->
        Tendsto (fun n => ‖functionCorrelation M f f n‖) atTop (nhds 0)))

def HasSimpleLebesgueSpectrum (D : HilbertOperatorData.{u}) : Prop :=
  ∃ μ : CircleMeasureData, ∃ multiplicity : Circle -> ENNReal,
    HasSpectralMultiplicityData D μ multiplicity ∧
    MeasureTheory.Measure.AbsolutelyContinuous μ.μ MeasureTheory.Measure.haar ∧
    MeasureTheory.Measure.AbsolutelyContinuous MeasureTheory.Measure.haar μ.μ ∧
    multiplicity =ᵐ[μ.μ] fun _ => 1

def IsKoopmanModelFor (D : HilbertOperatorData.{u}) (M : System.{u}) : Prop :=
  ∃ W : (M.X -> ℂ) -> D.H,
    (∀ f g, f =ᵐ[M.μ] g -> W f = W g) ∧
    (∀ f g, W (fun x => f x + g x) = W f + W g) ∧
    (∀ c : ℂ, ∀ f, W (fun x => c * f x) = c • W f) ∧
    (∀ f, M.lpMember 2 f ->
      ‖W f‖ = (MeasureTheory.eLpNorm f 2 M.μ).toReal) ∧
    (∀ y : D.H, ∀ ε : ℝ, 0 < ε ->
      ∃ f : M.X -> ℂ, M.lpMember 2 f ∧ ‖y - W f‖ < ε) ∧
    ∀ f, W (Chapter01.koopman M.T f) = D.U (W f)

def BanachSimpleLebesgueSpectrumProblem : Prop :=
  ∃ M : System.{u}, IsErgodic M ∧
    ∃ D : HilbertOperatorData.{u}, IsUnitary D ∧
      IsKoopmanModelFor D M ∧ HasSimpleLebesgueSpectrum D

end Chapter02
