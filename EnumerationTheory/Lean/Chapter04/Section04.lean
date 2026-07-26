import Chapter04.Spectral.LpMultiplier
import share.Lean.NLFirst_Pfd28c3cf0fb145e58f2b0f19d4e83368
import Mathlib.Algebra.Category.Grp.Injective

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter04

universe u v

namespace Section04

open CategoryTheory

/--
Source: Definition 4.4.1, Chapter 4, Section 4.
A measure-preserving system has discrete spectrum when L² admits an orthogonal
basis of Koopman eigenfunctions.
-/
def discreteSpectrum (M : System.{u}) : Prop :=
  HasDiscreteSpectrum M

/--
Source: Remark 4.4.2, Chapter 4, Section 4.
A system with discrete spectrum is invertible modulo null sets; in that case
the inverse system is also considered on the same measure algebra.
-/
def discreteSpectrumInvertibleRemark : Prop :=
  ∀ M : System.{u}, Chapter01.IsMeasurePreservingSystem M ->
    Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace ->
      HasDiscreteSpectrum M -> IsInvertibleModNull M

/--
Source: Lemma 4.4.3, Chapter 4, Section 4.
For a probability space and `h ∈ L²`, the function `h` is essentially bounded
exactly when multiplication by `h` sends every `L²` function back into `L²`.
-/
theorem lTwoMultiplierCharacterizesLinfty
    (P : ProbabilitySpace.{u}) (h : P.X -> ℂ) :
    Chapter01.IsProbabilitySpace P -> P.lpMember 2 h ->
      (P.lpMember ⊤ h ↔
        ∀ f : P.X -> ℂ, P.lpMember 2 f -> P.lpMember 2 (fun x => h x * f x)) := by
  intro hprob hh
  letI : MeasureTheory.IsProbabilityMeasure P.μ := hprob
  constructor
  · intro hinf f hf
    exact hf.mul' hinf
  · exact LpMultiplier.memLp_top_of_multiplication_memLp P.μ h hh


/--
Source: Lemma 4.4.4, Chapter 4, Section 4.
If `K` is a divisible subgroup of a discrete abelian group `H`, the identity on
`K` extends to a homomorphism from `H` to `K`.
-/
theorem divisibleSubgroupRetraction (H : Type u) [CommGroup H]
    (K : Subgroup H) : HasDivisibleRetraction H K := by
  intro hroot
  letI : RootableBy K ℕ := hroot
  letI : DivisibleBy (Additive K) ℕ :=
    { div := fun a n => Additive.ofMul (RootableBy.root a.toMul n)
      div_zero := by
        intro a
        apply Additive.toMul.injective
        exact RootableBy.root_zero a.toMul
      div_cancel := by
        intro n a hn
        apply Additive.toMul.injective
        simpa using RootableBy.root_cancel a.toMul hn }
  letI : DivisibleBy (Additive K) ℤ :=
    AddGroup.divisibleByIntOfDivisibleByNat (Additive K)
  let i : AddCommGrpCat.of (Additive K) ⟶ AddCommGrpCat.of (Additive H) :=
    AddCommGrpCat.ofHom K.subtype.toAdditive
  letI : Mono i := (AddCommGrpCat.mono_iff_injective i).2 K.subtype_injective
  let e : AddCommGrpCat.of (Additive H) ⟶ AddCommGrpCat.of (Additive K) :=
    Injective.factorThru (𝟙 (AddCommGrpCat.of (Additive K))) i
  have he : i ≫ e = 𝟙 (AddCommGrpCat.of (Additive K)) :=
    Injective.comp_factorThru _ _
  let θ : H →* K := e.hom.toMultiplicative
  refine ⟨θ, ?_⟩
  intro k
  have hk := DFunLike.congr_fun
    (congrArg AddCommGrpCat.Hom.hom he) (Additive.ofMul k)
  exact congrArg Additive.toMul hk

/--
Source: Theorem 4.4.5, Chapter 4, Section 4.
Halmos-von Neumann theorem: ergodic systems with discrete spectrum are classified
up to conjugacy by their eigenvalue groups.
-/
theorem halmosVonNeumannDiscreteSpectrumClassification
    (M N : System.{u}) :
    Chapter02.IsErgodic M -> Chapter02.IsErgodic N ->
      HasDiscreteSpectrum M -> HasDiscreteSpectrum N ->
        (IsSpectrallyIsomorphic M N ↔ eigenvalueSet M = eigenvalueSet N) ∧
        (eigenvalueSet M = eigenvalueSet N ↔ IsSystemConjugate M N) ∧
        (IsSpectrallyIsomorphic M N ↔ IsSystemConjugate M N) := by
  exact MathCopilotPrior.chapter04_results.halmos_von_neumann M N

/--
Source: Remark 4.4.6, Chapter 4, Section 4.
For a discrete-spectrum system, eigenfunctions may be chosen multiplicatively on
the eigenvalue group after normalizing constants.
-/
def multiplicativeEigenfunctionChoiceRemark : Prop :=
  ∀ M : System.{u}, Chapter02.IsErgodic M ->
    HasDiscreteSpectrum M -> HasEigenfunctionMultiplicativeChoice M

/--
Source: Remark 4.4.7, Chapter 4, Section 4.
The later proof of Halmos-von Neumann proceeds through joinings and compact
rotation models.
-/
def halmosVonNeumannJoiningProofRemark : String :=
  "A later chapter gives another proof of the Halmos–von Neumann theorem using joinings and compact rotation models."

/--
Source: Corollary 4.4.8, Chapter 4, Section 4.
A measure-preserving system with discrete spectrum is conjugate to its inverse.
-/
theorem discreteSpectrumSystemConjugateToInverse
    (M : System.{u}) :
    HasDiscreteSpectrum M ->
      IsConjugateToInverseSystem M := by
  exact
    MathCopilotPrior.chapter04_results.discrete_spectrum_conjugate_to_inverse M

/--
Source: Definition following Corollary 4.4.8, Chapter 4, Section 4.
A compact group rotation is a measure-preserving system given by left
translation on a compact group with Haar probability measure.
-/
def compactGroupRotationSystemDefinition (M : System.{u}) : Prop :=
  IsCompactAbelianRotationSystem M

/--
Source: Proposition 4.4.9, Chapter 4, Section 4.
For a compact abelian rotation, the eigenvalues are obtained from the characters
evaluated at the rotation element.
-/
theorem compactGroupRotationEigenvalues
    (M : System.{u}) (G : Type u)
    [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (η : MeasureTheory.Measure G) (e : M.X -> G) (inv : G -> M.X) (a : G)
    (hmodel : IsCompactAbelianRotationModel M G η e inv a)
    (hergodic : Chapter02.IsErgodic M) :
    (∀ lam : ℂ, ∀ f : M.X -> ℂ, Chapter02.Eigenfunction M lam f ->
      RotationCharacterEigenfunctionForModel e a lam f) ∧
    (∀ lam : ℂ, Chapter02.Eigenvalue M lam ↔
      RotationCharacterEigenvalueForModel a lam) ∧
    HasDiscreteSpectrum M := by
  exact MathCopilotPrior.chapter04_results.compact_rotation_eigenvalues
    M G η e inv a hmodel hergodic

/--
Source: Theorem 4.4.10, Chapter 4, Section 4.
An ergodic system has discrete spectrum exactly when it is conjugate to a compact
abelian group rotation.
-/
theorem discreteSpectrumIffCompactAbelianRotation (M : System.{u}) :
    Chapter02.IsErgodic M ->
      (HasDiscreteSpectrum M ↔ ∃ N : System.{u},
        IsCompactAbelianRotationSystem N ∧ Chapter02.IsErgodic N ∧
          IsSystemConjugate M N) ∧
      (IsLebesgueProbabilitySpace M.toProbabilitySpace -> HasDiscreteSpectrum M ->
        ∃ N : System.{u}, IsMetrizableCompactAbelianRotationSystem N ∧
          Chapter02.IsErgodic N ∧ IsSystemConjugate M N) := by
  exact
    MathCopilotPrior.chapter04_results.discrete_spectrum_iff_compact_rotation M

/--
Source: Theorem 4.4.11, Chapter 4, Section 4.
Every subgroup of the circle group can occur as the eigenvalue group of an
ergodic discrete-spectrum system.
-/
theorem circleSubgroupRealizedAsEigenvalueGroup (H : Set ℂ) :
    IsCircleSubgroup H ->
      ∃ M : System.{u}, Chapter02.IsErgodic M ∧ HasDiscreteSpectrum M ∧ eigenvalueSet M = H := by
  exact MathCopilotPrior.chapter04_results.circle_subgroup_realization H

end Section04
end Chapter04
