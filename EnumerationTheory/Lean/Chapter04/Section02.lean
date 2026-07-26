import Chapter04.MeasureAlgebra.MeasureAlgebraPullback
import Chapter04.Descriptive.Invertibility
import Chapter04.Descriptive.DynamicsSpatial
import Chapter04.MeasureAlgebra.MeasureAlgebraDynamics
import Chapter04.MeasureAlgebra.MeasureAlgebraStoneDynamics
import Chapter04.MeasureAlgebra.InvariantSubSigmaFactor
import Chapter04.MeasureAlgebra.InvariantSubSigmaQuotient
import Chapter04.Descriptive.CountableCodeFactor

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter04

universe u v

namespace Section02

/--
Source: Remark 4.2.1, Chapter 4, Section 2.
System isomorphism is an equivalence relation, isomorphism is preserved by
iterates, and invertible systems may be compared on invariant full-measure sets.
-/
def systemIsomorphismBasicPropertiesRemark : Prop :=
  (∀ M : System.{u}, Chapter01.IsMeasurePreservingSystem M ->
    Chapter01.IsIsomorphicSystems M M) ∧
  (∀ M N : System.{u}, Chapter01.IsMeasurePreservingSystem M ->
    Chapter01.IsMeasurePreservingSystem N -> Chapter01.IsIsomorphicSystems M N ->
    Chapter01.IsIsomorphicSystems N M) ∧
  (∀ M N K : System.{u}, Chapter01.IsMeasurePreservingSystem M ->
    Chapter01.IsMeasurePreservingSystem N -> Chapter01.IsMeasurePreservingSystem K ->
    Chapter01.IsIsomorphicSystems M N ->
    Chapter01.IsIsomorphicSystems N K -> Chapter01.IsIsomorphicSystems M K) ∧
  ∀ M N : System.{u}, Chapter01.IsMeasurePreservingSystem M ->
    Chapter01.IsMeasurePreservingSystem N -> Chapter01.IsIsomorphicSystems M N -> ∀ n : ℕ,
    Chapter01.IsIsomorphicSystems { M with T := M.T^[n] } { N with T := N.T^[n] }

/--
Source: Definition 4.2.2, Chapter 4, Section 2.
Conjugacy and semi-conjugacy of measure-preserving systems are defined via
isomorphisms and homomorphisms of their measure-algebra systems.
-/
def measurePreservingSystemConjugacy (M N : System.{u}) : Prop :=
  IsSystemConjugate M N

/--
Source: Proposition 4.2.3, Chapter 4, Section 2.
An isomorphism of systems implies conjugacy, and each factor map induces a
homomorphism of measure-algebra systems.
-/
theorem systemIsomorphismAndFactorMapsInduceMeasureAlgebraMaps
    (M N : System.{u}) (π : M.X -> N.X) :
    (Chapter01.IsIsomorphicSystems M N -> IsSystemConjugate M N) ∧
      (Chapter01.IsFactorMap M N π ->
        ∃ Φ : MeasureAlgebraHomData (inducedMeasureAlgebra N.toProbabilitySpace)
          (inducedMeasureAlgebra M.toProbabilitySpace), IsMeasureAlgebraHom Φ) := by
  exact ⟨MeasureAlgebraPullback.isomorphism_of_system_isomorphism M N,
    MeasureAlgebraPullback.hom_of_factor_map M N π⟩

/--
Source: Theorem 4.2.4, Chapter 4, Section 2.
An isomorphism of measure-algebra systems can be realized by measure-preserving
systems whose induced measure-algebra systems are the given ones.
-/
theorem measureAlgebraSystemIsomorphismHasSpatialModel
    (A B : MeasureAlgebraSystemData.{u}) :
    IsMeasureAlgebraSystem A ->
      A.measure A.top = 1 -> IsSeparableMeasureAlgebra A.toMeasureAlgebraData ->
      IsMeasureAlgebraSystem B ->
      B.measure B.top = 1 -> IsSeparableMeasureAlgebra B.toMeasureAlgebraData ->
      IsMeasureAlgebraSystemIsomorphism B A ->
      ∃ M N : System.{u},
        IsSpatialModelOfMeasureAlgebraSystem A M ∧
        IsSpatialModelOfMeasureAlgebraSystem B N ∧
        Chapter01.IsIsomorphicSystems M N := by
  intro hA hATop _hAsep hB _hBTop _hBsep hBA
  obtain ⟨Θ, hΘ, hAM⟩ :=
    MeasureAlgebraStoneDynamics.spatialModel_stoneSystem A hA hATop
  let M : System.{u} :=
    MeasureAlgebraStoneDynamics.stoneSystem hA.1 Θ hΘ.1
  have hM : Chapter01.IsMeasurePreservingSystem M :=
    MeasureAlgebraStoneDynamics.isMeasurePreservingSystem_stoneSystem
      hA.1 Θ hΘ.1 hATop
  have hInduced :
      IsMeasureAlgebra (inducedMeasureAlgebraSystem M).toMeasureAlgebraData :=
    isMeasureAlgebra_inducedMeasureAlgebra M.toProbabilitySpace hM.1
  have hBM : IsSpatialModelOfMeasureAlgebraSystem B M :=
    MeasureAlgebraStoneDynamics.systemIsomorphism_trans
      hB.1 hA.1 hInduced hBA hAM
  exact ⟨M, M, hAM, hBM,
    MeasureAlgebraStoneDynamics.systemIsomorphism_refl M hM⟩

/--
Source: Theorem 4.2.5, Chapter 4, Section 2.
For Lebesgue systems, a measure-algebra-system isomorphism is realized by a
Borel isomorphism on invariant full-measure subsets.
-/
theorem lebesgueSystemConjugacyRealizedByBorelIsomorphism
    (M N : System.{u}) :
    Chapter01.IsMeasurePreservingSystem M ->
      Chapter01.IsMeasurePreservingSystem N ->
      IsLebesgueProbabilitySpace M.toProbabilitySpace ->
      IsLebesgueProbabilitySpace N.toProbabilitySpace ->
        IsSystemConjugate M N -> Chapter01.IsIsomorphicSystems M N := by
  intro hM hN hMLeb hNLeb hconj
  obtain ⟨φ, ψ, hφm, hψm, hφmp, hψmp, hψφ, hφψ, hint⟩ :=
    DynamicsSpatial.global_realizers_of_system_conjugacy
      M N hM hN hMLeb hNLeb hconj
  exact DynamicsSpatial.system_isomorphism_of_global_realizers
    M N hM hN hMLeb hNLeb φ ψ hφm hψm hφmp hψmp hψφ hφψ hint

/--
Source: Remark 4.2.6, Chapter 4, Section 2.
Measure-algebra dynamics are often the clean primary object; spatial models are
chosen after passing to invariant full-measure subsets.
-/
def measureAlgebraDynamicsPrimaryRemark : Prop :=
  ∀ M N : System.{u}, IsSystemConjugate M N ->
    IsMeasureAlgebraSystemIsomorphism
      (inducedMeasureAlgebraSystem N) (inducedMeasureAlgebraSystem M)

/--
Source: Proposition 4.2.7, Chapter 4, Section 2.
An invariant sub-sigma-algebra of a Lebesgue system yields a factor; if the
sub-sigma-algebra is strictly invariant, the factor can be taken invertible.
-/
theorem invariantSubsigmaAlgebraGivesFactor
    (M : System.{u}) (F : SetFamily M.X) :
    Chapter01.IsMeasurePreservingSystem M ->
      IsLebesgueProbabilitySpace M.toProbabilitySpace ->
      Chapter00.IsSigmaAlgebraFamily F -> F ⊆ M.𝓧 ->
      (∀ A : Set M.X, A ∈ F -> M.T ⁻¹' A ∈ F) ->
        ∃ N : System.{u}, ∃ π : M.X -> N.X,
          Chapter01.IsFactorMap M N π ∧
          IsLebesgueProbabilitySpace N.toProbabilitySpace ∧
          (∀ A : Set M.X, A ∈ F ->
            ∃ B : Set N.X, B ∈ N.𝓧 ∧
              M.μ (Chapter00.symmDiff A (π ⁻¹' B)) = 0) ∧
          (∀ B : Set N.X, B ∈ N.𝓧 -> π ⁻¹' B ∈ F) ∧
          ({A : Set M.X | ∃ B ∈ F, A = M.T ⁻¹' B} = F ->
            IsInvertibleModNull N) := by
  intro hM hLeb hF hsub hInv
  exact CountableCodeFactor.exists_lebesgueFactor_of_invariantSubSigma
    M F hM hLeb hF hsub hInv

/--
Source: Proposition 4.2.8, Chapter 4, Section 2.
A system is invertible modulo null sets exactly when its induced sigma algebra is
surjective modulo the measure algebra.
-/
theorem invertibleModNullIffInducedSigmaAlgebraSurjective
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hLeb : IsLebesgueProbabilitySpace M.toProbabilitySpace) :
    IsInvertibleModNull M ↔ IsInducedSigmaAlgebraSurjective M := by
  constructor
  · exact Invertibility.inducedSigmaAlgebraSurjective_of_invertibleModNull M hM
  · exact Invertibility.invertibleModNull_of_inducedSigmaAlgebraSurjective M hM hLeb

/--
Source: Definition 4.2.9, Chapter 4, Section 2.
A spectral isomorphism is a unitary intertwiner between the Koopman operators.
-/
def spectralIsomorphism (M N : System.{u}) : Prop :=
  IsSpectrallyIsomorphic M N

/--
Source: Remark 4.2.10, Chapter 4, Section 2.
Conditions (1) and (2) say that the intertwiner is a Hilbert-space isomorphism;
condition (3) is the additional dynamical intertwining requirement.
-/
def spectralIsomorphismRemark : String :=
  "In Definition 4.2.9, conditions (1) and (2) say that W is a Hilbert-space isomorphism, while condition (3) adds the dynamical intertwining relation."

/--
Source: Theorem 4.2.11, Chapter 4, Section 2.
Two systems are conjugate exactly when a spectral isomorphism also preserves the
bounded-function algebraic structure.
-/
theorem systemConjugacyIffAlgebraicSpectralIsomorphism
    (M N : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N) :
    IsSystemConjugate M N ↔ IsAlgebraicSpectralIsomorphism M N := by
  constructor
  · rintro ⟨Φ, hΦ, hcomm⟩
    let W : (N.X → ℂ) → M.X → ℂ :=
      MeasureAlgebraLtwo.rawLtwoMap
        M.toProbabilitySpace N.toProbabilitySpace hM.1 hN.1 Φ hΦ.1
    have hAlg :
        IsLtwoAlgebraUnitaryFor
          M.toProbabilitySpace N.toProbabilitySpace W := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro f g hf hg hfg
        exact MeasureAlgebraLtwo.rawLtwoMap_ae
          M.toProbabilitySpace N.toProbabilitySpace
          hM.1 hN.1 Φ hΦ.1 f g hf hg hfg
      · intro f g hf hg
        exact MeasureAlgebraLtwo.rawLtwoMap_add
          M.toProbabilitySpace N.toProbabilitySpace
          hM.1 hN.1 Φ hΦ.1 f g hf hg
      · intro c f hf
        exact MeasureAlgebraLtwo.rawLtwoMap_smul
          M.toProbabilitySpace N.toProbabilitySpace
          hM.1 hN.1 Φ hΦ.1 c f hf
      · intro f hf
        exact MeasureAlgebraLtwo.rawLtwoMap_ltwo
          M.toProbabilitySpace N.toProbabilitySpace
          hM.1 hN.1 Φ hΦ.1 f hf
      · intro h hh ε hε
        exact MeasureAlgebraLtwo.rawLtwoMap_dense
          M.toProbabilitySpace N.toProbabilitySpace
          hM.1 hN.1 Φ hΦ h hh ε hε
      · intro f hf
        exact LinfClosure.rawLtwoMap_memLp_top
          M.toProbabilitySpace N.toProbabilitySpace
          hM.1 hN.1 Φ hΦ.1 f hf
      · intro h hh
        exact InverseLtwo.rawLtwoMap_memLp_top_surjective
          M.toProbabilitySpace N.toProbabilitySpace
          hM.1 hN.1 Φ hΦ h hh
      · exact MeasureAlgebraLtwo.rawLtwoMap_one
          M.toProbabilitySpace N.toProbabilitySpace
          hM.1 hN.1 Φ hΦ.1
      · intro f g hf hg
        exact AlgebraClosure.rawLtwoMap_mul
          M.toProbabilitySpace N.toProbabilitySpace
          hM.1 hN.1 Φ hΦ.1 f g hf hg
    rcases hAlg with
      ⟨hae, hadd, hsmul, hLtwo, hdense, hLinf, hLinfSurj, hone, hmul⟩
    refine ⟨W, ?_, ?_⟩
    · exact ⟨hae, hadd, hsmul, hLtwo, hdense, fun f hf =>
        MeasureAlgebraDynamics.rawLtwoMap_comp
          M N hM hN Φ hΦ hcomm f hf⟩
    · exact
        ⟨hae, hadd, hsmul, hLtwo, hdense,
          hLinf, hLinfSurj, hone, hmul⟩
  · exact LtwoProjection.systemConjugate_of_algebraicSpectralIsomorphism
      M N hM hN

end Section02
end Chapter04
