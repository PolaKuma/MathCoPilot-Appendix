import Chapter01.Common

noncomputable section

open Classical

namespace Chapter01
namespace Section01

universe u v w

private theorem measurePreserving_of_isMeasurePreservingMap
    (P : ProbabilitySpaceData.{u}) (Q : ProbabilitySpaceData.{v})
    (T : P.X -> Q.X)
    (hT : IsMeasurePreservingMap P.𝓧 P.μ Q.𝓧 Q.μ T) :
    MeasureTheory.MeasurePreserving T P.μ Q.μ := by
  have hmeas : Measurable T := by
    intro B hB
    exact hT.1 B hB
  refine ⟨hmeas, ?_⟩
  apply MeasureTheory.Measure.ext
  intro B hB
  rw [MeasureTheory.Measure.map_apply hmeas hB]
  exact hT.2 B hB

/--
Source: Definition 1.1.1, Chapter 1, Section 1.
Measurable, measure-preserving, and invertible measure-preserving maps between
probability spaces.
-/
def measurableMeasurePreservingAndInvertibleMaps {X : Type u} {Y : Type v}
    (𝓧 : SetFamily X) (μ : Set X -> ENNReal)
    (𝓨 : SetFamily Y) (ν : Set Y -> ENNReal) (T : X -> Y) : Prop :=
  IsMeasurableMap 𝓧 𝓨 T ∧
    IsMeasurePreservingMap 𝓧 μ 𝓨 ν T ∧
    IsInvertibleMeasurePreservingMap 𝓧 μ 𝓨 ν T

/--
Source: Definition 1.1.2, Chapter 1, Section 1.
A probability space with a measure-preserving self-map is a measure-preserving
system.
-/
def measurePreservingSystemDefinition (S : MeasurePreservingSystemData.{u}) : Prop :=
  IsMeasurePreservingSystem S

/--
Source: Definition 1.1.3, Chapter 1, Section 1.
Factor, extension, and isomorphism of measure-preserving systems, up to
invariant full-measure subsets.
-/
def factorExtensionAndIsomorphismDefinitions (S₁ : MeasurePreservingSystemData.{u})
    (S₂ : MeasurePreservingSystemData.{v}) : Prop :=
  (∃ φ : S₁.X -> S₂.X, IsFactorMap S₁ S₂ φ) ∧
    (∃ φ : S₂.X -> S₁.X, IsFactorMap S₂ S₁ φ) ∧
    IsIsomorphicSystems S₁ S₂

/--
Source: Lemma 1.1.4, Chapter 1, Section 1.
It suffices to verify measurability and equality of measures on a semialgebra
generating the target sigma-algebra.
-/
theorem measurePreservingFromGeneratingSemiAlgebra {X : Type u} {Y : Type v}
    (𝓧 : SetFamily X) (μ : Set X -> ENNReal)
    (𝓨 : SetFamily Y) (ν : Set Y -> ENNReal) (T : X -> Y)
    (S₂ : SetFamily Y) (hS₂ : Chapter00.IsSemiAlgebra S₂)
    (hgen : Chapter00.generatedSigmaAlgebra S₂ = 𝓨)
    (hμ : Chapter00.IsProbabilityMeasureOn 𝓧 μ)
    (hν : Chapter00.IsProbabilityMeasureOn 𝓨 ν)
    (hcheck : ∀ A : Set Y, A ∈ S₂ -> T ⁻¹' A ∈ 𝓧 ∧ μ (T ⁻¹' A) = ν A) :
    IsMeasurePreservingMap 𝓧 μ 𝓨 ν T := by
  letI : MeasurableSpace Y := MeasurableSpace.generateFrom S₂
  have h𝓨 : ∀ A : Set Y, MeasurableSet A ↔ A ∈ 𝓨 := by
    intro A
    change A ∈ Chapter00.generatedSigmaAlgebra S₂ ↔ A ∈ 𝓨
    rw [hgen]
  have hempty : (∅ : Set X) ∈ 𝓧 := by
    have huniv := hμ.1.1.1
    simpa using hμ.1.1.2.1 Set.univ huniv
  have hpre : ∀ A : Set Y, MeasurableSet A -> T ⁻¹' A ∈ 𝓧 := by
    intro A hA
    exact MeasurableSpace.generateFrom_induction S₂
      (fun B _ => T ⁻¹' B ∈ 𝓧)
      (fun B hBS _ => (hcheck B hBS).1)
      (by simpa using hempty)
      (fun B _ ih => by
        simpa only [Set.preimage_compl] using
          hμ.1.1.2.1 (T ⁻¹' B) ih)
      (fun B _ ih => by
        simpa only [Set.preimage_iUnion] using
          hμ.1.1.2.2 (fun n => T ⁻¹' B n) ih)
      A hA
  let νm : MeasureTheory.Measure Y := MeasureTheory.Measure.ofMeasurable
    (fun A _ => ν A)
    (by exact hν.1.2.1)
    (by
      intro A hA hdisj
      exact hν.1.2.2 A (fun n => (h𝓨 (A n)).mp (hA n)) hdisj)
  let μpull : MeasureTheory.Measure Y := MeasureTheory.Measure.ofMeasurable
    (fun A _ => μ (T ⁻¹' A))
    (by simpa using hμ.1.2.1)
    (by
      intro A hA hdisj
      simpa only [Set.preimage_iUnion] using
        hμ.1.2.2 (fun n => T ⁻¹' A n) (fun n => hpre (A n) (hA n))
          (fun i j hij => Set.disjoint_left.2 (by
            intro x hxi hxj
            exact Set.disjoint_left.1 (hdisj hij) hxi hxj)))
  have hνm_univ : νm Set.univ = 1 := by
    dsimp only [νm]
    rw [MeasureTheory.Measure.ofMeasurable_apply Set.univ MeasurableSet.univ]
    exact hν.2
  letI : MeasureTheory.IsFiniteMeasure νm :=
    ⟨by rw [hνm_univ]; exact ENNReal.one_lt_top⟩
  have hmeasures : νm = μpull := by
    apply MeasureTheory.ext_of_generate_finite S₂ rfl hS₂.1.isPiSystem
    · intro A hA
      have hAmeas : MeasurableSet A :=
        MeasurableSpace.measurableSet_generateFrom hA
      dsimp only [νm, μpull]
      rw [MeasureTheory.Measure.ofMeasurable_apply A hAmeas,
        MeasureTheory.Measure.ofMeasurable_apply A hAmeas]
      exact (hcheck A hA).2.symm
    · dsimp only [νm, μpull]
      rw [MeasureTheory.Measure.ofMeasurable_apply Set.univ MeasurableSet.univ,
        MeasureTheory.Measure.ofMeasurable_apply Set.univ MeasurableSet.univ]
      simpa using hν.2.trans hμ.2.symm
  refine ⟨?_, ?_⟩
  · intro A hA
    exact hpre A ((h𝓨 A).mpr hA)
  · intro A hA
    have hAmeas : MeasurableSet A := (h𝓨 A).mpr hA
    have heval := congrArg (fun m : MeasureTheory.Measure Y => m A) hmeasures
    dsimp only [νm, μpull] at heval
    rw [MeasureTheory.Measure.ofMeasurable_apply A hAmeas,
      MeasureTheory.Measure.ofMeasurable_apply A hAmeas] at heval
    exact heval.symm

/--
Source: Definition 1.1.5, Chapter 1, Section 1.
Definition of the Koopman operator and its elementary algebraic, positivity,
indicator, composition, and iterate properties.
-/
theorem koopmanOperatorDefinitionAndBasicProperties {X : Type u} {Y : Type v}
    {Z : Type w} (T : X -> Y) (S : Y -> Z) :
    IsKoopmanOperatorFor T (koopman T) ∧ KoopmanBasicProperties T S ∧
      (∀ R : X -> X, ∀ n : ℕ, ∀ f : X -> ℂ,
        ((koopman R)^[n]) f = koopman (iterateMap R n) f) := by
  constructor
  · intro f
    rfl
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro f g a b
      rfl
    · intro f g
      rfl
    · intro c
      rfl
    · intro f hf
      exact ⟨fun x => hf.1 (T x), fun x => hf.2 (T x)⟩
    · intro B
      rfl
    · intro f
      rfl
  · intro R n f
    induction n generalizing f with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply, ih]
        funext x
        simp only [koopman, iterateMap]
        rw [Function.iterate_succ_apply']

/--
Source: Lemma 1.1.6, Chapter 1, Section 1.
For a measure-preserving map, the Koopman pullback preserves integrals.
-/
theorem koopmanPreservesIntegrals (P : ProbabilitySpaceData.{u})
    (Q : ProbabilitySpaceData.{v}) (T : P.X -> Q.X)
    (hT : IsMeasurePreservingMap P.𝓧 P.μ Q.𝓧 Q.μ T) :
    PreservesIntegrals P Q T := by
  intro f hf
  have hMP := measurePreserving_of_isMeasurePreservingMap P Q T hT
  have hfstrong : MeasureTheory.AEStronglyMeasurable f Q.μ :=
    hf.aestronglyMeasurable
  constructor
  · simpa only [koopman, Function.comp_def] using hMP.integrable_comp hfstrong
  · intro _
    unfold ProbabilitySpaceData.integral
    have hfmap : MeasureTheory.AEStronglyMeasurable f
        (MeasureTheory.Measure.map T P.μ) := by
      rw [hMP.map_eq]
      exact hfstrong
    calc
      ∫ x, koopman T f x ∂P.μ =
          ∫ y, f y ∂MeasureTheory.Measure.map T P.μ := by
            exact (MeasureTheory.integral_map hMP.measurable.aemeasurable hfmap).symm
      _ = ∫ y, f y ∂Q.μ := by rw [hMP.map_eq]

/--
Source: Corollary 1.1.7, Chapter 1, Section 1.
A measurable self-map preserves the probability measure iff the Koopman
pullback preserves integrals of all bounded functions.
-/
theorem measurePreservingIffIntegralInvariantForBoundedFunctions
    (P : ProbabilitySpaceData.{u}) (T : P.X -> P.X)
    (hT : IsMeasurableMap P.𝓧 P.𝓧 T) :
    IsMeasurePreservingMap P.𝓧 P.μ P.𝓧 P.μ T ↔ PreservesIntegrals P P T := by
  constructor
  · exact koopmanPreservesIntegrals P P T
  · intro hpres
    refine ⟨hT, ?_⟩
    intro B hB
    have hBmeas : MeasurableSet B := hB
    have hpre : MeasurableSet (T ⁻¹' B) := hT B hB
    let f : P.X -> ℂ := B.indicator (fun _ => 1)
    have hf : Measurable f := measurable_const.indicator hBmeas
    have hcomp : koopman T f = (T ⁻¹' B).indicator (fun _ => 1) := by
      funext x
      simp only [koopman, f, Set.indicator_apply, Set.mem_preimage]
    have hint := (hpres f hf).1
    have hfinite : P.μ (T ⁻¹' B) ≠ ⊤ ↔ P.μ B ≠ ⊤ := by
      have hpreint :
          MeasureTheory.Integrable
              ((T ⁻¹' B).indicator (fun _ => (1 : ℂ))) P.μ ↔
            P.μ (T ⁻¹' B) ≠ ⊤ := by
        simp [MeasureTheory.integrable_indicator_iff hpre, lt_top_iff_ne_top]
      have hBint : MeasureTheory.Integrable f P.μ ↔ P.μ B ≠ ⊤ := by
        dsimp only [f]
        simp [MeasureTheory.integrable_indicator_iff hBmeas, lt_top_iff_ne_top]
      rw [← hpreint, ← hBint]
      simpa only [hcomp] using hint
    by_cases hBtop : P.μ B = ⊤
    · have hpretop : P.μ (T ⁻¹' B) = ⊤ := by
        by_contra hne
        exact (hfinite.mp hne) hBtop
      exact hpretop.trans hBtop.symm
    · have hfint : MeasureTheory.Integrable f P.μ := by
        have hiff : MeasureTheory.Integrable f P.μ ↔ P.μ B ≠ ⊤ := by
          dsimp only [f]
          simp [MeasureTheory.integrable_indicator_iff hBmeas,
            lt_top_iff_ne_top]
        exact hiff.mpr hBtop
      have heq := (hpres f hf).2 hfint
      unfold ProbabilitySpaceData.integral at heq
      rw [hcomp] at heq
      have hleft :
          ∫ x, (T ⁻¹' B).indicator (fun _ => (1 : ℂ)) x ∂P.μ =
            ((P.μ (T ⁻¹' B)).toReal : ℂ) := by
        simpa using
          (MeasureTheory.integral_indicator_const (μ := P.μ) (1 : ℂ) hpre)
      have hright :
          ∫ x, B.indicator (fun _ => (1 : ℂ)) x ∂P.μ =
            ((P.μ B).toReal : ℂ) := by
        simpa using
          (MeasureTheory.integral_indicator_const (μ := P.μ) (1 : ℂ) hBmeas)
      rw [hleft, hright] at heq
      have hpretop : P.μ (T ⁻¹' B) ≠ ⊤ := hfinite.mpr hBtop
      exact (ENNReal.toReal_eq_toReal hpretop hBtop).mp
        (Complex.ofReal_injective heq)

/--
Source: Theorem 1.1.8, Chapter 1, Section 1.
For every `p ≥ 1`, the Koopman operator maps `L^p` into `L^p`, is an isometry,
and preserves real-valued `L^p` functions.
-/
theorem koopmanLpIsometryAndRealSubspace (P : ProbabilitySpaceData.{u})
    (Q : ProbabilitySpaceData.{v}) (T : P.X -> Q.X)
    (hT : IsMeasurePreservingMap P.𝓧 P.μ Q.𝓧 Q.μ T) :
    KoopmanIsLpIsometry P Q T ∧ KoopmanPreservesRealLp P Q T := by
  have hMP := measurePreserving_of_isMeasurePreservingMap P Q T hT
  constructor
  · intro p _hp
    constructor
    · intro f hf
      change MeasureTheory.MemLp (f ∘ T) p P.μ
      exact hf.comp_measurePreserving hMP
    · intro f hf
      unfold ProbabilitySpaceData.lpNorm
      change (MeasureTheory.eLpNorm (f ∘ T) p P.μ).toReal =
        (MeasureTheory.eLpNorm f p Q.μ).toReal
      exact congrArg ENNReal.toReal
        (MeasureTheory.eLpNorm_comp_measurePreserving hf.1 hMP)
  · intro p _hp f _hf hreal x
    exact hreal (T x)

/--
Source: Definition 1.1.9, Chapter 1, Section 1.
Inverse limit of a coherent inverse sequence of measure-preserving systems.
-/
def inverseLimitSystemDefinition (D : InverseSequenceData.{u})
    (L : MeasurePreservingSystemData.{u}) (π : ∀ i : ℕ, L.X -> (D.system i).X) : Prop :=
  IsInverseLimitSystem D L π

/--
Source: Definition 1.1.10, Chapter 1, Section 1.
Natural extension of a measure-preserving system as an invertible extension
factoring onto the original system.
-/
def naturalExtensionDefinition (S : MeasurePreservingSystemData.{u})
    (Stilde : MeasurePreservingSystemData.{v}) (φ : Stilde.X -> S.X) : Prop :=
  IsNaturalExtension S Stilde φ

end Section01
end Chapter01
