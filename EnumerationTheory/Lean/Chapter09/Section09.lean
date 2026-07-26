import Chapter09.Section08

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter09
namespace Section09

universe u

/-- Source: Question 9.9.1.  The `L²` half was later answered by Walsh;
the almost-everywhere half remains the question recorded by the book. -/
def nilpotentPolynomialMultipleAverageConvergenceQuestion : Prop :=
  NilpotentPolynomialAverageQuestionStatement.{u}

/-- Source: Theorem 9.9.2, Chapter 9, Section 9. -/
theorem walshNilpotentPolynomialMultipleAverageConvergence :
    WalshNilpotentPolynomialAverageStatement := by
  sorry

/-- Source: Definition 9.9.3, Chapter 9, Section 9. -/
def nilpotentGroupsNilmanifoldsNilSystems
    (M : MeasurableSystem.{u}) (d : ℕ) : Prop :=
  IsNilSystem M d

/-- Source: Definition 9.9.4, Chapter 9, Section 9. -/
def hostKraSeminormsAndSystemsOfOrder
    (M : MeasurableSystem.{u}) (d : ℕ) : Prop :=
  Nonempty (HostKraOrderData M d)

/-- Source: Theorem 9.9.5, Chapter 9, Section 9. -/
theorem hostKraSeminormControlsLinearMultipleAverages
    (M : MeasurableSystem.{u}) (d : ℕ) :
    HostKraSeminormControlsAverages M d := by
  sorry

/-- Source: Theorem 9.9.6, Chapter 9, Section 9. -/
theorem hostKraStructureTheoremForSystemsOfOrder
    (M : MeasurableSystem.{u}) (d : ℕ) :
    HostKraStructureEquivalence M d := by
  sorry

/-- Source: Theorem 9.9.7, Chapter 9, Section 9. -/
theorem topologicalCubeMinimality
    (S : TopologicalSystem.{u}) (d : ℕ) :
    CubeMinimalityStatement S d := by
  sorry

/-- Source: Theorem 9.9.8, Chapter 9, Section 9. -/
theorem measurableCubeErgodicity
    (M : MeasurableSystem.{u}) (d : ℕ) :
    MeasurableCubeErgodicityStatement M d := by
  sorry

/-- Source: Theorem 9.9.9, Chapter 9, Section 9. -/
theorem hostKraMaassTopologicalProNilCharacterization
    (S : TopologicalSystem.{u}) (d : ℕ) :
    TopologicalProNilCharacterization S d := by
  sorry

/-- Source: Definition 9.9.10, Chapter 9, Section 9. -/
def regionallyProximalRelationOfOrder
    (S : TopologicalSystem.{u}) [PseudoMetricSpace S.X]
    (d : ℕ) (x y : S.X) : Prop :=
  RegionallyProximalOfOrder S d x y

/-- Source: Theorem 9.9.11, Chapter 9, Section 9. -/
theorem regionallyProximalRelationStructureTheorem
    (S : TopologicalSystem.{u}) (d : ℕ) :
    RegionallyProximalRelationStatement S d := by
  sorry

/-- Source: Theorem 9.9.12, Chapter 9, Section 9. -/
theorem bourgainPointwiseConvergenceTheorems
    (M : MeasurableSystem.{u}) :
    BourgainPointwiseConvergenceStatement M := by
  sorry

/-- Source: Theorem 9.9.13, Chapter 9, Section 9. -/
theorem glasnerCubeOrbitClosureMinimality
    (S : TopologicalSystem.{u}) (d : ℕ) :
    ProgressionOrbitClosureMinimalityStatement S d := by
  sorry

/-- Source: Theorem 9.9.14, Chapter 9, Section 9. -/
theorem strictlyErgodicModelsForCubeSystems
    (M : MeasurableSystem.{u}) (d : ℕ) :
    StrictlyErgodicModelForCubesStatement M d := by
  sorry

/-- Source: Theorem 9.9.15, Chapter 9, Section 9. -/
theorem pointwiseConvergenceForTwoParameterProgressionAverages
    (M : MeasurableSystem.{u}) (d : ℕ) :
    TwoParameterProgressionAverageConvergenceStatement M d := by
  sorry

/-- Source: Theorem 9.9.16, Chapter 9, Section 9. -/
theorem pointwiseConvergenceForDistalSystems
    (M : MeasurableSystem.{u}) (d : ℕ) :
    IsMeasureDistal M -> PointwiseMultipleAverageConvergenceStatement M d := by
  sorry

/-- Source: Theorem 9.9.17, Chapter 9, Section 9. -/
theorem pointwiseConvergenceForWeakMixingPIDSystems
    (M : MeasurableSystem.{u}) (d : ℕ) :
    Chapter02.IsWeakMixing M -> IsPIDSystem M ->
      PointwiseMultipleAverageConvergenceStatement M d := by
  sorry

/-- Source: Theorem 9.9.18, Chapter 9, Section 9. -/
theorem hostKraCubeGroupAverageConvergence
    (M : MeasurableSystem.{u}) (d : ℕ) :
    CubeGroupAverageConvergenceStatement M d := by
  sorry

end Section09
end Chapter09
