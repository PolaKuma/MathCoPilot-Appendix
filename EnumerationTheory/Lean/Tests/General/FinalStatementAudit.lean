import Textbook

noncomputable section

open Classical
open scoped BigOperators

universe u v w

/-!
This file is the compilation root for the final Chapter 0--9 semantic repair.
Each audit statement exposes a mathematical field that would disappear again
if one of the repaired definitions were weakened or collapsed.
-/

def Chapter00AuditStatement : Prop :=
  (∀ (X : Type u) [TopologicalSpace X] (A : Set X),
    (Chapter00.Section02.denseAndSeparableDefinition A).1 =
        (closure A = Set.univ) ∧
      (Chapter00.Section02.denseAndSeparableDefinition A).2 =
        (∃ D : Set X, D.Countable ∧ closure D = Set.univ)) ∧
  (∀ (X : Type u) [PseudoMetricSpace X] (A : Set C(X, ℂ)),
    (Chapter00.Section02.boundedEquicontinuousPointwiseCompactFamilyDefinition A).2.2 =
      Chapter00.IsPointwiseRelativelyCompactContinuousMapFamily A) ∧
  ∀ (k : ℕ) (A : Matrix (Fin k) (Fin k) ℝ) (lam : ℝ) (p q : Fin k -> ℝ),
    (Chapter00.Section05.leftRightEigenvectorDefinition k A lam p q).1 =
        (∀ j, (Finset.univ.sum fun i : Fin k => p i * A i j) = lam * p j) ∧
      (Chapter00.Section05.leftRightEigenvectorDefinition k A lam p q).2 =
        (∀ i, (Finset.univ.sum fun j : Fin k => A i j * q j) = lam * q i)

theorem chapter00_audit : Chapter00AuditStatement := by
  simp [Chapter00AuditStatement,
    Chapter00.Section02.denseAndSeparableDefinition,
    Chapter00.Section02.boundedEquicontinuousPointwiseCompactFamilyDefinition,
    Chapter00.Section05.leftRightEigenvectorDefinition]

def Chapter01AuditStatement : Prop :=
  (∀ (X : Type u) (Y : Type v) (Z : Type w)
      [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
      [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
      [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
      (S : Y -> Y) (φ : Y -> Z -> Z) (T : X -> X),
    Chapter01.IsSkewProductSystem X Y Z S φ T ↔
      Continuous S ∧ (∀ y, Continuous (φ y)) ∧
      Continuous (fun p : Y × Z => φ p.1 p.2) ∧ Continuous T ∧
      ∃ e : X ≃ₜ Y × Z, ∀ x : X,
        e (T x) = (S (e x).1, φ (e x).1 (e x).2)) ∧
  (∀ (X : Type u) (Y : Type v) (G : Type w)
      [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
      [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
      [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [TopologicalSpace.MetrizableSpace G]
      (S : Y -> Y) (φ : Y -> G) (T : X -> X),
    Chapter01.IsGroupExtensionSystem X Y G S φ T ↔
      Continuous S ∧ Continuous φ ∧ Continuous T ∧
      ∃ e : X ≃ₜ Y × G, ∀ x : X,
        e (T x) = (S (e x).1, φ (e x).1 * (e x).2)) ∧
  (∀ (S : Chapter01.MeasurePreservingSystemData.{u}) (k : ℕ)
      (p : Fin k -> ℝ),
    Chapter01.IsOneSidedBernoulliShiftWith S k p ->
      ∃ e : S.X ≃ (ℕ -> Fin k), Measurable e ∧ Measurable e.symm) ∧
  ∀ (k : ℕ) (_hk : 2 ≤ k) (p : Fin k -> ℝ)
      (_hp : ∀ i, 0 ≤ p i) (_hsum : ∑ i, p i = 1),
    Continuous (@Chapter01.oneSidedShift k) ∧
    Function.Surjective (@Chapter01.oneSidedShift k) ∧
    (∀ word : List (Fin k), IsClopen (Chapter01.oneSidedCylinder word)) ∧
    TopologicalSpace.IsTopologicalBasis (Chapter01.oneSidedCylinderFamily k) ∧
    Chapter01.IsFactorMap
      (Chapter01.oneSidedBernoulliSystem 2 (fun _ => (1 / 2 : ℝ)))
      (Chapter01.circleTimesSystem 2) Chapter01.binaryCoding ∧
    Chapter01.IsIsomorphicSystems
      (Chapter01.oneSidedBernoulliSystem 2 (fun _ => (1 / 2 : ℝ)))
      (Chapter01.circleTimesSystem 2)

theorem chapter01_audit : Chapter01AuditStatement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Chapter01.IsSkewProductSystem]
  · simp [Chapter01.IsGroupExtensionSystem]
  · intro S k p h
    rcases h with ⟨_, e, he, heinv, _⟩
    exact ⟨e, he, heinv⟩
  · intro k hk p hp hsum
    have h := Chapter01.Section02.oneSidedShiftSystemExample k hk p hp hsum
    rcases h with
      ⟨_, _, _, hcontinuous, hsurjective, _, _, hclopen, hbasis, _, hfactor, hisomorphic⟩
    exact ⟨hcontinuous, hsurjective, hclopen, hbasis, hfactor, hisomorphic⟩

def Chapter02AuditStatement : Prop :=
  (∀ (M : Chapter02.System.{u}) (K : Chapter00.SetFamily M.X),
    Chapter02.IsInvariantSubSigmaAlgebraFamily M K ↔
      Chapter00.IsSigmaAlgebraFamily K ∧ K ⊆ M.𝓧 ∧
        ∀ A : Set M.X, A ∈ K ↔ M.T ⁻¹' A ∈ K) ∧
  (∀ M : Chapter02.System.{u},
    Chapter02.HasDiscreteSpectrum M ↔ Chapter02.HasDenseEigenfunctionSpan M) ∧
  ∀ M : Chapter02.System.{u},
    Chapter02.IsCompactSystem M ↔ Chapter02.HasDenseCompactFunctions M

theorem chapter02_audit : Chapter02AuditStatement := by
  simp [Chapter02AuditStatement, Chapter02.IsInvariantSubSigmaAlgebraFamily,
    Chapter02.HasDiscreteSpectrum, Chapter02.IsCompactSystem]

def Chapter03AuditStatement : Prop :=
  (∀ a : Chapter03.PartialQuotients,
    Chapter03.IsNonnegativeRegularPartialQuotients a ↔
      0 ≤ a.a₀ ∧ Chapter03.IsRegularPartialQuotients a) ∧
  Chapter03.NonnegativeContinuedFractionClassification ∧
  (∀ x : Chapter03.GaussSpace,
    (Chapter03.gaussMap x).1 = Chapter03.gaussMapReal x.1) ∧
  Chapter03.IsMeasurePreservingGaussSystem
    { μ := Chapter03.gaussMeasure, T := Chapter03.gaussMap } ∧
  Chapter03.IsErgodicGaussSystem
    { μ := Chapter03.gaussMeasure, T := Chapter03.gaussMap }

theorem chapter03_audit : Chapter03AuditStatement := by
  refine ⟨?_,
    Chapter03.Section01.nonnegativeIrrationalHasUniqueContinuedFractionExpansion,
    ?_, Chapter03.Section02.continuedFractionSystemIsMeasurePreserving,
    Chapter03.Section02.continuedFractionSystemIsErgodic⟩
  · intro a
    rfl
  · intro x
    rfl

def Chapter04AuditStatement : Prop :=
  (∀ (M : Chapter04.System.{u}) (G : Type u)
      [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
      (η : MeasureTheory.Measure G) (e : M.X -> G) (inv : G -> M.X) (a : G),
    Chapter04.IsCompactAbelianRotationModel M G η e inv a ->
    Chapter02.IsErgodic M ->
      (∀ lam : ℂ, ∀ f : M.X -> ℂ, Chapter02.Eigenfunction M lam f ->
        Chapter04.RotationCharacterEigenfunctionForModel e a lam f) ∧
      (∀ lam : ℂ, Chapter02.Eigenvalue M lam ↔
        Chapter04.RotationCharacterEigenvalueForModel a lam) ∧
      Chapter04.HasDiscreteSpectrum M) ∧
  ∀ M : Chapter04.System.{u}, Chapter02.IsErgodic M ->
    Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace ->
    Chapter04.HasDiscreteSpectrum M ->
      ∃ N : Chapter04.System.{u},
        Chapter04.IsMetrizableCompactAbelianRotationSystem N ∧
        Chapter02.IsErgodic N ∧ Chapter04.IsSystemConjugate M N

theorem chapter04_audit : Chapter04AuditStatement := by
  constructor
  · intro M G _ _ _ _ _ _ η e inv a hmodel hergodic
    exact Chapter04.Section04.compactGroupRotationEigenvalues
      M G η e inv a hmodel hergodic
  · intro M hergodic hLebesgue hdiscrete
    exact (Chapter04.Section04.discreteSpectrumIffCompactAbelianRotation
      M hergodic).2 hLebesgue hdiscrete

def Chapter05AuditStatement : Prop :=
  Chapter05.Section03.oneSidedTwoSidedTransitivityRemark.{u} ↔
    ((∃ S : Chapter05.System.{0}, Chapter05.IsTopologicalSystem S ∧
      ∃ inv : S.X -> S.X, Chapter05.IsContinuousInverse S inv ∧
      ∃ x : S.X, Chapter05.IsTwoSidedTransitivePoint S inv x ∧
        ¬ Chapter05.IsTransitivePoint S x ∧
        ∃ p q : S.X, p ≠ q ∧ Chapter05.nonwanderingSet S = {p, q}) ∧
    ∀ S : Chapter05.System.{u}, Chapter05.IsTopologicalSystem S ->
      ∀ inv : S.X -> S.X, Chapter05.IsContinuousInverse S inv ->
        (Chapter05.IsTwoSidedMinimalSystem S inv ↔ Chapter05.IsMinimalSystem S))

theorem chapter05_audit : Chapter05AuditStatement := by
  rfl

def Chapter06AuditStatement : Prop :=
  ∀ (M : Chapter06.MeasurableSystem.{u}) (D : Chapter06.TopologicalModelData M),
    Chapter06.IsTopologicalModel M D ->
      Chapter05.IsTopologicalSystem D.topologicalSystem ∧
      D.modelMeasurableSpace = borel D.topologicalSystem.X ∧
      Chapter06.IsInvariantMeasure D.topologicalSystem D.invariantMeasure ∧
      Chapter01.IsIsomorphicSystems M D.modelSystem

theorem chapter06_audit : Chapter06AuditStatement := by
  intro M D h
  exact h

def Chapter07AuditStatement : Prop :=
  (∀ (M : Chapter07.MeasurableSystem.{u}) (A : Set M.X)
      (𝒯 : Set (Set M.X)) (x : M.X),
    Chapter07.conditionalProbability M A 𝒯 x =
      MeasureTheory.condExp (MeasurableSpace.generateFrom 𝒯) M.μ
        (A.indicator fun _ => (1 : ℝ)) x) ∧
  (∀ (M : Chapter07.MeasurableSystem.{u})
      (α β : Chapter07.FiniteMeasurablePartition M),
    Chapter07.partitionDistance M α β =
      Chapter07.conditionalEntropy M α
          (Chapter00.generatedSigmaAlgebra {A | A ∈ β.atoms}) +
        Chapter07.conditionalEntropy M β
          (Chapter00.generatedSigmaAlgebra {A | A ∈ α.atoms})) ∧
  ∀ M : Chapter07.MeasurableSystem.{u},
    Chapter07.hasDiscreteSpectrum M ↔ Chapter02.HasDiscreteSpectrum M

theorem chapter07_audit : Chapter07AuditStatement := by
  simp [Chapter07AuditStatement, Chapter07.conditionalProbability,
    Chapter07.partitionDistance, Chapter07.finitePartitionSigmaAlgebra,
    Chapter07.hasDiscreteSpectrum]

def Chapter08AuditStatement : Prop :=
  (∀ (M : Chapter08.MeasurableSystem.{u}) (N : Chapter08.MeasurableSystem.{v})
      (J : Chapter08.JoiningData M N)
      (K : MeasureTheory.Measure ((M.X × N.X) × M.X)),
    Chapter08.IsRelativelyIndependentSelfProductOverRight M N J K ->
      ∃ μy : N.X -> MeasureTheory.Measure M.X,
        (∀ A : Set M.X, MeasurableSet A -> Measurable fun y => μy y A) ∧
        (∀ᵐ y ∂N.μ, MeasureTheory.IsProbabilityMeasure (μy y))) ∧
  (∀ (M : Chapter08.MeasurableSystem.{u}) (N : Chapter08.MeasurableSystem.{v})
      (π : M.X -> N.X),
    Chapter08.IsCompactMeasureExtension M N π ->
      ∃ inv : M.X -> M.X,
        Function.LeftInverse inv M.T ∧ Function.RightInverse inv M.T ∧
        ∃ μy : N.X -> MeasureTheory.Measure M.X,
          Chapter08.IsFactorDisintegrationKernel M N π μy ∧
          ∀ f : M.X -> ℂ, M.lpMember 2 f -> ∀ ε : ℝ, 0 < ε ->
            ∃ g : M.X -> ℂ,
              Chapter08.IsRelativelyAlmostPeriodicFunction M N π inv μy g ∧
              MeasureTheory.eLpNorm (fun x => f x - g x) 2 M.μ < ENNReal.ofReal ε) ∧
  (∀ (M : Chapter08.MeasurableSystem.{u}) (𝒜 : Chapter08.SubSigmaAlgebra M),
    Chapter08.IsInvariantSubSigmaAlgebra M 𝒜 -> 𝒜 ⊆ M.𝓧) ∧
  ∀ (M : Chapter08.MeasurableSystem.{u}) (N : Chapter08.MeasurableSystem.{v}),
    Chapter08.JoiningSpaceTopologyProperties M N ->
      ∃ τ : TopologicalSpace (Chapter08.JoiningSpace M N),
        Nonempty (@TopologicalSpace.MetrizableSpace
          (Chapter08.JoiningSpace M N) τ)

theorem chapter08_audit : Chapter08AuditStatement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M N J K h
    rcases h with ⟨_, _, _, _, μy, hmeas, hprob, _, _⟩
    exact ⟨μy, hmeas, hprob⟩
  · intro M N π h
    rcases h with ⟨_, inv, _, hleft, hright, μy, hkernel, hdense⟩
    exact ⟨inv, hleft, hright, μy, hkernel, hdense⟩
  · intro M 𝒜 h
    exact h.2.1
  · intro M N h
    rcases h with ⟨_, _, _, _, τ, _, hmetrizable, _⟩
    exact ⟨τ, hmetrizable⟩

def Chapter09AuditStatement : Prop :=
  (∀ (E : Set ℕ) (n : ℕ),
    n ∈ Chapter09.naturalDifferenceSet E ↔
      ∃ a ∈ E, ∃ b ∈ E, b < a ∧ n = a - b) ∧
  (∀ (M : Chapter09.MeasurableSystem.{u}) (A : ℕ -> Set M.X),
    Chapter09.SeparatingSieve M A -> ∀ n, A (n + 1) ⊆ A n) ∧
  (∀ (M : Chapter09.MeasurableSystem.{u}) (N : Chapter09.MeasurableSystem.{v})
      (π : M.X -> N.X),
    Chapter02.IsErgodic M -> Chapter02.IsErgodic N ->
    Chapter09.IsCompactExtension M N π -> Chapter09.HasSZProperty N ->
      Chapter09.HasSZProperty M) ∧
  ∀ (M : Chapter09.MeasurableSystem.{u}) (N : Chapter09.MeasurableSystem.{v})
      (π : M.X -> N.X),
    Chapter02.IsErgodic M -> Chapter02.IsErgodic N ->
    Chapter09.IsRelativelyWeakMixingExtension M N π ->
    Chapter09.HasSZProperty N -> Chapter09.HasSZProperty M

theorem chapter09_audit : Chapter09AuditStatement := by
  refine ⟨?_, ?_,
    Chapter09.Section07.compactExtensionsPreserveSZProperty,
    Chapter09.Section07.relativelyWeakMixingExtensionsPreserveSZProperty⟩
  · simp [Chapter09.naturalDifferenceSet]
  · intro M A h n
    exact h.2.1 n

/-- Single rooted endpoint for the semantic interfaces of Chapters 0--9. -/
theorem main_theorem :
    Chapter00AuditStatement ∧ Chapter01AuditStatement ∧
    Chapter02AuditStatement ∧ Chapter03AuditStatement ∧ Chapter04AuditStatement ∧
    Chapter05AuditStatement ∧ Chapter06AuditStatement ∧
    Chapter07AuditStatement ∧ Chapter08AuditStatement ∧
    Chapter09AuditStatement := by
  exact ⟨chapter00_audit, chapter01_audit, chapter02_audit,
    chapter03_audit, chapter04_audit, chapter05_audit, chapter06_audit,
    chapter07_audit, chapter08_audit, chapter09_audit⟩
