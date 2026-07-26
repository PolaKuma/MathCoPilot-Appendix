import Chapter02.HallPetresco.CompactCentralCubeSurjective
import Chapter02.HostKra.HostKraHallPetrescoDecompositionReduction
import Chapter02.HallPetresco.LawfulCompactCentralAction

open Classical MeasureTheory Set

noncomputable section

namespace Chapter02.HostKraTorusHallPetrescoReduction

universe u

open Chapter02.CentralFiberFourfold
open Chapter02.HostKraCentralChangeVariables
open Chapter02.HostKraHallPetrescoCorrelation

/-- The remaining Hall--Petresco decomposition with its central compact
group specialized to a finite-dimensional torus.  This is the form
delivered by the connected reduction in BHK Section 8.3; cubing is
automatically onto and is no longer part of the structure hypothesis. -/
def FifteenDualTorusHallPetrescoDecomposition : Prop :=
  ∀ (M : System.{u}) [StandardBorelSpace M.X],
    ∀ (hM : Chapter01.IsMeasurePreservingSystem M),
    IsErgodic M →
    ∀ (A : Set M.X) (hA : MeasurableSet A),
    ∀ δ : ℝ, 0 < δ →
      ∃ c : ℕ → ℝ,
      ∃ d : ℕ,
      ∃ m : Measure (Fin d → Circle),
      ∃ _probG : IsProbabilityMeasure m,
      ∃ _haarG : m.IsHaarMeasure,
      ∃ X : Type, ∃ _metricX : MetricSpace X,
      ∃ _compactX : CompactSpace X,
      ∃ _measX : MeasurableSpace X, ∃ _borelX : BorelSpace X,
      ∃ μ : Measure X, ∃ _probX : IsProbabilityMeasure μ,
      ∃ D : Chapter02.LawfulCompactCentralAction
          (Fin d → Circle) X μ,
      ∃ f : C(X, ℝ),
        MultipleKhintchineSyndetic.TendsToZeroInUniformDensity
          (fun n ↦
            HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation
                M hM A hA n - c n) ∧
        (∫ x, f x ∂μ) = realMeasure M A ∧
        (∀ x, 0 ≤ f x) ∧
        HasHallPetrescoCorrelationOrbit
          m μ (Chapter02.toCompactCentralAction D) f c

/-- A torus Hall--Petresco decomposition supplies the general compact
central decomposition, because the cubing map on a torus is onto. -/
theorem hallPetrescoDecomposition
    (hTorus : FifteenDualTorusHallPetrescoDecomposition.{u}) :
    Chapter02.HostKraHallPetrescoDecompositionReduction.FifteenDualHallPetrescoDecomposition.{u} := by
  intro M instSB hM hErg A hA δ hδ
  obtain ⟨c, d, m, probG, haarG,
      X, metricX, compactX, measX, borelX, μ, probX, D, f,
      hnull, hmean, hf, horbit⟩ :=
    hTorus M hM hErg A hA δ hδ
  letI : IsProbabilityMeasure m := probG
  letI : m.IsHaarMeasure := haarG
  letI : MetricSpace X := metricX
  letI : CompactSpace X := compactX
  letI : MeasurableSpace X := measX
  letI : BorelSpace X := borelX
  letI : IsProbabilityMeasure μ := probX
  exact ⟨c, Fin d → Circle, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, m, inferInstance,
    inferInstance, X, inferInstance, inferInstance, inferInstance,
    inferInstance, μ, inferInstance,
    Chapter02.toCompactCentralAction D, f, hnull, hmean, hf,
    CompactCentralCubeSurjective.torus_cube_surjective, horbit⟩

/-- End-to-end reduction in the exact connected-torus form of the
remaining Host--Kra nilsystem theorem. -/
theorem multipleKhintchineStatement_firstClause
    (hTorus : FifteenDualTorusHallPetrescoDecomposition.{u})
    (M : System.{u}) :
    IsErgodic M →
      ∀ A : Set M.X, MeasurableSet A → 0 < M.μ A →
      ∀ ε : ℝ, 0 < ε →
        IsSyndetic {n : ℕ |
          realMeasure M
              (A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A) >
            (realMeasure M A) ^ 3 - ε} ∧
        IsSyndetic {n : ℕ |
          realMeasure M
              (A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A ∩
                preimageIter M (3 * n) A) >
            (realMeasure M A) ^ 4 - ε} :=
  Chapter02.HostKraHallPetrescoDecompositionReduction.multipleKhintchineStatement_firstClause
      (hallPetrescoDecomposition hTorus) M

end Chapter02.HostKraTorusHallPetrescoReduction
