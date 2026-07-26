import Chapter02.HostKra.HostKraHallPetrescoCorrelation
import Chapter02.HostKra.HostKraNilDecompositionReduction

open Classical MeasureTheory Set

noncomputable section

namespace Chapter02.HostKraHallPetrescoDecompositionReduction

universe u

open Chapter02.CentralFiberFourfold
open Chapter02.HostKraCentralChangeVariables
open Chapter02.HostKraHallPetrescoCorrelation

/-- The exact nilsystem output needed from the Host--Kra inverse-limit
theorem.  At every scale the structured correlation is UD-close to a
single Hall--Petresco orbit correlation on a reduced compact-central
two-step model, and the observation has the same mean as the original
indicator.

All sharp inequalities have deliberately been removed from this interface:
they follow from the checked Fourier/Haar calculation. -/
def FifteenDualHallPetrescoDecomposition : Prop :=
  ∀ (M : System.{u}) [StandardBorelSpace M.X],
    ∀ (hM : Chapter01.IsMeasurePreservingSystem M),
    IsErgodic M →
    ∀ (A : Set M.X) (hA : MeasurableSet A),
    ∀ δ : ℝ, 0 < δ →
      ∃ c : ℕ → ℝ,
      ∃ G : Type, ∃ _group : CommGroup G,
      ∃ _metricG : MetricSpace G, ∃ _compactG : CompactSpace G,
      ∃ _topGroup : IsTopologicalGroup G,
      ∃ _measG : MeasurableSpace G, ∃ _borelG : BorelSpace G,
      ∃ m : Measure G, ∃ _probG : IsProbabilityMeasure m,
      ∃ _haarG : m.IsHaarMeasure,
      ∃ X : Type, ∃ _metricX : MetricSpace X,
      ∃ _compactX : CompactSpace X,
      ∃ _measX : MeasurableSpace X, ∃ _borelX : BorelSpace X,
      ∃ μ : Measure X, ∃ _probX : IsProbabilityMeasure μ,
      ∃ C : CompactCentralAction G X μ,
      ∃ f : C(X, ℝ),
        MultipleKhintchineSyndetic.TendsToZeroInUniformDensity
          (fun n ↦
            HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation
                M hM A hA n - c n) ∧
        (∫ x, f x ∂μ) = realMeasure M A ∧
        (∀ x, 0 ≤ f x) ∧
        Function.Surjective (fun g : G ↦ g ^ 3) ∧
        HasHallPetrescoCorrelationOrbit m μ C f c

/-- The precise Hall--Petresco decomposition supplies the previously
isolated sharp nil-decomposition theorem. -/
theorem fifteenDualSharpNilDecomposition
    (hHP : FifteenDualHallPetrescoDecomposition.{u}) :
    HostKraNilDecompositionReduction.FifteenDualSharpNilDecomposition.{u} := by
  intro M instSB hM hErg A hA δ hδ
  obtain ⟨c, G, groupG, metricG, compactG, topGroupG,
      measG, borelG, m, probG, haarG,
      X, metricX, compactX, measX, borelX, μ, probX, C, f,
      hnull, hmean, hf, hcube, horbit⟩ :=
    hHP M hM hErg A hA δ hδ
  letI : CommGroup G := groupG
  letI : MetricSpace G := metricG
  letI : CompactSpace G := compactG
  letI : IsTopologicalGroup G := topGroupG
  letI : MeasurableSpace G := measG
  letI : BorelSpace G := borelG
  letI : IsProbabilityMeasure m := probG
  letI : m.IsHaarMeasure := haarG
  letI : MetricSpace X := metricX
  letI : CompactSpace X := compactX
  letI : MeasurableSpace X := measX
  letI : BorelSpace X := borelX
  letI : IsProbabilityMeasure μ := probX
  have hcminimal :
      HostKraStructuredRecurrence.IsUniformLimitOfMinimalOrbitSequences c := by
    intro η hη
    exact ⟨c,
      isMinimalOrbitSequence_of_correlationOrbit horbit,
      fun n ↦ by simpa using hη⟩
  refine ⟨c, hcminimal, hnull, ?_⟩
  obtain ⟨n, hn⟩ :=
    exists_high_of_correlationOrbit
      m hcube μ C f hf c horbit δ hδ
  refine ⟨n, ?_⟩
  rw [hmean] at hn
  exact hn

/-- End-to-end reduction with no sharp-bound hypothesis left: the exact
Hall--Petresco inverse-limit decomposition implies the original arbitrary
system statement. -/
theorem multipleKhintchineStatement_firstClause
    (hHP : FifteenDualHallPetrescoDecomposition.{u})
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
  HostKraNilDecompositionReduction.multipleKhintchineStatement_firstClause
    (fifteenDualSharpNilDecomposition hHP) M

end Chapter02.HostKraHallPetrescoDecompositionReduction
