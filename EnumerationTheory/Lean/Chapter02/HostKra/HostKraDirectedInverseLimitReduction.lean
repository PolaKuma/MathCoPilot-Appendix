import Chapter02.Dynamics.DirectedMinimalInverseLimit
import Chapter02.HostKra.HostKraContinuousCylinderReduction

open Classical MeasureTheory Set

noncomputable section

namespace Chapter02.HostKraDirectedInverseLimitReduction

universe u

/-- The exact topological inverse-limit data needed for each continuous
finite fifteen-dual cylinder correlation.  Unlike a bare pro-minimality
conclusion, this records the directed compact minimal stages, their bonding
maps, the jointly injective limit projections, and the orbit observation. -/
def ContinuousFiniteFifteenDualInverseLimitPresentation : Prop :=
  ∀ (M : System.{u}) [StandardBorelSpace M.X],
    ∀ (hM : Chapter01.IsMeasurePreservingSystem M),
    IsErgodic M →
    ∀ (A : Set M.X) (hA : MeasurableSet A),
    ∀ (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)),
    ∀ (ht : t.Finite),
      letI : IsProbabilityMeasure M.μ := hM.1
      letI : Fintype t := ht.fintype
      letI : IsFiniteMeasure
          (Measure.map
            (HostKraFiniteCylinderDensity.finiteCode M hM t) M.μ) :=
        Measure.isFiniteMeasure_map M.μ
          (HostKraFiniteCylinderDensity.finiteCode M hM t)
      ∀ φ : C(
          HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ),
        Nonempty
          (Chapter02.DirectedMinimalInverseLimit.Presentation
            (HostKraStructuredApproximation.lastSlotCorrelation
              M hM A hA
              (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
                (HostKraFiniteCylinderDensity.finiteCode M hM t)
                ⟨HostKraFiniteCylinderDensity.finiteCode_measurable
                    M hM t, rfl⟩
                (ContinuousMap.toLp 2
                  (Measure.map
                    (HostKraFiniteCylinderDensity.finiteCode M hM t) M.μ)
                  ℂ φ))))

/-- A genuine directed compact-minimal inverse-limit presentation supplies
the continuous finite-cylinder pro-minimality theorem. -/
theorem continuousFiniteFifteenDualProMinimality
    (hinverse :
      ContinuousFiniteFifteenDualInverseLimitPresentation.{u}) :
    HostKraContinuousCylinderReduction.ContinuousFiniteFifteenDualProMinimality.{u} := by
  intro M instSB hM hErg A hA t ht φ
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : Fintype t := ht.fintype
  letI : IsFiniteMeasure
      (Measure.map
        (HostKraFiniteCylinderDensity.finiteCode M hM t) M.μ) :=
    Measure.isFiniteMeasure_map M.μ
      (HostKraFiniteCylinderDensity.finiteCode M hM t)
  exact
    (hinverse M hM hErg A hA t ht φ).some
      |>.isUniformLimitOfMinimalOrbitSequences

/-- End-to-end reduction of the original multiple Khintchine clause to a
fully explicit Host--Kra directed inverse-limit presentation. -/
theorem multipleKhintchineStatement_firstClause
    (hinverse :
      ContinuousFiniteFifteenDualInverseLimitPresentation.{u})
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
  HostKraContinuousCylinderReduction.multipleKhintchineStatement_firstClause
    (continuousFiniteFifteenDualProMinimality hinverse) M

end Chapter02.HostKraDirectedInverseLimitReduction
