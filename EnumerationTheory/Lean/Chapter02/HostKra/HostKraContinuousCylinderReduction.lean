import Chapter02.HostKra.HostKraFiniteCylinderDensity
import Chapter02.HostKra.HostKraFiniteMinimalReduction

open Classical MeasureTheory Set

noncomputable section

namespace Chapter02.HostKraContinuousCylinderReduction

universe u

/-- A strong finite-stage Host--Kra structure statement: a continuous
function of finitely many canonical fifteen-dual coordinates has a
compact-minimal orbit model for its fourfold last-slot correlation.

This exact form is useful as a sufficient condition, but the inverse-limit
theorem naturally supplies the weaker pro-minimal statement below. -/
def ContinuousFiniteFifteenDualMinimality : Prop :=
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
        HostKraStructuredRecurrence.IsMinimalOrbitSequence.{0}
          (HostKraStructuredApproximation.lastSlotCorrelation
            M hM A hA
            (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
              (HostKraFiniteCylinderDensity.finiteCode M hM t)
              ⟨HostKraFiniteCylinderDensity.finiteCode_measurable
                  M hM t, rfl⟩
              (ContinuousMap.toLp 2
                (Measure.map
                  (HostKraFiniteCylinderDensity.finiteCode M hM t) M.μ)
                ℂ φ)))

/-- The semantically exact remaining Host--Kra structure theorem: the
last-slot correlation of every continuous finite fifteen-dual cylinder is a
uniform limit of compact-minimal orbit sequences.

In classical terminology this is the continuous finite-cylinder consequence
of the theorem that the `Z₃` factor is an inverse limit of ergodic
three-step nilsystems. -/
def ContinuousFiniteFifteenDualProMinimality : Prop :=
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
        HostKraStructuredRecurrence.IsUniformLimitOfMinimalOrbitSequences
          (HostKraStructuredApproximation.lastSlotCorrelation
            M hM A hA
            (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
              (HostKraFiniteCylinderDensity.finiteCode M hM t)
              ⟨HostKraFiniteCylinderDensity.finiteCode_measurable
                  M hM t, rfl⟩
              (ContinuousMap.toLp 2
                (Measure.map
                  (HostKraFiniteCylinderDensity.finiteCode M hM t) M.μ)
                ℂ φ)))

/-- The strong exact-minimality statement implies the pro-minimal statement. -/
theorem proMinimality_of_minimality
    (hcontinuous : ContinuousFiniteFifteenDualMinimality.{u}) :
    ContinuousFiniteFifteenDualProMinimality.{u} := by
  intro M instSB hM hErg A hA t ht φ η hη
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : Fintype t := ht.fintype
  letI : IsFiniteMeasure
      (Measure.map
        (HostKraFiniteCylinderDensity.finiteCode M hM t) M.μ) :=
    Measure.isFiniteMeasure_map M.μ
      (HostKraFiniteCylinderDensity.finiteCode M hM t)
  refine ⟨HostKraStructuredApproximation.lastSlotCorrelation
      M hM A hA
      (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
        (HostKraFiniteCylinderDensity.finiteCode M hM t)
        ⟨HostKraFiniteCylinderDensity.finiteCode_measurable M hM t, rfl⟩
        (ContinuousMap.toLp 2
          (Measure.map
            (HostKraFiniteCylinderDensity.finiteCode M hM t) M.μ)
          ℂ φ)),
    hcontinuous M hM hErg A hA t ht φ, ?_⟩
  intro n
  simpa only [sub_self, abs_zero] using hη

/-- Finite-coordinate `L²` density and continuous-cylinder pro-minimality
give the required pro-minimal representation of the complete fifteen-dual
structured correlation. -/
theorem fifteenDualStructuredCorrelation_uniformLimit
    (hcontinuous : ContinuousFiniteFifteenDualProMinimality.{u})
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    HostKraStructuredRecurrence.IsUniformLimitOfMinimalOrbitSequences
      (HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation
        M hM A hA) := by
  intro η hη
  have hη3 : 0 < η / 3 := by positivity
  obtain ⟨t, ht, Q, hQmeas, hPQ⟩ :=
    HostKraFiniteCoordinate.exists_finite_fifteenDual_projection_approximation
      M hM
      (MultipleKhintchineCharacteristic.indicatorLp M hM A hA)
      hη3
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : Fintype t := ht.fintype
  letI : IsFiniteMeasure
      (Measure.map
        (HostKraFiniteCylinderDensity.finiteCode M hM t) M.μ) :=
    Measure.isFiniteMeasure_map M.μ
      (HostKraFiniteCylinderDensity.finiteCode M hM t)
  obtain ⟨φ, hQR⟩ :=
    HostKraFiniteCylinderDensity.exists_continuous_finiteCode_norm_sub_lt
      M hM t ht Q hQmeas hη3
  let R : Lp ℂ 2 M.μ :=
    MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
      (HostKraFiniteCylinderDensity.finiteCode M hM t)
      ⟨HostKraFiniteCylinderDensity.finiteCode_measurable M hM t, rfl⟩
      (ContinuousMap.toLp 2
        (Measure.map
          (HostKraFiniteCylinderDensity.finiteCode M hM t) M.μ)
        ℂ φ)
  have hPR :
      ‖HostKraDualSigma.condExpL2Value M.μ
            (HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM)
            (MultipleKhintchineCharacteristic.indicatorLp M hM A hA) -
          R‖ < 2 * (η / 3) := by
    calc
      ‖HostKraDualSigma.condExpL2Value M.μ
            (HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM)
            (MultipleKhintchineCharacteristic.indicatorLp M hM A hA) -
          R‖ ≤
        ‖HostKraDualSigma.condExpL2Value M.μ
              (HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM)
              (MultipleKhintchineCharacteristic.indicatorLp M hM A hA) -
            Q‖ + ‖Q - R‖ := by
          simpa only [sub_add_sub_cancel] using
            norm_add_le
              (HostKraDualSigma.condExpL2Value M.μ
                  (HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le
                    M hM)
                  (MultipleKhintchineCharacteristic.indicatorLp
                    M hM A hA) - Q)
              (Q - R)
      _ < η / 3 + η / 3 := add_lt_add hPQ hQR
      _ = 2 * (η / 3) := by ring
  obtain ⟨b, hbminimal, hRb⟩ :=
    hcontinuous M hM hErg A hA t ht φ (η / 3) hη3
  refine ⟨b, hbminimal, fun n ↦ ?_⟩
  have hSR :=
    HostKraStructuredApproximation.uniform_lastSlot_approximation_of_projection_approximation
      M hM A hA R (2 * (η / 3)) hPR n
  have htri :
      |HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation
            M hM A hA n - b n| ≤
        |HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation
              M hM A hA n -
            HostKraStructuredApproximation.lastSlotCorrelation
              M hM A hA R n| +
          |HostKraStructuredApproximation.lastSlotCorrelation
              M hM A hA R n - b n| := by
    simpa only [sub_add_sub_cancel] using
      abs_add_le
        (HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation
          M hM A hA n -
          HostKraStructuredApproximation.lastSlotCorrelation
            M hM A hA R n)
        (HostKraStructuredApproximation.lastSlotCorrelation
          M hM A hA R n - b n)
  calc
    |HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation
          M hM A hA n - b n| ≤ _ := htri
    _ < 2 * (η / 3) + η / 3 := add_lt_add hSR (hRb n)
    _ = η := by ring

/-- The exact continuous-cylinder pro-nil consequence implies the fourfold
BHK theorem on every standard-Borel ergodic system. -/
theorem standardBorelQuadrupleKhintchine
    (hcontinuous : ContinuousFiniteFifteenDualProMinimality.{u}) :
    MultipleKhintchineAssembly.StandardBorelQuadrupleKhintchine.{u} := by
  intro M instSB hErg A hA hApos ε hε
  exact
    HostKraStructuredRecurrence.quadruple_syndetic_of_structured_uniformLimit
      M hErg.1 hErg A hA
      (fifteenDualStructuredCorrelation_uniformLimit
        hcontinuous M hErg.1 hErg A hA)
      ε hε

/-- End-to-end reduction of the original axiom to the semantically exact
continuous finite-cylinder pro-minimal Host--Kra structure theorem. -/
theorem multipleKhintchineStatement_firstClause
    (hcontinuous : ContinuousFiniteFifteenDualProMinimality.{u})
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
  MultipleKhintchineAssembly.multipleKhintchineStatement_firstClause
    (standardBorelQuadrupleKhintchine hcontinuous) M

/-- The stronger exact-minimality formulation is also sufficient for the
original statement. -/
theorem multipleKhintchineStatement_firstClause_of_minimality
    (hcontinuous : ContinuousFiniteFifteenDualMinimality.{u})
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
  multipleKhintchineStatement_firstClause
    (proMinimality_of_minimality hcontinuous) M

end Chapter02.HostKraContinuousCylinderReduction
