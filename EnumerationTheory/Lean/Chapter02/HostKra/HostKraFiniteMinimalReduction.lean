import Chapter02.HostKra.HostKraFiniteCoordinate
import Chapter02.Recurrence.MultipleKhintchineAssembly

open Classical MeasureTheory Set

noncomputable section

namespace Chapter02.HostKraFiniteMinimalReduction

universe u

/-- The exact finite-coordinate Host--Kra structure statement still needed
for the fourfold theorem.  It says that every `L²` vector measurable with
respect to finitely many canonical fifteen-dual coordinates can be
approximated by vectors whose fourfold last-slot correlation is a continuous
orbit observation on a compact minimal system.

Mathematically, this is the finite-coordinate form of the fact that the
`Z₃` factor is an inverse limit of ergodic three-step nilsystems. -/
def FiniteFifteenDualMinimalDensity : Prop :=
  ∀ (M : System.{u}) [StandardBorelSpace M.X],
    ∀ (hM : Chapter01.IsMeasurePreservingSystem M),
    IsErgodic M →
    ∀ (A : Set M.X) (hA : MeasurableSet A),
    ∀ (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)),
    t.Finite →
    ∀ Q : Lp ℂ 2 M.μ,
    Q ∈ MeasureTheory.lpMeas ℂ ℂ
      (HostKraFiniteCoordinate.finiteFifteenDualMeasurableSpace M hM t)
      2 M.μ →
    ∀ η : ℝ, 0 < η →
      ∃ R : Lp ℂ 2 M.μ,
        ‖Q - R‖ < η ∧
        HostKraStructuredRecurrence.IsMinimalOrbitSequence.{0}
          (HostKraStructuredApproximation.lastSlotCorrelation
            M hM A hA R)

/-- Finite-coordinate minimal-model density supplies exactly the `L²`
minimal approximants required by the checked structured recurrence
reduction. -/
theorem exists_projection_minimal_approximant
    (hfinite : FiniteFifteenDualMinimalDensity.{u})
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (η : ℝ) (hη : 0 < η) :
    ∃ R : Lp ℂ 2 M.μ,
      ‖HostKraDualSigma.condExpL2Value M.μ
            (HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM)
            (MultipleKhintchineCharacteristic.indicatorLp M hM A hA) -
          R‖ < η ∧
        HostKraStructuredRecurrence.IsMinimalOrbitSequence.{0}
          (HostKraStructuredApproximation.lastSlotCorrelation
            M hM A hA R) := by
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨t, ht, Q, hQmeas, hPQ⟩ :=
    HostKraFiniteCoordinate.exists_finite_fifteenDual_projection_approximation
      M hM
      (MultipleKhintchineCharacteristic.indicatorLp M hM A hA)
      hη2
  obtain ⟨R, hQR, hRminimal⟩ :=
    hfinite M hM hErg A hA t ht Q hQmeas (η / 2) hη2
  refine ⟨R, ?_, hRminimal⟩
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
                (HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM)
                (MultipleKhintchineCharacteristic.indicatorLp M hM A hA) -
              Q)
            (Q - R)
    _ < η / 2 + η / 2 := add_lt_add hPQ hQR
    _ = η := by ring

/-- The finite-coordinate Host--Kra structure statement implies the exact
fourfold BHK theorem on every standard-Borel ergodic system. -/
theorem standardBorelQuadrupleKhintchine
    (hfinite : FiniteFifteenDualMinimalDensity.{u}) :
    MultipleKhintchineAssembly.StandardBorelQuadrupleKhintchine.{u} := by
  intro M instSB hErg A hA hApos ε hε
  exact
    HostKraStructuredApproximation.quadruple_syndetic_of_L2_minimal_approximants
      M hErg.1 hErg A hA
      (fun η hη ↦
        exists_projection_minimal_approximant
          hfinite M hErg.1 hErg A hA η hη)
      ε hε

/-- End-to-end reduction to one genuine structure theorem: finite
fifteen-dual-coordinate minimal-model density implies the original
threefold-and-fourfold Khintchine statement on arbitrary systems. -/
theorem multipleKhintchineStatement_firstClause
    (hfinite : FiniteFifteenDualMinimalDensity.{u})
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
    (standardBorelQuadrupleKhintchine hfinite) M

end Chapter02.HostKraFiniteMinimalReduction
