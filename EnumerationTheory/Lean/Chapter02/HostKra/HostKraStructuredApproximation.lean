import Chapter02.HostKra.HostKraStructuredRecurrence

open Classical MeasureTheory Set

noncomputable section

namespace Chapter02.HostKraStructuredApproximation

universe u

open HostKraU4ProgressionDecay

/-- The Hilbert-valued three-factor progression is linear in its final
`L²` slot.  This elementary identity is kept here because it is the exact
linearity needed to turn `L²` approximation of the fifteen-dual projection
into uniform approximation of the scalar structured correlation. -/
lemma tripleKoopmanProduct_sub_right
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G P Q : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (n : ℕ) :
    tripleKoopmanProduct M hM F G (P - Q) hFtop hGtop n =
      tripleKoopmanProduct M hM F G P hFtop hGtop n -
        tripleKoopmanProduct M hM F G Q hFtop hGtop n := by
  unfold tripleKoopmanProduct
  have hiter :
      ((KData M hM).U^[3 * n]) (P - Q) =
        ((KData M hM).U^[3 * n]) P -
          ((KData M hM).U^[3 * n]) Q := by
    induction (3 * n) with
    | zero => simp
    | succ m ih =>
        simp only [Function.iterate_succ_apply']
        rw [ih, map_sub]
  rw [hiter, MultipleKhintchineKronecker.lpPointwiseMul_sub_right]

/-- The fourfold progression obtained by putting an arbitrary `L²` vector
in the final dynamic slot and taking the real part. -/
def lastSlotCorrelation
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (Q : Lp ℂ 2 M.μ) (n : ℕ) : ℝ :=
  let F := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
    (fun x ↦ F x) (fun x ↦ F x)
    (fun x ↦ F x) (fun x ↦ Q x) n x ∂M.μ).re

/-- The last-slot correlation is globally `1`-Lipschitz in its `L²`
argument, uniformly in the progression time. -/
theorem abs_lastSlotCorrelation_sub_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (P Q : Lp ℂ 2 M.μ) (n : ℕ) :
    |lastSlotCorrelation M hM A hA P n -
        lastSlotCorrelation M hM A hA Q n| ≤ ‖P - Q‖ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let F := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  let hFtop :=
    MultipleKhintchineCharacteristic.indicatorLp_mem_top M hM A hA
  let V :=
    tripleKoopmanProduct M hM F F (P - Q) hFtop hFtop n
  have hF_norm : ‖F‖ ≤ 1 := by
    have hμ : measureUnivNNReal M.μ = 1 := by
      apply NNReal.eq
      simp [measureUnivNNReal]
    simpa [hμ] using
      (MeasureTheory.Lp.norm_le_of_ae_bound (p := (2 : ENNReal))
        (f := F) (by norm_num)
        (MultipleKhintchineCharacteristic.indicatorLp_norm_le_one
          M hM A hA))
  have hV_norm : ‖V‖ ≤ ‖P - Q‖ := by
    have hbound :=
      norm_tripleKoopmanProduct_le M hM F F (P - Q)
        hFtop hFtop 1 1 (by norm_num) (by norm_num)
        (MultipleKhintchineCharacteristic.indicatorLp_norm_le_one
          M hM A hA)
        (MultipleKhintchineCharacteristic.indicatorLp_norm_le_one
          M hM A hA) n
    simpa only [V, one_mul] using hbound
  have hinner :
      @inner ℂ (Lp ℂ 2 M.μ) _
          (ForwardKroneckerFactor.lpStar M F) V =
        @inner ℂ (Lp ℂ 2 M.μ) _
            (ForwardKroneckerFactor.lpStar M F)
            (tripleKoopmanProduct M hM F F P hFtop hFtop n) -
          @inner ℂ (Lp ℂ 2 M.μ) _
            (ForwardKroneckerFactor.lpStar M F)
            (tripleKoopmanProduct M hM F F Q hFtop hFtop n) := by
    change
      @inner ℂ (Lp ℂ 2 M.μ) _
          (ForwardKroneckerFactor.lpStar M F)
          (tripleKoopmanProduct M hM F F (P - Q) hFtop hFtop n) =
        _
    rw [tripleKoopmanProduct_sub_right, inner_sub_right]
  rw [lastSlotCorrelation, lastSlotCorrelation]
  rw [←
    Chapter02.HostKraU4Characteristic.inner_lpStar_tripleKoopmanProduct_eq_integral_quadruple
      M hM F F F P hFtop hFtop n]
  rw [←
    Chapter02.HostKraU4Characteristic.inner_lpStar_tripleKoopmanProduct_eq_integral_quadruple
      M hM F F F Q hFtop hFtop n]
  rw [← Complex.sub_re, ← hinner]
  calc
    |(@inner ℂ (Lp ℂ 2 M.μ) _
        (ForwardKroneckerFactor.lpStar M F) V).re| ≤
        ‖@inner ℂ (Lp ℂ 2 M.μ) _
          (ForwardKroneckerFactor.lpStar M F) V‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖ForwardKroneckerFactor.lpStar M F‖ * ‖V‖ :=
      norm_inner_le_norm _ _
    _ ≤ 1 * ‖P - Q‖ := by
      rw [ForwardKroneckerFactor.norm_lpStar]
      exact mul_le_mul hF_norm hV_norm (norm_nonneg _) (by norm_num)
    _ = ‖P - Q‖ := one_mul _

/-- The previously isolated fifteen-dual structured sequence is precisely
the last-slot sequence of its conditional `L²` projection. -/
theorem fifteenDualStructuredCorrelation_eq_lastSlotCorrelation
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) :
    let F := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
    let P := HostKraDualSigma.condExpL2Value M.μ
      (HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM) F
    HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation
        M hM A hA n =
      lastSlotCorrelation M hM A hA P n := by
  exact
    HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation_eq_projectionIntegral
      M hM A hA n

/-- A family of `L²` approximants to the fifteen-dual conditional
projection gives uniform approximation of the entire structured
correlation sequence. -/
theorem uniform_lastSlot_approximation_of_projection_approximation
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (Q : Lp ℂ 2 M.μ) (η : ℝ)
    (hQ : ‖HostKraDualSigma.condExpL2Value M.μ
          (HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM)
          (MultipleKhintchineCharacteristic.indicatorLp M hM A hA) -
        Q‖ < η) :
    ∀ n : ℕ,
      |HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation
            M hM A hA n -
          lastSlotCorrelation M hM A hA Q n| < η := by
  intro n
  rw [fifteenDualStructuredCorrelation_eq_lastSlotCorrelation]
  exact lt_of_le_of_lt
    (abs_lastSlotCorrelation_sub_le M hM A hA _ Q n) hQ

/-- It is now enough to approximate the fifteen-dual projection in `L²`
by vectors whose scalar last-slot correlations have compact-minimal orbit
models.  This is the exact finite-cylinder/minimal-model obligation left to
the structure theorem. -/
theorem fifteenDualStructuredCorrelation_uniformLimit_of_L2_approximants
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (happrox :
      ∀ η : ℝ, 0 < η →
        ∃ Q : Lp ℂ 2 M.μ,
          ‖HostKraDualSigma.condExpL2Value M.μ
                (HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM)
                (MultipleKhintchineCharacteristic.indicatorLp M hM A hA) -
              Q‖ < η ∧
            HostKraStructuredRecurrence.IsMinimalOrbitSequence.{0}
              (lastSlotCorrelation M hM A hA Q)) :
    HostKraStructuredRecurrence.IsUniformLimitOfMinimalOrbitSequences
      (HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation
        M hM A hA) := by
  intro η hη
  obtain ⟨Q, hQ, hminimal⟩ := happrox η hη
  exact ⟨lastSlotCorrelation M hM A hA Q, hminimal,
    uniform_lastSlot_approximation_of_projection_approximation
      M hM A hA Q η hQ⟩

/-- Direct end-to-end form of the fourfold reduction: finite-model `L²`
approximants to the fifteen-dual projection, with compact-minimal scalar
orbit models, imply the exact BHK fourfold syndetic conclusion. -/
theorem quadruple_syndetic_of_L2_minimal_approximants
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (happrox :
      ∀ η : ℝ, 0 < η →
        ∃ Q : Lp ℂ 2 M.μ,
          ‖HostKraDualSigma.condExpL2Value M.μ
                (HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM)
                (MultipleKhintchineCharacteristic.indicatorLp M hM A hA) -
              Q‖ < η ∧
            HostKraStructuredRecurrence.IsMinimalOrbitSequence.{0}
              (lastSlotCorrelation M hM A hA Q))
    (ε : ℝ) (hε : 0 < ε) :
    IsSyndetic {n : ℕ |
      MultipleKhintchineSyndetic.quadrupleCorrelation M A n >
        (realMeasure M A) ^ 4 - ε} := by
  apply
    HostKraStructuredRecurrence.quadruple_syndetic_of_structured_uniformLimit
      M hM hErg A hA
  · exact
      fifteenDualStructuredCorrelation_uniformLimit_of_L2_approximants
        M hM A hA happrox
  · exact hε

end Chapter02.HostKraStructuredApproximation
