import Chapter02.HostKra.HostKraU3IndicatorCharacteristic
import Chapter02.Recurrence.MultipleKhintchineAssembly

open Classical Filter MeasureTheory Set

noncomputable section

namespace Chapter02.HostKraU3UniformBlockReduction

universe u

/-- A real sequence has translated-uniform Cesàro liminf at least `c`. -/
def HasUniformCesaroLiminfAtLeast (a : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      c - ε < cesaroAverage (fun n ↦ a (i + n)) N

/-- Translated-uniform signed Cesàro closeness transfers a uniform lower
limit, with an arbitrarily small loss, into one concrete uniform block
lower bound. -/
theorem hasUniformBlockLowerBound_of_signed_cesaro_close
    (a b : ℕ → ℝ) (c ε : ℝ) (hε : 0 < ε)
    (hclose :
      ∀ η : ℝ, 0 < η →
        ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
          |cesaroAverage (fun n ↦ a (i + n) - b (i + n)) N| < η)
    (hb : HasUniformCesaroLiminfAtLeast b c) :
    MultipleKhintchineSyndetic.HasUniformBlockLowerBound a (c - ε) := by
  have hε2 : 0 < ε / 2 := by positivity
  have hev :
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        |cesaroAverage (fun n ↦ a (i + n) - b (i + n)) N| < ε / 2 ∧
        c - ε / 2 < cesaroAverage (fun n ↦ b (i + n)) N := by
    filter_upwards [hclose (ε / 2) hε2, hb (ε / 2) hε2]
      with N hcloseN hbN
    exact fun i ↦ ⟨hcloseN i, hbN i⟩
  obtain ⟨N, hN⟩ := hev.exists
  let L := N + 1
  have hL : 0 < L := by
    dsimp only [L]
    omega
  refine ⟨L, hL, ?_⟩
  intro i
  have hi := hN i
  have hsplit :
      cesaroAverage (fun n ↦ a (i + n) - b (i + n)) N =
        cesaroAverage (fun n ↦ a (i + n)) N -
          cesaroAverage (fun n ↦ b (i + n)) N := by
    simp only [cesaroAverage, Finset.sum_sub_distrib, mul_sub]
  rw [hsplit] at hi
  have haavg :
      c - ε < cesaroAverage (fun n ↦ a (i + n)) N := by
    have hlower :
        -(ε / 2) <
          cesaroAverage (fun n ↦ a (i + n)) N -
            cesaroAverage (fun n ↦ b (i + n)) N :=
      (abs_lt.mp hi.1).1
    linarith [hi.2]
  unfold cesaroAverage at haavg
  change
    (Finset.range L).sum (fun j ↦ a (i + j)) >
      (L : ℝ) * (c - ε)
  have hNR : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hsum :
      ((N + 1 : ℕ) : ℝ) * (c - ε) <
        (Finset.range (N + 1)).sum (fun j ↦ a (i + j)) :=
    (lt_inv_mul_iff₀ hNR).mp haavg
  simpa only [L] using hsum

/-- The exact remaining two-step structure statement for the uniform-block
route: the last-slot seven-dual structured correlation has sharp
translated-uniform Cesàro liminf.  This is the output supplied by the
`Z₂` inverse-limit and uniquely ergodic Hall--Petresco analysis. -/
def SevenDualStructuredUniformLowerBound : Prop :=
  ∀ (M : System.{u}) [StandardBorelSpace M.X],
    ∀ (hM : Chapter01.IsMeasurePreservingSystem M),
    IsErgodic M →
    ∀ (A : Set M.X) (hA : MeasurableSet A),
      HasUniformCesaroLiminfAtLeast
        (HostKraU3IndicatorCharacteristic.sevenDualStructuredCorrelation
          M hM A hA)
        ((realMeasure M A) ^ 4)

/-- The seven-dual uniform lower-bound theorem and the already checked
`U³` characteristic estimate imply the standard-Borel fourfold
Khintchine theorem. -/
theorem standardBorelQuadrupleKhintchine
    (hstructure : SevenDualStructuredUniformLowerBound.{u}) :
    MultipleKhintchineAssembly.StandardBorelQuadrupleKhintchine.{u} := by
  intro M instSB hErg A hA hApos ε hε
  let a : ℕ → ℝ :=
    MultipleKhintchineSyndetic.quadrupleCorrelation M A
  let b : ℕ → ℝ :=
    HostKraU3IndicatorCharacteristic.sevenDualStructuredCorrelation
      M hErg.1 A hA
  have hclose :
      ∀ η : ℝ, 0 < η →
        ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
          |cesaroAverage (fun n ↦ a (i + n) - b (i + n)) N| < η := by
    simpa only [a, b] using
      HostKraU3IndicatorCharacteristic.quadrupleCorrelation_sub_sevenDualStructured_uniform_cesaro_zero
        M hErg.1 hErg A hA
  have hb :
      HasUniformCesaroLiminfAtLeast b ((realMeasure M A) ^ 4) := by
    simpa only [b] using hstructure M hErg.1 hErg A hA
  have hblock :
      MultipleKhintchineSyndetic.HasUniformBlockLowerBound
        a ((realMeasure M A) ^ 4 - ε) :=
    hasUniformBlockLowerBound_of_signed_cesaro_close
      a b ((realMeasure M A) ^ 4) ε hε hclose hb
  exact
    MultipleKhintchineSyndetic.isSyndetic_superlevel_of_uniformBlockLowerBound
      a ((realMeasure M A) ^ 4 - ε) hblock

/-- End-to-end reduction of the exact first multiple-Khintchine clause to
the two-step seven-dual uniform lower-bound theorem. -/
theorem multipleKhintchineStatement_firstClause
    (hstructure : SevenDualStructuredUniformLowerBound.{u})
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
    (standardBorelQuadrupleKhintchine hstructure) M

end Chapter02.HostKraU3UniformBlockReduction
