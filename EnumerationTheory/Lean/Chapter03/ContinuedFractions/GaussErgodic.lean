import Chapter02.Ergodic.ErgodicBirkhoffBridge
import Chapter03.ContinuedFractions.GaussMeasure

noncomputable section

open Classical Filter MeasureTheory
open scoped BigOperators ENNReal

namespace Chapter03

def gaussSystem : Chapter02.System where
  X := GaussSpace
  measurableSpace := inferInstance
  μ := gaussMeasure
  T := gaussMap

theorem gaussSystem_isMeasurePreserving :
    Chapter01.IsMeasurePreservingSystem gaussSystem := by
  constructor
  · exact ⟨by simpa [gaussSystem] using gaussMeasure_isProbability.measure_univ⟩
  · exact gaussMap_measurePreserving

theorem gaussSystem_ergodic_iff :
    IsErgodicGaussSystem { μ := gaussMeasure, T := gaussMap } ↔
      Chapter02.IsErgodic gaussSystem := by
  constructor
  · rintro ⟨hpres, hsets⟩
    refine ⟨gaussSystem_isMeasurePreserving, ?_⟩
    intro A hA hnull
    exact hsets A hA hnull
  · rintro ⟨hpres, hsets⟩
    refine ⟨⟨rfl, rfl, gaussMeasure_isProbability, gaussMap_measurePreserving⟩, ?_⟩
    intro A hA hnull
    exact hsets A hA hnull

theorem gaussMap_quasiMeasurePreserving :
    MeasureTheory.Measure.QuasiMeasurePreserving gaussMap gaussMeasure gaussMeasure :=
  gaussMap_measurePreserving.quasiMeasurePreserving

theorem gaussMap_quasiErgodic_of_preErgodic
    (hpre : PreErgodic gaussMap gaussMeasure) :
    QuasiErgodic gaussMap gaussMeasure :=
  ⟨gaussMap_quasiMeasurePreserving, hpre⟩

theorem gaussMap_preimage_ae_eq_preimage
    {A B : Set GaussSpace} (hAB : A =ᶠ[ae gaussMeasure] B) :
    gaussMap ⁻¹' A =ᶠ[ae gaussMeasure] gaussMap ⁻¹' B := by
  simpa only [Function.comp_def] using
    gaussMap_quasiMeasurePreserving.ae_eq_comp hAB

theorem gaussMap_iterate_preimage_ae_eq
    {A B : Set GaussSpace} (n : ℕ)
    (hAB : A =ᶠ[ae gaussMeasure] B) :
    (gaussMap^[n]) ⁻¹' A =ᶠ[ae gaussMeasure] (gaussMap^[n]) ⁻¹' B := by
  induction n with
  | zero => simpa using hAB
  | succ n ih =>
      simpa only [Set.preimage_preimage, Function.iterate_succ_apply] using
        gaussMap_preimage_ae_eq_preimage ih

theorem gaussMap_preimage_ae_eq_self_of_symmDiff_zero
    {A : Set GaussSpace}
    (hnull : gaussMeasure (Chapter00.symmDiff (gaussMap ⁻¹' A) A) = 0) :
    gaussMap ⁻¹' A =ᶠ[ae gaussMeasure] A := by
  rw [MeasureTheory.ae_eq_set]
  unfold Chapter00.symmDiff at hnull
  exact ⟨MeasureTheory.measure_mono_null Set.subset_union_left hnull,
    MeasureTheory.measure_mono_null Set.subset_union_right hnull⟩

theorem gaussMap_iterate_preimage_ae_eq_self
    {A : Set GaussSpace}
    (hnull : gaussMeasure (Chapter00.symmDiff (gaussMap ⁻¹' A) A) = 0)
    (n : ℕ) :
    (gaussMap^[n]) ⁻¹' A =ᶠ[ae gaussMeasure] A := by
  have hstep := gaussMap_preimage_ae_eq_self_of_symmDiff_zero hnull
  induction n with
  | zero => simp
  | succ n ih =>
      have hpre := gaussMap_preimage_ae_eq_preimage ih
      have htrans := hpre.trans hstep
      simpa only [Set.preimage_preimage, Function.iterate_succ_apply] using htrans

def gaussInvariantRepresentative (A : Set GaussSpace) : Set GaussSpace :=
  ⋃ n : ℕ, ⋂ k : ℕ, (gaussMap^[n + k]) ⁻¹' A

theorem gaussInvariantRepresentative_invariant (A : Set GaussSpace) :
    gaussMap ⁻¹' gaussInvariantRepresentative A = gaussInvariantRepresentative A := by
  ext x
  simp only [gaussInvariantRepresentative, Set.mem_preimage, Set.mem_iUnion,
    Set.mem_iInter]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, fun k => ?_⟩
    simpa only [Nat.add_assoc, Nat.one_add, Function.iterate_succ_apply] using hn k
  · rintro ⟨n, hn⟩
    refine ⟨n, fun k => ?_⟩
    simpa only [Nat.add_assoc, Function.iterate_succ_apply] using hn (k + 1)

theorem gaussInvariantRepresentative_measurable
    {A : Set GaussSpace} (hA : MeasurableSet A) :
    MeasurableSet (gaussInvariantRepresentative A) := by
  exact MeasurableSet.iUnion fun n => MeasurableSet.iInter fun k =>
    hA.preimage (gaussMap_measurable.iterate (n + k))

theorem gaussInvariantRepresentative_ae_eq
    {A : Set GaussSpace}
    (hnull : gaussMeasure (Chapter00.symmDiff (gaussMap ⁻¹' A) A) = 0) :
    gaussInvariantRepresentative A =ᶠ[ae gaussMeasure] A := by
  have hall : ∀ᵐ x ∂gaussMeasure, ∀ n : ℕ,
      ((gaussMap^[n]) ⁻¹' A) x = A x :=
    MeasureTheory.ae_all_iff.2 fun n =>
      gaussMap_iterate_preimage_ae_eq_self hnull n
  filter_upwards [hall] with x hx
  apply propext
  constructor
  · intro hxrep
    change x ∈ ⋃ n : ℕ, ⋂ k : ℕ, (gaussMap^[n + k]) ⁻¹' A at hxrep
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxrep
    have hn0 := Set.mem_iInter.mp hn 0
    simp only [Nat.add_zero] at hn0
    change ((gaussMap^[n]) ⁻¹' A) x at hn0
    rw [hx n] at hn0
    exact hn0
  · intro hxA
    change x ∈ ⋃ n : ℕ, ⋂ k : ℕ, (gaussMap^[n + k]) ⁻¹' A
    apply Set.mem_iUnion.mpr
    refine ⟨0, Set.mem_iInter.mpr fun k => ?_⟩
    simp only [Nat.zero_add]
    change ((gaussMap^[k]) ⁻¹' A) x
    rw [hx k]
    exact hxA


private structure BranchMatrix where
  A : ℕ
  B : ℕ
  C : ℕ
  D : ℕ

private def BranchMatrix.one : BranchMatrix := ⟨1, 0, 0, 1⟩

private def BranchMatrix.append (M : BranchMatrix) (n : ℕ) : BranchMatrix :=
  ⟨M.B, M.A + (n + 1) * M.B, M.D, M.C + (n + 1) * M.D⟩

private def branchMatrix (d : ℕ → ℕ) : ℕ → BranchMatrix
  | 0 => BranchMatrix.one
  | n + 1 => (branchMatrix d n).append (d n)

private def branchWord (d : ℕ → ℕ) : ℕ → ℝ → ℝ
  | 0 => id
  | n + 1 => fun y => branchWord d n (gaussBranch (d n) y)

private theorem gaussBranch_mem_gaussSpace (n : ℕ) (y : ℝ)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    gaussBranch n y ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · dsimp [gaussBranch]
    apply inv_nonneg.mpr
    exact add_nonneg (by positivity) hy.1
  · dsimp [gaussBranch]
    have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos n
    have hden : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + y :=
      add_pos_of_pos_of_nonneg hnpos hy.1
    rw [inv_le_one₀ hden]
    have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    simpa using add_le_add hn1 hy.1

private theorem branchWord_mem_gaussSpace (d : ℕ → ℕ) (n : ℕ) (y : ℝ)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    branchWord d n y ∈ Set.Icc (0 : ℝ) 1 := by
  induction n generalizing y with
  | zero => exact hy
  | succ n ih =>
      rw [branchWord]
      exact ih _ (gaussBranch_mem_gaussSpace (d n) y hy)

theorem gaussBranch_mem_iff_of_invariant {S : Set GaussSpace}
    (hInv : gaussMap ⁻¹' S = S) (n : ℕ) (y : ℝ)
    (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    (⟨gaussBranch n y, gaussBranch_mem_gaussSpace n y ⟨hy.1, hy.2.le⟩⟩ ∈ S) ↔
      (⟨y, ⟨hy.1, hy.2.le⟩⟩ ∈ S) := by
  have hmap : gaussMap
      ⟨gaussBranch n y, gaussBranch_mem_gaussSpace n y ⟨hy.1, hy.2.le⟩⟩ =
      ⟨y, ⟨hy.1, hy.2.le⟩⟩ := by
    apply Subtype.ext
    exact gaussMapReal_gaussBranch n y hy
  have hmem := Set.ext_iff.mp hInv
    ⟨gaussBranch n y, gaussBranch_mem_gaussSpace n y ⟨hy.1, hy.2.le⟩⟩
  simpa [hmap] using hmem.symm

private theorem gaussBranch_irrational (n : ℕ) (y : ℝ)
    (hy : Irrational y) : Irrational (gaussBranch n y) := by
  dsimp [gaussBranch]
  have hsum : Irrational (((n + 1 : ℕ) : ℝ) + y) := by
    simpa [add_comm] using hy.natCast_add (n + 1)
  exact hsum.inv

theorem branchWord_mem_iff_of_invariant {S : Set GaussSpace}
    (hInv : gaussMap ⁻¹' S = S) (d : ℕ → ℕ) (n : ℕ)
    (z : GaussSpace) (hzlt : z.1 < 1) (hzirr : Irrational z.1) :
    ((⟨branchWord d n z.1, branchWord_mem_gaussSpace d n z.1 z.2⟩ : GaussSpace) ∈ S) ↔
      z ∈ S := by
  induction n generalizing z with
  | zero => simp [branchWord]
  | succ n ih =>
      simp only [branchWord]
      have hbr : gaussBranch (d n) z.1 ∈ Set.Icc (0 : ℝ) 1 :=
        gaussBranch_mem_gaussSpace (d n) z.1 z.2
      have hirrbr : Irrational (gaussBranch (d n) z.1) :=
        gaussBranch_irrational (d n) z.1 hzirr
      have hbrlt : gaussBranch (d n) z.1 < 1 := by
        exact lt_of_le_of_ne hbr.2 (by
          intro heq
          exact hirrbr ⟨(1 : ℚ), by simp [heq]⟩)
      let zbr : GaussSpace := ⟨gaussBranch (d n) z.1, hbr⟩
      have hzbr : zbr.1 < 1 := hbrlt
      have hzirrbr : Irrational zbr.1 := hirrbr
      have hstep := ih zbr hzbr hzirrbr
      have htail := gaussBranch_mem_iff_of_invariant hInv (d n) z.1
        ⟨z.2.1, hzlt⟩
      simpa [zbr] using hstep.trans htail

theorem branchWord_image_subset_invariant
    {S : Set GaussSpace} (hInv : gaussMap ⁻¹' S = S)
    (d : ℕ → ℕ) (n : ℕ) (E : Set ℝ)
    (hEI : E ⊆ Set.Ico (0 : ℝ) 1)
    (hES : E ⊆ Subtype.val '' S)
    (hEirr : ∀ y ∈ E, Irrational y) :
    branchWord d n '' E ⊆ Subtype.val '' S := by
  rintro w ⟨y, hy, rfl⟩
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(hEI hy).1, (hEI hy).2.le⟩
  let z : GaussSpace := ⟨y, hyIcc⟩
  have hzS : z ∈ S := by
    rcases hES hy with ⟨z', hz', hzval⟩
    have : z' = z := Subtype.ext hzval
    simpa [this] using hz'
  have hzbranch :
      (⟨branchWord d n y, branchWord_mem_gaussSpace d n y hyIcc⟩ : GaussSpace) ∈ S := by
    have hiff := branchWord_mem_iff_of_invariant hInv d n z
      (hEI hy).2 (hEirr y hy)
    exact hiff.mpr hzS
  exact ⟨⟨branchWord d n y, branchWord_mem_gaussSpace d n y hyIcc⟩,
    hzbranch, rfl⟩


private def BranchMatrix.eval (M : BranchMatrix) (y : ℝ) : ℝ :=
  ((M.A : ℝ) * y + M.B) / ((M.C : ℝ) * y + M.D)

private theorem branchWord_eq_eval (d : ℕ → ℕ) (n : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    branchWord d n y = (branchMatrix d n).eval y := by
  induction n generalizing y with
  | zero => simp [branchWord, branchMatrix, BranchMatrix.one, BranchMatrix.eval]
  | succ n ih =>
      rw [branchWord]
      change branchWord d n (gaussBranch (d n) y) = _
      rw [ih _ (by dsimp [gaussBranch]; positivity)]
      simp only [branchMatrix]
      dsimp [BranchMatrix.append, BranchMatrix.eval, gaussBranch]
      by_cases hden : (((d n + 1 : ℕ) : ℝ) + y) = 0
      · have : 0 < (((d n + 1 : ℕ) : ℝ) + y) := by positivity
        exact (this.ne' hden).elim
      · field_simp [hden]
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        ring

private theorem branchMatrix_nonnegative (d : ℕ → ℕ) (n : ℕ) :
    (branchMatrix d n).C ≤ (branchMatrix d n).D ∧
      0 < (branchMatrix d n).D := by
  induction n with
  | zero => simp [branchMatrix, BranchMatrix.one]
  | succ n ih =>
      rcases ih with ⟨hCD, hD⟩
      simp only [branchMatrix]
      dsimp [BranchMatrix.append]
      constructor
      · have hmul : (branchMatrix d n).D ≤
            (d n + 1) * (branchMatrix d n).D := by
          exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
        omega
      · positivity

private theorem branchMatrix_determinant (d : ℕ → ℕ) (n : ℕ) :
    |((branchMatrix d n).A : ℤ) * (branchMatrix d n).D -
      ((branchMatrix d n).B : ℤ) * (branchMatrix d n).C| = 1 := by
  induction n with
  | zero => norm_num only [branchMatrix, BranchMatrix.one]
  | succ n ih =>
      simp only [branchMatrix]
      dsimp [BranchMatrix.append]
      calc
        |((branchMatrix d n).B : ℤ) *
              ((branchMatrix d n).C + (d n + 1) * (branchMatrix d n).D) -
            ((branchMatrix d n).A + (d n + 1) * (branchMatrix d n).B) *
              (branchMatrix d n).D| =
            |-(((branchMatrix d n).A : ℤ) * (branchMatrix d n).D -
              ((branchMatrix d n).B : ℤ) * (branchMatrix d n).C)| := by
              congr 1
              ring
        _ = 1 := by rw [abs_neg, ih]

private theorem branchMatrix_C_le_D (d : ℕ → ℕ) (n : ℕ) :
    (branchMatrix d n).C ≤ (branchMatrix d n).D :=
  (branchMatrix_nonnegative d n).1

private theorem branchMatrix_D_pos (d : ℕ → ℕ) (n : ℕ) :
    0 < (branchMatrix d n).D :=
  (branchMatrix_nonnegative d n).2

private theorem branchMatrix_C_pos (d : ℕ → ℕ) (n : ℕ) (hn : 0 < n) :
    0 < (branchMatrix d n).C := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [branchMatrix]
  dsimp [BranchMatrix.append]
  exact branchMatrix_D_pos d k

private theorem branchMatrix_D_ge_index (d : ℕ → ℕ) (n : ℕ) :
    n ≤ (branchMatrix d n).D := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp only [branchMatrix]
      dsimp [BranchMatrix.append]
      by_cases hn : n = 0
      · subst n
        simp [branchMatrix, BranchMatrix.one]
      · have hC : 0 < (branchMatrix d n).C :=
          branchMatrix_C_pos d n (Nat.pos_of_ne_zero hn)
        have hmul : (branchMatrix d n).D ≤
            (d n + 1) * (branchMatrix d n).D :=
          Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
        omega

private theorem tendsto_branchMatrix_D_atTop (d : ℕ → ℕ) :
    Tendsto (fun n => ((branchMatrix d n).D : ℝ)) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt b
  filter_upwards [eventually_ge_atTop N] with n hn
  have hindex := branchMatrix_D_ge_index d n
  have hcast : (n : ℝ) ≤ (branchMatrix d n).D := by exact_mod_cast hindex
  have hNcast : b ≤ (N : ℝ) := hN.le
  have hncast : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem branchRadius_tendsto_zero (d : ℕ → ℕ) :
    Tendsto (fun n => (((branchMatrix d n).D : ℝ) ^ 2)⁻¹) atTop (nhds 0) := by
  have hD := tendsto_branchMatrix_D_atTop d
  have hsq : Tendsto (fun n => ((branchMatrix d n).D : ℝ) ^ 2) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hD (eventually_ge_atTop b)] with n hn
    change b ≤ (branchMatrix d n).D at hn
    have hDn : (1 : ℝ) ≤ (branchMatrix d n).D := by
      have hnat : 1 ≤ (branchMatrix d n).D := by
        exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (branchMatrix_D_pos d n))
      exact_mod_cast hnat
    nlinarith [sq_nonneg ((branchMatrix d n).D : ℝ)]
  exact tendsto_inv_atTop_zero.comp hsq

theorem branchRadius_pos (d : ℕ → ℕ) (n : ℕ) :
    0 < (((branchMatrix d n).D : ℝ) ^ 2)⁻¹ := by
  have hD : (0 : ℝ) < (branchMatrix d n).D := by
    exact_mod_cast branchMatrix_D_pos d n
  positivity

theorem branchBall_volume (d : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    volume (Metric.closedBall x (((branchMatrix d n).D : ℝ) ^ 2)⁻¹) =
      ENNReal.ofReal (2 * (((branchMatrix d n).D : ℝ) ^ 2)⁻¹) := by
  exact Real.volume_closedBall x _

private def BranchMatrix.detReal (M : BranchMatrix) : ℝ :=
  (M.A : ℝ) * M.D - (M.B : ℝ) * M.C

private theorem branchMatrix_abs_detReal (d : ℕ → ℕ) (n : ℕ) :
    |(branchMatrix d n).detReal| = 1 := by
  let z : ℤ := ((branchMatrix d n).A : ℤ) * (branchMatrix d n).D -
    ((branchMatrix d n).B : ℤ) * (branchMatrix d n).C
  have hzabs : |z| = 1 := branchMatrix_determinant d n
  have hz : z = 1 ∨ z = -1 := (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hzabs
  have hcast : (branchMatrix d n).detReal = (z : ℝ) := by
    dsimp [BranchMatrix.detReal, z]
    push_cast
    ring
  rw [hcast]
  rcases hz with hz | hz
  · rw [hz]
    norm_num
  · rw [hz]
    norm_num

private theorem BranchMatrix.hasDerivAt_eval (M : BranchMatrix) (y : ℝ)
    (hden : (M.C : ℝ) * y + M.D ≠ 0) :
    HasDerivAt M.eval
      (M.detReal / (((M.C : ℝ) * y + M.D) ^ 2)) y := by
  have hnum : HasDerivAt (fun z : ℝ => (M.A : ℝ) * z + M.B) M.A y := by
    simpa using ((hasDerivAt_id y).const_mul (M.A : ℝ)).add_const (M.B : ℝ)
  have hden' : HasDerivAt (fun z : ℝ => (M.C : ℝ) * z + M.D) M.C y := by
    simpa using ((hasDerivAt_id y).const_mul (M.C : ℝ)).add_const (M.D : ℝ)
  have hquot := hnum.div hden' hden
  simpa only [BranchMatrix.eval] using hquot.congr_deriv (by
    dsimp [BranchMatrix.detReal]
    congr 1
    ring)

private theorem branchWord_abs_deriv (d : ℕ → ℕ) (n : ℕ) (y : ℝ)
    (hy : 0 ≤ y) :
    HasDerivWithinAt (branchWord d n)
      (((((branchMatrix d n).C : ℝ) * y +
        (branchMatrix d n).D) ^ 2)⁻¹ *
        (branchMatrix d n).detReal) (Set.Ici 0) y := by
  have hD : 0 < ((branchMatrix d n).D : ℝ) := by
    exact_mod_cast branchMatrix_D_pos d n
  have hden : ((branchMatrix d n).C : ℝ) * y +
      (branchMatrix d n).D ≠ 0 := by positivity
  have heval := (branchMatrix d n).hasDerivAt_eval y hden
  have hwithin : HasDerivWithinAt (branchWord d n)
      ((branchMatrix d n).detReal /
        (((branchMatrix d n).C : ℝ) * y + (branchMatrix d n).D) ^ 2)
      (Set.Ici 0) y := by
    apply heval.hasDerivWithinAt.congr
    · intro z hz
      exact branchWord_eq_eval d n z hz
    · exact branchWord_eq_eval d n y hy
  convert hwithin using 1
  field_simp

private def branchJacobian (d : ℕ → ℕ) (n : ℕ) (y : ℝ) : ℝ :=
  (((branchMatrix d n).C : ℝ) * y + (branchMatrix d n).D)⁻¹ ^ 2

private theorem branchWord_deriv_abs (d : ℕ → ℕ) (n : ℕ) (y : ℝ)
    (hy : 0 ≤ y) :
    |((((((branchMatrix d n).C : ℝ) * y +
        (branchMatrix d n).D) ^ 2)⁻¹) *
        (branchMatrix d n).detReal)| = branchJacobian d n y := by
  rw [abs_mul, branchMatrix_abs_detReal]
  simp only [mul_one, branchJacobian]
  have hden : 0 ≤ ((branchMatrix d n).C : ℝ) * y +
      (branchMatrix d n).D := by positivity
  rw [abs_of_nonneg (by positivity :
    0 ≤ (((((branchMatrix d n).C : ℝ) * y +
      (branchMatrix d n).D) ^ 2)⁻¹))]
  rw [inv_pow]

private theorem branchWord_injOn (d : ℕ → ℕ) (n : ℕ) :
    Set.InjOn (branchWord d n) (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  rw [branchWord_eq_eval d n x hx, branchWord_eq_eval d n y hy] at hxy
  have hDx : 0 < ((branchMatrix d n).C : ℝ) * x +
      (branchMatrix d n).D := by
    have hD : 0 < ((branchMatrix d n).D : ℝ) := by
      exact_mod_cast branchMatrix_D_pos d n
    have hx0 : 0 ≤ x := hx
    positivity
  have hDy : 0 < ((branchMatrix d n).C : ℝ) * y +
      (branchMatrix d n).D := by
    have hD : 0 < ((branchMatrix d n).D : ℝ) := by
      exact_mod_cast branchMatrix_D_pos d n
    have hy0 : 0 ≤ y := hy
    positivity
  have hdet : (branchMatrix d n).detReal ≠ 0 := by
    intro hzero
    have habs := branchMatrix_abs_detReal d n
    rw [hzero, abs_zero] at habs
    norm_num at habs
  dsimp [BranchMatrix.eval] at hxy
  have hxy' :
      (((branchMatrix d n).A : ℝ) * x + (branchMatrix d n).B) *
          (((branchMatrix d n).C : ℝ) * y + (branchMatrix d n).D) =
        (((branchMatrix d n).A : ℝ) * y + (branchMatrix d n).B) *
          (((branchMatrix d n).C : ℝ) * x + (branchMatrix d n).D) := by
    exact (div_eq_div_iff hDx.ne' hDy.ne').mp hxy
  have hfactor : (branchMatrix d n).detReal * (x - y) = 0 := by
    dsimp [BranchMatrix.detReal]
    calc
      (((branchMatrix d n).A : ℝ) * (branchMatrix d n).D -
          (branchMatrix d n).B * (branchMatrix d n).C) * (x - y) =
          ((((branchMatrix d n).A : ℝ) * x + (branchMatrix d n).B) *
            (((branchMatrix d n).C : ℝ) * y + (branchMatrix d n).D) -
          (((branchMatrix d n).A : ℝ) * y + (branchMatrix d n).B) *
            (((branchMatrix d n).C : ℝ) * x + (branchMatrix d n).D)) := by ring
      _ = 0 := sub_eq_zero.mpr hxy'
  rcases mul_eq_zero.mp hfactor with hbad | hsub
  · exact (hdet hbad).elim
  · exact sub_eq_zero.mp hsub

private theorem branchJacobian_lower (d : ℕ → ℕ) (n : ℕ) (y : ℝ)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (((2 : ℝ) * (branchMatrix d n).D) ^ 2)⁻¹ ≤
      branchJacobian d n y := by
  have hC : ((branchMatrix d n).C : ℝ) ≤ (branchMatrix d n).D := by
    exact_mod_cast branchMatrix_C_le_D d n
  have hD : 0 < ((branchMatrix d n).D : ℝ) := by
    exact_mod_cast branchMatrix_D_pos d n
  have hC0 : 0 ≤ ((branchMatrix d n).C : ℝ) := Nat.cast_nonneg _
  have hdenpos : 0 < ((branchMatrix d n).C : ℝ) * y +
      (branchMatrix d n).D := by
    nlinarith [mul_nonneg hC0 hy.1]
  have hdenle : ((branchMatrix d n).C : ℝ) * y +
      (branchMatrix d n).D ≤ 2 * (branchMatrix d n).D := by
    have hmul := mul_le_mul_of_nonneg_left hy.2 hC0
    nlinarith
  dsimp [branchJacobian]
  rw [inv_pow]
  exact inv_anti₀ (sq_pos_of_pos hdenpos)
    ((sq_le_sq₀ hdenpos.le (by positivity)).2 hdenle)

private theorem branchJacobian_upper (d : ℕ → ℕ) (n : ℕ) (y : ℝ)
    (hy : 0 ≤ y) :
    branchJacobian d n y ≤ (((branchMatrix d n).D : ℝ) ^ 2)⁻¹ := by
  have hD : 0 < ((branchMatrix d n).D : ℝ) := by
    exact_mod_cast branchMatrix_D_pos d n
  have hden : ((branchMatrix d n).D : ℝ) ≤
      ((branchMatrix d n).C : ℝ) * y + (branchMatrix d n).D := by
    have hprod : 0 ≤ ((branchMatrix d n).C : ℝ) * y :=
      mul_nonneg (Nat.cast_nonneg _) hy
    linarith
  dsimp [branchJacobian]
  rw [inv_pow]
  exact inv_anti₀ (sq_pos_of_pos hD)
    ((sq_le_sq₀ hD.le (by positivity)).2 hden)

private theorem volume_branchWord_image (d : ℕ → ℕ) (n : ℕ)
    (E : Set ℝ) (hE : MeasurableSet E) (hEI : E ⊆ Set.Icc (0 : ℝ) 1) :
    volume (branchWord d n '' E) =
      ∫⁻ y in E, ENNReal.ofReal (branchJacobian d n y) ∂volume := by
  rw [← MeasureTheory.setLIntegral_one (branchWord d n '' E)]
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul hE
    (fun y hy => (branchWord_abs_deriv d n y (hEI hy).1).mono
      (fun _ hz => (hEI hz).1))
    ((branchWord_injOn d n).mono fun _ hy => (hEI hy).1)]
  apply MeasureTheory.lintegral_congr_ae
  filter_upwards [ae_restrict_mem hE] with y hy
  rw [branchWord_deriv_abs d n y (hEI hy).1]
  simp

private theorem volume_branchWord_image_lower (d : ℕ → ℕ) (n : ℕ)
    (E : Set ℝ) (hE : MeasurableSet E) (hEI : E ⊆ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal ((((2 : ℝ) * (branchMatrix d n).D) ^ 2)⁻¹) * volume E ≤
      volume (branchWord d n '' E) := by
  rw [volume_branchWord_image d n E hE hEI]
  rw [← MeasureTheory.setLIntegral_const]
  apply MeasureTheory.lintegral_mono_ae
  filter_upwards [ae_restrict_mem hE] with y hy
  exact ENNReal.ofReal_le_ofReal (branchJacobian_lower d n y (hEI hy))

theorem branchWord_image_volume_lower (d : ℕ → ℕ) (n : ℕ)
    (E : Set ℝ) (hE : MeasurableSet E) (hEI : E ⊆ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal ((((2 : ℝ) * (branchMatrix d n).D) ^ 2)⁻¹) * volume E ≤
      volume (branchWord d n '' E) :=
  volume_branchWord_image_lower d n E hE hEI

private theorem gaussDensity_lower (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (Real.log 2 * 2)⁻¹ ≤ gaussDensityReal x := by
  dsimp [gaussDensityReal]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hleft : 0 < Real.log 2 * (1 + x) :=
    mul_pos hlog (by linarith [hx.1])
  have hright : 0 < Real.log 2 * 2 := mul_pos hlog (by norm_num)
  rw [inv_eq_one_div, inv_eq_one_div]
  apply one_div_le_one_div_of_le hleft
  nlinarith [hx.2, hlog]

theorem volume_subtype_image_zero_of_gaussMeasure_zero
    {s : Set GaussSpace} (hs : MeasurableSet s)
    (hzero : gaussMeasure s = 0) :
    volume (Subtype.val '' s) = 0 := by
  have hS : MeasurableSet (Subtype.val '' s) :=
    measurableSet_Icc.subtype_image hs
  rw [gaussMeasure_apply hs] at hzero
  let c : ENNReal := ENNReal.ofReal ((Real.log 2 * 2)⁻¹)
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hle : c * volume (Subtype.val '' s) ≤
      ∫⁻ x in Subtype.val '' s,
        ENNReal.ofReal (gaussDensityReal x) ∂volume := by
    calc
      c * volume (Subtype.val '' s) =
          ∫⁻ _ in Subtype.val '' s, c ∂volume := by
            rw [MeasureTheory.lintegral_const]
            simp
      _ ≤ ∫⁻ x in Subtype.val '' s,
          ENNReal.ofReal (gaussDensityReal x) ∂volume := by
        apply MeasureTheory.lintegral_mono_ae
        filter_upwards [ae_restrict_mem hS] with x hx
        rcases hx with ⟨z, hz, rfl⟩
        exact ENNReal.ofReal_le_ofReal (gaussDensity_lower z.1 z.2)
  have hmul : c * volume (Subtype.val '' s) = 0 := by
    exact le_antisymm (hle.trans_eq hzero) bot_le
  exact (mul_eq_zero.mp hmul).resolve_left hc

theorem gaussMeasure_zero_of_volume_subtype_image_zero
    {s : Set GaussSpace} (hs : MeasurableSet s)
    (hzero : volume (Subtype.val '' s) = 0) :
    gaussMeasure s = 0 := by
  rw [gaussMeasure_apply hs]
  have hres : volume.restrict (Subtype.val '' s) = 0 := by
    rw [Measure.restrict_eq_zero]
    exact hzero
  rw [hres]
  simp

theorem ae_gaussMeasure_irrational :
    ∀ᵐ z ∂gaussMeasure, Irrational z.1 := by
  let R : Set ℝ := Set.range (fun q : ℚ => (q : ℝ))
  have hR : MeasurableSet R := (Set.countable_range _).measurableSet
  let s : Set GaussSpace := Subtype.val ⁻¹' R
  have hs : MeasurableSet s := measurable_subtype_coe hR
  have hRzero : volume R = 0 := (Set.countable_range _).measure_zero volume
  have hSzero : volume (Subtype.val '' s) = 0 := by
    apply measure_mono_null
    · rintro x ⟨z, hz, rfl⟩
      change z.1 ∈ R at hz
      exact hz
    · exact hRzero
  have hμzero : gaussMeasure s = 0 :=
    gaussMeasure_zero_of_volume_subtype_image_zero hs hSzero
  rw [MeasureTheory.ae_iff]
  simpa [s, R, Irrational] using hμzero

theorem volume_Icc_inter_rational_zero :
    volume (Set.Icc (0 : ℝ) 1 ∩ Set.range (fun q : ℚ => (q : ℝ))) = 0 := by
  apply measure_mono_null
  · exact Set.inter_subset_right
  · exact (Set.countable_range _).measure_zero volume

theorem ae_volume_irrational : ∀ᵐ x ∂volume, Irrational x := by
  rw [MeasureTheory.ae_iff]
  simpa [Irrational] using
    (Set.countable_range (fun q : ℚ => (q : ℝ))).measure_zero volume

theorem ae_density_and_irrational (s : Set ℝ) (hs : MeasurableSet s) :
    ∀ᵐ x ∂volume,
      (Tendsto (fun r => volume (s ∩ Metric.closedBall x r) /
        volume (Metric.closedBall x r))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (s.indicator 1 x))) ∧ Irrational x := by
  exact (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hs).and
    ae_volume_irrational

theorem exists_irrational_density_zero_in_positive_set
    {s C : Set ℝ} (hs : MeasurableSet s) (hC : MeasurableSet C)
    (hCpos : 0 < volume C) (hCsub : C ⊆ sᶜ) :
    ∃ x : ℝ, x ∈ C ∧ Irrational x ∧
      Tendsto (fun r => volume (s ∩ Metric.closedBall x r) /
        volume (Metric.closedBall x r))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hne : volume.restrict C ≠ 0 := by
    intro hzero
    have hz : (volume.restrict C) C = 0 := by rw [hzero]; simp
    rw [Measure.restrict_apply hC] at hz
    simp only [Set.inter_self] at hz
    exact hCpos.ne' hz
  letI : (ae (volume.restrict C)).NeBot := MeasureTheory.ae_neBot.mpr hne
  have hgood := MeasureTheory.ae_restrict_of_ae (s := C)
    (ae_density_and_irrational s hs)
  have hmem := ae_restrict_mem (μ := volume) hC
  obtain ⟨x, hxgood, hxC⟩ := (hgood.and hmem).exists
  refine ⟨x, hxC, hxgood.2, ?_⟩
  have hxnot : x ∉ s := hCsub hxC
  simpa [Set.indicator, hxnot] using hxgood.1

theorem exists_positive_irrational_image_subset
    {s : Set GaussSpace} (hs : MeasurableSet s)
    (hμ : 0 < gaussMeasure s) :
    ∃ E : Set ℝ, MeasurableSet E ∧ 0 < volume E ∧
      E ⊆ Set.Ico (0 : ℝ) 1 ∧ E ⊆ Subtype.val '' s ∧
      ∀ y ∈ E, Irrational y := by
  let S : Set ℝ := Subtype.val '' s
  let R : Set ℝ := Set.range (fun q : ℚ => (q : ℝ))
  have hS : MeasurableSet S := measurableSet_Icc.subtype_image hs
  have hR : MeasurableSet R := (Set.countable_range _).measurableSet
  have hSpos : 0 < volume S := by
    by_contra h
    have hz : volume S = 0 := le_antisymm (not_lt.mp h) bot_le
    exact (ne_of_gt hμ) (gaussMeasure_zero_of_volume_subtype_image_zero hs hz)
  have hRzero : volume R = 0 := (Set.countable_range _).measure_zero volume
  let E : Set ℝ := S \ R
  have hEmeas : MeasurableSet E := hS.diff hR
  have hEvol : volume E = volume S := MeasureTheory.measure_diff_null hRzero
  have hEpos : 0 < volume E := by simpa [hEvol] using hSpos
  refine ⟨E, hEmeas, hEpos, ?_, ?_, ?_⟩
  · intro y hy
    change y ∈ S ∧ y ∉ R at hy
    rcases hy.1 with ⟨z, hz, rfl⟩
    constructor
    · exact z.2.1
    · exact lt_of_le_of_ne z.2.2 (by
        intro heq
        apply hy.2
        rw [heq]
        exact ⟨(1 : ℚ), by norm_num⟩)
  · intro y hy
    change y ∈ S ∧ y ∉ R at hy
    exact hy.1
  · intro y hy
    change y ∈ S ∧ y ∉ R at hy
    simpa [Irrational, R] using hy.2

theorem closedBall_subset_gaussSpace (x : ℝ) (_hx : x ∈ Set.Icc (0 : ℝ) 1)
    (r : ℝ) (hrx : r ≤ x) (hr1 : r ≤ 1 - x) :
    Metric.closedBall x r ⊆ Set.Icc (0 : ℝ) 1 := by
  rw [Real.closedBall_eq_Icc]
  intro y hy
  constructor <;> linarith [_hx.1, _hx.2, hy.1, hy.2]

private theorem branchWord_dist_le (d : ℕ → ℕ) (n : ℕ)
    (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    dist (branchWord d n x) (branchWord d n y) ≤
      (((branchMatrix d n).D : ℝ) ^ 2)⁻¹ := by
  rw [branchWord_eq_eval d n x hx.1, branchWord_eq_eval d n y hy.1]
  let M := branchMatrix d n
  have hD : 0 < (M.D : ℝ) := by
    exact_mod_cast branchMatrix_D_pos d n
  have hC0 : 0 ≤ (M.C : ℝ) := Nat.cast_nonneg _
  have hdx : 0 < (M.C : ℝ) * x + M.D := by
    nlinarith [mul_nonneg hC0 hx.1]
  have hdy : 0 < (M.C : ℝ) * y + M.D := by
    nlinarith [mul_nonneg hC0 hy.1]
  have hformula :
      M.eval x - M.eval y =
    M.detReal * (x - y) /
          (((M.C : ℝ) * x + M.D) * ((M.C : ℝ) * y + M.D)) := by
    dsimp [BranchMatrix.eval, BranchMatrix.detReal]
    have hdx' : x * (M.C : ℝ) + M.D ≠ 0 := by nlinarith
    have hdy' : y * (M.C : ℝ) + M.D ≠ 0 := by nlinarith
    field_simp [hdx.ne', hdy.ne', hdx', hdy']
    ring
  rw [Real.dist_eq, hformula, abs_div, abs_mul,
    branchMatrix_abs_detReal d n, one_mul, abs_mul,
    abs_of_pos hdx, abs_of_pos hdy]
  have habs : |x - y| ≤ 1 := by
    apply (abs_le).2
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hdxD : (M.D : ℝ) ≤ (M.C : ℝ) * x + M.D := by
    nlinarith [mul_nonneg hC0 hx.1]
  have hdyD : (M.D : ℝ) ≤ (M.C : ℝ) * y + M.D := by
    nlinarith [mul_nonneg hC0 hy.1]
  have hprod : (M.D : ℝ) ^ 2 ≤
      ((M.C : ℝ) * x + M.D) * ((M.C : ℝ) * y + M.D) := by
    have hmul := mul_le_mul hdxD hdyD hD.le (by positivity :
      0 ≤ (M.C : ℝ) * x + M.D)
    simpa [pow_two] using hmul
  have hmain : |x - y| /
      (((M.C : ℝ) * x + M.D) * ((M.C : ℝ) * y + M.D)) ≤
      ((M.D : ℝ) ^ 2)⁻¹ := by
    apply (div_le_iff₀ (mul_pos hdx hdy)).2
    calc
      |x - y| ≤ ((M.C : ℝ) * x + M.D) *
          ((M.C : ℝ) * y + M.D) / (M.D : ℝ) ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hD)).2
        calc
          |x - y| * (M.D : ℝ) ^ 2 ≤ 1 * (M.D : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right habs (sq_nonneg _)
          _ = (M.D : ℝ) ^ 2 := by ring
          _ ≤ ((M.C : ℝ) * x + M.D) * ((M.C : ℝ) * y + M.D) := hprod
      _ = ((M.D : ℝ) ^ 2)⁻¹ *
          (((M.C : ℝ) * x + M.D) * ((M.C : ℝ) * y + M.D)) := by
        rw [div_eq_mul_inv]
        ring
  exact hmain

theorem branchWord_distance_le (d : ℕ → ℕ) (n : ℕ)
    (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    dist (branchWord d n x) (branchWord d n y) ≤
      (((branchMatrix d n).D : ℝ) ^ 2)⁻¹ :=
  branchWord_dist_le d n x y hx hy

theorem branchWord_image_inter_closedBall_lower
    (d : ℕ → ℕ) (n : ℕ) (E S : Set ℝ)
    (hE : MeasurableSet E) (hEI : E ⊆ Set.Icc (0 : ℝ) 1)
    (himage : branchWord d n '' E ⊆ S)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal ((((2 : ℝ) * (branchMatrix d n).D) ^ 2)⁻¹) * volume E ≤
      volume (S ∩ Metric.closedBall (branchWord d n x)
        (((branchMatrix d n).D : ℝ) ^ 2)⁻¹) := by
  have himageBall : branchWord d n '' E ⊆
      Metric.closedBall (branchWord d n x)
        (((branchMatrix d n).D : ℝ) ^ 2)⁻¹ := by
    rintro z ⟨y, hy, rfl⟩
    change dist (branchWord d n y) (branchWord d n x) ≤
      (((branchMatrix d n).D : ℝ) ^ 2)⁻¹
    simpa [dist_comm] using branchWord_distance_le d n x y hx (hEI hy)
  calc
    ENNReal.ofReal ((((2 : ℝ) * (branchMatrix d n).D) ^ 2)⁻¹) * volume E ≤
        volume (branchWord d n '' E) :=
      branchWord_image_volume_lower d n E hE hEI
    _ ≤ volume (S ∩ Metric.closedBall (branchWord d n x)
        (((branchMatrix d n).D : ℝ) ^ 2)⁻¹) := by
      apply measure_mono
      intro z hz
      exact ⟨himage hz, himageBall hz⟩

theorem branch_density_ratio_lower
    (d : ℕ → ℕ) (n : ℕ) (E S : Set ℝ)
    (hE : MeasurableSet E) (hEI : E ⊆ Set.Icc (0 : ℝ) 1)
    (himage : branchWord d n '' E ⊆ S)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (ENNReal.ofReal ((((2 : ℝ) * (branchMatrix d n).D) ^ 2)⁻¹) * volume E) /
        volume (Metric.closedBall (branchWord d n x)
          (((branchMatrix d n).D : ℝ) ^ 2)⁻¹) ≤
      volume (S ∩ Metric.closedBall (branchWord d n x)
        (((branchMatrix d n).D : ℝ) ^ 2)⁻¹) /
        volume (Metric.closedBall (branchWord d n x)
          (((branchMatrix d n).D : ℝ) ^ 2)⁻¹) := by
  exact ENNReal.div_le_div_right
    (branchWord_image_inter_closedBall_lower d n E S hE hEI himage x hx) _

theorem branchJacobian_ball_ratio (d : ℕ → ℕ) (n : ℕ) :
    ENNReal.ofReal ((((2 : ℝ) * (branchMatrix d n).D) ^ 2)⁻¹) /
        ENNReal.ofReal (2 * (((branchMatrix d n).D : ℝ) ^ 2)⁻¹) =
      ENNReal.ofReal ((1 : ℝ) / 8) := by
  have hD : (0 : ℝ) < (branchMatrix d n).D := by
    exact_mod_cast branchMatrix_D_pos d n
  have hden : (0 : ℝ) < 2 * (((branchMatrix d n).D : ℝ) ^ 2)⁻¹ := by
    positivity
  rw [← ENNReal.ofReal_div_of_pos hden]
  congr 1
  field_simp
  ring

theorem branch_density_ratio_uniform_lower
    (d : ℕ → ℕ) (n : ℕ) (E S : Set ℝ)
    (hE : MeasurableSet E) (hEI : E ⊆ Set.Icc (0 : ℝ) 1)
    (himage : branchWord d n '' E ⊆ S)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal ((1 : ℝ) / 8) * volume E ≤
      volume (S ∩ Metric.closedBall (branchWord d n x)
        (((branchMatrix d n).D : ℝ) ^ 2)⁻¹) /
        volume (Metric.closedBall (branchWord d n x)
          (((branchMatrix d n).D : ℝ) ^ 2)⁻¹) := by
  have hratio := branch_density_ratio_lower d n E S hE hEI himage x hx
  rw [branchBall_volume]
  rw [branchBall_volume] at hratio
  calc
    ENNReal.ofReal ((1 : ℝ) / 8) * volume E =
        (ENNReal.ofReal ((((2 : ℝ) * (branchMatrix d n).D) ^ 2)⁻¹) /
          ENNReal.ofReal (2 * (((branchMatrix d n).D : ℝ) ^ 2)⁻¹)) * volume E := by
            rw [branchJacobian_ball_ratio]
    _ = ENNReal.ofReal ((((2 : ℝ) * (branchMatrix d n).D) ^ 2)⁻¹) * volume E /
          ENNReal.ofReal (2 * (((branchMatrix d n).D : ℝ) ^ 2)⁻¹) := by
            simp [div_eq_mul_inv, mul_assoc, mul_comm]
    _ ≤ _ := hratio

theorem not_tendsto_zero_of_eventually_ge
    {f : ℕ → ENNReal} {c : ENNReal} (hc : 0 < c)
    (hlim : Tendsto f atTop (nhds 0))
    (hbound : ∀ᶠ n : ℕ in atTop, c ≤ f n) : False := by
  have hlt : ∀ᶠ n : ℕ in atTop, f n < c :=
    hlim.eventually (Iio_mem_nhds hc)
  rcases (hbound.and hlt).exists with ⟨n, hn⟩
  exact (not_lt_of_ge hn.1) hn.2

theorem tendsto_along_positive_radius
    {F : ℝ → ENNReal} {r : ℕ → ℝ}
    (hF : Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hr : Tendsto r atTop (nhds 0))
    (hpos : ∀ᶠ n : ℕ in atTop, r n ∈ Set.Ioi (0 : ℝ)) :
    Tendsto (F ∘ r) atTop (nhds 0) := by
  apply hF.comp
  apply (tendsto_nhdsWithin_iff).2
  exact ⟨hr, hpos⟩

theorem contradiction_of_branch_density_lower
    (d : ℕ → ℕ) (E S : Set ℝ) (hE : MeasurableSet E)
    (hEI : E ⊆ Set.Icc (0 : ℝ) 1) (hvol : 0 < volume E)
    (x : ℝ) (y : ℕ → ℝ)
    (hy : ∀ n, y n ∈ Set.Icc (0 : ℝ) 1)
    (hcenter : ∀ n, branchWord d n (y n) = x)
    (himage : ∀ n, branchWord d n '' E ⊆ S)
    (hlim : Tendsto (fun n =>
      volume (S ∩ Metric.closedBall x (((branchMatrix d n).D : ℝ) ^ 2)⁻¹) /
        volume (Metric.closedBall x (((branchMatrix d n).D : ℝ) ^ 2)⁻¹))
      atTop (nhds 0)) : False := by
  let c : ENNReal := ENNReal.ofReal ((1 : ℝ) / 8) * volume E
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hbound : ∀ᶠ n : ℕ in atTop, c ≤
      volume (S ∩ Metric.closedBall x (((branchMatrix d n).D : ℝ) ^ 2)⁻¹) /
        volume (Metric.closedBall x (((branchMatrix d n).D : ℝ) ^ 2)⁻¹) := by
    filter_upwards [] with n
    have h := branch_density_ratio_uniform_lower d n E S hE hEI
      (himage n) (y n) (hy n)
    simpa [c, hcenter n] using h
  exact not_tendsto_zero_of_eventually_ge hc hlim hbound

theorem density_ratio_along_branch_radius
    (d : ℕ → ℕ) (S : Set ℝ) (x : ℝ)
    (hlim : Tendsto (fun r =>
      volume (S ∩ Metric.closedBall x r) /
        volume (Metric.closedBall x r))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Tendsto (fun n =>
      volume (S ∩ Metric.closedBall x (((branchMatrix d n).D : ℝ) ^ 2)⁻¹) /
        volume (Metric.closedBall x (((branchMatrix d n).D : ℝ) ^ 2)⁻¹))
      atTop (nhds 0) := by
  exact tendsto_along_positive_radius hlim
    (branchRadius_tendsto_zero d)
    (Filter.Eventually.of_forall (fun n => by
      exact branchRadius_pos d n))

theorem invariant_positive_branch_data
    {S : Set GaussSpace} (hS : MeasurableSet S)
    (hInv : gaussMap ⁻¹' S = S) (hμ : 0 < gaussMeasure S)
    (d : ℕ → ℕ) :
    ∃ E : Set ℝ, MeasurableSet E ∧ 0 < volume E ∧
      E ⊆ Set.Ico (0 : ℝ) 1 ∧ E ⊆ Subtype.val '' S ∧
      (∀ y ∈ E, Irrational y) ∧
      (∀ n, branchWord d n '' E ⊆ Subtype.val '' S) := by
  obtain ⟨E, hE, hvol, hEI, hES, hIrr⟩ :=
    exists_positive_irrational_image_subset hS hμ
  refine ⟨E, hE, hvol, hEI, hES, hIrr, ?_⟩
  intro n
  exact branchWord_image_subset_invariant hInv d n E hEI hES hIrr

private def gaussOrbit (x : ℝ) (n : ℕ) : ℝ := (gaussMapReal^[n]) x

private theorem gaussOrbit_mem (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    gaussOrbit x n ∈ Set.Icc (0 : ℝ) 1 := by
  induction n with
  | zero => simpa [gaussOrbit] using hx
  | succ n ih =>
      simpa [gaussOrbit, Function.iterate_succ_apply'] using
        gaussMapReal_mem_gaussSpace (gaussOrbit x n)

private theorem gaussOrbit_irrational (x : ℝ) (hx : Irrational x) (n : ℕ) :
    Irrational (gaussOrbit x n) := by
  induction n with
  | zero => simpa [gaussOrbit] using hx
  | succ n ih =>
      rw [gaussOrbit, Function.iterate_succ_apply']
      exact (ih.inv).sub_intCast _

private theorem gaussOrbit_pos_lt_one (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hirr : Irrational x) (n : ℕ) : gaussOrbit x n ∈ Set.Ioo (0 : ℝ) 1 := by
  have h := gaussOrbit_mem x hx n
  have hi := gaussOrbit_irrational x hirr n
  exact ⟨lt_of_le_of_ne h.1 (by intro hzero; exact hi ⟨0, by simp [hzero]⟩),
    lt_of_le_of_ne h.2 (by intro hone; exact hi ⟨1, by simp [hone]⟩)⟩

private noncomputable def chosenDigit (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hirr : Irrational x) (n : ℕ) : ℕ :=
  (Classical.choose (exists_gaussBranch_eq (gaussOrbit x n)
    ⟨(gaussOrbit_pos_lt_one x hx hirr n).1,
      (gaussOrbit_pos_lt_one x hx hirr n).2.le⟩))

private theorem chosenDigit_spec (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hirr : Irrational x) (n : ℕ) :
    ∃ y : ℝ, y ∈ Set.Ico (0 : ℝ) 1 ∧
      gaussBranch (chosenDigit x hx hirr n) y = gaussOrbit x n ∧
      gaussMapReal (gaussOrbit x n) = y :=
  Classical.choose_spec (exists_gaussBranch_eq (gaussOrbit x n)
    ⟨(gaussOrbit_pos_lt_one x hx hirr n).1,
      (gaussOrbit_pos_lt_one x hx hirr n).2.le⟩)

private noncomputable def chosenTail (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hirr : Irrational x) (n : ℕ) : ℝ :=
  Classical.choose (chosenDigit_spec x hx hirr n)

private theorem chosenTail_spec (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hirr : Irrational x) (n : ℕ) :
    chosenTail x hx hirr n ∈ Set.Ico (0 : ℝ) 1 ∧
      gaussBranch (chosenDigit x hx hirr n) (chosenTail x hx hirr n) =
        gaussOrbit x n ∧
      gaussMapReal (gaussOrbit x n) = chosenTail x hx hirr n :=
  Classical.choose_spec (chosenDigit_spec x hx hirr n)

private theorem branchWord_chosenOrbit (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hirr : Irrational x) (n : ℕ) :
    branchWord (chosenDigit x hx hirr) n (gaussOrbit x n) = x := by
  induction n with
  | zero => simp [branchWord, gaussOrbit]
  | succ n ih =>
      rw [branchWord]
      change branchWord (chosenDigit x hx hirr) n
        (gaussBranch (chosenDigit x hx hirr n) (gaussOrbit x (n + 1))) = x
      have htail :
          gaussBranch (chosenDigit x hx hirr n) (gaussOrbit x (n + 1)) =
            gaussOrbit x n := by
        have ht : gaussOrbit x (n + 1) = chosenTail x hx hirr n := by
          simpa [gaussOrbit, Function.iterate_succ_apply'] using
            (chosenTail_spec x hx hirr n |>.2.2)
        rw [ht]
        exact chosenTail_spec x hx hirr n |>.2.1
      rw [htail]
      exact ih

theorem chosenBranchWord_hits_orbit (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hirr : Irrational x) (n : ℕ) :
    branchWord (chosenDigit x hx hirr) n (gaussOrbit x n) = x :=
  branchWord_chosenOrbit x hx hirr n

theorem invariant_density_point_contradiction
    {S : Set GaussSpace} (hS : MeasurableSet S)
    (hInv : gaussMap ⁻¹' S = S) (hμ : 0 < gaussMeasure S)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hirr : Irrational x)
    (hlim : Tendsto (fun n =>
      volume (Subtype.val '' S ∩ Metric.closedBall x
          (((branchMatrix (chosenDigit x hx hirr) n).D : ℝ) ^ 2)⁻¹) /
        volume (Metric.closedBall x
          (((branchMatrix (chosenDigit x hx hirr) n).D : ℝ) ^ 2)⁻¹))
      atTop (nhds 0)) : False := by
  let d : ℕ → ℕ := chosenDigit x hx hirr
  obtain ⟨E, hE, hvol, hEI, hES, hIrr, himage⟩ :=
    invariant_positive_branch_data hS hInv hμ d
  apply contradiction_of_branch_density_lower d E (Subtype.val '' S)
    hE (fun y hy => ⟨(hEI hy).1, (hEI hy).2.le⟩) hvol x
      (fun n => gaussOrbit x n)
  · intro n
    exact gaussOrbit_mem x hx n
  · intro n
    simpa [d] using chosenBranchWord_hits_orbit x hx hirr n
  · intro n
    exact himage n
  · simpa [d] using hlim

theorem exact_invariant_gaussMeasure_zero_or_one
    {S : Set GaussSpace} (hS : MeasurableSet S)
    (hInv : gaussMap ⁻¹' S = S) :
    gaussMeasure S = 0 ∨ gaussMeasure S = 1 := by
  by_cases hzero : gaussMeasure S = 0
  · exact Or.inl hzero
  right
  by_contra hone
  have hpos : 0 < gaussMeasure S := pos_iff_ne_zero.mpr hzero
  have hle : gaussMeasure S ≤ 1 := by
    rw [← gaussMeasure_isProbability.measure_univ]
    exact MeasureTheory.measure_mono (Set.subset_univ S)
  have hlt : gaussMeasure S < 1 :=
    lt_of_le_of_ne hle hone
  have htop : gaussMeasure S ≠ ⊤ := by
    intro ht
    rw [ht] at hlt
    exact (not_lt_of_ge le_top) hlt
  have hcomp : 0 < gaussMeasure Sᶜ := by
    rw [MeasureTheory.measure_compl hS htop,
      gaussMeasure_isProbability.measure_univ]
    exact tsub_pos_iff_lt.mpr hlt
  obtain ⟨E, hE, hEpos, hEI, hESc, hEirr⟩ :=
    exists_positive_irrational_image_subset hS.compl hcomp
  let SR : Set ℝ := Subtype.val '' S
  have hSR : MeasurableSet SR := measurableSet_Icc.subtype_image hS
  have hEsub : E ⊆ SRᶜ := by
    intro y hyE hyS
    obtain ⟨z, hzC, rfl⟩ := hESc hyE
    obtain ⟨w, hwS, hw⟩ := hyS
    have hzw : z = w := Subtype.ext hw.symm
    subst w
    exact hzC hwS
  obtain ⟨x, hxE, hirr, hlim⟩ :=
    exists_irrational_density_zero_in_positive_set hSR hE hEpos hEsub
  have hx : x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(hEI hxE).1, (hEI hxE).2.le⟩
  have hseq := density_ratio_along_branch_radius
    (chosenDigit x hx hirr) SR x hlim
  exact invariant_density_point_contradiction hS hInv hpos x hx hirr hseq

theorem gaussSystem_isErgodic :
    IsErgodicGaussSystem { μ := gaussMeasure, T := gaussMap } := by
  refine ⟨⟨rfl, rfl, gaussMeasure_isProbability, gaussMap_measurePreserving⟩, ?_⟩
  intro A hA hnull
  let B := gaussInvariantRepresentative A
  have hB : MeasurableSet B := gaussInvariantRepresentative_measurable hA
  have hBinv : gaussMap ⁻¹' B = B := gaussInvariantRepresentative_invariant A
  have hBAE : B =ᶠ[ae gaussMeasure] A :=
    gaussInvariantRepresentative_ae_eq hnull
  have hmeasure : gaussMeasure B = gaussMeasure A :=
    MeasureTheory.measure_congr hBAE
  rcases exact_invariant_gaussMeasure_zero_or_one hB hBinv with hzero | hone
  · exact Or.inl (hmeasure ▸ hzero)
  · exact Or.inr (hmeasure ▸ hone)

theorem gauss_ergodicAverage_ae_tendsto
    (f : GaussSpace → ℂ) (hf : MeasureTheory.MemLp f 1 gaussMeasure) :
    ∀ᵐ x ∂gaussMeasure,
      Tendsto (fun n => Chapter02.ergodicAverage gaussSystem f n x) atTop
        (nhds (∫ y, f y ∂gaussMeasure)) := by
  exact Chapter02.ErgodicBirkhoffBridge.ergodicTimeAverage_tendsto_integral
    gaussSystem ((gaussSystem_ergodic_iff).mp gaussSystem_isErgodic) f hf

end Chapter03
