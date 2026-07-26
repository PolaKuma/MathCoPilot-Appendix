import Chapter02.Spectral.DenseMaximalVectors

open Classical Filter Set

noncomputable section

namespace Chapter02.OrderedSpectralDecomposition

universe u

theorem inter_reducing (D : HilbertOperatorData.{u})
    (K L : Submodule ℂ D.H)
    (hK : IsClosedReducingSubspace D (K : Set D.H))
    (hL : IsClosedReducingSubspace D (L : Set D.H)) :
    IsClosedReducingSubspace D ((K ⊓ L : Submodule ℂ D.H) : Set D.H) := by
  refine ⟨⟨K.zero_mem, L.zero_mem⟩, ?_, ?_, ?_⟩
  · intro x hx y hy a b
    exact ⟨K.add_mem (K.smul_mem a hx.1) (K.smul_mem b hy.1),
      L.add_mem (L.smul_mem a hx.2) (L.smul_mem b hy.2)⟩
  · intro s hs x hlim
    exact ⟨hK.2.2.1 s (fun n ↦ (hs n).1) x hlim,
      hL.2.2.1 s (fun n ↦ (hs n).2) x hlim⟩
  · intro x
    constructor
    · intro hx
      exact ⟨(hK.2.2.2 x).mp hx.1, (hL.2.2.2 x).mp hx.2⟩
    · intro hx
      exact ⟨(hK.2.2.2 x).mpr hx.1, (hL.2.2.2 x).mpr hx.2⟩

theorem isClosed_of_reducing (D : HilbertOperatorData.{u})
    (S : Submodule ℂ D.H)
    (hS : IsClosedReducingSubspace D (S : Set D.H)) :
    IsClosed (S : Set D.H) := by
  rw [← isSeqClosed_iff_isClosed]
  intro s x hs hlim
  exact hS.2.2.1 s hs x hlim

noncomputable def reducingProjection (D : HilbertOperatorData.{u})
    (S : Submodule ℂ D.H)
    (hS : IsClosedReducingSubspace D (S : Set D.H)) (y : D.H) : D.H := by
  letI : CompleteSpace S := (isClosed_of_reducing D S hS).completeSpace_coe
  letI : S.HasOrthogonalProjection := inferInstance
  exact S.starProjection y

theorem reducingProjection_mem (D : HilbertOperatorData.{u})
    (S : Submodule ℂ D.H)
    (hS : IsClosedReducingSubspace D (S : Set D.H)) (y : D.H) :
    reducingProjection D S hS y ∈ S := by
  letI : CompleteSpace S := (isClosed_of_reducing D S hS).completeSpace_coe
  letI : S.HasOrthogonalProjection := inferInstance
  exact S.starProjection_apply_mem y

theorem sub_reducingProjection_mem_orthogonal (D : HilbertOperatorData.{u})
    (S : Submodule ℂ D.H)
    (hS : IsClosedReducingSubspace D (S : Set D.H)) (y : D.H) :
    y - reducingProjection D S hS y ∈ Sᗮ := by
  letI : CompleteSpace S := (isClosed_of_reducing D S hS).completeSpace_coe
  letI : S.HasOrthogonalProjection := inferInstance
  exact Submodule.sub_starProjection_mem_orthogonal y

def residualSubmodule (D : HilbertOperatorData.{u})
    (S : Submodule ℂ D.H) (x : D.H) : Submodule ℂ D.H :=
  S ⊓ (SpectralDecomposition.cyclicSubmodule D x)ᗮ

theorem residualSubmodule_reducing (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (S : Submodule ℂ D.H) (hS : IsClosedReducingSubspace D (S : Set D.H))
    (x : D.H) :
    IsClosedReducingSubspace D (residualSubmodule D S x : Set D.H) := by
  exact inter_reducing D S (SpectralDecomposition.cyclicSubmodule D x)ᗮ hS
    (SpectralRelations.orthogonal_reducing D hD _
      (SpectralDecomposition.cyclicSubmodule_reducing D x))

structure ResidualState (D : HilbertOperatorData.{u}) where
  space : Submodule ℂ D.H
  reducing : IsClosedReducingSubspace D (space : Set D.H)

def initialState (D : HilbertOperatorData.{u}) : ResidualState D where
  space := ⊤
  reducing := by
    refine ⟨by simp, ?_, ?_, by simp⟩
    · simp
    · simp

def targetIndex (n : ℕ) : ℕ := (Nat.unpair n).1

def targetTolerance (n : ℕ) : ℝ := 1 / ((Nat.unpair n).2 + 1 : ℕ)

theorem targetTolerance_pos (n : ℕ) : 0 < targetTolerance n := by
  unfold targetTolerance
  positivity

noncomputable def selectedVector (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) (n : ℕ) (A : ResidualState D) : D.H :=
  Classical.choose (DenseMaximalVectors.exists_near_maximalVector_on_submodule
    D hsep hD A.space A.reducing
    (reducingProjection D A.space A.reducing (d (targetIndex n)))
    (reducingProjection_mem D A.space A.reducing _) (targetTolerance_pos n))

theorem selectedVector_spec (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) (n : ℕ) (A : ResidualState D) :
    selectedVector D hsep hD d n A ∈ A.space ∧
      ‖reducingProjection D A.space A.reducing (d (targetIndex n)) -
        selectedVector D hsep hD d n A‖ < targetTolerance n ∧
      ∀ z : D.H, z ∈ A.space →
        SpectralMeasureDominatesVector D (selectedVector D hsep hD d n A) z :=
  Classical.choose_spec (DenseMaximalVectors.exists_near_maximalVector_on_submodule
    D hsep hD A.space A.reducing
    (reducingProjection D A.space A.reducing (d (targetIndex n)))
    (reducingProjection_mem D A.space A.reducing _) (targetTolerance_pos n))

noncomputable def nextState (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) (n : ℕ) (A : ResidualState D) : ResidualState D where
  space := residualSubmodule D A.space (selectedVector D hsep hD d n A)
  reducing := residualSubmodule_reducing D hD A.space A.reducing _

noncomputable def stateSequence (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) : ℕ → ResidualState D
  | 0 => initialState D
  | n + 1 => nextState D hsep hD d n (stateSequence D hsep hD d n)

noncomputable def orderedVector (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) (n : ℕ) : D.H :=
  selectedVector D hsep hD d n (stateSequence D hsep hD d n)

theorem stateSequence_succ_space (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) (n : ℕ) :
    (stateSequence D hsep hD d (n + 1)).space =
      residualSubmodule D (stateSequence D hsep hD d n).space
        (orderedVector D hsep hD d n) := by
  rfl

theorem orderedVector_mem_state (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) (n : ℕ) :
    orderedVector D hsep hD d n ∈ (stateSequence D hsep hD d n).space := by
  exact (selectedVector_spec D hsep hD d n _).1

theorem orderedVector_close_projection (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) (n : ℕ) :
    ‖reducingProjection D (stateSequence D hsep hD d n).space
        (stateSequence D hsep hD d n).reducing (d (targetIndex n)) -
      orderedVector D hsep hD d n‖ < targetTolerance n := by
  exact (selectedVector_spec D hsep hD d n _).2.1

theorem orderedVector_dominates_state (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) (n : ℕ) (z : D.H)
    (hz : z ∈ (stateSequence D hsep hD d n).space) :
    SpectralMeasureDominatesVector D (orderedVector D hsep hD d n) z := by
  exact (selectedVector_spec D hsep hD d n _).2.2 z hz

theorem stateSequence_succ_le (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) (n : ℕ) :
    (stateSequence D hsep hD d (n + 1)).space ≤
      (stateSequence D hsep hD d n).space := by
  rw [stateSequence_succ_space]
  exact inf_le_left

theorem stateSequence_succ_le_cyclicOrthogonal (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) (n : ℕ) :
    (stateSequence D hsep hD d (n + 1)).space ≤
      (SpectralDecomposition.cyclicSubmodule D
        (orderedVector D hsep hD d n))ᗮ := by
  rw [stateSequence_succ_space]
  exact inf_le_right

theorem stateSequence_antitone (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) : Antitone (fun n ↦ (stateSequence D hsep hD d n).space) := by
  exact antitone_nat_of_succ_le (stateSequence_succ_le D hsep hD d)

theorem orderedVector_succ_mem_state (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) (n : ℕ) :
    orderedVector D hsep hD d (n + 1) ∈
      (stateSequence D hsep hD d n).space :=
  stateSequence_succ_le D hsep hD d n
    (orderedVector_mem_state D hsep hD d (n + 1))

theorem orderedVector_orthogonal_of_lt (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) {i j : ℕ} (hijlt : i < j) :
    OrthogonalCyclicSubspaces D (orderedVector D hsep hD d i)
      (orderedVector D hsep hD d j) := by
  have hjstate : orderedVector D hsep hD d j ∈
      (stateSequence D hsep hD d (i + 1)).space :=
    (stateSequence_antitone D hsep hD d (Nat.succ_le_iff.mpr hijlt))
      (orderedVector_mem_state D hsep hD d j)
  have hjorth : orderedVector D hsep hD d j ∈
      (SpectralDecomposition.cyclicSubmodule D
        (orderedVector D hsep hD d i))ᗮ :=
    stateSequence_succ_le_cyclicOrthogonal D hsep hD d i hjstate
  exact SpectralRelations.cyclic_subspaces_orthogonal_of_mem D
    (SpectralDecomposition.cyclicSubmodule D (orderedVector D hsep hD d i))
    _ _ (SpectralDecomposition.cyclicSubmodule_reducing D _)
    (SpectralRelations.orthogonal_reducing D hD _
      (SpectralDecomposition.cyclicSubmodule_reducing D _))
    (SpectralDecomposition.generator_mem_cyclicSubmodule D _) hjorth

theorem orderedVector_pairwise_orthogonal (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) {i j : ℕ} (hij : i ≠ j) :
    OrthogonalCyclicSubspaces D (orderedVector D hsep hD d i)
      (orderedVector D hsep hD d j) := by
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact orderedVector_orthogonal_of_lt D hsep hD d hijlt
  · exact OrthogonalCyclicDecomposition.orthogonalCyclicSubspaces_symm D
      (orderedVector_orthogonal_of_lt D hsep hD d hjilt)

theorem orderedVector_dominates_succ (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) (n : ℕ) :
    SpectralMeasureDominatesVector D (orderedVector D hsep hD d n)
      (orderedVector D hsep hD d (n + 1)) :=
  orderedVector_dominates_state D hsep hD d n _
    (orderedVector_succ_mem_state D hsep hD d n)

theorem commonOrthogonal_mem_state (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) (r : D.H)
    (hr : ∀ n, r ∈ (SpectralDecomposition.cyclicSubmodule D
      (orderedVector D hsep hD d n))ᗮ) :
    ∀ n, r ∈ (stateSequence D hsep hD d n).space := by
  intro n
  induction n with
  | zero => simp [stateSequence, initialState]
  | succ n ih =>
      rw [stateSequence_succ_space]
      exact ⟨ih, hr n⟩

theorem inner_denseTarget_eq_zero_of_commonOrthogonal
    (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) (r : D.H)
    (hr : ∀ n, r ∈ (SpectralDecomposition.cyclicSubmodule D
      (orderedVector D hsep hD d n))ᗮ) :
    ∀ k, @inner ℂ D.H _ r (d k) = 0 := by
  intro k
  by_contra hne
  have hr0 : r ≠ 0 := by
    intro hrz
    subst r
    simp at hne
  have hquot : 0 < ‖@inner ℂ D.H _ r (d k)‖ / ‖r‖ :=
    div_pos (norm_pos_iff.mpr hne) (norm_pos_iff.mpr hr0)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hquot
  let n := Nat.pair k m
  let A := stateSequence D hsep hD d n
  let p := reducingProjection D A.space A.reducing (d k)
  let x := orderedVector D hsep hD d n
  have hnindex : targetIndex n = k := by
    simp [n, targetIndex, Nat.unpair_pair]
  have hntol : targetTolerance n = 1 / ((m : ℝ) + 1) := by
    simp [n, targetTolerance, Nat.unpair_pair]
  have hrA : r ∈ A.space := commonOrthogonal_mem_state D hsep hD d r hr n
  have hres : d k - p ∈ A.spaceᗮ := by
    exact sub_reducingProjection_mem_orthogonal D A.space A.reducing (d k)
  have hrdp0 : @inner ℂ D.H _ r (d k - p) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hrA hres
  have hrdp : @inner ℂ D.H _ r (d k) = @inner ℂ D.H _ r p := by
    rw [inner_sub_right] at hrdp0
    exact sub_eq_zero.mp hrdp0
  have hxr0 : @inner ℂ D.H _ x r = 0 :=
    ((Submodule.mem_orthogonal _ _).mp (hr n)) x
      (SpectralDecomposition.generator_mem_cyclicSubmodule D x)
  have hrx0 : @inner ℂ D.H _ r x = 0 := by
    rw [← inner_conj_symm, hxr0, map_zero]
  have heq : @inner ℂ D.H _ r (d k) = @inner ℂ D.H _ r (p - x) := by
    rw [hrdp, inner_sub_right, hrx0, sub_zero]
  have hclose : ‖p - x‖ < 1 / ((m : ℝ) + 1) := by
    simpa [p, x, A, hnindex, hntol] using
      (orderedVector_close_projection D hsep hD d n)
  have hbound : ‖@inner ℂ D.H _ r (d k)‖ <
      ‖r‖ * (1 / ((m : ℝ) + 1)) := by
    rw [heq]
    exact lt_of_le_of_lt (norm_inner_le_norm r (p - x))
      (mul_lt_mul_of_pos_left hclose (norm_pos_iff.mpr hr0))
  have hmul : ‖r‖ * (1 / ((m : ℝ) + 1)) <
      ‖@inner ℂ D.H _ r (d k)‖ := by
    calc
      ‖r‖ * (1 / ((m : ℝ) + 1)) <
          ‖r‖ * (‖@inner ℂ D.H _ r (d k)‖ / ‖r‖) :=
        mul_lt_mul_of_pos_left hm (norm_pos_iff.mpr hr0)
      _ = ‖@inner ℂ D.H _ r (d k)‖ := by
        field_simp
  exact (not_lt_of_ge hbound.le) hmul

theorem eq_zero_of_dense_inner_zero (D : HilbertOperatorData.{u})
    (d : ℕ → D.H) (hdense : DenseRange d) (r : D.H)
    (hr : ∀ k, @inner ℂ D.H _ r (d k) = 0) : r = 0 := by
  by_contra hr0
  have hself : @inner ℂ D.H _ r r ≠ 0 := by
    exact fun h ↦ hr0 (inner_self_eq_zero.mp h)
  have hε : 0 < ‖@inner ℂ D.H _ r r‖ / ‖r‖ :=
    div_pos (norm_pos_iff.mpr hself) (norm_pos_iff.mpr hr0)
  obtain ⟨k, hk⟩ := hdense.exists_dist_lt r hε
  have heq : @inner ℂ D.H _ r r = @inner ℂ D.H _ r (r - d k) := by
    rw [inner_sub_right, hr k, sub_zero]
  have hbound : ‖@inner ℂ D.H _ r r‖ <
      ‖r‖ * (‖@inner ℂ D.H _ r r‖ / ‖r‖) := by
    calc
      ‖@inner ℂ D.H _ r r‖ = ‖@inner ℂ D.H _ r (r - d k)‖ :=
        congrArg norm heq
      _ ≤ ‖r‖ * ‖r - d k‖ := norm_inner_le_norm r (r - d k)
      _ < ‖r‖ * (‖@inner ℂ D.H _ r r‖ / ‖r‖) := by
        rw [← dist_eq_norm]
        exact mul_lt_mul_of_pos_left hk (norm_pos_iff.mpr hr0)
  have hcancel : ‖r‖ * (‖@inner ℂ D.H _ r r‖ / ‖r‖) =
      ‖@inner ℂ D.H _ r r‖ := by
    field_simp
  rw [hcancel] at hbound
  exact (lt_irrefl _ hbound)

theorem orderedVector_complete (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) (hdense : DenseRange d) (r : D.H)
    (hr : ∀ n, r ∈ (SpectralDecomposition.cyclicSubmodule D
      (orderedVector D hsep hD d n))ᗮ) : r = 0 :=
  eq_zero_of_dense_inner_zero D d hdense r
    (inner_denseTarget_eq_zero_of_commonOrthogonal D hsep hD d r hr)

theorem orderedVector_isOrderedSpectralDecomposition
    (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (d : ℕ → D.H) (hdense : DenseRange d) :
    IsOrderedSpectralDecomposition D (orderedVector D hsep hD d) := by
  refine ⟨SpectralDecomposition.orthogonalCyclicDecomposition_of_complete D _
    (fun i j hij ↦ orderedVector_pairwise_orthogonal D hsep hD d hij)
    (orderedVector_complete D hsep hD d hdense), ?_⟩
  exact orderedVector_dominates_succ D hsep hD d

theorem exists_orderedSpectralDecomposition (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D) :
    ∃ x : ℕ → D.H, IsOrderedSpectralDecomposition D x := by
  letI : TopologicalSpace.SeparableSpace D.H := hsep
  obtain ⟨d, hdense⟩ := TopologicalSpace.exists_dense_seq D.H
  exact ⟨orderedVector D hsep hD d,
    orderedVector_isOrderedSpectralDecomposition D hsep hD d hdense⟩

theorem firstVector_dominates_component (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H)
    (hord : ∀ n, SpectralMeasureDominatesVector D (x n) (x (n + 1))) :
    ∀ n, SpectralMeasureDominatesVector D (x 0) (x n) := by
  intro n
  induction n with
  | zero => exact DenseMaximalVectors.spectralMeasureDominatesVector_refl D hD _
  | succ n ih =>
      exact DenseMaximalVectors.spectralMeasureDominatesVector_trans D hD ih (hord n)

theorem component_dominates_later (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H)
    (hord : ∀ n, SpectralMeasureDominatesVector D (x n) (x (n + 1)))
    {i j : ℕ} (hij : i ≤ j) :
    SpectralMeasureDominatesVector D (x i) (x j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction k with
  | zero =>
      simpa using DenseMaximalVectors.spectralMeasureDominatesVector_refl D hD (x i)
  | succ k ih =>
      exact DenseMaximalVectors.spectralMeasureDominatesVector_trans D hD ih
        (by simpa [Nat.add_assoc] using hord (i + k))

theorem firstVector_dominates_every_vector (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H)
    (hord : IsOrderedSpectralDecomposition D x) (y : D.H) :
    SpectralMeasureDominatesVector D (x 0) y := by
  intro μbase μy hμbase hμy
  choose μ hμ hμprob using fun i ↦ SpectralMeasure.spectralMeasure D hD (x i)
  let z : ℕ → D.H := SpectralDecomposition.cyclicProjectionFamily D x y
  choose ν hν hac using fun i ↦
    MaximalSpectralType.exists_projection_spectralMeasure_ac D hD x μ hμ y i
  have hzsum : HasSum z y := by
    have hsum := SpectralDecomposition.cyclicProjectionFamily_summable
      D x hord.1.1 y
    exact (SpectralDecomposition.tsum_cyclicProjectionFamily_eq D x hord.1 y) ▸
      hsum.hasSum
  have hzorth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (z i) (z j) :=
    MaximalSpectralType.cyclicProjectionFamily_pairwise_cyclic_orthogonal
      D x hord.1.1 y
  have hzsq : Summable (fun i ↦ ‖z i‖ ^ 2) :=
    SpectralDecomposition.cyclicProjectionFamily_norm_sq_summable D x hord.1.1 y
  let νsum := MaximalSpectralType.spectralSumMeasure D z ν hν hzsq
  have hνsum : HasSpectralMeasure D y νsum :=
    MaximalSpectralType.spectralSumMeasure_isSpectral
      D hD z y hzsum hzorth ν hν hzsq
  have heqy : μy = νsum := SpectralMeasure.eq_of_nat_moments _ _
    (fun n ↦ (hμy n).trans (hνsum n).symm)
  subst μy
  refine MeasureTheory.Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  change (MeasureTheory.Measure.sum (fun i ↦ (ν i).μ)) s = 0
  rw [MeasureTheory.Measure.sum_apply _ hs]
  apply ENNReal.tsum_eq_zero.mpr
  intro i
  have hbasei := firstVector_dominates_component D hD x hord.2 i
  exact (hac i |>.trans (hbasei μbase (μ i) hμbase (hμ i))) hzero

theorem firstVectors_equivalent (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x y : ℕ → D.H)
    (hx : IsOrderedSpectralDecomposition D x)
    (hy : IsOrderedSpectralDecomposition D y) :
    SpectralMeasureEquivalentVectors D (x 0) (y 0) :=
  ⟨firstVector_dominates_every_vector D hD x hx (y 0),
    firstVector_dominates_every_vector D hD y hy (x 0)⟩

end Chapter02.OrderedSpectralDecomposition
