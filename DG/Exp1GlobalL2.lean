import Exp1
import Exp2StandardSobolev

open scoped ENNReal MeasureTheory Topology BigOperators
open MeasureTheory Set Filter

noncomputable section

namespace Exp1

/-- Canonical global representative of a broken field.  It agrees with the cell representative
on each open cell and is zero on interfaces; interface choices are irrelevant in `L²`. -/
def assembleGlobal {N : ℕ} (mesh : PeriodicMesh N) (v : DGField N) : ℝ → ℝ :=
  fun x ↦ ∑ j : Fin N, (meshCell mesh j : Set ℝ).indicator (v j) x

theorem meshCell_disjoint {N : ℕ} (mesh : PeriodicMesh N)
    {i j : Fin N} (hij : i ≠ j) :
    Disjoint (meshCell mesh i : Set ℝ) (meshCell mesh j : Set ℝ) := by
  wlog hlt : i < j generalizing i j
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
    exact (this (Ne.symm hij) hji).symm
  refine Set.disjoint_left.2 ?_
  intro x hxi hxj
  have hindex : i.succ ≤ j.castSucc := by
    change i.1 + 1 ≤ j.1
    omega
  have hnodes : mesh.nodes i.succ ≤ mesh.nodes j.castSucc :=
    mesh.nodes_strictMono.monotone hindex
  have hxi' : x < cellRight mesh i := by
    simpa [meshCell, Exp2.cell, cellLength] using hxi.2
  have hxj' : cellLeft mesh j < x := by
    simpa [meshCell, Exp2.cell] using hxj.1
  exact (not_lt_of_ge hnodes) (lt_trans hxj' hxi')

theorem meshCells_pairwiseDisjoint {N : ℕ} (mesh : PeriodicMesh N) :
    Pairwise (fun i j : Fin N ↦
      Disjoint (meshCell mesh i : Set ℝ) (meshCell mesh j : Set ℝ)) := by
  intro i j hij
  exact meshCell_disjoint mesh hij

theorem meshCell_subset_unit {N : ℕ} (mesh : PeriodicMesh N) (j : Fin N) :
    (meshCell mesh j : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro x hx
  have hleftIndex : (0 : Fin (N + 1)) ≤ j.castSucc := by
    exact Fin.zero_le _
  have hrightIndex : j.succ ≤ Fin.last N := by
    change j.1 + 1 ≤ N
    omega
  have hleftNode : 0 ≤ cellLeft mesh j := by
    rw [cellLeft, ← mesh.left_boundary]
    exact mesh.nodes_strictMono.monotone hleftIndex
  have hrightNode : cellRight mesh j ≤ 1 := by
    rw [cellRight, ← mesh.right_boundary]
    exact mesh.nodes_strictMono.monotone hrightIndex
  have hx' : x ∈ Set.Ioo (cellLeft mesh j) (cellRight mesh j) := by
    simpa [meshCell, Exp2.cell, cellLength] using hx
  exact ⟨lt_of_le_of_lt hleftNode hx'.1, lt_of_lt_of_le hx'.2 hrightNode⟩

/-- The cell lengths telescope to the length of the periodic domain. -/
theorem sum_cellLength {N : ℕ} (mesh : PeriodicMesh N) :
    ∑ j : Fin N, cellLength mesh j = 1 := by
  let f : ℕ → ℝ := fun i ↦
    if hi : i < N + 1 then mesh.nodes ⟨i, hi⟩ else 0
  calc
    ∑ j : Fin N, cellLength mesh j =
        ∑ j : Fin N, (f (j.1 + 1) - f j.1) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [cellLength, cellLeft, cellRight, f]
          rw [dif_pos (by omega), dif_pos (by omega)]
          congr 2 <;> apply Fin.ext <;> rfl
    _ = ∑ i ∈ Finset.range N, (f (i + 1) - f i) :=
      Fin.sum_univ_eq_sum_range (fun i ↦ f (i + 1) - f i) N
    _ = f N - f 0 := Finset.sum_range_sub f N
    _ = 1 := by
      rw [show f N = 1 by
        simp only [f]
        rw [dif_pos (Nat.lt_succ_self N)]
        change mesh.nodes (Fin.last N) = 1
        exact mesh.right_boundary,
        show f 0 = 0 by simp [f, mesh.left_boundary]]
      norm_num

/-- The disjoint open cells have the full Lebesgue measure of `(0,1)`. -/
theorem measure_iUnion_meshCell {N : ℕ} (mesh : PeriodicMesh N) :
    volume (⋃ j : Fin N, (meshCell mesh j : Set ℝ)) = 1 := by
  rw [measure_iUnion (meshCells_pairwiseDisjoint mesh)
    (fun j ↦ (meshCell mesh j).2.measurableSet), tsum_fintype]
  have hcell : ∀ j : Fin N,
      volume (meshCell mesh j : Set ℝ) = ENNReal.ofReal (cellLength mesh j) := by
    intro j
    simp [meshCell, Exp2.cell, cellLength, Real.volume_Ioo]
  rw [Finset.sum_congr rfl (fun j _ ↦ hcell j)]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [sum_cellLength mesh]
    norm_num
  · intro j hj
    exact (cellLength_pos mesh j).le

/-- Apart from the finite set of mesh interfaces, the open cells cover
`(0,1)`.  This measure-theoretic form is exactly what is needed for global
`L²` representatives. -/
theorem meshCells_ae_cover_reference {N : ℕ} (mesh : PeriodicMesh N) :
    ∀ᵐ x ∂(volume.restrict (Exp2.referenceCell : Set ℝ)),
      ∃ j : Fin N, x ∈ (meshCell mesh j : Set ℝ) := by
  let U : Set ℝ := ⋃ j : Fin N, (meshCell mesh j : Set ℝ)
  have hUmeas : MeasurableSet U :=
    MeasurableSet.iUnion fun j ↦ (meshCell mesh j).2.measurableSet
  have hUsub : U ⊆ (Exp2.referenceCell : Set ℝ) := by
    intro x hx
    simp only [U, Set.mem_iUnion] at hx
    obtain ⟨j, hxj⟩ := hx
    simpa [Exp2.referenceCell, Exp2.cell] using
      meshCell_subset_unit mesh j hxj
  have hdiff :
      volume ((Exp2.referenceCell : Set ℝ) \ U) = 0 := by
    rw [measure_diff hUsub hUmeas.nullMeasurableSet (by
      rw [measure_iUnion_meshCell mesh]
      norm_num)]
    rw [show volume (Exp2.referenceCell : Set ℝ) = 1 by
      simp [Exp2.referenceCell, Exp2.cell],
      measure_iUnion_meshCell mesh]
    norm_num
  rw [ae_iff]
  have hbad :
      {x : ℝ | ¬ ∃ j : Fin N, x ∈ (meshCell mesh j : Set ℝ)} = Uᶜ := by
    ext x
    simp [U]
  have hbadMeas :
      MeasurableSet {x : ℝ | ¬ ∃ j : Fin N,
        x ∈ (meshCell mesh j : Set ℝ)} := by
    rw [hbad]
    exact hUmeas.compl
  rw [Measure.restrict_apply hbadMeas]
  rw [hbad]
  change volume (Uᶜ ∩ (Exp2.referenceCell : Set ℝ)) = 0
  rw [Set.inter_comm]
  exact hdiff

theorem assembleGlobal_apply_of_mem {N : ℕ} (mesh : PeriodicMesh N)
    (v : DGField N) (j : Fin N) {x : ℝ} (hx : x ∈ (meshCell mesh j : Set ℝ)) :
    assembleGlobal mesh v x = v j x := by
  classical
  unfold assembleGlobal
  rw [Finset.sum_eq_single j]
  · simp [hx]
  · intro i hi hne
    have hdis := meshCell_disjoint mesh hne
    have hnot : x ∉ (meshCell mesh i : Set ℝ) := by
      intro hxi
      exact Set.disjoint_left.1 hdis hxi hx
    simp [hnot]
  · simp

/-- Any single-valued global function agreeing with the broken representatives
on every open cell is almost everywhere equal to `assembleGlobal`.  Thus the
zero convention of `assembleGlobal` differs from the PDF's global error
function only at mesh interfaces. -/
theorem assembleGlobal_ae_eq_of_cellwise {N : ℕ} (mesh : PeriodicMesh N)
    (v : DGField N) (f : ℝ → ℝ)
    (hcell : ∀ j : Fin N, ∀ x ∈ (meshCell mesh j : Set ℝ), f x = v j x) :
    assembleGlobal mesh v
      =ᵐ[volume.restrict (Exp2.referenceCell : Set ℝ)] f := by
  filter_upwards [meshCells_ae_cover_reference mesh] with x hx
  obtain ⟨j, hxj⟩ := hx
  rw [assembleGlobal_apply_of_mem mesh v j hxj]
  exact (hcell j x hxj).symm

theorem assembleGlobal_sq {N : ℕ} (mesh : PeriodicMesh N)
    (v : DGField N) (x : ℝ) :
    ‖assembleGlobal mesh v x‖ ^ 2 =
      ∑ j : Fin N, (meshCell mesh j : Set ℝ).indicator
        (fun y ↦ ‖v j y‖ ^ 2) x := by
  classical
  by_cases hex : ∃ j : Fin N, x ∈ (meshCell mesh j : Set ℝ)
  · obtain ⟨j, hx⟩ := hex
    rw [assembleGlobal_apply_of_mem mesh v j hx]
    rw [Finset.sum_eq_single j]
    · simp [hx]
    · intro i hi hne
      have hdis := meshCell_disjoint mesh hne
      have hnot : x ∉ (meshCell mesh i : Set ℝ) := by
        intro hxi
        exact Set.disjoint_left.1 hdis hxi hx
      simp [hnot]
    · simp
  · have hnone : ∀ j : Fin N, x ∉ (meshCell mesh j : Set ℝ) := by
      intro j hx
      exact hex ⟨j, hx⟩
    simp [assembleGlobal, hnone]

theorem cellIndicator_memLp_volume {N : ℕ} (mesh : PeriodicMesh N)
    (v : DGField N) (j : Fin N)
    (hv : MemLp (v j) 2 (volume.restrict (meshCell mesh j : Set ℝ))) :
    MemLp ((meshCell mesh j : Set ℝ).indicator (v j)) 2 volume := by
  have hs : MeasurableSet (meshCell mesh j : Set ℝ) :=
    (meshCell mesh j).2.measurableSet
  exact (memLp_indicator_iff_restrict hs).2 hv

theorem assembleGlobal_memLp {N : ℕ} (mesh : PeriodicMesh N)
    (v : DGField N)
    (hv : ∀ j : Fin N,
      MemLp (v j) 2 (volume.restrict (meshCell mesh j : Set ℝ))) :
    MemLp (assembleGlobal mesh v) 2
      (volume.restrict (Exp2.referenceCell : Set ℝ)) := by
  classical
  have hterm : ∀ j : Fin N,
      MemLp ((meshCell mesh j : Set ℝ).indicator (v j)) 2 volume :=
    fun j ↦ cellIndicator_memLp_volume mesh v j (hv j)
  have hsum :
      MemLp (∑ j : Fin N, (meshCell mesh j : Set ℝ).indicator (v j)) 2 volume := by
    induction (Finset.univ : Finset (Fin N)) using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact (hterm j).add ih
  have hrestricted := hsum.mono_measure
    (μ := volume) (ν := volume.restrict (Exp2.referenceCell : Set ℝ))
    Measure.restrict_le_self
  have heq :
      assembleGlobal mesh v =
        ∑ j : Fin N, (meshCell mesh j : Set ℝ).indicator (v j) := by
    funext x
    simp [assembleGlobal]
  rw [heq]
  exact hrestricted

theorem restrictedUnit_restrict_meshCell {N : ℕ} (mesh : PeriodicMesh N)
    (j : Fin N) :
    (volume.restrict (Exp2.referenceCell : Set ℝ)).restrict
        (meshCell mesh j : Set ℝ) =
      volume.restrict (meshCell mesh j : Set ℝ) := by
  have hs : MeasurableSet (meshCell mesh j : Set ℝ) :=
    (meshCell mesh j).2.measurableSet
  calc
    _ = volume.restrict
        ((meshCell mesh j : Set ℝ) ∩ (Exp2.referenceCell : Set ℝ)) :=
      Measure.restrict_restrict hs
    _ = _ := by
      rw [Set.inter_eq_left.mpr]
      simpa [Exp2.referenceCell, Exp2.cell] using meshCell_subset_unit mesh j

theorem cell_l2Norm_sq {N : ℕ} (mesh : PeriodicMesh N)
    (v : DGField N) (j : Fin N)
    (hv : MemLp (v j) 2 (volume.restrict (meshCell mesh j : Set ℝ))) :
    (Exp2.l2NormOn (meshCell mesh j) (v j)) ^ 2 =
      ∫ x, ‖v j x‖ ^ 2 ∂(volume.restrict (meshCell mesh j : Set ℝ)) := by
  rw [Exp2.l2NormOn_eq_sqrt_integral_sq hv]
  exact Real.sq_sqrt (integral_nonneg fun x ↦ sq_nonneg ‖v j x‖)

/-- The canonical assembled function has exactly the broken norm.  This is the formal bridge
from the project's broken representation to the PDF's global `L²(0,1)` norm. -/
theorem l2NormOn_assembleGlobal_eq_brokenL2Norm {N : ℕ}
    (mesh : PeriodicMesh N) (v : DGField N)
    (hv : ∀ j : Fin N,
      MemLp (v j) 2 (volume.restrict (meshCell mesh j : Set ℝ))) :
    Exp2.l2NormOn Exp2.referenceCell (assembleGlobal mesh v) =
      brokenL2Norm mesh v := by
  classical
  let μ := volume.restrict (Exp2.referenceCell : Set ℝ)
  have hglobalLp := assembleGlobal_memLp mesh v hv
  have htermLp : ∀ j : Fin N,
      MemLp ((meshCell mesh j : Set ℝ).indicator (v j)) 2 μ := by
    intro j
    exact (cellIndicator_memLp_volume mesh v j (hv j)).mono_measure
      Measure.restrict_le_self
  have htermInt : ∀ j : Fin N,
      Integrable
        (fun x ↦ ‖(meshCell mesh j : Set ℝ).indicator (v j) x‖ ^ 2) μ := by
    intro j
    exact (memLp_two_iff_integrable_sq_norm (htermLp j).aestronglyMeasurable).1
      (htermLp j)
  have hglobalInt :
      (∫ x, ‖assembleGlobal mesh v x‖ ^ 2 ∂μ) =
        ∑ j : Fin N,
          ∫ x, ‖v j x‖ ^ 2
            ∂(volume.restrict (meshCell mesh j : Set ℝ)) := by
    calc
      _ = ∫ x, ∑ j : Fin N, (meshCell mesh j : Set ℝ).indicator
          (fun y ↦ ‖v j y‖ ^ 2) x ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            exact assembleGlobal_sq mesh v x
      _ = ∑ j : Fin N, ∫ x,
          (meshCell mesh j : Set ℝ).indicator
            (fun y ↦ ‖v j y‖ ^ 2) x ∂μ := by
            rw [integral_finset_sum]
            intro j hj
            apply (htermInt j).congr
            filter_upwards with x
            by_cases hx : x ∈ (meshCell mesh j : Set ℝ) <;> simp [hx]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        have hs : MeasurableSet (meshCell mesh j : Set ℝ) :=
          (meshCell mesh j).2.measurableSet
        calc
          _ = ∫ x, ‖v j x‖ ^ 2
              ∂(μ.restrict (meshCell mesh j : Set ℝ)) :=
            integral_indicator hs
          _ = _ := by rw [restrictedUnit_restrict_meshCell mesh j]
  rw [Exp2.l2NormOn_eq_sqrt_integral_sq hglobalLp]
  unfold brokenL2Norm
  congr 1
  rw [hglobalInt]
  apply Finset.sum_congr rfl
  intro j hj
  exact (cell_l2Norm_sq mesh v j (hv j)).symm

/-- Exp1's final estimate stated in the genuine global `L²(0,1)` norm.
The cellwise error is assembled with the canonical zero-valued convention on
interfaces; changing those values does not change its `L²` class. -/
theorem global_main_theorem (K : ℕ) {a ρ : ℝ}
    (ha : 0 < a) (hρ : 1 ≤ ρ) :
    ∀ T : ℝ, 0 < T → ∀ solution : SmoothPeriodicAdvectionSolution K a T,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ {N : ℕ} (mesh : PeriodicMesh N), IsQuasiUniform ρ mesh →
        ∀ uh : DGTrajectory N,
          IsSemiDiscreteUpwindDG K a T mesh uh →
          HasGaussRadauInitialData K mesh solution.u uh →
          Exp2.l2NormOn Exp2.referenceCell
              (assembleGlobal mesh
                (fun j x ↦ solution.u x T - uh T j x)) ≤
            C * mesh.meshSize ^ (K + 1) := by
  intro T hT solution
  obtain ⟨C, hC, hestimate⟩ := main_theorem K ha hρ T hT solution
  refine ⟨C, hC, ?_⟩
  intro N mesh hmesh uh huh hinitial
  have hbroken := hestimate mesh hmesh uh huh hinitial
  obtain ⟨uht, hregularity, hscheme⟩ := huh
  have hTmem : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hv : ∀ j : Fin N,
      MemLp (fun x ↦ solution.u x T - uh T j x) 2
        (volume.restrict (meshCell mesh j : Set ℝ)) := by
    intro j
    exact (solutionValue_memLp K mesh solution T hTmem j).sub
      (dgField_memLp mesh (uh T)
        (hregularity.value_isDGField T hTmem) j)
  rw [l2NormOn_assembleGlobal_eq_brokenL2Norm mesh _ hv]
  exact hbroken

end Exp1
