import Exp1Energy

open scoped ENNReal MeasureTheory Topology Interval BigOperators
open MeasureTheory Set Filter

noncomputable section
namespace Exp1

/-- Theorem 1, with the proof-intended quantifier order: for every fixed `T > 0` there is a
constant `C_T`, independent of the number of cells, the mesh size, and the DG solution, on all
meshes sharing the fixed quasi-uniformity ratio `ρ`. -/
theorem main_theorem (K : ℕ) {a ρ : ℝ} (ha : 0 < a) (hρ : 1 ≤ ρ) :
    ∀ T : ℝ, 0 < T → ∀ solution : SmoothPeriodicAdvectionSolution K a T,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ {N : ℕ} (mesh : PeriodicMesh N), IsQuasiUniform ρ mesh →
        ∀ uh : DGTrajectory N,
          IsSemiDiscreteUpwindDG K a T mesh uh →
          HasGaussRadauInitialData K mesh solution.u uh →
          brokenL2Norm mesh (fun j x ↦ solution.u x T - uh T j x) ≤
            C * mesh.meshSize ^ (K + 1) := by
  intro T hT solution
  obtain ⟨Cη, hCη, hη⟩ := gaussRadau_projection_error_bound K hT hρ solution
  obtain ⟨Cξ, hCξ, hξ⟩ := discrete_error_bound K ha hT hρ solution
  refine ⟨Cη + Cξ, add_nonneg hCη hCξ, ?_⟩
  intro N mesh hmesh uh huh hinit
  let projection := Classical.choice (projectionTrajectory_exists K mesh solution)
  have hηT := hη mesh hmesh projection
  have hξT := hξ mesh hmesh uh huh hinit projection
  have hTmem : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  obtain ⟨uht, huhRegularity, huhScheme⟩ := huh
  have hηMem : ∀ j : Fin N, MemLp
      (fun x ↦ solution.u x T - projection.value T j x) 2
      (volume.restrict (meshCell mesh j : Set ℝ)) := by
    intro j
    exact (solutionValue_memLp K mesh solution T hTmem j).sub
      (projectionValue_memLp K mesh solution projection T hTmem j)
  have hξMem : ∀ j : Fin N, MemLp
      (fun x ↦ projection.value T j x - uh T j x) 2
      (volume.restrict (meshCell mesh j : Set ℝ)) := by
    intro j
    exact (projectionValue_memLp K mesh solution projection T hTmem j).sub
      (dgField_memLp mesh (uh T)
        (huhRegularity.value_isDGField T hTmem) j)
  have htriangle := brokenL2Norm_triangle mesh
    (fun j x ↦ solution.u x T - projection.value T j x)
    (fun j x ↦ projection.value T j x - uh T j x)
    hηMem hξMem
  have hdecomp :
      (fun j x ↦ (solution.u x T - projection.value T j x) +
        (projection.value T j x - uh T j x)) =
      (fun j x ↦ solution.u x T - uh T j x) := by
    funext j x
    ring
  rw [hdecomp] at htriangle
  calc
    brokenL2Norm mesh (fun j x ↦ solution.u x T - uh T j x) ≤
        brokenL2Norm mesh (fun j x ↦ solution.u x T - projection.value T j x) +
          brokenL2Norm mesh (fun j x ↦ projection.value T j x - uh T j x) := htriangle
    _ ≤ Cη * mesh.meshSize ^ (K + 1) + Cξ * mesh.meshSize ^ (K + 1) :=
      add_le_add hηT hξT
    _ = (Cη + Cξ) * mesh.meshSize ^ (K + 1) := by ring

end Exp1
