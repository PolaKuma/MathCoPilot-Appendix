import Chapter02.HallPetresco.CentralFiberFourfold
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Classical

noncomputable section

namespace Chapter02.CompactCentralCubeSurjective

/-- The cubing map on the circle is onto.  This is the concrete
central-fiber fact used for connected three-step nilsystems. -/
theorem circle_cube_surjective :
    Function.Surjective (fun z : Circle ↦ z ^ 3) := by
  exact (Circle.isQuotientCoveringMap_npow 3).surjective

/-- Cubing is coordinatewise onto on every finite-dimensional torus. -/
theorem torus_cube_surjective {ι : Type*} :
    Function.Surjective (fun z : ι → Circle ↦ z ^ 3) := by
  intro z
  choose w hw using fun i ↦ circle_cube_surjective (z i)
  refine ⟨w, funext fun i ↦ ?_⟩
  simpa only [Pi.pow_apply] using hw i

end Chapter02.CompactCentralCubeSurjective
