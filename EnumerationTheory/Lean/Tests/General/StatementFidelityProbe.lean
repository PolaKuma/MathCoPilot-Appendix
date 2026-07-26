import Mathlib

#check LocallyConvexSpace
#check IsTopologicalAddGroup
#check ContinuousSMul
#check T2Space
#check NormedSpace

example {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E] : True := by
  trivial
