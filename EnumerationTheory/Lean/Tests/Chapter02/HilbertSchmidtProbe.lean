import Chapter02.Spectral.HilbertSchmidtConsequences

noncomputable section

open MeasureTheory

namespace Chapter02

universe u

example (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hdense : HasDenseCompactFunctions M) :
    ∀ f : M.X → ℂ, M.lpMember 2 f → ∀ ε : ℝ, 0 < ε →
      ∃ g : M.X → ℂ, IsIntegrableKernelRangeFunction M g ∧
        eLpNorm (fun x ↦ f x - g x) 2 M.μ < ENNReal.ofReal ε := by
  exact HilbertSchmidtConsequences.denseCompactFunctions_imply_dense_integrableKernelRange
    M hM hdense

end Chapter02
