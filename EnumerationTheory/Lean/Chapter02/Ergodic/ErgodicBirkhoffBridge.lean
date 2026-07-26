import Chapter02.Ergodic.Birkhoff
import Chapter02.Ergodic.ErgodicBridge

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.ErgodicBirkhoffBridge

universe u

/-- On an ergodic probability-preserving system, the forward Birkhoff
averages of every integrable complex function converge almost everywhere
to its space integral.

This risk-isolated version deliberately avoids importing the section-level
module that still depends on the BHK statement under construction. -/
theorem ergodicTimeAverage_tendsto_integral
    (M : System.{u}) (hM : IsErgodic M)
    (f : M.X → ℂ) (hf : M.lpMember 1 f) :
    ∀ᵐ x ∂M.μ,
      Tendsto (fun n ↦ ergodicAverage M f n x) atTop
        (nhds (∫ y, f y ∂M.μ)) := by
  obtain ⟨fstar, hfstar, hfinv, hlim, hint⟩ :=
    Chapter02.Birkhoff.birkhoffPointwiseErgodic M hM.1 f hf
  obtain ⟨c, hc⟩ :=
    (Chapter02.ErgodicBridge.isErgodic_to_mathlibErgodic M hM)
      |>.ae_eq_const_of_ae_eq_comp_ae
        hfstar.aestronglyMeasurable hfinv
  letI : IsProbabilityMeasure M.μ := hM.1.1
  have hci : (∫ x, fstar x ∂M.μ) = c := by
    calc
      (∫ x, fstar x ∂M.μ) = ∫ _x, c ∂M.μ :=
        integral_congr_ae hc
      _ = c := by simp
  have hc_eq : c = ∫ x, f x ∂M.μ := hci.symm.trans hint
  filter_upwards [hlim, hc] with x hx hcx
  simpa [hcx, hc_eq] using hx

end Chapter02.ErgodicBirkhoffBridge
