import Chapter02.Common
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Classical Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Chapter02.HostKraUniformComponentIntegration

universe u v

/-- Dominated integration preserves translated-uniform decay.

The filter `comap Prod.fst atTop` encodes exactly “the first index tends
to infinity, uniformly over every value of the second index”.  Applying
dominated convergence to this filter avoids choosing bad subsequences and
is the abstract integration step needed after ergodic disintegration. -/
theorem integral_uniform_tendsto_zero_of_ae
    {S : Type u} [MeasurableSpace S]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure S)
    (b : ℕ → ℕ → S → E)
    (bound : S → ℝ)
    (hbmeas : ∀ N i, AEStronglyMeasurable (b N i) μ)
    (hbound : ∀ N i, ∀ᵐ s ∂μ, ‖b N i s‖ ≤ bound s)
    (hboundInt : Integrable bound μ)
    (hzero : ∀ᵐ s ∂μ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ‖b N i s‖ < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        ‖∫ s, b N i s ∂μ‖ < ε := by
  let l : Filter (ℕ × ℕ) := Filter.comap Prod.fst atTop
  let F : (ℕ × ℕ) → S → E := fun p ↦ b p.1 p.2
  have hpoint :
      ∀ᵐ s ∂μ, Tendsto (fun p ↦ F p s) l (𝓝 0) := by
    filter_upwards [hzero] with s hs
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.eventually_comap]
    filter_upwards [hs ε hε] with N hN
    intro p hp
    subst N
    simpa only [F, dist_zero_right] using hN p.2
  have hInt :
      Tendsto (fun p ↦ ∫ s, F p s ∂μ) l (𝓝 0) := by
    simpa only [integral_zero] using
      (tendsto_integral_filter_of_dominated_convergence
        (l := l) (F := F) (f := fun _ ↦ (0 : E))
        bound
        (Filter.Eventually.of_forall
          (fun p ↦ hbmeas p.1 p.2))
        (Filter.Eventually.of_forall
          (fun p ↦ hbound p.1 p.2))
        hboundInt hpoint)
  intro ε hε
  have hevent :
      ∀ᶠ p in l, ‖∫ s, F p s ∂μ‖ < ε := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      hInt.eventually (Metric.ball_mem_nhds (0 : E) hε)
  rw [Filter.eventually_comap] at hevent
  filter_upwards [hevent] with N hN
  intro i
  have hi := hN (N, i) rfl
  simpa only [F, Metric.mem_ball, dist_zero_right] using hi

end Chapter02.HostKraUniformComponentIntegration
