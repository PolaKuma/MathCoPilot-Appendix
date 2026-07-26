import Chapter04.Section03
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section

open Classical Filter
open scoped ENNReal Topology

namespace Chapter04.LpMultiplier

variable {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)

theorem multiplication_linearMap_continuous (h : X → ℂ)
    (hall : ∀ f : X → ℂ, MeasureTheory.MemLp f 2 μ →
      MeasureTheory.MemLp (fun x ↦ h x * f x) 2 μ) :
    ∃ T : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ,
      ∀ f : MeasureTheory.Lp ℂ 2 μ,
        T f = (hall (fun x ↦ f x) (MeasureTheory.Lp.memLp f)).toLp
          (fun x ↦ h x * f x) := by
  let T₀ : MeasureTheory.Lp ℂ 2 μ →ₗ[ℂ] MeasureTheory.Lp ℂ 2 μ :=
    { toFun := fun f ↦
        (hall (fun x ↦ f x) (MeasureTheory.Lp.memLp f)).toLp
          (fun x ↦ h x * f x)
      map_add' := by
        intro f g
        let hf := hall (fun x ↦ f x) (MeasureTheory.Lp.memLp f)
        let hg := hall (fun x ↦ g x) (MeasureTheory.Lp.memLp g)
        let hfg := hall (fun x ↦ (f + g) x) (MeasureTheory.Lp.memLp (f + g))
        calc
          hfg.toLp (fun x ↦ h x * (f + g) x) =
              (hf.add hg).toLp
                ((fun x ↦ h x * f x) + fun x ↦ h x * g x) := by
            apply MeasureTheory.MemLp.toLp_congr
            filter_upwards [MeasureTheory.Lp.coeFn_add f g] with x hx
            simp only [Pi.add_apply] at hx ⊢
            rw [hx, mul_add]
          _ = hf.toLp (fun x ↦ h x * f x) +
              hg.toLp (fun x ↦ h x * g x) := hf.toLp_add hg
      map_smul' := by
        intro c f
        let hf := hall (fun x ↦ f x) (MeasureTheory.Lp.memLp f)
        let hcf := hall (fun x ↦ (c • f) x) (MeasureTheory.Lp.memLp (c • f))
        calc
          hcf.toLp (fun x ↦ h x * (c • f) x) =
              (hf.const_smul c).toLp (c • fun x ↦ h x * f x) := by
            apply MeasureTheory.MemLp.toLp_congr
            filter_upwards [MeasureTheory.Lp.coeFn_smul c f] with x hx
            simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢
            rw [hx]
            ring
          _ = c • hf.toLp (fun x ↦ h x * f x) :=
            MeasureTheory.MemLp.toLp_const_smul c hf }
  have hclosed : ∀ (u : ℕ → MeasureTheory.Lp ℂ 2 μ) x y,
      Tendsto u atTop (𝓝 x) → Tendsto (T₀ ∘ u) atTop (𝓝 y) → y = T₀ x := by
    intro u x y hux hTuy
    obtain ⟨ns, hns, huxae⟩ :=
      (MeasureTheory.tendstoInMeasure_of_tendsto_Lp hux).exists_seq_tendsto_ae
    have hTuy' : Tendsto (fun i ↦ T₀ (u (ns i))) atTop (𝓝 y) :=
      hTuy.comp hns.tendsto_atTop
    obtain ⟨ms, hms, hTuyae⟩ :=
      (MeasureTheory.tendstoInMeasure_of_tendsto_Lp hTuy').exists_seq_tendsto_ae
    apply MeasureTheory.Lp.ext
    filter_upwards [huxae, hTuyae,
      MeasureTheory.ae_all_iff.2 (fun n ↦
        (hall (fun z ↦ u n z) (MeasureTheory.Lp.memLp (u n))).coeFn_toLp),
      (hall (fun z ↦ x z) (MeasureTheory.Lp.memLp x)).coeFn_toLp] with z huz hTuz hmul hmulx
    have huz' : Tendsto (fun i ↦ u (ns (ms i)) z) atTop (𝓝 (x z)) :=
      huz.comp hms.tendsto_atTop
    have hprod : Tendsto (fun i ↦ h z * u (ns (ms i)) z) atTop
        (𝓝 (h z * x z)) := tendsto_const_nhds.mul huz'
    have hTy : Tendsto (fun i ↦ T₀ (u (ns (ms i))) z) atTop (𝓝 (y z)) := hTuz
    have heq : (fun i ↦ T₀ (u (ns (ms i))) z) =
        fun i ↦ h z * u (ns (ms i)) z := by
      funext i
      exact hmul (ns (ms i))
    rw [heq] at hTy
    exact tendsto_nhds_unique hTy hprod |>.trans hmulx.symm
  let T : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ :=
    ContinuousLinearMap.ofSeqClosedGraph hclosed
  refine ⟨T, ?_⟩
  intro f
  rfl

theorem memLp_top_of_multiplication_memLp [MeasureTheory.IsFiniteMeasure μ]
    (h : X → ℂ) (hh : MeasureTheory.MemLp h 2 μ)
    (hall : ∀ f : X → ℂ, MeasureTheory.MemLp f 2 μ →
      MeasureTheory.MemLp (fun x ↦ h x * f x) 2 μ) :
    MeasureTheory.MemLp h ⊤ μ := by
  obtain ⟨T, hT⟩ := multiplication_linearMap_continuous μ h hall
  let g : X → ℂ := hh.1.mk h
  have hg : MeasureTheory.StronglyMeasurable g := hh.1.stronglyMeasurable_mk
  have hgh : h =ᵐ[μ] g := hh.1.ae_eq_mk
  let C : ℝ := ‖T‖ + 1
  let A : Set X := {x | C < ‖g x‖}
  have hA : MeasurableSet A := by
    exact measurableSet_lt measurable_const hg.norm.measurable
  by_cases hμA : μ A = 0
  · apply MeasureTheory.memLp_top_of_bound hh.1 C
    have hnotA : ∀ᵐ x ∂μ, x ∉ A := by
      apply MeasureTheory.ae_iff.mpr
      simpa only [Set.mem_setOf_eq, not_not] using hμA
    filter_upwards [hgh, hnotA] with x hx hxA
    rw [hx]
    exact le_of_not_gt hxA
  · have hμAfin : μ A ≠ ∞ := MeasureTheory.measure_ne_top μ A
    let fA : MeasureTheory.Lp ℂ 2 μ :=
      MeasureTheory.indicatorConstLp 2 hA hμAfin (1 : ℂ)
    let cA : MeasureTheory.Lp ℂ 2 μ :=
      MeasureTheory.indicatorConstLp 2 hA hμAfin (C : ℂ)
    have hfA_mem : MeasureTheory.MemLp (fun x ↦ fA x) 2 μ :=
      MeasureTheory.Lp.memLp fA
    have hprod_mem := hall (fun x ↦ fA x) hfA_mem
    have hlowerE : MeasureTheory.eLpNorm (fun x ↦ cA x) 2 μ ≤
        MeasureTheory.eLpNorm (fun x ↦ h x * fA x) 2 μ := by
      apply MeasureTheory.eLpNorm_mono_ae
      filter_upwards [hgh,
        MeasureTheory.indicatorConstLp_coeFn (p := (2 : ENNReal))
          (hs := hA) (hμs := hμAfin) (c := (1 : ℂ)),
        MeasureTheory.indicatorConstLp_coeFn (p := (2 : ENNReal))
          (hs := hA) (hμs := hμAfin) (c := (C : ℂ))] with x hx hf hxC
      by_cases hxA : x ∈ A
      · rw [hx, hf, hxC, Set.indicator_of_mem hxA, Set.indicator_of_mem hxA]
        simp only [mul_one, Complex.norm_real, Real.norm_eq_abs]
        have hC0 : 0 ≤ C := by dsimp [C]; positivity
        simpa [abs_of_nonneg hC0] using (show C < ‖g x‖ from hxA).le
      · rw [hf, hxC, Set.indicator_of_notMem hxA, Set.indicator_of_notMem hxA]
        simp
    have hlower : ‖cA‖ ≤ ‖T fA‖ := by
      rw [MeasureTheory.Lp.norm_def, hT fA,
        MeasureTheory.Lp.norm_toLp]
      exact ENNReal.toReal_mono hprod_mem.eLpNorm_ne_top hlowerE
    have hop : ‖T fA‖ ≤ ‖T‖ * ‖fA‖ := T.le_opNorm fA
    have hfAnorm : ‖fA‖ = μ.real A ^ (1 / (2 : ENNReal).toReal) := by
      simpa [fA] using
        (MeasureTheory.norm_indicatorConstLp (p := (2 : ENNReal))
          (hs := hA) (hμs := hμAfin) (c := (1 : ℂ)) (by norm_num) (by norm_num))
    have hcAnorm : ‖cA‖ = C * μ.real A ^ (1 / (2 : ENNReal).toReal) := by
      have hC0 : 0 ≤ C := by dsimp [C]; positivity
      simpa [cA, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC0] using
        (MeasureTheory.norm_indicatorConstLp (p := (2 : ENNReal))
          (hs := hA) (hμs := hμAfin) (c := (C : ℂ)) (by norm_num) (by norm_num))
    have hrpos : 0 < μ.real A ^ (1 / (2 : ENNReal).toReal) := by
      apply Real.rpow_pos_of_pos
      exact lt_of_le_of_ne MeasureTheory.measureReal_nonneg
        ((MeasureTheory.measureReal_ne_zero_iff hμAfin).2 hμA).symm
    rw [hcAnorm] at hlower
    rw [hfAnorm] at hop
    have : C ≤ ‖T‖ := by
      exact le_of_mul_le_mul_right (hlower.trans hop) hrpos
    dsimp [C] at this
    linarith

end Chapter04.LpMultiplier
