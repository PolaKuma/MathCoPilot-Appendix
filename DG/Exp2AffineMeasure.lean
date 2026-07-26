import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped ENNReal MeasureTheory
open MeasureTheory

noncomputable section

namespace Exp2AffineMeasure

/-- Full-line affine change of variables for Bochner integrals. -/
theorem integral_comp_affine (f : ℝ → ℝ) (a h : ℝ) :
    (∫ x, f (a + h * x)) = |h⁻¹| • (∫ y, f y) := by
  have hscale := Measure.integral_comp_smul (volume : Measure ℝ)
    (fun y : ℝ ↦ f (a + y)) h
  have htrans := (measurePreserving_add_left (volume : Measure ℝ) a).integral_comp
    (MeasurableEquiv.addLeft a).measurableEmbedding f
  have hscale' :
      (∫ x, f (a + h * x)) = |h⁻¹| • (∫ x, f (a + x)) := by
    simpa [smul_eq_mul] using hscale
  calc
    (∫ x, f (a + h * x)) = |h⁻¹| • (∫ x, f (a + x)) := hscale'
    _ = |h⁻¹| • (∫ y, f y) := by rw [htrans]

/-- Restricted affine change of variables on the reference and physical open cells. -/
theorem setIntegral_comp_affine_Ioo (f : ℝ → ℝ) {a h : ℝ} (hh : 0 < h) :
    (∫ x in Set.Ioo (0 : ℝ) 1, f (a + h * x)) =
      h⁻¹ • (∫ y in Set.Ioo a (a + h), f y) := by
  let s : Set ℝ := Set.Ioo a (a + h)
  let g : ℝ → ℝ := s.indicator f
  have hfull := integral_comp_affine g a h
  have hleft :
      (fun x : ℝ ↦ g (a + h * x)) =
        (Set.Ioo (0 : ℝ) 1).indicator (fun x ↦ f (a + h * x)) := by
    funext x
    by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
    · have hxmem : a + h * x ∈ s := by
        dsimp [s]
        constructor <;> nlinarith [hh, hx.1, hx.2]
      simp [g, s, Set.indicator, hx, hxmem]
    · simp only [Set.indicator, hx, if_false]
      by_cases hpre : a + h * x ∈ s
      · exfalso
        simp only [s, Set.mem_Ioo] at hpre
        have hxmem : x ∈ Set.Ioo (0 : ℝ) 1 := by
          constructor <;> nlinarith [hh, hpre.1, hpre.2]
        exact hx hxmem
      · simp [g, s, hpre]
  have hright :
      (∫ y, g y) = (∫ y in Set.Ioo a (a + h), f y) := by
    simpa [g, s] using (integral_indicator (μ := (volume : Measure ℝ)) measurableSet_Ioo)
  have hleftInt :
      (∫ x, g (a + h * x)) =
        (∫ x in Set.Ioo (0 : ℝ) 1, f (a + h * x)) := by
    rw [hleft]
    exact integral_indicator measurableSet_Ioo
  rw [hleftInt, hright] at hfull
  simpa [abs_of_pos hh, smul_eq_mul, s] using hfull

/-- The affine map sends restricted reference Lebesgue measure to the expected scaled physical
measure. -/
theorem map_affine_restrict_Ioo {a h : ℝ} (hh : 0 < h) :
    Measure.map (fun x : ℝ ↦ a + h * x)
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) =
      ENNReal.ofReal h⁻¹ • volume.restrict (Set.Ioo a (a + h)) := by
  let e : ℝ ≃ᵐ ℝ :=
    (MeasurableEquiv.mulRight₀ h hh.ne').trans (MeasurableEquiv.addLeft a)
  have he : (e : ℝ → ℝ) = fun x ↦ a + h * x := by
    funext x
    simp [e, mul_comm]
  have hmapAffine : Measure.map (fun x : ℝ ↦ a + h * x) (volume : Measure ℝ) =
      ENNReal.ofReal h⁻¹ • (volume : Measure ℝ) := by
    change Measure.map ((fun y : ℝ ↦ a + y) ∘ (fun x : ℝ ↦ h * x))
      (volume : Measure ℝ) = _
    rw [← Measure.map_map]
    · rw [Real.map_volume_mul_left hh.ne']
      rw [Measure.map_smul]
      rw [(measurePreserving_add_left (volume : Measure ℝ) a).map_eq]
      rw [abs_of_pos (inv_pos.mpr hh)]
    · exact measurable_const.add measurable_id
    · exact measurable_const.mul measurable_id
  have hmap : Measure.map (e : ℝ → ℝ) (volume : Measure ℝ) =
      ENNReal.ofReal h⁻¹ • (volume : Measure ℝ) := by
    rw [he]
    exact hmapAffine
  have hpre : e ⁻¹' Set.Ioo a (a + h) = Set.Ioo (0 : ℝ) 1 := by
    rw [he]
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor
    · intro hx
      constructor <;> nlinarith [hh, hx.1, hx.2]
    · intro hx
      constructor <;> nlinarith [hh, hx.1, hx.2]
  have hr := e.restrict_map (volume : Measure ℝ) (Set.Ioo a (a + h))
  rw [hmap, Measure.restrict_smul, hpre] at hr
  rw [← he]
  exact hr.symm

/-- Exact `eLpNorm` scaling under the affine map, for functions measurable on the physical cell.
The measure map and the exponent are both retained explicitly. -/
theorem eLpNorm_comp_affine_restrict_Ioo {p : ℝ≥0∞} (f : ℝ → ℝ)
    {a h : ℝ} (hh : 0 < h)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioo a (a + h)))) :
    eLpNorm (fun x ↦ f (a + h * x)) p
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) =
      (ENNReal.ofReal h⁻¹) ^ (1 / p).toReal •
        eLpNorm f p (volume.restrict (Set.Ioo a (a + h))) := by
  let e : ℝ ≃ᵐ ℝ :=
    (MeasurableEquiv.mulRight₀ h hh.ne').trans (MeasurableEquiv.addLeft a)
  have he : (e : ℝ → ℝ) = fun x ↦ a + h * x := by
    funext x
    simp [e, mul_comm]
  have hmap : Measure.map (e : ℝ → ℝ)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) =
      ENNReal.ofReal h⁻¹ • volume.restrict (Set.Ioo a (a + h)) := by
    rw [he]
    exact map_affine_restrict_Ioo hh
  let c : ℝ≥0∞ := ENNReal.ofReal h⁻¹
  have hc : c ≠ 0 := by
    dsimp [c]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hh))
  have hfc : AEStronglyMeasurable f
      (c • volume.restrict (Set.Ioo a (a + h))) := hf.smul_measure c
  have hfc' : AEStronglyMeasurable f
      (Measure.map (e : ℝ → ℝ) (volume.restrict (Set.Ioo (0 : ℝ) 1))) := by
    rw [hmap]
    exact hfc
  have hnorm := eLpNorm_map_measure (p := p) (μ := volume.restrict (Set.Ioo (0 : ℝ) 1))
      (f := (e : ℝ → ℝ)) (g := f) hfc' e.measurable.aemeasurable
  rw [hmap] at hnorm
  rw [eLpNorm_smul_measure_of_ne_zero hc] at hnorm
  have hfun : (fun x : ℝ ↦ f (a + h * x)) = f ∘ (e : ℝ → ℝ) := by
    funext x
    rw [Function.comp_apply, he]
  calc
    eLpNorm (fun x ↦ f (a + h * x)) p
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) =
        eLpNorm (f ∘ (e : ℝ → ℝ)) p
          (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by rw [hfun]
    _ = c ^ (1 / p).toReal •
        eLpNorm f p (volume.restrict (Set.Ioo a (a + h))) := hnorm.symm
    _ = (ENNReal.ofReal h⁻¹) ^ (1 / p).toReal •
        eLpNorm f p (volume.restrict (Set.Ioo a (a + h))) := by rfl

end Exp2AffineMeasure
