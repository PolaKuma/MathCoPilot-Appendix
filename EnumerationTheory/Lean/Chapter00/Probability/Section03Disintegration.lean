import Chapter00.Probability.Section03L1
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Disintegration.Unique

noncomputable section

open Classical Filter MeasureTheory ProbabilityTheory

namespace Chapter00.Section03

universe u v

theorem measureDisintegrationAux
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (φ : X -> Y) (μ : Measure X)
    [IsProbabilityMeasure μ] (hφ : Measurable φ) :
    HasMeasureDisintegration φ μ (Measure.map φ μ) := by
  letI : Nonempty X := nonempty_of_isProbabilityMeasure μ
  letI : Nonempty Y := ⟨φ (Classical.choice (inferInstance : Nonempty X))⟩
  let κ : Kernel Y X := condDistrib id φ μ
  refine ⟨hφ, rfl, κ, ?_, ?_, ?_, ?_⟩
  · have hcomp := condDistrib_comp φ (Y := (id : X → X))
      (mβ := (inferInstance : MeasurableSpace Y)) (μ := μ)
      measurable_id.aemeasurable hφ
    have hself := condDistrib_self (μ := μ) φ
    filter_upwards [hcomp, hself] with y hc hs
    have hmap : Measure.map φ (κ y) = Measure.dirac y := by
      rw [← Kernel.map_apply κ hφ y, ← hc]
      have hid : (condDistrib (φ ∘ id) φ μ) y = (condDistrib φ φ μ) y := by
        congr 2
      rw [hid, hs, Kernel.id_apply]
    refine ⟨inferInstance, ?_⟩
    rw [← Measure.map_apply hφ (measurableSet_singleton y), hmap]
    exact Measure.dirac_apply_of_mem (Set.mem_singleton y)
  · intro B hB
    exact Kernel.measurable_coe κ hB
  · intro B hB
    have hbind := congrArg (fun m : Measure X => m B)
      (condDistrib_comp_map (μ := μ) hφ.aemeasurable measurable_id.aemeasurable)
    rw [Measure.map_id] at hbind
    simpa [κ, Measure.bind_apply hB (Kernel.measurable κ).aemeasurable] using hbind.symm
  · intro μy' hprob hmeas hdecomp
    let κ' : Kernel Y X := Kernel.mk μy'
      (Measure.measurable_of_measurable_coe μy' hmeas)
    have hprob' : ∀ᵐ y ∂Measure.map φ μ, IsProbabilityMeasure (κ' y) := by
      simpa [κ'] using hprob.mono fun y hy => hy.1
    have hμ0 : μ ≠ 0 := by
      intro hz
      have hu : μ Set.univ = 1 := measure_univ
      simp [hz] at hu
    have hmap0 : Measure.map φ μ ≠ 0 :=
      (Measure.map_eq_zero_iff hφ.aemeasurable).not.mpr hμ0
    obtain ⟨η, hκη, hη⟩ := Kernel.exists_ae_eq_isMarkovKernel hprob' hmap0
    have hjoint : Measure.map (fun x => (φ x, x)) μ = Measure.map φ μ ⊗ₘ η := by
      apply Measure.ext_prod
      intro s t hs ht
      rw [Measure.map_apply (Measurable.prod (f := fun x => (φ x, x)) hφ measurable_id)
        (hs.prod ht)]
      rw [Measure.compProd_apply_prod hs ht]
      change μ (φ ⁻¹' s ∩ t) = _
      have hB : MeasurableSet (φ ⁻¹' s ∩ t) := (hs.preimage hφ).inter ht
      rw [hdecomp (φ ⁻¹' s ∩ t) hB]
      rw [← lintegral_indicator hs]
      apply lintegral_congr_ae
      filter_upwards [hprob, hκη] with y hy hηy
      have hηval : η y t = μy' y t := by
        simpa [κ'] using congrArg (fun m : Measure X => m t) hηy.symm
      have hfmeas : MeasurableSet (φ ⁻¹' {y}) :=
        (measurableSet_singleton y).preimage hφ
      have haefiber : ∀ᵐ x ∂μy' y, x ∈ φ ⁻¹' {y} := by
        letI : IsProbabilityMeasure (μy' y) := hy.1
        rw [ae_iff]
        change μy' y (φ ⁻¹' {y})ᶜ = 0
        rw [measure_compl hfmeas (measure_ne_top _ _), hy.2]
        simp
      by_cases hys : y ∈ s
      · rw [Set.indicator_of_mem hys]
        rw [hηval]
        apply measure_congr
        filter_upwards [haefiber] with x hx
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
        apply propext
        constructor
        · exact fun h => h.2
        · exact fun hxt => ⟨by simpa [hx] using hys, hxt⟩
      · simp only [Set.indicator, hys, ↓reduceIte]
        have hnone : ∀ᵐ x ∂μy' y, x ∉ φ ⁻¹' s ∩ t := by
          filter_upwards [haefiber] with x hx
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
          intro hmem
          exact hys (by simpa [hx] using hmem.1)
        simpa only [not_not] using (ae_iff.mp hnone)
    have hcond : (condDistrib id φ μ : Y → Measure X) =ᵐ[Measure.map φ μ] η :=
      condDistrib_ae_eq_of_measure_eq_compProd φ measurable_id.aemeasurable hjoint
    exact hcond.trans (hκη.symm.trans (by rfl))

end Chapter00.Section03
