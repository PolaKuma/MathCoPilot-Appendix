import Chapter00.Probability.Section03ConditionalExpectation
import Mathlib.MeasureTheory.Function.FactorsThrough

noncomputable section

open Classical Filter

namespace Chapter00.Section03

theorem conditionalExpectationExtendsToL1Aux
    (P Q : BasicProbabilitySpaceData) (φ : P.X -> Q.X)
    (hφ : Measurable φ) (hpush : MeasureTheory.Measure.map φ P.μ = Q.μ) :
    ∃ E : (P.X -> ℂ) -> Q.X -> ℂ,
      (∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
        MeasureTheory.Integrable (E f) Q.μ) ∧
      (∀ f g : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
        MeasureTheory.Integrable g P.μ -> ∀ a b : ℂ,
        E (fun x => a * f x + b * g x) =ᵐ[Q.μ]
          fun y => a * E f y + b * E g y) ∧
      (∀ f : P.X -> ℝ, MeasureTheory.Integrable f P.μ ->
        (∀ᵐ x ∂P.μ, 0 ≤ f x) -> ∀ᵐ y ∂Q.μ, 0 ≤ (E (fun x => f x) y).re) ∧
      (∀ g : Q.X -> ℂ, MeasureTheory.Integrable g Q.μ ->
        E (g ∘ φ) =ᵐ[Q.μ] g) ∧
      (∀ f : P.X -> ℂ, ∀ g : Q.X -> ℂ,
        MeasureTheory.Integrable f P.μ -> MeasureTheory.Integrable g Q.μ ->
        MeasureTheory.Integrable (fun x => g (φ x) * f x) P.μ ->
        MeasureTheory.Integrable (fun y => g y * E f y) Q.μ ->
        E (fun x => g (φ x) * f x) =ᵐ[Q.μ] fun y => g y * E f y) ∧
      ∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
        ∫ x, f x ∂P.μ = ∫ y, E f y ∂Q.μ := by
  have hmp : MeasureTheory.MeasurePreserving φ P.μ Q.μ := ⟨hφ, hpush⟩
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving φ P.μ Q.μ :=
    hmp.quasiMeasurePreserving
  let mA : MeasurableSpace P.X := Q.measurableSpace.comap φ
  have hm : mA ≤ P.measurableSpace := hφ.comap_le
  letI : MeasureTheory.SigmaFinite (P.μ.trim hm) := inferInstance
  have hfactor : ∀ f : P.X → ℂ,
      ∃ e : Q.X → ℂ, MeasureTheory.StronglyMeasurable e ∧
        MeasureTheory.condExp mA P.μ f = e ∘ φ := by
    intro f
    exact MeasureTheory.StronglyMeasurable.exists_eq_measurable_comp
      (MeasureTheory.stronglyMeasurable_condExp (m := mA) (μ := P.μ) (f := f))
  choose E hEstrong hEcomp using hfactor
  have hae_iff {u v : Q.X → ℂ} (hu : MeasureTheory.StronglyMeasurable u)
      (hv : MeasureTheory.StronglyMeasurable v) :
      u =ᵐ[Q.μ] v ↔ u ∘ φ =ᵐ[P.μ] v ∘ φ := by
    rw [← hpush]
    have heq : MeasurableSet {y | u y = v y} := by
      change MeasurableSet ((fun y => (u y, v y)) ⁻¹' Set.diagonal ℂ)
      exact (Measurable.prod (f := fun y => (u y, v y))
        hu.measurable hv.measurable) measurableSet_diagonal
    exact MeasureTheory.ae_map_iff hφ.aemeasurable
      heq
  have pull_ae {u v : Q.X → ℂ} (huv : u =ᵐ[Q.μ] v) :
      u ∘ φ =ᵐ[P.μ] v ∘ φ := by
    exact @MeasureTheory.Measure.QuasiMeasurePreserving.ae_eq_comp
      P.X Q.X ℂ P.measurableSpace Q.measurableSpace P.μ Q.μ φ u v
      hqmp huv
  refine ⟨E, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    apply (hmp.integrable_comp (hEstrong f).aestronglyMeasurable).mp
    rw [← hEcomp f]
    exact MeasureTheory.integrable_condExp
  · intro f g hf hg a b
    apply (hae_iff (hEstrong _) ((hEstrong f).const_mul a |>.add
      ((hEstrong g).const_mul b))).mpr
    have hs :=
      (MeasureTheory.condExp_add (hf.const_mul a) (hg.const_mul b) mA).trans
        ((MeasureTheory.condExp_smul a f mA).add
          (MeasureTheory.condExp_smul b g mA))
    filter_upwards [hs] with x hx
    change E (fun x => a * f x + b * g x) (φ x) =
      a * E f (φ x) + b * E g (φ x)
    have hlin := congrFun (hEcomp (fun x => a * f x + b * g x)) x
    have hEf := congrFun (hEcomp f) x
    have hEg := congrFun (hEcomp g) x
    simp only [Function.comp_apply] at hlin hEf hEg
    rw [← hlin, ← hEf, ← hEg]
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hx
  · intro f hf hnonneg
    have hsrc := MeasureTheory.condExp_nonneg (m := mA) hnonneg
    have hre := Complex.reCLM.comp_condExp_comm (hf.ofReal) (m := mA)
    have hp : ∀ᵐ x ∂P.μ, 0 ≤ (E (fun x => (f x : ℂ)) (φ x)).re := by
      filter_upwards [hsrc, hre] with x hx hre
      have hEf := congrFun (hEcomp (fun x => (f x : ℂ))) x
      simp only [Function.comp_apply] at hEf
      rw [← hEf]
      exact hx.trans_eq hre.symm
    rw [← hpush]
    have hmeas : Measurable fun y => (E (fun x => (f x : ℂ)) y).re :=
      Complex.continuous_re.measurable.comp (hEstrong _).measurable
    exact (MeasureTheory.ae_map_iff hφ.aemeasurable
      (hmeas measurableSet_Ici)).mpr hp
  · intro g hg
    let gm : Q.X → ℂ := hg.1.mk g
    have hgm : MeasureTheory.StronglyMeasurable gm := hg.1.stronglyMeasurable_mk
    have hgmQ : gm =ᵐ[Q.μ] g := hg.1.ae_eq_mk.symm
    have hgmP : gm ∘ φ =ᵐ[P.μ] g ∘ φ := pull_ae hgmQ
    have hgmInt : MeasureTheory.Integrable gm Q.μ := hg.congr hgmQ.symm
    have hgmA : @MeasureTheory.StronglyMeasurable P.X ℂ _ mA (gm ∘ φ) :=
      hgm.comp_measurable (Measurable.of_comap_le le_rfl)
    have hcegm : MeasureTheory.condExp mA P.μ (gm ∘ φ) = gm ∘ φ :=
      MeasureTheory.condExp_of_stronglyMeasurable hm hgmA
        ((hmp.integrable_comp hgm.aestronglyMeasurable).mpr hgmInt)
    have hEm : E (g ∘ φ) =ᵐ[Q.μ] gm := by
      apply (hae_iff (hEstrong _) hgm).mpr
      have hc := MeasureTheory.condExp_congr_ae (m := mA) hgmP.symm
      filter_upwards [hc] with x hx
      rw [← congrFun (hEcomp (g ∘ φ)) x]
      exact hx.trans (congrFun hcegm x)
    exact hEm.trans hgmQ
  · intro f g hf hg hgf hprod
    let gm : Q.X → ℂ := hg.1.mk g
    have hgm : MeasureTheory.StronglyMeasurable gm := hg.1.stronglyMeasurable_mk
    have hgmQ : gm =ᵐ[Q.μ] g := hg.1.ae_eq_mk.symm
    have hgmP : gm ∘ φ =ᵐ[P.μ] g ∘ φ := pull_ae hgmQ
    have hinput : (fun x => g (φ x) * f x) =ᵐ[P.μ]
        fun x => gm (φ x) * f x := by
      filter_upwards [hgmP] with x hx
      exact congrArg (fun z => z * f x) hx.symm
    have hgf' : MeasureTheory.Integrable (fun x => gm (φ x) * f x) P.μ :=
      hgf.congr hinput
    have hgmA : @MeasureTheory.AEStronglyMeasurable P.X ℂ _ mA
        P.measurableSpace (gm ∘ φ) P.μ :=
      (hgm.comp_measurable (Measurable.of_comap_le le_rfl)).aestronglyMeasurable
    have hpull := MeasureTheory.condExp_bilin_of_aestronglyMeasurable_left
      (.mul ℝ ℂ) hgmA hgf' hf
    have hEm : E (fun x => g (φ x) * f x) =ᵐ[Q.μ]
        fun y => gm y * E f y := by
      apply (hae_iff (hEstrong _) (hgm.mul (hEstrong f))).mpr
      have hc := MeasureTheory.condExp_congr_ae (m := mA) hinput
      filter_upwards [hc, hpull] with x hc hp
      change E (fun x => g (φ x) * f x) (φ x) = gm (φ x) * E f (φ x)
      have hEin := congrFun (hEcomp (fun x => g (φ x) * f x)) x
      have hEf := congrFun (hEcomp f) x
      simp only [Function.comp_apply] at hEin hEf
      rw [← hEin, ← hEf]
      exact hc.trans hp
    exact hEm.trans (by
      filter_upwards [hgmQ] with y hy
      exact congrArg (fun z => z * E f y) hy)
  · intro f hf
    calc
      ∫ x, f x ∂P.μ = ∫ x, MeasureTheory.condExp mA P.μ f x ∂P.μ :=
        (MeasureTheory.integral_condExp hm).symm
      _ = ∫ x, (E f ∘ φ) x ∂P.μ := by rw [hEcomp]
      _ = ∫ x, E f (φ x) ∂P.μ := rfl
      _ = ∫ y, E f y ∂Q.μ := by
        rw [← hpush]
        exact (MeasureTheory.integral_map hφ.aemeasurable
          (hEstrong f).aestronglyMeasurable).symm

end Chapter00.Section03
