import Chapter00.Section02

noncomputable section

open Classical Filter

namespace Chapter00.Section03

private def familyMeasurableSpace {X : Type*} (A : SetFamily X)
    (hA : IsSigmaAlgebraFamily A) : MeasurableSpace X where
  MeasurableSet' := A
  measurableSet_empty := by
    simpa using hA.2.1 Set.univ hA.1
  measurableSet_compl := hA.2.1
  measurableSet_iUnion := hA.2.2

private theorem customCE_eq_condExp
    (P : BasicProbabilitySpaceData) (A : SetFamily P.X)
    (hA : IsSigmaAlgebraFamily A) (hsub : A ⊆ P.𝓧)
    (E : ConditionalExpectationData P A) (hE : IsConditionalExpectation P A E)
    (f : P.X → ℂ) (hf : MeasureTheory.Integrable f P.μ) :
    E.op f =ᵐ[P.μ]
      MeasureTheory.condExp (familyMeasurableSpace A hA) P.μ f := by
  let mA : MeasurableSpace P.X := familyMeasurableSpace A hA
  have hm : mA ≤ P.measurableSpace := by
    intro s hs
    exact hsub hs
  letI : MeasureTheory.SigmaFinite (P.μ.trim hm) := inferInstance
  obtain ⟨hEmeas, hEint, hEsets⟩ := hE f hf
  have hmeas : @Measurable P.X ℂ mA (borel ℂ) (E.op f) :=
    measurable_of_isClosed fun s hs => hEmeas s hs
  exact MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm hf
    (fun _ _ _ => hEint.integrableOn)
    (fun s hs _ => hEsets s hs) hmeas.aestronglyMeasurable

private theorem complex_norm_condExp_le
    {X : Type*} {m m0 : MeasurableSpace X} (mu : MeasureTheory.Measure X)
    (hm : m ≤ m0) [MeasureTheory.SigmaFinite (mu.trim hm)]
    (f : X → ℂ) (hf : MeasureTheory.Integrable f mu) :
    (fun x => ‖MeasureTheory.condExp m mu f x‖) ≤ᵐ[mu]
      MeasureTheory.condExp m mu (fun x => ‖f x‖) := by
  let z : X → ℂ := MeasureTheory.condExp m mu f
  let phase : X → ℂ := fun x =>
    if z x = 0 then 0 else star (z x) / (‖z x‖ : ℂ)
  have hzmeas : @MeasureTheory.StronglyMeasurable X ℂ _ m z := by
    exact MeasureTheory.stronglyMeasurable_condExp
  have hphasemeas : @MeasureTheory.StronglyMeasurable X ℂ _ m phase := by
    apply Measurable.stronglyMeasurable
    apply Measurable.ite
    · exact hzmeas.measurable (measurableSet_singleton 0)
    · exact measurable_const
    · exact (Complex.continuous_conj.measurable.comp hzmeas.measurable).div
        ((Complex.continuous_ofReal.comp continuous_norm).measurable.comp hzmeas.measurable)
  have hphase_norm : ∀ x, ‖phase x‖ ≤ 1 := by
    intro x
    by_cases hx : z x = 0
    · simp [phase, hx]
    · have hn : ‖z x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      simp [phase, hx, hn]
  have hphase_mul : ∀ x, (phase x * z x).re = ‖z x‖ := by
    intro x
    by_cases hx : z x = 0
    · simp [phase, hx]
    · have hn : ‖z x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      simp only [phase, if_neg hx]
      rw [div_mul_eq_mul_div]
      have hconj : star (z x) * z x = (Complex.normSq (z x) : ℂ) := by
        simpa using Complex.normSq_eq_conj_mul_self.symm
      rw [hconj, Complex.normSq_eq_norm_sq]
      norm_num [pow_two, hn]
  have hpoint : ∀ x, (phase x * f x).re ≤ ‖f x‖ := by
    intro x
    calc
      (phase x * f x).re ≤ ‖phase x * f x‖ := Complex.re_le_norm _
      _ = ‖phase x‖ * ‖f x‖ := norm_mul _ _
      _ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right (hphase_norm x) (norm_nonneg _)
      _ = ‖f x‖ := one_mul _
  have hphaseint : MeasureTheory.Integrable (fun x => phase x * f x) mu :=
    hf.bdd_mul (hphasemeas.mono hm).aestronglyMeasurable
      (Filter.Eventually.of_forall hphase_norm)
  have hpull := MeasureTheory.condExp_bilin_of_aestronglyMeasurable_left
    (m := m) (.mul ℝ ℂ) hphasemeas.aestronglyMeasurable hphaseint hf
  let reCLM : ℂ →L[ℝ] ℝ := Complex.reCLM
  have hre := reCLM.comp_condExp_comm hphaseint (m := m)
  have hmono := MeasureTheory.condExp_mono
    (m := m) (reCLM.integrable_comp hphaseint) hf.norm
      (Filter.Eventually.of_forall hpoint)
  filter_upwards [hpull, hre, hmono] with x hpullx hrex hmonox
  change ‖z x‖ ≤ MeasureTheory.condExp m mu (fun x => ‖f x‖) x
  calc
    ‖z x‖ = (phase x * z x).re := (hphase_mul x).symm
    _ = (MeasureTheory.condExp m mu (fun y => phase y * f y) x).re := by
      simpa only [ContinuousLinearMap.mul_apply, z] using congrArg Complex.re hpullx.symm
    _ = MeasureTheory.condExp m mu (fun y => (phase y * f y).re) x := hrex
    _ ≤ MeasureTheory.condExp m mu (fun y => ‖f y‖) x := hmonox

theorem conditionalExpectationExistsAux
    (P : BasicProbabilitySpaceData) (A : SetFamily P.X) :
    IsSigmaAlgebraFamily A -> A ⊆ P.𝓧 ->
      ∃ E : ConditionalExpectationData P A,
        IsConditionalExpectation P A E ∧
        (∀ f g : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
          MeasureTheory.Integrable g P.μ -> ∀ a b : ℂ,
          E.op (fun x => a * f x + b * g x) =ᵐ[P.μ]
            fun x => a * E.op f x + b * E.op g x) ∧
        (∀ f : P.X -> ℝ, MeasureTheory.Integrable f P.μ ->
          (∀ᵐ x ∂P.μ, 0 ≤ f x) ->
            ∀ᵐ x ∂P.μ, 0 ≤ (E.op (fun y => (f y : ℂ)) x).re) ∧
        (∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
          (∫ x, ‖E.op f x‖ ∂P.μ) ≤ ∫ x, ‖f x‖ ∂P.μ) ∧
        (∀ f g : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
          IsMeasurableForFamily A g ->
          MeasureTheory.Integrable (fun x => g x * f x) P.μ ->
          MeasureTheory.Integrable (fun x => g x * E.op f x) P.μ ->
          E.op (fun x => g x * f x) =ᵐ[P.μ] fun x => g x * E.op f x) ∧
        (∀ C : SetFamily P.X, C ⊆ A -> IsSigmaAlgebraFamily C ->
          ∀ EC : ConditionalExpectationData P C, IsConditionalExpectation P C EC ->
          ∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
            EC.op (E.op f) =ᵐ[P.μ] EC.op f) ∧
        (∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
          IsMeasurableForFamily A f -> E.op f =ᵐ[P.μ] f) ∧
        (∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
          ∀ᵐ x ∂P.μ, ‖E.op f x‖ ≤ (E.op (fun y => ‖f y‖) x).re) ∧
        ∀ E' : ConditionalExpectationData P A,
          IsConditionalExpectation P A E' ->
          ∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
            E.op f =ᵐ[P.μ] E'.op f := by
  intro hA hsub
  let mA : MeasurableSpace P.X := familyMeasurableSpace A hA
  have hm : mA ≤ P.measurableSpace := by
    intro s hs
    exact hsub hs
  letI : MeasureTheory.SigmaFinite (P.μ.trim hm) := inferInstance
  let E : ConditionalExpectationData P A :=
    ⟨fun f => MeasureTheory.condExp mA P.μ f⟩
  have hE : IsConditionalExpectation P A E := by
    intro f hf
    refine ⟨?_, MeasureTheory.integrable_condExp, ?_⟩
    · intro C hC
      change @MeasurableSet P.X mA
        ((MeasureTheory.condExp mA P.μ f) ⁻¹' C)
      exact MeasureTheory.stronglyMeasurable_condExp.measurable hC.measurableSet
    · intro B hBA
      exact MeasureTheory.setIntegral_condExp hm hf hBA
  refine ⟨E, hE, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g hf hg a b
    filter_upwards [MeasureTheory.condExp_add (hf.const_mul a) (hg.const_mul b) mA,
      MeasureTheory.condExp_smul a f mA,
      MeasureTheory.condExp_smul b g mA] with x hadd ha hb
    simpa [E, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hadd.trans (congrArg₂ (· + ·) ha hb)
  · intro f hf hnonneg
    let reCLM : ℂ →L[ℝ] ℝ := Complex.reCLM
    have hre := reCLM.comp_condExp_comm (hf.ofReal) (m := mA)
    have hpos := MeasureTheory.condExp_nonneg (m := mA) hnonneg
    filter_upwards [hre, hpos] with x hx hpx
    simpa [E, reCLM] using hpx.trans_eq hx.symm
  · intro f hf
    have hle := complex_norm_condExp_le P.μ hm f hf
    calc
      (∫ x, ‖E.op f x‖ ∂P.μ) ≤
          ∫ x, MeasureTheory.condExp mA P.μ (fun y => ‖f y‖) x ∂P.μ := by
        exact MeasureTheory.integral_mono_ae
          (MeasureTheory.integrable_condExp (m := mA) (μ := P.μ) (f := f)).norm
          (MeasureTheory.integrable_condExp (m := mA) (μ := P.μ)
            (f := fun y => ‖f y‖)) hle
      _ = ∫ x, ‖f x‖ ∂P.μ := MeasureTheory.integral_condExp hm
  · intro f g hf hgmeas hgf _hgfE
    have hgmeas' : @Measurable P.X ℂ mA (borel ℂ) g :=
      measurable_of_isClosed fun s hs => hgmeas s hs
    have hgstrong : @MeasureTheory.StronglyMeasurable P.X ℂ _ mA g :=
      hgmeas'.stronglyMeasurable
    simpa [E, Pi.mul_apply] using
      (MeasureTheory.condExp_bilin_of_aestronglyMeasurable_left
        (.mul ℝ ℂ) hgstrong.aestronglyMeasurable hgf hf)
  · intro C hCA hC EC hEC f hf
    let mC : MeasurableSpace P.X := familyMeasurableSpace C hC
    have hmC : mC ≤ P.measurableSpace := by
      intro s hs
      exact hsub (hCA hs)
    have hmCA : mC ≤ mA := by
      intro s hs
      exact hCA hs
    letI : MeasureTheory.SigmaFinite (P.μ.trim hmC) := inferInstance
    have hEC_outer := customCE_eq_condExp P C hC (fun _ hs => hsub (hCA hs)) EC hEC
      (E.op f) (hE f hf).2.1
    have hEC_f := customCE_eq_condExp P C hC (fun _ hs => hsub (hCA hs)) EC hEC f hf
    have htower := MeasureTheory.condExp_condExp_of_le
      (μ := P.μ) (m₁ := mC) (m₂ := mA) (m₀ := P.measurableSpace)
      (f := f) hmCA hm
    exact hEC_outer.trans (htower.trans hEC_f.symm)
  · intro f hf hfmeas
    have hfmeas' : @Measurable P.X ℂ mA (borel ℂ) f :=
      measurable_of_isClosed fun s hs => hfmeas s hs
    have hstrong : @MeasureTheory.StronglyMeasurable P.X ℂ _ mA f :=
      hfmeas'.stronglyMeasurable
    have heq := MeasureTheory.condExp_of_stronglyMeasurable hm hstrong hf
    exact Filter.Eventually.of_forall fun x => congrFun heq x
  · intro f hf
    have hnorm := complex_norm_condExp_le P.μ hm f hf
    let reCLM : ℂ →L[ℝ] ℝ := Complex.reCLM
    have hre := reCLM.comp_condExp_comm (hf.norm.ofReal) (m := mA)
    filter_upwards [hnorm, hre] with x hx hre
    simpa [E, reCLM] using hx.trans_eq hre.symm
  · intro E' hE' f hf
    exact (customCE_eq_condExp P A hA hsub E hE f hf).trans
      (customCE_eq_condExp P A hA hsub E' hE' f hf).symm

end Chapter00.Section03
