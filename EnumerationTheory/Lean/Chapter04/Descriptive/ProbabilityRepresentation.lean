import Chapter04.Descriptive.StandardBorel
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.CDF

noncomputable section

open Classical MeasureTheory ProbabilityTheory Set ENNReal unitInterval Filter Topology Function
open scoped ENNReal Topology

namespace Chapter04.ProbabilityRepresentation

universe u

/-- Injective measurable changes of coordinates preserve the absence of atoms.
This elementary lemma is used when the measure of a standard Borel probability
space is transported to the unit interval. -/
theorem map_singleton_eq_zero_of_injective
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β]
    (μ : Measure α) (f : α → β) (hf : Measurable f) (hinj : Injective f)
    (hμ : ∀ x, μ {x} = 0) (y : β) :
    (μ.map f) {y} = 0 := by
  rw [Measure.map_apply hf (MeasurableSet.singleton y)]
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    have hpreimage : f ⁻¹' {f x} = {x} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact hinj.eq_iff
    rw [hpreimage, hμ x]
  · have hpreimage : f ⁻¹' {y} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false]
      intro hxy
      exact hy ⟨x, hxy⟩
    rw [hpreimage, measure_empty]

/-- The cdf of an atomless real probability measure is continuous. -/
theorem continuous_cdf_of_singletons_eq_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ x, μ {x} = 0) :
    Continuous (cdf μ) := by
  rw [continuous_iff_continuousAt]
  intro x
  refine (monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim.mpr ?_
  have hcontinuous_right : ContinuousWithinAt (cdf μ) (Ioi x) x :=
    ((cdf μ).right_continuous x).mono (by exact Ioi_subset_Ici_self)
  have hright : rightLim (cdf μ) x = cdf μ x :=
    (monotone_cdf μ).continuousWithinAt_Ioi_iff_rightLim_eq.mp hcontinuous_right
  have hatom := StieltjesFunction.measure_singleton (cdf μ) x
  rw [measure_cdf μ, hμ x] at hatom
  have hdiff : cdf μ x - leftLim (cdf μ) x ≤ 0 := by
    simpa only [ENNReal.ofReal_eq_zero] using hatom.symm
  have hleft : leftLim (cdf μ) x = cdf μ x :=
    le_antisymm ((monotone_cdf μ).leftLim_le le_rfl) (sub_nonpos.mp hdiff)
  exact hleft.trans hright.symm

private def unitIntervalDistribution
    (μ : Measure I) [IsProbabilityMeasure μ] (x : I) : I :=
  ⟨μ.real (Icc 0 x), measureReal_nonneg, measureReal_le_one⟩

private def unitIntervalQuantile (μ : Measure I) (t : I) : I :=
  sSup {x : I | μ.real (Icc 0 x) < t}

private theorem unitIntervalQuantile_measurable_map
    (μ : Measure I) [IsProbabilityMeasure μ] :
    Measurable (unitIntervalQuantile μ) ∧
      volume.map (unitIntervalQuantile μ) = μ := by
  let f := unitIntervalQuantile μ
  have hmono : Monotone (fun x : I => μ.real (Icc 0 x)) :=
    fun x y hxy => measureReal_mono (by gcongr)
  have hf : Measurable f := by
    refine measurable_of_Ioi fun a => ?_
    have hs :
        {t : I | a < f t} =
          ⋃ (q : ℚ) (hqI : (q : ℝ) ∈ I) (_ : a < (q : ℝ)),
            {t : I | μ.real (Icc 0 ⟨q, hqI⟩) < t} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, f, unitIntervalQuantile]
      constructor
      · intro hat
        rw [lt_sSup_iff] at hat
        obtain ⟨y, hy, hay⟩ := hat
        have hay' : (a : ℝ) < (y : ℝ) := hay
        obtain ⟨q, haq, hqy⟩ := exists_rat_btwn hay'
        refine ⟨q, ?_, haq, ?_⟩
        · exact ⟨a.2.1.trans haq.le, hqy.le.trans y.2.2⟩
        · exact lt_of_le_of_lt (hmono hqy.le) hy
      · rintro ⟨q, hqI, haq, hqt⟩
        rw [lt_sSup_iff]
        exact ⟨⟨q, hqI⟩, hqt, haq⟩
    change MeasurableSet {t : I | a < f t}
    rw [hs]
    refine MeasurableSet.iUnion fun q =>
      MeasurableSet.iUnion fun hqI =>
        MeasurableSet.iUnion fun haq => ?_
    exact measurableSet_lt measurable_const measurable_subtype_coe
  refine ⟨hf, (volume.map f).ext_of_Iic μ fun x => ?_⟩
  have hxI : μ.real (Icc 0 x) ∈ I :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  rw [Measure.map_apply hf measurableSet_Iic]
  have hIic : Iic x = Icc 0 x := by
    ext y
    simp
  rw [← ofReal_measureReal (measure_ne_top μ (Iic x))]
  rw [show μ.real (Iic x) = μ.real (Icc 0 x) by rw [hIic]]
  rw [← unitInterval.volume_Iic ⟨μ.real (Icc 0 x), hxI⟩]
  congr 1
  ext t
  simp only [Set.mem_preimage, Set.mem_Iic]
  constructor
  · intro htx
    change t ≤ μ.real (Icc 0 x)
    by_cases hx : x = 1
    · simp [hx, ← univ_eq_Icc, t.2.2]
    let g := fun y : I => μ.real (Icc 0 y)
    letI : NeBot (𝓝[>] x) := by
      refine nhdsGT_neBot_of_exists_gt ?_
      exact ⟨1, lt_of_le_of_ne x.2.2 hx⟩
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] x) (g := g)
      continuousWithinAt_const ?_ ?_
    · let h := cdf (μ.map Subtype.val)
      have hc := continuousWithinAt_Ioi_iff_Ici.mpr (h.right_continuous x)
      simpa only [g, ← unitInterval.cdf_eq_real μ] using
        hc.comp (Continuous.continuousWithinAt continuous_subtype_val)
          (fun y hy => hy)
    · refine eventually_nhdsWithin_of_forall fun y hy => ?_
      by_contra! h
      simp only [sSup_le_iff, f, unitIntervalQuantile] at htx
      specialize htx y h
      grind
  · intro htx
    simp only [sSup_le_iff, f, unitIntervalQuantile]
    intro c hc
    by_contra! h
    have hnot :
        ¬ μ.real (Icc 0 x) ≤ μ.real (Icc 0 c) :=
      not_le.mpr (lt_of_le_of_lt' htx hc)
    refine hnot ?_
    gcongr
    simp

private theorem unitIntervalDistribution_continuous
    (μ : Measure I) [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0) :
    Continuous (unitIntervalDistribution μ) := by
  let ν := μ.map Subtype.val
  letI : IsProbabilityMeasure ν := by
    constructor
    dsimp [ν]
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
    simp
  have hν : ∀ x, ν {x} = 0 :=
    map_singleton_eq_zero_of_injective μ Subtype.val measurable_subtype_coe
      Subtype.val_injective hμ
  have hc := continuous_cdf_of_singletons_eq_zero ν hν
  have hr : Continuous (fun x : I => μ.real (Icc 0 x)) := by
    simpa only [← unitInterval.cdf_eq_real μ] using hc.comp continuous_subtype_val
  exact hr.subtype_mk _

private theorem unitIntervalDistribution_surjective
    (μ : Measure I) [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0) :
    Surjective (unitIntervalDistribution μ) := by
  have hzero : unitIntervalDistribution μ 0 = 0 := by
    apply Subtype.ext
    simp [unitIntervalDistribution, measureReal_def, hμ]
  have hone : unitIntervalDistribution μ 1 = 1 := by
    apply Subtype.ext
    simp [unitIntervalDistribution, ← univ_eq_Icc]
  intro t
  have ht :
      t ∈ Icc (unitIntervalDistribution μ 0) (unitIntervalDistribution μ 1) := by
    rw [hzero, hone]
    exact ⟨t.2.1, t.2.2⟩
  obtain ⟨x, -, hx⟩ :=
    (intermediate_value_Icc (a := (0 : I)) (b := 1) (by simp)
      (unitIntervalDistribution_continuous μ hμ).continuousOn) ht
  exact ⟨x, hx⟩

private theorem unitIntervalDistribution_quantile
    (μ : Measure I) [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0) (t : I) :
    unitIntervalDistribution μ (unitIntervalQuantile μ t) = t := by
  have hmono : Monotone (unitIntervalDistribution μ) := by
    intro x y hxy
    exact measureReal_mono (by gcongr)
  have hzero : unitIntervalDistribution μ 0 = 0 := by
    apply Subtype.ext
    simp [unitIntervalDistribution, measureReal_def, hμ]
  have himage :
      unitIntervalDistribution μ ''
          {x : I | unitIntervalDistribution μ x < t} =
        Iio t := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hz
      obtain ⟨x, rfl⟩ := unitIntervalDistribution_surjective μ hμ z
      exact ⟨x, hz, rfl⟩
  change
    unitIntervalDistribution μ
        (sSup {x : I | unitIntervalDistribution μ x < t}) = t
  rw [hmono.map_sSup_of_continuousAt
      (unitIntervalDistribution_continuous μ hμ).continuousAt hzero, himage]
  apply le_antisymm
  · exact sSup_le fun z hz => hz.le
  · by_contra h
    have hlt : sSup (Iio t) < t := lt_of_not_ge h
    obtain ⟨z, hz₁, hz₂⟩ := exists_between hlt
    exact (not_le_of_gt hz₁) (le_sSup hz₂)

/-- An atomless probability measure on the unit interval has the exact
distribution/quantile model required by Theorem 4.1.10. -/
theorem unitInterval_atomless_model
    (μ : Measure I) [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0) :
    ∃ e inv : I → I,
      Measurable e ∧ Measurable inv ∧
      (fun x => inv (e x)) =ᵐ[μ] id ∧
      (∀ t, e (inv t) = t) ∧
      ∀ B : Set I, MeasurableSet B →
        μ (e ⁻¹' B) = volume (Subtype.val '' B) := by
  let e := unitIntervalDistribution μ
  let inv := unitIntervalQuantile μ
  have he : Measurable e := (unitIntervalDistribution_continuous μ hμ).measurable
  obtain ⟨hinv, hinv_map⟩ := unitIntervalQuantile_measurable_map μ
  have hright : ∀ t, e (inv t) = t :=
    unitIntervalDistribution_quantile μ hμ
  have he_map : μ.map e = volume := by
    calc
      μ.map e = (volume.map inv).map e := by rw [hinv_map]
      _ = volume.map (e ∘ inv) := by
        rw [Measure.map_map he hinv]
      _ = volume := by
        rw [show e ∘ inv = id by funext t; exact hright t, Measure.map_id]
  have hleft : (fun x => inv (e x)) =ᵐ[μ] id := by
    rw [← hinv_map]
    refine (MeasureTheory.ae_map_iff hinv.aemeasurable
      (measurableSet_eq_fun (hinv.comp he) measurable_id)).mpr ?_
    exact Filter.Eventually.of_forall fun t => congrArg inv (hright t)
  refine ⟨e, inv, he, hinv, hleft, hright, ?_⟩
  intro B hB
  rw [← Measure.map_apply he hB, he_map, unitInterval.volume_apply]

private theorem unitInterval_not_countable : ¬ Countable I := by
  intro hI
  letI : Countable I := hI
  have hR : Countable ℝ := unitInterval.sigmoid_injective.countable
  exact (not_countable_iff.mpr inferInstance) hR

private theorem not_countable_of_atomless_probability
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0) :
    ¬ Countable α := by
  intro hα
  letI : Countable α := hα
  have hzero : μ = 0 := by
    apply Measure.ext_of_singleton
    intro x
    simpa using hμ x
  have hone := measure_univ (μ := μ)
  rw [hzero] at hone
  simpa using hone

private theorem transport_unitInterval_model
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (b : α ≃ᵐ I)
    (hlocal :
      ∃ eI invI : I → I,
        Measurable eI ∧ Measurable invI ∧
        (fun x => invI (eI x)) =ᵐ[μ.map b] id ∧
        (∀ t, eI (invI t) = t) ∧
        ∀ B : Set I, MeasurableSet B →
          (μ.map b) (eI ⁻¹' B) = volume (Subtype.val '' B)) :
    ∃ e : α → I, ∃ inv : I → α,
      Measurable e ∧ Measurable inv ∧
      (fun x => inv (e x)) =ᵐ[μ] id ∧
      (∀ t, e (inv t) = t) ∧
      ∀ B : Set I, MeasurableSet B →
        μ (e ⁻¹' B) = volume (Subtype.val '' B) := by
  obtain ⟨eI, invI, heI, hinvI, hleftI, hrightI, hmeasureI⟩ := hlocal
  let e := eI ∘ b
  let inv := b.symm ∘ invI
  have he : Measurable e := heI.comp b.measurable
  have hinv : Measurable inv := b.symm.measurable.comp hinvI
  have hpull :
      (fun x => invI (eI (b x))) =ᵐ[μ] fun x => b x := by
    refine (MeasureTheory.ae_map_iff b.measurable.aemeasurable
      (measurableSet_eq_fun (hinvI.comp heI) measurable_id)).mp ?_
    simpa only [Function.comp_apply, id_eq] using hleftI
  have hleft : (fun x => inv (e x)) =ᵐ[μ] id := by
    filter_upwards [hpull] with x hx
    simp only [inv, e, Function.comp_apply, id_eq]
    rw [hx, b.symm_apply_apply]
  have hright : ∀ t, e (inv t) = t := by
    intro t
    simp only [e, inv, Function.comp_apply, b.apply_symm_apply]
    exact hrightI t
  refine ⟨e, inv, he, hinv, hleft, hright, ?_⟩
  intro B hB
  have hpre : MeasurableSet (eI ⁻¹' B) := heI hB
  calc
    μ (e ⁻¹' B) = μ (b ⁻¹' (eI ⁻¹' B)) := by rfl
    _ = (μ.map b) (eI ⁻¹' B) := by
      rw [Measure.map_apply b.measurable hpre]
    _ = volume (Subtype.val '' B) := hmeasureI B hB

/-- Full atomless standard-Borel probability classification used in Theorem
4.1.10, obtained by transporting the interval distribution/quantile model. -/
theorem atomless_standardBorel_unitInterval_model
    (P : ProbabilitySpace.{u}) (hP : IsLebesgueProbabilitySpace P)
    (hC : IsContinuousProbabilityMeasure P) :
    IsLebesgueUnitIntervalModel P := by
  letI : StandardBorelSpace P.X :=
    StandardBorel.instanceOfData
      { X := P.X, measurableSpace := P.measurableSpace } hP.2
  letI : IsProbabilityMeasure P.μ := hP.1
  have hX : ¬ Countable P.X :=
    not_countable_of_atomless_probability P.μ hC.2
  let b : P.X ≃ᵐ I :=
    PolishSpace.measurableEquivOfNotCountable hX unitInterval_not_countable
  let μI : Measure I := P.μ.map b
  letI : IsProbabilityMeasure μI := by
    constructor
    dsimp [μI]
    rw [Measure.map_apply b.measurable MeasurableSet.univ]
    simpa using hP.1.measure_univ
  have hμI : ∀ t, μI {t} = 0 :=
    map_singleton_eq_zero_of_injective P.μ b b.measurable b.injective hC.2
  exact transport_unitInterval_model P.μ b
    (unitInterval_atomless_model μI hμI)

/-- A probability measure on one of the chapter's standard Borel spaces is a
measurable image of Lebesgue measure on the unit interval.

This is the forward (measure-representation) half of Theorem 4.1.10.  The
atomlessness hypothesis of that theorem is needed only for upgrading this map
to a mod-null isomorphism. -/
theorem exists_unitInterval_map
    (P : ProbabilitySpace.{u}) (hP : IsLebesgueProbabilitySpace P) :
    ∃ f : Set.Icc (0 : ℝ) 1 → P.X,
      Measurable f ∧ Measure.map f volume = P.μ := by
  letI : StandardBorelSpace P.X :=
    StandardBorel.instanceOfData
      { X := P.X, measurableSpace := P.measurableSpace } hP.2
  letI : IsProbabilityMeasure P.μ := hP.1
  have hne : Nonempty P.X := by
    by_contra h
    letI : IsEmpty P.X := ⟨fun x => h ⟨x⟩⟩
    have huniv : (Set.univ : Set P.X) = ∅ := by
      ext x
      exact False.elim (isEmptyElim x)
    have := hP.1.measure_univ
    rw [huniv, measure_empty] at this
    exact zero_ne_one this
  letI : Nonempty P.X := hne
  let g := unitInterval.sigmoid ∘ embeddingReal P.X
  have hg : MeasurableEmbedding g :=
    measurableEmbedding_sigmoid_comp_embeddingReal P.X
  let μg : Measure I := P.μ.map g
  letI : IsProbabilityMeasure μg := by
    constructor
    dsimp [μg]
    rw [Measure.map_apply hg.measurable MeasurableSet.univ]
    simpa using hP.1.measure_univ
  obtain ⟨hf, hmap⟩ := unitIntervalQuantile_measurable_map μg
  refine ⟨fun t => hg.invFun (unitIntervalQuantile μg t), by fun_prop, ?_⟩
  calc
    Measure.map (fun t => hg.invFun (unitIntervalQuantile μg t)) volume =
        Measure.map hg.invFun (Measure.map (unitIntervalQuantile μg) volume) := by
          rw [Measure.map_map (by fun_prop) hf]
          rfl
    _ = Measure.map hg.invFun μg := by rw [hmap]
    _ = P.μ := by
      dsimp [μg]
      rw [Measure.map_map (by fun_prop) hg.measurable]
      have hcomp : hg.invFun ∘ g = id :=
        funext hg.leftInverse_invFun
      rw [hcomp, Measure.map_id]

end Chapter04.ProbabilityRepresentation
