import Chapter01.Coding.BinaryCoding

noncomputable section

open Classical
open scoped BigOperators ENNReal NNReal

namespace Chapter01

noncomputable def cauchyUniformCoordinate (x : ℝ) : ℝ :=
  (Real.arctan x + Real.pi / 2) / Real.pi

theorem cauchyUniformCoordinate_continuous :
    Continuous cauchyUniformCoordinate := by
  unfold cauchyUniformCoordinate
  fun_prop

theorem cauchyUniformCoordinate_mem (x : ℝ) :
    cauchyUniformCoordinate x ∈ Set.Ioo (0 : ℝ) 1 := by
  rcases Real.arctan_mem_Ioo x with ⟨hx0, hx1⟩
  unfold cauchyUniformCoordinate
  constructor
  · exact div_pos (by linarith) Real.pi_pos
  · exact (div_lt_one Real.pi_pos).2 (by linarith)

private theorem arctan_le_iff {x y : ℝ} :
    Real.arctan x ≤ Real.arctan y ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hn
    have hlt := Real.arctan_lt_arctan (lt_of_not_ge hn)
    linarith
  · exact Real.arctan_le_arctan

private theorem cauchyUniformCoordinate_preimage_Iic {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    cauchyUniformCoordinate ⁻¹' Set.Iic t =
      Set.Iic (Real.tan (Real.pi * t - Real.pi / 2)) := by
  let a := Real.pi * t - Real.pi / 2
  have ha0 : -(Real.pi / 2) < a := by
    dsimp [a]
    nlinarith [Real.pi_pos]
  have ha1 : a < Real.pi / 2 := by
    dsimp [a]
    nlinarith [Real.pi_pos]
  have hat : Real.arctan (Real.tan a) = a := Real.arctan_tan ha0 ha1
  ext x
  simp only [Set.mem_preimage, Set.mem_Iic]
  constructor
  · intro hx
    apply arctan_le_iff.mp
    rw [hat]
    unfold cauchyUniformCoordinate at hx
    dsimp [a]
    have hpi := Real.pi_pos
    have h := (div_le_iff₀ hpi).mp hx
    nlinarith
  · intro hx
    have harc := arctan_le_iff.mpr hx
    rw [hat] at harc
    unfold cauchyUniformCoordinate
    dsimp [a] at harc
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith

theorem cauchyMeasure_Iic (x : ℝ) :
    cauchyMeasure (Set.Iic x) =
      ENNReal.ofReal ((Real.arctan x + Real.pi / 2) / Real.pi) := by
  rw [cauchyMeasure, MeasureTheory.withDensity_apply _ measurableSet_Iic]
  have hfun : (fun t : ℝ => (Real.pi * (1 + t ^ 2))⁻¹) =
      fun t : ℝ => Real.pi⁻¹ * (1 + t ^ 2)⁻¹ := by
    funext t
    rw [mul_inv_rev]
    exact mul_comm _ _
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => (Real.pi * (1 + t ^ 2))⁻¹) (Set.Iic x)
      MeasureTheory.volume := by
    rw [hfun]
    exact (integrable_inv_one_add_sq.const_mul Real.pi⁻¹).integrableOn
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Iic x)]
      (fun t : ℝ => (Real.pi * (1 + t ^ 2))⁻¹) := by
    filter_upwards with t
    positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  congr 1
  rw [hfun, MeasureTheory.integral_const_mul,
    integral_Iic_inv_one_add_sq]
  field_simp [Real.pi_ne_zero]

theorem cauchyMeasure_univ : cauchyMeasure Set.univ = 1 := by
  rw [cauchyMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  have hfun : (fun t : ℝ => (Real.pi * (1 + t ^ 2))⁻¹) =
      fun t : ℝ => Real.pi⁻¹ * (1 + t ^ 2)⁻¹ := by
    funext t
    rw [mul_inv_rev]
    exact mul_comm _ _
  have hint : MeasureTheory.Integrable
      (fun t : ℝ => (Real.pi * (1 + t ^ 2))⁻¹) MeasureTheory.volume := by
    rw [hfun]
    exact integrable_inv_one_add_sq.const_mul Real.pi⁻¹
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume]
      (fun t : ℝ => (Real.pi * (1 + t ^ 2))⁻¹) := by
    filter_upwards with t
    positivity
  simp only [MeasureTheory.Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [hfun, MeasureTheory.integral_const_mul,
    integral_univ_inv_one_add_sq]
  field_simp [Real.pi_ne_zero]
  norm_num

theorem cauchyUniformCoordinate_map :
    MeasureTheory.Measure.map cauchyUniformCoordinate cauchyMeasure =
      MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1) := by
  letI : MeasureTheory.IsProbabilityMeasure cauchyMeasure := ⟨cauchyMeasure_univ⟩
  apply MeasureTheory.Measure.ext_of_Iic
  intro t
  rw [MeasureTheory.Measure.map_apply cauchyUniformCoordinate_continuous.measurable
    measurableSet_Iic, MeasureTheory.Measure.restrict_apply measurableSet_Iic]
  by_cases ht0 : t ≤ 0
  · have hpre : cauchyUniformCoordinate ⁻¹' Set.Iic t = (∅ : Set ℝ) := by
      ext x
      have hx := (cauchyUniformCoordinate_mem x).1
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false]
      constructor
      · intro h
        exact (not_lt_of_ge (le_trans h ht0)) hx
      · intro h
        contradiction
    have hinter : Set.Iic t ∩ Set.Ioc (0 : ℝ) 1 = (∅ : Set ℝ) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc,
        Set.mem_empty_iff_false]
      constructor
      · rintro ⟨hxt, hx0, hx1⟩
        exact (not_lt_of_ge (le_trans hxt ht0)) hx0
      · intro h
        contradiction
    rw [hpre, hinter]
    simp
  · have ht0' : 0 < t := lt_of_not_ge ht0
    by_cases ht1 : 1 ≤ t
    · have hpre : cauchyUniformCoordinate ⁻¹' Set.Iic t = Set.univ := by
        ext x
        have hx := (cauchyUniformCoordinate_mem x).2
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
        linarith
      have hinter : Set.Iic t ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioc 0 1 := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨le_trans h.2 ht1, h⟩
      rw [hpre, hinter, cauchyMeasure_univ, Real.volume_Ioc]
      norm_num
    · have ht1' : t < 1 := lt_of_not_ge ht1
      rw [cauchyUniformCoordinate_preimage_Iic ht0' ht1', cauchyMeasure_Iic]
      have ha0 : -(Real.pi / 2) < Real.pi * t - Real.pi / 2 := by
        nlinarith [Real.pi_pos]
      have ha1 : Real.pi * t - Real.pi / 2 < Real.pi / 2 := by
        nlinarith [Real.pi_pos]
      rw [Real.arctan_tan ha0 ha1]
      have hinter : Set.Iic t ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioc 0 t := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
        constructor
        · exact fun h => ⟨h.2.1, h.1⟩
        · intro h
          exact ⟨h.2, h.1, le_trans h.2 (le_of_lt ht1')⟩
      rw [hinter, Real.volume_Ioc]
      congr 1
      field_simp [Real.pi_ne_zero]
      ring

noncomputable def cauchyToCircle (x : ℝ) : AddCircle (1 : ℝ) :=
  (cauchyUniformCoordinate x : AddCircle (1 : ℝ))

noncomputable def cauchyFromCircle (y : AddCircle (1 : ℝ)) : ℝ :=
  Real.tan (Real.pi * circleIcoRepresentative y - Real.pi / 2)

theorem cauchyToCircle_measurable : Measurable cauchyToCircle := by
  exact AddCircle.measurable_mk'.comp cauchyUniformCoordinate_continuous.measurable

theorem cauchyFromCircle_measurable : Measurable cauchyFromCircle := by
  unfold cauchyFromCircle
  have harg : Measurable (fun y : AddCircle (1 : ℝ) =>
      Real.pi * circleIcoRepresentative y - Real.pi / 2) :=
    (measurable_const.mul circleIcoRepresentative_measurable).sub measurable_const
  simpa only [Real.tan_eq_sin_div_cos] using harg.sin.div harg.cos

theorem cauchyToCircle_map :
    MeasureTheory.Measure.map cauchyToCircle cauchyMeasure =
      AddCircle.haarAddCircle := by
  rw [show cauchyToCircle =
      ((↑) : ℝ → AddCircle (1 : ℝ)) ∘ cauchyUniformCoordinate by rfl,
    ← MeasureTheory.Measure.map_map AddCircle.measurable_mk'
      cauchyUniformCoordinate_continuous.measurable,
    cauchyUniformCoordinate_map]
  have hvol :
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
        AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  rw [← hvol]
  simpa only [zero_add] using
    (AddCircle.measurePreserving_mk (1 : ℝ) (0 : ℝ)).map_eq

private theorem circleIocRepresentative_cauchyToCircle (x : ℝ) :
    circleIcoRepresentative (cauchyToCircle x) = cauchyUniformCoordinate x := by
  let q := AddCircle.measurableEquivIoc 1 0
  let z : Set.Ioc (0 : ℝ) (0 + 1) :=
    ⟨cauchyUniformCoordinate x, (cauchyUniformCoordinate_mem x).1,
      by simpa using le_of_lt (cauchyUniformCoordinate_mem x).2⟩
  have hq : q (cauchyToCircle x) = z := by
    apply q.symm.injective
    rw [q.symm_apply_apply]
    change cauchyToCircle x = ((z.1 : ℝ) : AddCircle (1 : ℝ))
    rfl
  exact congrArg Subtype.val hq

theorem cauchyFromCircle_toCircle (x : ℝ) :
    cauchyFromCircle (cauchyToCircle x) = x := by
  unfold cauchyFromCircle
  rw [circleIocRepresentative_cauchyToCircle]
  unfold cauchyUniformCoordinate
  have hpi := Real.pi_ne_zero
  rw [show Real.pi * ((Real.arctan x + Real.pi / 2) / Real.pi) -
      Real.pi / 2 = Real.arctan x by field_simp; ring]
  exact Real.tan_arctan x

theorem cauchyToCircle_fromCircle {y : AddCircle (1 : ℝ)} (hy : y ≠ 0) :
    cauchyToCircle (cauchyFromCircle y) = y := by
  let r := circleIcoRepresentative y
  have hr := circleIcoRepresentative_mem y
  have hr1 : r < 1 := by
    apply lt_of_le_of_ne hr.2
    intro heq
    have hcoe := circleIcoRepresentative_coe y
    change circleIcoRepresentative y = 1 at heq
    rw [heq] at hcoe
    apply hy
    calc
      y = (((1 : ℝ) : AddCircle (1 : ℝ))) := hcoe.symm
      _ = 0 := by simp
  let a := Real.pi * r - Real.pi / 2
  have ha0 : -(Real.pi / 2) < a := by
    dsimp [a]
    nlinarith [Real.pi_pos, hr.1]
  have ha1 : a < Real.pi / 2 := by
    dsimp [a]
    nlinarith [Real.pi_pos, hr1]
  unfold cauchyToCircle cauchyFromCircle cauchyUniformCoordinate
  rw [Real.arctan_tan ha0 ha1]
  have hreal : (a + Real.pi / 2) / Real.pi = r := by
    dsimp [a]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hreal]
  exact circleIcoRepresentative_coe y

private theorem tan_two_mul_sub_pi_div_two (a : ℝ) (ha : Real.tan a ≠ 0) :
    Real.tan (2 * a - Real.pi / 2) =
      (Real.tan a - (Real.tan a)⁻¹) / 2 := by
  have hcos : Real.cos a ≠ 0 := by
    intro h
    apply ha
    rw [Real.tan_eq_sin_div_cos, h]
    simp
  have hsin : Real.sin a ≠ 0 := by
    intro h
    apply ha
    rw [Real.tan_eq_sin_div_cos, h]
    simp
  have hden : 2 * Real.sin a * Real.cos a ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hsin) hcos
  rw [Real.tan_eq_sin_div_cos, Real.sin_sub, Real.cos_sub,
    Real.sin_two_mul, Real.cos_two_mul, Real.sin_pi_div_two,
    Real.cos_pi_div_two, Real.tan_eq_sin_div_cos]
  have hsq := Real.sin_sq_add_cos_sq a
  field_simp [hcos, hsin, hden]
  linear_combination (-2 * Real.sin a * Real.cos a) * hsq

def circleNondyadicSet : Set (AddCircle (1 : ℝ)) :=
  {y | ∀ n : ℕ, circleTimes (2 ^ n) y ≠ 0}

theorem circleNondyadicSet_measurable : MeasurableSet circleNondyadicSet := by
  rw [show circleNondyadicSet =
      ⋂ n : ℕ, (circleTimes (2 ^ n)) ⁻¹' ({0} : Set (AddCircle (1 : ℝ)))ᶜ by
    ext y
    simp [circleNondyadicSet]]
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.preimage
  · exact MeasurableSet.compl (MeasurableSet.singleton 0)
  · unfold circleTimes
    fun_prop

theorem circleNondyadicSet_measure :
    AddCircle.haarAddCircle circleNondyadicSet = 1 := by
  have hvol :
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
        AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  have hzero : AddCircle.haarAddCircle ({0} : Set (AddCircle (1 : ℝ))) = 0 := by
    let q : AddCircle (1 : ℝ) ≃ᵐ Set.Ioc (0 : ℝ) (0 + 1) :=
      AddCircle.measurableEquivIoc 1 0
    have hq : MeasureTheory.MeasurePreserving q AddCircle.haarAddCircle
        (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) := by
      rw [← hvol]
      simpa [q] using (AddCircle.measurePreserving_equivIoc (1 : ℝ) (a := 0))
    have hs : MeasurableSet ({q 0} : Set (Set.Ioc (0 : ℝ) (0 + 1))) :=
      MeasurableSet.singleton _
    rw [show ({0} : Set (AddCircle (1 : ℝ))) = q ⁻¹' {q 0} by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact q.injective.eq_iff.symm]
    rw [hq.measure_preimage hs.nullMeasurableSet]
    rw [MeasureTheory.Measure.comap_apply Subtype.val Subtype.val_injective
      (fun t ht => measurableSet_Ioc.subtype_image ht) MeasureTheory.volume hs]
    simp
  have hnull : AddCircle.haarAddCircle circleNondyadicSetᶜ = 0 := by
    rw [show circleNondyadicSetᶜ =
        ⋃ n : ℕ, (circleTimes (2 ^ n)) ⁻¹' ({0} : Set (AddCircle (1 : ℝ))) by
      ext y
      simp [circleNondyadicSet]]
    apply MeasureTheory.measure_iUnion_null
    intro n
    have hnz : ((2 ^ n : ℕ) : ℤ) ≠ 0 := by positivity
    have hmp :=
      (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle (1 : ℝ))).measurePreserving_zsmul hnz
    exact hmp.preimage_null hzero
  calc
    AddCircle.haarAddCircle circleNondyadicSet =
        AddCircle.haarAddCircle circleNondyadicSet +
          AddCircle.haarAddCircle circleNondyadicSetᶜ := by rw [hnull, add_zero]
    _ = AddCircle.haarAddCircle (circleNondyadicSet ∪ circleNondyadicSetᶜ) := by
      rw [MeasureTheory.measure_union]
      · exact Set.disjoint_left.mpr (by
          intro x hx hxc
          exact hxc hx)
      · exact circleNondyadicSet_measurable.compl
    _ = 1 := by simp

theorem circleNondyadicSet_compl_measure :
    AddCircle.haarAddCircle circleNondyadicSetᶜ = 0 := by
  rw [MeasureTheory.measure_compl circleNondyadicSet_measurable]
  · rw [circleNondyadicSet_measure]
    simp
  · rw [circleNondyadicSet_measure]
    norm_num

theorem circleNondyadicSet_invariant {y : AddCircle (1 : ℝ)}
    (hy : y ∈ circleNondyadicSet) :
    circleTimes 2 y ∈ circleNondyadicSet := by
  intro n hn
  apply hy (n + 1)
  rw [← circleOrbit_succ y n]
  rw [show circleTimes (2 ^ n) (circleTimes 2 y) =
      circleTimes 2 (circleTimes (2 ^ n) y) by
    unfold circleTimes
    rw [← mul_nsmul, ← mul_nsmul, mul_comm]] at hn
  exact hn

theorem circleNondyadicSet_ne_zero {y : AddCircle (1 : ℝ)}
    (hy : y ∈ circleNondyadicSet) : y ≠ 0 := by
  simpa [circleTimes] using hy 0

def cauchyCanonicalSet : Set ℝ := cauchyToCircle ⁻¹' circleNondyadicSet

theorem cauchyCanonicalSet_measurable : MeasurableSet cauchyCanonicalSet := by
  exact circleNondyadicSet_measurable.preimage cauchyToCircle_measurable

theorem cauchyCanonicalSet_measure : cauchyMeasure cauchyCanonicalSet = 1 := by
  have hφ : MeasureTheory.MeasurePreserving cauchyToCircle cauchyMeasure
      AddCircle.haarAddCircle :=
    ⟨cauchyToCircle_measurable, cauchyToCircle_map⟩
  exact (hφ.measure_preimage circleNondyadicSet_measurable.nullMeasurableSet).trans
    circleNondyadicSet_measure

theorem cauchyCanonicalSet_compl_measure : cauchyMeasure cauchyCanonicalSetᶜ = 0 := by
  have hφ : MeasureTheory.MeasurePreserving cauchyToCircle cauchyMeasure
      AddCircle.haarAddCircle :=
    ⟨cauchyToCircle_measurable, cauchyToCircle_map⟩
  change cauchyMeasure (cauchyToCircle ⁻¹' circleNondyadicSetᶜ) = 0
  exact hφ.preimage_null circleNondyadicSet_compl_measure

theorem cauchyFromCircle_map :
    MeasureTheory.Measure.map cauchyFromCircle AddCircle.haarAddCircle =
      cauchyMeasure := by
  rw [← cauchyToCircle_map,
    MeasureTheory.Measure.map_map cauchyFromCircle_measurable
      cauchyToCircle_measurable]
  rw [show cauchyFromCircle ∘ cauchyToCircle = id by
    funext x
    exact cauchyFromCircle_toCircle x]
  exact MeasureTheory.Measure.map_id

theorem cauchyDoublingMap_measurable : Measurable cauchyDoublingMap := by
  unfold cauchyDoublingMap
  apply Measurable.ite (MeasurableSet.singleton 0)
  · exact measurable_const
  · exact (measurable_id.sub measurable_id.inv).div_const 2

theorem cauchyFromCircle_dynamics {y : AddCircle (1 : ℝ)}
    (hy : y ∈ circleNondyadicSet) :
    cauchyFromCircle (circleTimes 2 y) =
      cauchyDoublingMap (cauchyFromCircle y) := by
  have hy0 : y ≠ 0 := circleNondyadicSet_ne_zero hy
  have hy2mem : circleTimes 2 y ∈ circleNondyadicSet :=
    circleNondyadicSet_invariant hy
  have hy20 : circleTimes 2 y ≠ 0 := circleNondyadicSet_ne_zero hy2mem
  have hx0 : cauchyFromCircle y ≠ 0 := by
    intro hx
    have hto : cauchyToCircle 0 = y := by
      rw [← cauchyToCircle_fromCircle hy0, hx]
    apply hy20
    rw [← hto]
    have hr0 := circleIocRepresentative_cauchyToCircle 0
    have hhalf : cauchyUniformCoordinate 0 = (1 / 2 : ℝ) := by
      unfold cauchyUniformCoordinate
      rw [Real.arctan_zero]
      field_simp [Real.pi_ne_zero]
      ring
    rw [hhalf] at hr0
    have hd := circleIcoRepresentative_double (cauchyToCircle 0)
    rw [hr0] at hd
    norm_num at hd
    have hcoe := circleIcoRepresentative_coe (circleTimes 2 (cauchyToCircle 0))
    rw [hd] at hcoe
    exact hcoe.symm.trans (by simp)
  let r := circleIcoRepresentative y
  let a := Real.pi * r - Real.pi / 2
  have htrig : Real.tan (2 * a - Real.pi / 2) =
      (Real.tan a - (Real.tan a)⁻¹) / 2 := by
    apply tan_two_mul_sub_pi_div_two
    simpa [a, r, cauchyFromCircle] using hx0
  unfold cauchyDoublingMap
  rw [if_neg hx0]
  unfold cauchyFromCircle
  rw [circleIcoRepresentative_double]
  change Real.tan
      (Real.pi * (if r ≤ 1 / 2 then 2 * r else 2 * r - 1) - Real.pi / 2) =
    (Real.tan a - (Real.tan a)⁻¹) / 2
  by_cases hr : r ≤ 1 / 2
  · rw [if_pos hr]
    rw [show Real.pi * (2 * r) - Real.pi / 2 =
        (2 * a - Real.pi / 2) + Real.pi by
      dsimp [a]
      ring, Real.tan_add_pi]
    exact htrig
  · rw [if_neg hr]
    rw [show Real.pi * (2 * r - 1) - Real.pi / 2 =
        2 * a - Real.pi / 2 by
      dsimp [a]
      ring]
    exact htrig

theorem cauchyToCircle_dynamics {x : ℝ} (hx : x ∈ cauchyCanonicalSet) :
    cauchyToCircle (cauchyDoublingMap x) =
      circleTimes 2 (cauchyToCircle x) := by
  have hy : cauchyToCircle x ∈ circleNondyadicSet := hx
  have hy2 : circleTimes 2 (cauchyToCircle x) ∈ circleNondyadicSet :=
    circleNondyadicSet_invariant hy
  have hdyn := cauchyFromCircle_dynamics hy
  have hleft : cauchyFromCircle (cauchyToCircle x) = x :=
    cauchyFromCircle_toCircle x
  rw [hleft] at hdyn
  calc
    cauchyToCircle (cauchyDoublingMap x) =
        cauchyToCircle
          (cauchyFromCircle (circleTimes 2 (cauchyToCircle x))) := by rw [hdyn]
    _ = circleTimes 2 (cauchyToCircle x) :=
      cauchyToCircle_fromCircle (circleNondyadicSet_ne_zero hy2)

theorem cauchyCanonicalSet_invariant {x : ℝ} (hx : x ∈ cauchyCanonicalSet) :
    cauchyDoublingMap x ∈ cauchyCanonicalSet := by
  change cauchyToCircle (cauchyDoublingMap x) ∈ circleNondyadicSet
  rw [cauchyToCircle_dynamics hx]
  exact circleNondyadicSet_invariant hx

theorem cauchyDoublingMap_measurePreserving :
    MeasureTheory.MeasurePreserving cauchyDoublingMap cauchyMeasure
      cauchyMeasure := by
  refine ⟨cauchyDoublingMap_measurable, ?_⟩
  apply MeasureTheory.Measure.ext
  intro B hB
  rw [MeasureTheory.Measure.map_apply cauchyDoublingMap_measurable hB,
    ← cauchyFromCircle_map,
    MeasureTheory.Measure.map_apply cauchyFromCircle_measurable
      (cauchyDoublingMap_measurable hB),
    MeasureTheory.Measure.map_apply cauchyFromCircle_measurable hB]
  have hae : ∀ᵐ y ∂AddCircle.haarAddCircle, y ∈ circleNondyadicSet := by
    apply MeasureTheory.ae_iff.mpr
    exact circleNondyadicSet_compl_measure
  calc
    AddCircle.haarAddCircle
        (cauchyFromCircle ⁻¹' (cauchyDoublingMap ⁻¹' B)) =
      AddCircle.haarAddCircle
        ((circleTimes 2) ⁻¹' (cauchyFromCircle ⁻¹' B)) := by
          apply MeasureTheory.measure_congr
          filter_upwards [hae] with y hy
          apply propext
          change cauchyDoublingMap (cauchyFromCircle y) ∈ B ↔
            cauchyFromCircle (circleTimes 2 y) ∈ B
          rw [cauchyFromCircle_dynamics hy]
    _ = AddCircle.haarAddCircle (cauchyFromCircle ⁻¹' B) := by
      have hmp :=
        (AddCircle.haarAddCircle :
          MeasureTheory.Measure (AddCircle (1 : ℝ))).measurePreserving_zsmul
            (by norm_num : (2 : ℤ) ≠ 0)
      exact hmp.measure_preimage
        (cauchyFromCircle_measurable hB).nullMeasurableSet

theorem cauchyDoublingSystem_isomorphism :
    IsIsomorphicSystems cauchyDoublingSystem (circleTimesSystem 2) := by
  let S := cauchyDoublingSystem
  let C := circleTimesSystem 2
  have hS : IsMeasurePreservingSystem S := by
    refine ⟨?_, cauchyDoublingMap_measurePreserving⟩
    change MeasureTheory.IsProbabilityMeasure cauchyMeasure
    exact ⟨cauchyMeasure_univ⟩
  have hC : IsMeasurePreservingSystem C := by
    constructor
    · change MeasureTheory.IsProbabilityMeasure
        (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle (1 : ℝ)))
      infer_instance
    · change MeasureTheory.MeasurePreserving (circleTimes 2)
        AddCircle.haarAddCircle AddCircle.haarAddCircle
      exact
        (AddCircle.haarAddCircle :
          MeasureTheory.Measure (AddCircle (1 : ℝ))).measurePreserving_zsmul
            (by norm_num : (2 : ℤ) ≠ 0)
  have hφ : MeasureTheory.MeasurePreserving cauchyToCircle S.μ C.μ :=
    ⟨cauchyToCircle_measurable, cauchyToCircle_map⟩
  have hψ : MeasureTheory.MeasurePreserving cauchyFromCircle C.μ S.μ :=
    ⟨cauchyFromCircle_measurable, cauchyFromCircle_map⟩
  have haeS : ∀ᵐ x ∂S.μ, x ∈ cauchyCanonicalSet := by
    apply MeasureTheory.ae_iff.mpr
    exact cauchyCanonicalSet_compl_measure
  have haeC : ∀ᵐ y ∂C.μ, y ∈ circleNondyadicSet := by
    apply MeasureTheory.ae_iff.mpr
    exact circleNondyadicSet_compl_measure
  have hforward : IsMeasurePreservingOnFullSets S C
      cauchyCanonicalSet circleNondyadicSet cauchyToCircle := by
    refine ⟨cauchyCanonicalSet_measurable, circleNondyadicSet_measurable,
      cauchyCanonicalSet_measure, circleNondyadicSet_measure, (fun x hx => hx), ?_⟩
    intro B hB
    change MeasurableSet B at hB
    constructor
    · exact cauchyCanonicalSet_measurable.inter
        (hφ.measurable (hB.inter circleNondyadicSet_measurable))
    · calc
        S.μ (cauchyCanonicalSet ∩
            cauchyToCircle ⁻¹' (B ∩ circleNondyadicSet)) =
            S.μ (cauchyToCircle ⁻¹' B) := by
          apply MeasureTheory.measure_congr
          filter_upwards [haeS] with x hx
          apply propext
          constructor
          · exact fun h => h.2.1
          · intro h
            exact ⟨hx, h, hx⟩
        _ = C.μ B := hφ.measure_preimage hB.nullMeasurableSet
        _ = C.μ (B ∩ circleNondyadicSet) := by
          apply MeasureTheory.measure_congr
          filter_upwards [haeC] with y hy
          exact propext ⟨fun h => ⟨h, hy⟩, fun h => h.1⟩
  have hbackward : IsMeasurePreservingOnFullSets C S
      circleNondyadicSet cauchyCanonicalSet cauchyFromCircle := by
    refine ⟨circleNondyadicSet_measurable, cauchyCanonicalSet_measurable,
      circleNondyadicSet_measure, cauchyCanonicalSet_measure, ?_, ?_⟩
    · intro y hy
      change cauchyToCircle (cauchyFromCircle y) ∈ circleNondyadicSet
      rw [cauchyToCircle_fromCircle (circleNondyadicSet_ne_zero hy)]
      exact hy
    · intro B hB
      change MeasurableSet B at hB
      constructor
      · exact circleNondyadicSet_measurable.inter
          (hψ.measurable (hB.inter cauchyCanonicalSet_measurable))
      · calc
          C.μ (circleNondyadicSet ∩
              cauchyFromCircle ⁻¹' (B ∩ cauchyCanonicalSet)) =
              C.μ (cauchyFromCircle ⁻¹' B) := by
            apply MeasureTheory.measure_congr
            filter_upwards [haeC] with y hy
            apply propext
            constructor
            · exact fun h => h.2.1
            · intro h
              refine ⟨hy, h, ?_⟩
              change cauchyToCircle (cauchyFromCircle y) ∈ circleNondyadicSet
              rw [cauchyToCircle_fromCircle (circleNondyadicSet_ne_zero hy)]
              exact hy
          _ = S.μ B := hψ.measure_preimage hB.nullMeasurableSet
          _ = S.μ (B ∩ cauchyCanonicalSet) := by
            apply MeasureTheory.measure_congr
            filter_upwards [haeS] with x hx
            exact propext ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩
  refine ⟨hS, hC, cauchyCanonicalSet, circleNondyadicSet,
    cauchyToCircle, cauchyFromCircle,
    cauchyCanonicalSet_measure, circleNondyadicSet_measure,
    (fun _ hx => cauchyCanonicalSet_invariant hx),
    (fun _ hy => circleNondyadicSet_invariant hy),
    hforward, hbackward, ?_, ?_⟩
  · intro x hx
    exact ⟨hx, cauchyFromCircle_toCircle x, cauchyToCircle_dynamics hx⟩
  · intro y hy
    constructor
    · change cauchyToCircle (cauchyFromCircle y) ∈ circleNondyadicSet
      rw [cauchyToCircle_fromCircle (circleNondyadicSet_ne_zero hy)]
      exact hy
    exact ⟨cauchyToCircle_fromCircle (circleNondyadicSet_ne_zero hy),
      cauchyFromCircle_dynamics hy⟩

end Chapter01
