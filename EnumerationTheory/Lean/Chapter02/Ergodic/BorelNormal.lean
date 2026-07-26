import Chapter02.Section02
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section

open Classical Filter

namespace Chapter02
namespace BorelNormal

abbrev UnitCircle := AddCircle (1 : ℝ)

def binaryHalf (d : ℤ) : Set UnitCircle :=
  {q | ⌊2 * (AddCircle.equivIco 1 0 q : ℝ)⌋ = d}

lemma binaryHalf_zero :
    binaryHalf 0 =
      (fun q : UnitCircle => (AddCircle.equivIco 1 0 q : ℝ)) ⁻¹'
        Set.Ico 0 (1 / 2 : ℝ) := by
  ext q
  let r : ℝ := AddCircle.equivIco 1 0 q
  have hr := (AddCircle.equivIco 1 0 q).property
  change ⌊2 * r⌋ = 0 ↔ 0 ≤ r ∧ r < 1 / 2
  rw [Int.floor_eq_iff]
  norm_num only at *
  constructor
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

lemma binaryHalf_one :
    binaryHalf 1 =
      (fun q : UnitCircle => (AddCircle.equivIco 1 0 q : ℝ)) ⁻¹'
        Set.Ico (1 / 2 : ℝ) 1 := by
  ext q
  let r : ℝ := AddCircle.equivIco 1 0 q
  have hr := (AddCircle.equivIco 1 0 q).property
  change ⌊2 * r⌋ = 1 ↔ 1 / 2 ≤ r ∧ r < 1
  rw [Int.floor_eq_iff]
  norm_num only at *
  constructor
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

lemma binaryHalf_measurable (d : ℤ) (hd : d = 0 ∨ d = 1) :
    MeasurableSet (binaryHalf d) := by
  rcases hd with rfl | rfl
  · rw [binaryHalf_zero]
    exact (measurable_subtype_coe.comp
      (AddCircle.measurableEquivIco 1 0).measurable) measurableSet_Ico
  · rw [binaryHalf_one]
    exact (measurable_subtype_coe.comp
      (AddCircle.measurableEquivIco 1 0).measurable) measurableSet_Ico

lemma coe_mem_binaryHalf_zero {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    (x : UnitCircle) ∈ binaryHalf 0 ↔ x < 1 / 2 ∨ x = 1 := by
  rw [binaryHalf_zero]
  simp only [Set.mem_preimage, AddCircle.coe_equivIco_mk_apply, div_one, mul_one,
    Set.mem_Ico]
  by_cases h1 : x = 1
  · subst x
    simp
  · have hxlt : x < 1 := lt_of_le_of_ne hx.2 h1
    rw [Int.fract_eq_self.mpr ⟨hx.1.le, hxlt⟩]
    constructor
    · intro h
      exact Or.inl h.2
    · rintro (h | h)
      · exact ⟨hx.1.le, h⟩
      · exact (h1 h).elim

lemma coe_mem_binaryHalf_one {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    (x : UnitCircle) ∈ binaryHalf 1 ↔ 1 / 2 ≤ x ∧ x < 1 := by
  rw [binaryHalf_one]
  simp only [Set.mem_preimage, AddCircle.coe_equivIco_mk_apply, div_one, mul_one,
    Set.mem_Ico]
  by_cases h1 : x = 1
  · subst x
    simp
  · have hxlt : x < 1 := lt_of_le_of_ne hx.2 h1
    rw [Int.fract_eq_self.mpr ⟨hx.1.le, hxlt⟩]

lemma binaryDigit_eq_floor_two_fract (x : ℝ) (n : ℕ) :
    binaryDigit x n = ⌊2 * Int.fract ((2 : ℝ) ^ n * x)⌋ := by
  let y : ℝ := (2 : ℝ) ^ n * x
  have hpow : (2 : ℝ) ^ (n + 1) * x = 2 * y := by
    simp [y, pow_succ]
    ring
  rw [binaryDigit, hpow]
  have hy : (2 : ℝ) * y = ((2 * ⌊y⌋ : ℤ) : ℝ) + 2 * Int.fract y := by
    norm_num only [Int.cast_mul, Int.cast_ofNat]
    nlinarith [Int.floor_add_fract y]
  rw [hy, Int.floor_intCast_add]
  simp [y]

lemma iterate_two_nsmul (q : UnitCircle) (n : ℕ) :
    ((fun z : UnitCircle => 2 • z)^[n]) q = (2 ^ n) • q := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [pow_succ, mul_nsmul]

lemma orbit_binaryHalf_iff (x : ℝ) (n : ℕ) (d : ℤ) :
    ((fun z : UnitCircle => 2 • z)^[n]) (x : UnitCircle) ∈ binaryHalf d ↔
      binaryDigit x n = d := by
  rw [iterate_two_nsmul]
  change ⌊2 * (AddCircle.equivIco 1 0 ((2 ^ n : ℕ) • (x : UnitCircle)) : ℝ)⌋ = d ↔ _
  rw [← AddCircle.coe_nsmul]
  simp only [AddCircle.coe_equivIco_mk_apply, div_one, mul_one]
  rw [binaryDigit_eq_floor_two_fract]
  simp [nsmul_eq_mul]

lemma restricted_preimage_binaryHalf_zero :
    (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))
      (((↑) : ℝ → UnitCircle) ⁻¹' binaryHalf 0) = ENNReal.ofReal (1 / 2 : ℝ) := by
  have hmeas : MeasurableSet (((↑) : ℝ → UnitCircle) ⁻¹' binaryHalf 0) :=
    AddCircle.measurable_mk' (binaryHalf_measurable 0 (Or.inl rfl))
  rw [MeasureTheory.Measure.restrict_apply hmeas]
  have hset :
      ((↑) : ℝ → UnitCircle) ⁻¹' binaryHalf 0 ∩ Set.Ioc (0 : ℝ) 1 =
        Set.Ioo 0 (1 / 2 : ℝ) ∪ {1} := by
    ext x
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
    · change ((x : UnitCircle) ∈ binaryHalf 0 ∧ x ∈ Set.Ioc (0 : ℝ) 1) ↔ _
      rw [coe_mem_binaryHalf_zero hx]
      simp only [hx, and_true, Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff]
      constructor
      · rintro (hlt | h1)
        · exact Or.inl ⟨hx.1, hlt⟩
        · exact Or.inr h1
      · rintro (hlt | h1)
        · exact Or.inl hlt.2
        · exact Or.inr h1
    · simp only [Set.mem_inter_iff, hx, and_false, false_iff]
      intro h
      rcases h with h | h
      · exact hx ⟨h.1, h.2.le.trans (by norm_num only)⟩
      · subst x
        exact hx ⟨by norm_num only, le_rfl⟩
  rw [hset, MeasureTheory.measure_union]
  · simp
  · exact Set.disjoint_singleton_right.mpr (fun h => by linarith [h.2])
  · exact measurableSet_singleton (1 : ℝ)

lemma restricted_preimage_binaryHalf_one :
    (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))
      (((↑) : ℝ → UnitCircle) ⁻¹' binaryHalf 1) = ENNReal.ofReal (1 / 2 : ℝ) := by
  have hmeas : MeasurableSet (((↑) : ℝ → UnitCircle) ⁻¹' binaryHalf 1) :=
    AddCircle.measurable_mk' (binaryHalf_measurable 1 (Or.inr rfl))
  rw [MeasureTheory.Measure.restrict_apply hmeas]
  have hset :
      ((↑) : ℝ → UnitCircle) ⁻¹' binaryHalf 1 ∩ Set.Ioc (0 : ℝ) 1 =
        Set.Ico (1 / 2 : ℝ) 1 := by
    ext x
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
    · change ((x : UnitCircle) ∈ binaryHalf 1 ∧ x ∈ Set.Ioc (0 : ℝ) 1) ↔ _
      rw [coe_mem_binaryHalf_one hx]
      simp only [hx, and_true, Set.mem_Ico]
    · simp only [Set.mem_inter_iff, hx, and_false, false_iff, Set.mem_Ico]
      intro h
      exact hx ⟨by linarith, h.2.le⟩
  rw [hset]
  simp
  have hreal : (1 - 2⁻¹ : ℝ) = 1 / 2 := by norm_num only
  rw [hreal]
  rw [ENNReal.ofReal_div_of_pos (by norm_num only : (0 : ℝ) < 2)]
  rw [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  rw [one_div]

lemma binaryHalf_measure (d : ℤ) (hd : d = 0 ∨ d = 1) :
    AddCircle.haarAddCircle (binaryHalf d) = ENNReal.ofReal (1 / 2 : ℝ) := by
  have hpre := (UnitAddCircle.measurePreserving_mk 0).measure_preimage
    (binaryHalf_measurable d hd).nullMeasurableSet
  have hvol :
      (MeasureTheory.volume : MeasureTheory.Measure UnitCircle) =
        AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  rw [hvol] at hpre
  rw [← hpre]
  rcases hd with rfl | rfl
  · simpa using restricted_preimage_binaryHalf_zero
  · simpa using restricted_preimage_binaryHalf_one

theorem borel_normal_of_orbit_visit
    (hvisit : OrbitVisitDensityStatement (circleEndomorphismSystem 2))
    (herg : IsErgodic (circleEndomorphismSystem 2)) :
    BorelNormalNumberTheoremStatement := by
  have hdensity (d : ℤ) (hd : d = 0 ∨ d = 1) :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)),
        Tendsto
          (fun n : ℕ => if n = 0 then 0 else
            (((Finset.range n).filter (fun i => binaryDigit x i = d)).card : ℝ) / n)
          atTop (nhds (1 / 2 : ℝ)) := by
    have hcircle := hvisit herg (binaryHalf d) (binaryHalf_measurable d hd)
    have hvol :
        (MeasureTheory.volume : MeasureTheory.Measure UnitCircle) =
          AddCircle.haarAddCircle := by
      simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
    change (∀ᵐ x : UnitCircle ∂AddCircle.haarAddCircle, _) at hcircle
    rw [← hvol] at hcircle
    have hpull := (UnitAddCircle.measurePreserving_mk 0).quasiMeasurePreserving.tendsto_ae
      hcircle
    change (∀ᵐ x : ℝ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
      (Set.Ioc (0 : ℝ) (0 + 1))), _) at hpull
    simp only [Set.mem_setOf_eq] at hpull
    have hpull' :
        ∀ᵐ x : ℝ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Ioo (0 : ℝ) 1)),
          Tendsto
            (fun n : ℕ => if n = 0 then 0 else
              ((n : ℝ)⁻¹) * ((Finset.range n).filter
                (fun i =>
                  ((fun z : UnitCircle => 2 • z)^[i]) (x : UnitCircle) ∈
                    binaryHalf d)).card)
            atTop (nhds (realMeasure (circleEndomorphismSystem 2) (binaryHalf d))) := by
      simpa only [zero_add, MeasureTheory.restrict_Ioo_eq_restrict_Ioc,
        circleEndomorphismSystem] using hpull
    filter_upwards [hpull'] with x hx
    have hseq :
        (fun n : ℕ => if n = 0 then 0 else
          ((n : ℝ)⁻¹) * ((Finset.range n).filter
            (fun i => ((fun z : UnitCircle => 2 • z)^[i]) (x : UnitCircle) ∈
              binaryHalf d)).card) =
        (fun n : ℕ => if n = 0 then 0 else
          (((Finset.range n).filter (fun i => binaryDigit x i = d)).card : ℝ) / n) := by
      funext n
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, if_false]
        have hfilters :
            (Finset.range n).filter
                (fun i => ((fun z : UnitCircle => 2 • z)^[i]) (x : UnitCircle) ∈
                  binaryHalf d) =
              (Finset.range n).filter (fun i => binaryDigit x i = d) := by
          apply Finset.filter_congr
          intro i hi
          exact orbit_binaryHalf_iff x i d
        rw [hfilters]
        simp [div_eq_mul_inv, mul_comm]
    rw [hseq] at hx
    have hmeasure :
        realMeasure (circleEndomorphismSystem 2) (binaryHalf d) = 1 / 2 := by
      unfold realMeasure
      change (AddCircle.haarAddCircle (binaryHalf d)).toReal = 1 / 2
      rw [binaryHalf_measure d hd, ENNReal.toReal_ofReal (by norm_num only)]
    simpa [hmeasure] using hx
  filter_upwards [hdensity 0 (Or.inl rfl), hdensity 1 (Or.inr rfl)] with x h0 h1
  intro d hd
  rcases hd with rfl | rfl
  · exact h0
  · exact h1

end BorelNormal
end Chapter02
