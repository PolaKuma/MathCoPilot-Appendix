import Exp2BoundedProbe

open scoped ENNReal MeasureTheory Topology Interval
open MeasureTheory Set Filter

noncomputable section
namespace Exp2

lemma primitive_zero_near_left {g : ℝ → ℝ}
    (_hgcd : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hgt : tsupport g ⊆ Set.Ioo (0 : ℝ) 1) :
    ∃ ε > 0, ∀ y, dist y 0 < ε → zeroMeanPrimitive g y = 0 := by
  let q := zeroMeanPart g
  have hqt : tsupport q ⊆ Set.Ioo (0 : ℝ) 1 := zeroMeanPart_tsupport_subset hgt
  have hq0 : 0 ∉ tsupport q := by
    intro h
    exact (hqt h).1.false
  obtain ⟨ε, hε, hqε⟩ := (Metric.eventually_nhds_iff.mp
    (eventuallyEq_zero_of_not_mem_tsupport hq0))
  refine ⟨ε / 2, by linarith, ?_⟩
  intro y hy
  have hyabs : |y| < ε / 2 := by simpa [Real.dist_eq] using hy
  by_cases hy0 : 0 ≤ y
  · change (∫ t in (0 : ℝ)..y, q t) = 0
    apply intervalIntegral_eq_zero_of_forall hy0
    intro t ht
    have hylt : y < ε / 2 := by simpa [abs_of_nonneg hy0] using hyabs
    have htabs : |t| < ε := by
      rw [abs_of_nonneg ht.1.le]
      linarith [hylt, ht.2]
    exact hqε (by simpa [Real.dist_eq, abs_of_nonneg ht.1.le] using htabs)
  · have hy0' : y ≤ 0 := le_of_not_ge hy0
    change (∫ t in (0 : ℝ)..y, q t) = 0
    rw [intervalIntegral.integral_of_ge hy0', neg_eq_zero]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hylt : -y < ε / 2 := by simpa [abs_of_nonpos hy0'] using hyabs
    have htabs : |t| < ε := by
      rw [abs_of_nonpos ht.2]
      linarith [hylt, ht.1]
    exact hqε (by simpa [Real.dist_eq, abs_of_nonpos ht.2] using htabs)

lemma primitive_zero_near_right {g : ℝ → ℝ}
    (hgcd : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hg : HasCompactSupport g)
    (hgt : tsupport g ⊆ Set.Ioo (0 : ℝ) 1) :
    ∃ ε > 0, ∀ y, dist y 1 < ε → zeroMeanPrimitive g y = 0 := by
  let q := zeroMeanPart g
  have hqt : tsupport q ⊆ Set.Ioo (0 : ℝ) 1 := zeroMeanPart_tsupport_subset hgt
  have hq1 : 1 ∉ tsupport q := by
    intro h
    exact (hqt h).2.false
  obtain ⟨ε, hε, hqε⟩ := (Metric.eventually_nhds_iff.mp
    (eventuallyEq_zero_of_not_mem_tsupport hq1))
  have hqInt : Integrable q :=
    (zeroMeanPart_contDiff hgcd).continuous.integrable_of_hasCompactSupport
      (zeroMeanPart_hasCompactSupport hg)
  have hqglobal : (∫ x, q x) = 0 := zeroMeanPart_integral hgcd hg
  have hqoutside : (∫ x in (Set.Ioc (0 : ℝ) 1)ᶜ, q x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (MeasurableSet.compl measurableSet_Ioc)] with x hx
    have hnot : x ∉ Set.Ioo (0 : ℝ) 1 := by
      intro h
      exact hx ⟨h.1, le_of_lt h.2⟩
    have hxs : x ∉ Function.support q := fun hs => hnot (hqt (subset_tsupport q hs))
    simpa [Function.mem_support] using hxs
  have hP1 : zeroMeanPrimitive g 1 = 0 := by
    change (∫ t in (0 : ℝ)..1, q t) = 0
    rw [intervalIntegral.integral_of_le (by norm_num)]
    have hdecomp := integral_add_compl (s := Set.Ioc (0 : ℝ) 1)
      measurableSet_Ioc hqInt
    linarith

  have hfirst : (∫ t in (0 : ℝ)..1, q t) = 0 := by exact hP1
  refine ⟨ε / 2, by linarith, ?_⟩
  intro y hy
  have hyabs : |y - 1| < ε / 2 := by
    simpa [Real.dist_eq, abs_sub_comm] using hy
  by_cases hy1 : 1 ≤ y
  · have hylt : y - 1 < ε / 2 := by simpa [abs_of_nonneg (sub_nonneg.mpr hy1)] using hyabs
    have htail : (∫ t in (1 : ℝ)..y, q t) = 0 :=
      intervalIntegral_eq_zero_of_forall hy1 (by
        intro t ht
        have htabs : |t - 1| < ε := by
          rw [abs_of_nonneg (sub_nonneg.mpr ht.1.le)]
          linarith [hylt, ht.2]
        exact hqε (by simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1.le)] using htabs))
    change (∫ t in (0 : ℝ)..y, q t) = 0
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      ((zeroMeanPart_contDiff hgcd).continuous.intervalIntegrable (μ := volume) 0 1)
      ((zeroMeanPart_contDiff hgcd).continuous.intervalIntegrable (μ := volume) 1 y)
    rw [← hadd, hfirst, htail]
    simp
  · have hy1' : y ≤ 1 := le_of_not_ge hy1
    have hylt : 1 - y < ε / 2 := by simpa [abs_of_nonpos (sub_nonpos.mpr hy1')] using hyabs
    have htail : (∫ t in (y : ℝ)..1, q t) = 0 :=
      intervalIntegral_eq_zero_of_forall hy1' (by
        intro t ht
        have htabs : |t - 1| < ε := by
          rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
          linarith [hylt, ht.1]
        exact hqε (by simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)] using htabs))
    change (∫ t in (0 : ℝ)..y, q t) = 0
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      ((zeroMeanPart_contDiff hgcd).continuous.intervalIntegrable (μ := volume) 0 y)
      ((zeroMeanPart_contDiff hgcd).continuous.intervalIntegrable (μ := volume) y 1)
    have hEq := hadd
    rw [hfirst, htail] at hEq
    linarith

lemma primitive_zero_left {g : ℝ → ℝ}
    (_hgcd : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hgt : tsupport g ⊆ Set.Ioo (0 : ℝ) 1) :
    ∀ y ≤ 0, zeroMeanPrimitive g y = 0 := by
  intro y hy
  let q := zeroMeanPart g
  have hqt : tsupport q ⊆ Set.Ioo (0 : ℝ) 1 := zeroMeanPart_tsupport_subset hgt
  change (∫ t in (0 : ℝ)..y, q t) = 0
  rw [intervalIntegral.integral_of_ge hy, neg_eq_zero]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hnot : t ∉ Set.Ioo (0 : ℝ) 1 := by
    intro h
    exact (not_lt_of_ge ht.2) h.1
  have hts : t ∉ Function.support q := fun hs => hnot (hqt (subset_tsupport q hs))
  simpa [Function.mem_support] using hts

lemma primitive_zero_right {g : ℝ → ℝ}
    (hgcd : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hg : HasCompactSupport g)
    (hgt : tsupport g ⊆ Set.Ioo (0 : ℝ) 1) :
    ∀ y ≥ 1, zeroMeanPrimitive g y = 0 := by
  intro y hy
  let q := zeroMeanPart g
  have hqt : tsupport q ⊆ Set.Ioo (0 : ℝ) 1 := zeroMeanPart_tsupport_subset hgt
  have htail : (∫ t in (1 : ℝ)..y, q t) = 0 :=
    intervalIntegral_eq_zero_of_forall hy (by
      intro t ht
      have hnot : t ∉ Set.Ioo (0 : ℝ) 1 := by
        intro h
        exact (not_lt_of_ge (le_of_lt ht.1)) h.2
      have hts : t ∉ Function.support q := fun hs => hnot (hqt (subset_tsupport q hs))
      simpa [Function.mem_support] using hts)
  have hqInt : Integrable q :=
    (zeroMeanPart_contDiff hgcd).continuous.integrable_of_hasCompactSupport
      (zeroMeanPart_hasCompactSupport hg)
  have hqglobal : (∫ x, q x) = 0 := zeroMeanPart_integral hgcd hg
  have hqoutside : (∫ x in (Set.Ioc (0 : ℝ) 1)ᶜ, q x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (MeasurableSet.compl measurableSet_Ioc)] with x hx
    have hnot : x ∉ Set.Ioo (0 : ℝ) 1 := by
      intro h
      exact hx ⟨h.1, le_of_lt h.2⟩
    have hxs : x ∉ Function.support q := fun hs => hnot (hqt (subset_tsupport q hs))
    simpa [Function.mem_support] using hxs
  have hfirst : (∫ t in (0 : ℝ)..1, q t) = 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    have hdecomp := integral_add_compl (s := Set.Ioc (0 : ℝ) 1)
      measurableSet_Ioc hqInt
    linarith
  change (∫ t in (0 : ℝ)..y, q t) = 0
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    ((zeroMeanPart_contDiff hgcd).continuous.intervalIntegrable (μ := volume) 0 1)
    ((zeroMeanPart_contDiff hgcd).continuous.intervalIntegrable (μ := volume) 1 y)
  rw [← hadd, hfirst, htail]
  simp

lemma not_mem_tsupport_of_eventuallyEq_zero {f : ℝ → ℝ} {x : ℝ}
    (h : ∀ᶠ y in 𝓝 x, f y = 0) : x ∉ tsupport f := by
  intro hx
  rw [tsupport, mem_closure_iff_nhds] at hx
  have hzero : {y : ℝ | f y = 0} ∈ 𝓝 x := by simpa [Filter.eventually_iff] using h
  obtain ⟨y, hyzero, hysupp⟩ := hx {y : ℝ | f y = 0} hzero
  exact (Function.mem_support.mp hysupp) hyzero

lemma primitive_tsupport_subset {g : ℝ → ℝ}
    (hgcd : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hg : HasCompactSupport g)
    (hgt : tsupport g ⊆ Set.Ioo (0 : ℝ) 1) :
    tsupport (zeroMeanPrimitive g) ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro x hx
  by_cases hx0 : x < 0
  · have hev : ∀ᶠ y in 𝓝 x, zeroMeanPrimitive g y = 0 := by
      filter_upwards [isOpen_Iio.mem_nhds hx0] with y hy
      exact primitive_zero_left hgcd hgt y (le_of_lt hy)
    exact False.elim (not_mem_tsupport_of_eventuallyEq_zero hev hx)
  by_cases hx1 : 1 < x
  · have hev : ∀ᶠ y in 𝓝 x, zeroMeanPrimitive g y = 0 := by
      filter_upwards [isOpen_Ioi.mem_nhds hx1] with y hy
      exact primitive_zero_right hgcd hg hgt y (le_of_lt hy)
    exact False.elim (not_mem_tsupport_of_eventuallyEq_zero hev hx)
  constructor
  · by_contra hxzero
    have hxeq : x = 0 := by linarith
    obtain ⟨ε, hε, hev⟩ := primitive_zero_near_left hgcd hgt
    exact False.elim (not_mem_tsupport_of_eventuallyEq_zero
      ((Metric.eventually_nhds_iff.mpr ⟨ε, hε, hev⟩)) (hxeq ▸ hx))
  · by_contra hxone
    have hxeq : x = 1 := by linarith
    obtain ⟨ε, hε, hev⟩ := primitive_zero_near_right hgcd hg hgt
    exact False.elim (not_mem_tsupport_of_eventuallyEq_zero
      ((Metric.eventually_nhds_iff.mpr ⟨ε, hε, hev⟩)) (hxeq ▸ hx))

def primitiveTestFunction (g : TestFunction referenceCell ℝ ⊤) :
    TestFunction referenceCell ℝ ⊤ where
  toFun := zeroMeanPrimitive g
  contDiff' := zeroMeanPrimitive_contDiff g.contDiff
  hasCompactSupport' := by
    apply zeroMeanPrimitive_hasCompactSupport g.contDiff g.hasCompactSupport
    simpa [referenceCell, cell] using g.tsupport_subset
  tsupport_subset' := by
    have h := primitive_tsupport_subset g.contDiff g.hasCompactSupport (by
      simpa [referenceCell, cell] using g.tsupport_subset)
    simpa [referenceCell, cell] using h

end Exp2
