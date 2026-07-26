import Exp2Core
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

open scoped ENNReal MeasureTheory Topology Interval
open MeasureTheory Set Filter

noncomputable section

namespace Exp2

def traceBump : ContDiffBump (1 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def traceRho : ℝ → ℝ := traceBump.normed volume

theorem traceRho_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) traceRho := by
  simpa [traceRho] using
    (traceBump.contDiff_normed (μ := volume) (n := (⊤ : ℕ∞)))

theorem traceRho_hasCompactSupport : HasCompactSupport traceRho := by
  exact traceBump.hasCompactSupport_normed

theorem traceRho_integral : (∫ x, traceRho x) = 1 := by
  exact traceBump.integral_normed

theorem traceRho_tsupport_subset : tsupport traceRho ⊆ Set.Ioo (0 : ℝ) 1 := by
  rw [traceRho, traceBump.tsupport_normed_eq]
  intro x hx
  change dist x (1 / 2 : ℝ) ≤ 1 / 4 at hx
  rw [Real.dist_eq] at hx
  constructor <;> nlinarith [abs_le.mp hx]

theorem contDiff_primitive {q : ℝ → ℝ} (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x ↦ ∫ t in (0 : ℝ)..x, q t) := by
  have hhas : ∀ x : ℝ, HasDerivAt (fun x ↦ ∫ t in (0 : ℝ)..x, q t) (q x) x := by
    intro x
    exact intervalIntegral.integral_hasDerivAt_right
      (hq.continuous.intervalIntegrable (μ := volume) 0 x)
      (hq.continuous.stronglyMeasurableAtFilter volume (𝓝 x))
      hq.continuous.continuousAt
  have hdiff : Differentiable ℝ (fun x ↦ ∫ t in (0 : ℝ)..x, q t) :=
    fun x ↦ (hhas x).differentiableAt
  have hderiv : deriv (fun x ↦ ∫ t in (0 : ℝ)..x, q t) = q := by
    funext x
    exact (hhas x).deriv
  rw [contDiff_infty]
  intro n
  cases n with
  | zero => exact (contDiff_zero).2 hdiff.continuous
  | succ n =>
      rw [show (↑(n + 1) : WithTop ℕ∞) = (↑n : WithTop ℕ∞) + 1 by norm_num,
        contDiff_succ_iff_deriv, hderiv]
      exact ⟨hdiff, (by intro hn; norm_num at hn),
        hq.of_le (WithTop.coe_le_coe.mpr le_top)⟩

def zeroMeanPart (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ g x - (∫ y, g y) * traceRho x

theorem zeroMeanPart_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (zeroMeanPart g) := by
  exact hg.sub (contDiff_const.mul traceRho_contDiff)

theorem zeroMeanPart_hasCompactSupport {g : ℝ → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport (zeroMeanPart g) := by
  have hrho : HasCompactSupport (fun x ↦ (∫ y, g y) * traceRho x) := by
    have hc := traceRho_hasCompactSupport.comp_left
      (show (fun y : ℝ ↦ (∫ z, g z) * y) 0 = 0 by simp)
    simpa [Function.comp_def] using hc
  exact hg.sub hrho

theorem zeroMeanPart_tsupport_subset {g : ℝ → ℝ}
    (hg : tsupport g ⊆ Set.Ioo (0 : ℝ) 1) :
    tsupport (zeroMeanPart g) ⊆ Set.Ioo (0 : ℝ) 1 := by
  have hrho : tsupport (fun x ↦ (∫ y, g y) * traceRho x) ⊆ tsupport traceRho := by
    have hs := tsupport_comp_subset
      (g := fun y : ℝ ↦ (∫ z, g z) * y) (by simp) traceRho
    simpa [Function.comp_def] using hs
  intro x hx
  have hx' := tsupport_sub g (fun x ↦ (∫ y, g y) * traceRho x) hx
  rcases hx' with hxg | hxr
  · exact hg hxg
  · exact traceRho_tsupport_subset (hrho hxr)

theorem zeroMeanPart_integral {g : ℝ → ℝ}
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hgc : HasCompactSupport g) :
    (∫ x, zeroMeanPart g x) = 0 := by
  have hgInt : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hrInt : Integrable traceRho :=
    traceRho_contDiff.continuous.integrable_of_hasCompactSupport traceRho_hasCompactSupport
  rw [show zeroMeanPart g = fun x ↦ g x - (∫ y, g y) * traceRho x by rfl,
    integral_sub hgInt (hrInt.const_mul _), integral_const_mul, traceRho_integral]
  ring

def zeroMeanPrimitive (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ ∫ t in (0 : ℝ)..x, zeroMeanPart g t

theorem zeroMeanPrimitive_contDiff {g : ℝ → ℝ}
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (zeroMeanPrimitive g) := by
  exact contDiff_primitive (zeroMeanPart_contDiff hg)

theorem zeroMeanPrimitive_deriv {g : ℝ → ℝ}
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) :
    deriv (zeroMeanPrimitive g) = zeroMeanPart g := by
  funext x
  have hq := zeroMeanPart_contDiff hg
  exact (intervalIntegral.integral_hasDerivAt_right
    (hq.continuous.intervalIntegrable (μ := volume) 0 x)
    (hq.continuous.stronglyMeasurableAtFilter volume (𝓝 x))
    hq.continuous.continuousAt).deriv

lemma eventuallyEq_zero_of_not_mem_tsupport {f : ℝ → ℝ} {x : ℝ}
    (hx : x ∉ tsupport f) : ∀ᶠ y in 𝓝 x, f y = 0 := by
  have hnhds : (tsupport f)ᶜ ∈ 𝓝 x := by
    apply isClosed_closure.isOpen_compl.mem_nhds
    exact hx
  rw [Filter.eventually_iff]
  filter_upwards [hnhds] with y hy
  have hys : y ∉ Function.support f := by
    intro hys
    exact hy (subset_closure hys)
  simpa [Function.mem_support] using hys

lemma intervalIntegral_eq_zero_of_forall {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ∀ x ∈ Set.Ioc a b, f x = 0) :
    (∫ x in a..b, f x) = 0 := by
  rw [intervalIntegral.integral_of_le hab]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hf x hx

theorem zeroMeanPrimitive_hasCompactSupport {g : ℝ → ℝ}
    (hgcd : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hg : HasCompactSupport g)
    (hgt : tsupport g ⊆ Set.Ioo (0 : ℝ) 1) :
    HasCompactSupport (zeroMeanPrimitive g) := by
  let q := zeroMeanPart g
  have hqt : tsupport q ⊆ Set.Ioo (0 : ℝ) 1 := zeroMeanPart_tsupport_subset hgt
  have hqcomp : HasCompactSupport q := zeroMeanPart_hasCompactSupport hg
  have hqInt : Integrable q := by
    exact (zeroMeanPart_contDiff hgcd).continuous.integrable_of_hasCompactSupport hqcomp
  have hzero_left : ∀ x ≤ 0, zeroMeanPrimitive g x = 0 := by
    intro x hx
    change (∫ t in (0 : ℝ)..x, q t) = 0
    rw [intervalIntegral.integral_of_ge hx]
    rw [neg_eq_zero]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hy' : y ∉ Set.Ioo (0 : ℝ) 1 := by
      intro h
      exact (not_lt_of_ge hy.2) h.1
    have hys : y ∉ Function.support q := fun hs => hy' (hqt (subset_tsupport q hs))
    simpa [Function.mem_support] using hys
  have hqglobal : (∫ x, q x) = 0 := by
    exact zeroMeanPart_integral hgcd hg
  have hqoutside : (∫ x in (Set.Ioc (0 : ℝ) 1)ᶜ, q x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (MeasurableSet.compl measurableSet_Ioc)] with x hx
    have hnot : x ∉ Set.Ioo (0 : ℝ) 1 := by
      intro h
      exact hx ⟨h.1, le_of_lt h.2⟩
    have hxs : x ∉ Function.support q := fun hs => hnot (hqt (subset_tsupport q hs))
    simpa [Function.mem_support] using hxs
  have hqone : zeroMeanPrimitive g 1 = 0 := by
    change (∫ t in (0 : ℝ)..1, q t) = 0
    rw [intervalIntegral.integral_of_le (by norm_num)]
    have hdecomp := integral_add_compl (s := Set.Ioc (0 : ℝ) 1)
      measurableSet_Ioc hqInt
    linarith
  have hzero_right : ∀ x ≥ 1, zeroMeanPrimitive g x = 0 := by
    intro x hx
    change (∫ t in (0 : ℝ)..x, q t) = 0
    have hix : IntervalIntegrable q volume 0 x := hqInt.intervalIntegrable
    have h01 : IntervalIntegrable q volume 0 1 := hqInt.intervalIntegrable
    have h1x : IntervalIntegrable q volume 1 x := hqInt.intervalIntegrable
    have hadd := intervalIntegral.integral_add_adjacent_intervals h01 h1x
    have htail : (∫ t in (1 : ℝ)..x, q t) = 0 :=
      intervalIntegral_eq_zero_of_forall (by linarith) (by
        intro y hy
        have hnot : y ∉ Set.Ioo (0 : ℝ) 1 := by
          intro h
          exact (not_lt_of_ge (le_of_lt hy.1)) h.2
        have hys : y ∉ Function.support q := fun hs => hnot (hqt (subset_tsupport q hs))
        simpa [Function.mem_support] using hys)
    have hfirst : (∫ t in (0 : ℝ)..1, q t) = 0 := by
      exact hqone
    rw [← hadd]
    rw [hfirst, htail]
    simp
  have hsupp : Function.support (zeroMeanPrimitive g) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    by_contra h
    have hlt : x < 0 ∨ 1 < x := by
      by_cases hx0 : x < 0
      · exact Or.inl hx0
      · right
        have hx1 : ¬ x ≤ 1 := by
          intro hx1
          exact h ⟨le_of_not_gt hx0, hx1⟩
        exact lt_of_not_ge hx1
    rcases hlt with hlt | hgt
    · exact hx (hzero_left x (le_of_lt hlt))
    · exact hx (hzero_right x (le_of_lt hgt))
  have hts : tsupport (zeroMeanPrimitive g) ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [tsupport]
    exact closure_minimal hsupp isClosed_Icc
  change IsCompact (tsupport (zeroMeanPrimitive g))
  exact IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure hts

end Exp2
