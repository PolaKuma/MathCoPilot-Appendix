import Chapter02.Common
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.ContinuousMap.Weierstrass

open Classical Filter Set MeasureTheory
open scoped BigOperators ENNReal symmDiff

noncomputable section

namespace Chapter02.AlgebraSubSigma

universe u

def indicatorOne {X : Type*} (A : Set X) : X → ℂ :=
  A.indicator fun _ ↦ 1

def indicatorFamily (M : System.{u}) (H : Set (M.X → ℂ)) : SetFamily M.X :=
  {A | MeasurableSet A ∧ indicatorOne A ∈ H}

theorem indicatorOne_univ {X : Type*} :
    indicatorOne (Set.univ : Set X) = fun _ ↦ (1 : ℂ) := by
  funext x
  simp [indicatorOne]

theorem indicatorOne_compl {X : Type*} (A : Set X) :
    indicatorOne Aᶜ = fun x ↦ 1 - indicatorOne A x := by
  funext x
  by_cases hx : x ∈ A <;> simp [indicatorOne, hx]

theorem indicatorOne_union {X : Type*} (A B : Set X) :
    indicatorOne (A ∪ B) = fun x ↦
      indicatorOne A x + indicatorOne B x - indicatorOne A x * indicatorOne B x := by
  funext x
  by_cases hx : x ∈ A <;> by_cases hy : x ∈ B <;>
    simp [indicatorOne, hx, hy]

theorem indicatorFamily_univ
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H) :
    Set.univ ∈ indicatorFamily M H := by
  exact ⟨MeasurableSet.univ, by simpa [indicatorOne_univ] using hone⟩

theorem indicatorFamily_compl
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hH : IsClosedL2FunctionSubspace M H)
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H)
    {A : Set M.X} (hA : A ∈ indicatorFamily M H) :
    Aᶜ ∈ indicatorFamily M H := by
  rcases hH with ⟨_hzero, _hLp, hlin, _hae, _hclosed⟩
  refine ⟨hA.1.compl, ?_⟩
  have h := hlin (fun _ : M.X ↦ (1 : ℂ)) hone
    (indicatorOne A) hA.2 1 (-1)
  rw [indicatorOne_compl]
  convert h using 1
  funext x
  ring

theorem indicatorFamily_union
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hH : IsClosedL2FunctionSubspace M H)
    (hmul : ∀ f ∈ H, ∀ g ∈ H, (fun x ↦ f x * g x) ∈ H)
    {A B : Set M.X}
    (hA : A ∈ indicatorFamily M H) (hB : B ∈ indicatorFamily M H) :
    A ∪ B ∈ indicatorFamily M H := by
  rcases hH with ⟨_hzero, _hLp, hlin, _hae, _hclosed⟩
  refine ⟨hA.1.union hB.1, ?_⟩
  have hadd := hlin (indicatorOne A) hA.2 (indicatorOne B) hB.2 1 1
  have hprod := hmul (indicatorOne A) hA.2 (indicatorOne B) hB.2
  have h := hlin
    (fun x ↦ indicatorOne A x + indicatorOne B x) (by simpa using hadd)
    (fun x ↦ indicatorOne A x * indicatorOne B x) hprod 1 (-1)
  rw [indicatorOne_union]
  convert h using 1
  funext x
  ring

theorem indicatorFamily_accumulate
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hH : IsClosedL2FunctionSubspace M H)
    (hmul : ∀ f ∈ H, ∀ g ∈ H, (fun x ↦ f x * g x) ∈ H)
    (A : ℕ → Set M.X) (hA : ∀ n, A n ∈ indicatorFamily M H) :
    ∀ n, Set.accumulate A n ∈ indicatorFamily M H := by
  intro n
  induction n with
  | zero =>
      simpa using hA 0
  | succ n ih =>
      rw [Set.accumulate_succ]
      exact indicatorFamily_union M H hH hmul ih (hA (n + 1))

theorem indicatorFamily_iUnion
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hH : IsClosedL2FunctionSubspace M H)
    (hmul : ∀ f ∈ H, ∀ g ∈ H, (fun x ↦ f x * g x) ∈ H)
    (A : ℕ → Set M.X) (hA : ∀ n, A n ∈ indicatorFamily M H) :
    (⋃ n, A n) ∈ indicatorFamily M H := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let U : Set M.X := ⋃ n, A n
  let S : ℕ → Set M.X := Set.accumulate A
  have hS : ∀ n, S n ∈ indicatorFamily M H :=
    indicatorFamily_accumulate M H hH hmul A hA
  have hUmeas : MeasurableSet U := MeasurableSet.iUnion fun n ↦ (hA n).1
  refine ⟨hUmeas, ?_⟩
  rcases hH with ⟨_hzero, hLp, _hlin, _hae, hclosed⟩
  apply hclosed (fun n ↦ indicatorOne (S n)) (fun n ↦ (hS n).2)
    (indicatorOne U)
  · exact memLp_indicator_const 2 hUmeas (1 : ℂ) (Or.inr (by finiteness))
  · have hmono : Monotone S := by
      simpa [S] using (Set.monotone_accumulate (s := A))
    have hsub : ∀ n, S n ⊆ U := fun n ↦ Set.accumulate_subset_iUnion n
    have hsymm : ∀ n, S n ∆ U = U \ S n := by
      intro n
      ext x
      simp only [mem_symmDiff, mem_diff]
      tauto
    have hdiffmeas : ∀ n, MeasurableSet (U \ S n) :=
      fun n ↦ hUmeas.diff (hS n).1
    have hantitone : Antitone (fun n ↦ U \ S n) := by
      intro i j hij x hx
      exact ⟨hx.1, fun hxj ↦ hx.2 (hmono hij hxj)⟩
    have hinter : (⋂ n, U \ S n) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxall := Set.mem_iInter.mp hx
      have hxU : x ∈ U := (hxall 0).1
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxU
      exact (hxall n).2 (Set.subset_accumulate hxn)
    have hmeasure : Tendsto (fun n ↦ M.μ (S n ∆ U)) atTop (nhds 0) := by
      simp_rw [hsymm]
      have ht := tendsto_measure_iInter_atTop
        (μ := M.μ) (fun n ↦ (hdiffmeas n).nullMeasurableSet)
        hantitone ⟨0, by finiteness⟩
      rw [hinter, measure_empty] at ht
      exact ht
    have hrpow : Tendsto
        (fun n ↦ M.μ (S n ∆ U) ^ (1 / (2 : ENNReal).toReal))
        atTop (nhds 0) := by
      convert (ENNReal.continuous_rpow_const.tendsto 0).comp hmeasure using 1
      simp
    convert hrpow using 1
    funext n
    change eLpNorm
      ((S n).indicator (fun _ ↦ (1 : ℂ)) -
        U.indicator (fun _ ↦ (1 : ℂ))) 2 M.μ =
      M.μ (S n ∆ U) ^ (1 / (2 : ENNReal).toReal)
    rw [eLpNorm_indicator_sub_indicator]
    rw [eLpNorm_indicator_const (p := (2 : ENNReal)) (c := (1 : ℂ))
      ((hS n).1.symmDiff hUmeas) (by norm_num) (by norm_num)]
    simp

theorem indicatorFamily_isSigmaAlgebra
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hH : IsClosedL2FunctionSubspace M H)
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H)
    (hmul : ∀ f ∈ H, ∀ g ∈ H, (fun x ↦ f x * g x) ∈ H) :
    Chapter00.IsSigmaAlgebraFamily (indicatorFamily M H) := by
  exact ⟨indicatorFamily_univ M H hone,
    fun _ hA ↦ indicatorFamily_compl M H hH hone hA,
    fun A hA ↦ indicatorFamily_iUnion M H hM hH hmul A hA⟩

/-- The indicator family only needs multiplication closure for indicators,
not for arbitrary pairs of `L²` functions.  This is the exact strength needed
for subspaces such as the almost-periodic Koopman vectors, whose general
pointwise products need not belong to `L²`. -/
theorem indicatorFamily_union_of_indicator_mul
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hH : IsClosedL2FunctionSubspace M H)
    (hmulIndicator : ∀ {A B : Set M.X},
      indicatorOne A ∈ H → indicatorOne B ∈ H →
        (fun x ↦ indicatorOne A x * indicatorOne B x) ∈ H)
    {A B : Set M.X}
    (hA : A ∈ indicatorFamily M H) (hB : B ∈ indicatorFamily M H) :
    A ∪ B ∈ indicatorFamily M H := by
  rcases hH with ⟨_hzero, _hLp, hlin, _hae, _hclosed⟩
  refine ⟨hA.1.union hB.1, ?_⟩
  have hadd := hlin (indicatorOne A) hA.2
    (indicatorOne B) hB.2 1 1
  have hprod := hmulIndicator hA.2 hB.2
  have h := hlin
    (fun x ↦ indicatorOne A x + indicatorOne B x) (by simpa using hadd)
    (fun x ↦ indicatorOne A x * indicatorOne B x) hprod 1 (-1)
  rw [indicatorOne_union]
  convert h using 1
  funext x
  ring

theorem indicatorFamily_accumulate_of_indicator_mul
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hH : IsClosedL2FunctionSubspace M H)
    (hmulIndicator : ∀ {A B : Set M.X},
      indicatorOne A ∈ H → indicatorOne B ∈ H →
        (fun x ↦ indicatorOne A x * indicatorOne B x) ∈ H)
    (A : ℕ → Set M.X) (hA : ∀ n, A n ∈ indicatorFamily M H) :
    ∀ n, Set.accumulate A n ∈ indicatorFamily M H := by
  intro n
  induction n with
  | zero =>
      simpa using hA 0
  | succ n ih =>
      rw [Set.accumulate_succ]
      exact indicatorFamily_union_of_indicator_mul
        M H hH hmulIndicator ih (hA (n + 1))

theorem indicatorFamily_iUnion_of_indicator_mul
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hH : IsClosedL2FunctionSubspace M H)
    (hmulIndicator : ∀ {A B : Set M.X},
      indicatorOne A ∈ H → indicatorOne B ∈ H →
        (fun x ↦ indicatorOne A x * indicatorOne B x) ∈ H)
    (A : ℕ → Set M.X) (hA : ∀ n, A n ∈ indicatorFamily M H) :
    (⋃ n, A n) ∈ indicatorFamily M H := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let U : Set M.X := ⋃ n, A n
  let S : ℕ → Set M.X := Set.accumulate A
  have hS : ∀ n, S n ∈ indicatorFamily M H :=
    indicatorFamily_accumulate_of_indicator_mul
      M H hH hmulIndicator A hA
  have hUmeas : MeasurableSet U :=
    MeasurableSet.iUnion fun n ↦ (hA n).1
  refine ⟨hUmeas, ?_⟩
  rcases hH with ⟨_hzero, hLp, _hlin, _hae, hclosed⟩
  apply hclosed (fun n ↦ indicatorOne (S n)) (fun n ↦ (hS n).2)
    (indicatorOne U)
  · exact memLp_indicator_const 2 hUmeas (1 : ℂ)
      (Or.inr (by finiteness))
  · have hmono : Monotone S := by
      simpa [S] using (Set.monotone_accumulate (s := A))
    have hsub : ∀ n, S n ⊆ U :=
      fun n ↦ Set.accumulate_subset_iUnion n
    have hsymm : ∀ n, S n ∆ U = U \ S n := by
      intro n
      ext x
      simp only [mem_symmDiff, mem_diff]
      tauto
    have hdiffmeas : ∀ n, MeasurableSet (U \ S n) :=
      fun n ↦ hUmeas.diff (hS n).1
    have hantitone : Antitone (fun n ↦ U \ S n) := by
      intro i j hij x hx
      exact ⟨hx.1, fun hxj ↦ hx.2 (hmono hij hxj)⟩
    have hinter : (⋂ n, U \ S n) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxall := Set.mem_iInter.mp hx
      have hxU : x ∈ U := (hxall 0).1
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxU
      exact (hxall n).2 (Set.subset_accumulate hxn)
    have hmeasure :
        Tendsto (fun n ↦ M.μ (S n ∆ U)) atTop (nhds 0) := by
      simp_rw [hsymm]
      have ht := tendsto_measure_iInter_atTop
        (μ := M.μ) (fun n ↦ (hdiffmeas n).nullMeasurableSet)
        hantitone ⟨0, by finiteness⟩
      rw [hinter, measure_empty] at ht
      exact ht
    have hrpow : Tendsto
        (fun n ↦ M.μ (S n ∆ U) ^
          (1 / (2 : ENNReal).toReal)) atTop (nhds 0) := by
      convert
        (ENNReal.continuous_rpow_const.tendsto 0).comp hmeasure using 1
      simp
    convert hrpow using 1
    funext n
    change eLpNorm
      ((S n).indicator (fun _ ↦ (1 : ℂ)) -
        U.indicator (fun _ ↦ (1 : ℂ))) 2 M.μ =
      M.μ (S n ∆ U) ^ (1 / (2 : ENNReal).toReal)
    rw [eLpNorm_indicator_sub_indicator]
    rw [eLpNorm_indicator_const (p := (2 : ENNReal)) (c := (1 : ℂ))
      ((hS n).1.symmDiff hUmeas) (by norm_num) (by norm_num)]
    simp

/-- Indicator-local multiplication closure suffices to make
`indicatorFamily` a σ-algebra. -/
theorem indicatorFamily_isSigmaAlgebra_of_indicator_mul
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hH : IsClosedL2FunctionSubspace M H)
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H)
    (hmulIndicator : ∀ {A B : Set M.X},
      indicatorOne A ∈ H → indicatorOne B ∈ H →
        (fun x ↦ indicatorOne A x * indicatorOne B x) ∈ H) :
    Chapter00.IsSigmaAlgebraFamily (indicatorFamily M H) := by
  exact ⟨indicatorFamily_univ M H hone,
    fun _ hA ↦ indicatorFamily_compl M H hH hone hA,
    fun A hA ↦ indicatorFamily_iUnion_of_indicator_mul
      M H hM hH hmulIndicator A hA⟩

theorem mem_const
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hH : IsClosedL2FunctionSubspace M H)
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H) (c : ℂ) :
    (fun _ : M.X ↦ c) ∈ H := by
  rcases hH with ⟨_hzero, _hLp, hlin, _hae, _hclosed⟩
  have h := hlin (fun _ : M.X ↦ (1 : ℂ)) hone
    (fun _ : M.X ↦ (1 : ℂ)) hone c 0
  simpa using h

theorem mem_add
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hH : IsClosedL2FunctionSubspace M H)
    {f g : M.X → ℂ} (hf : f ∈ H) (hg : g ∈ H) :
    (fun x ↦ f x + g x) ∈ H := by
  simpa using hH.2.2.1 f hf g hg 1 1

theorem mem_sub
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hH : IsClosedL2FunctionSubspace M H)
    {f g : M.X → ℂ} (hf : f ∈ H) (hg : g ∈ H) :
    (fun x ↦ f x - g x) ∈ H := by
  have h := hH.2.2.1 f hf g hg 1 (-1)
  convert h using 1
  funext x
  ring

theorem mem_smul
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hH : IsClosedL2FunctionSubspace M H)
    {f : M.X → ℂ} (hf : f ∈ H) (c : ℂ) :
    (fun x ↦ c * f x) ∈ H := by
  have h := hH.2.2.1 f hf f hf c 0
  simpa using h

theorem mem_finset_sum
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hH : IsClosedL2FunctionSubspace M H)
    {ι : Type*} (s : Finset ι) (f : ι → M.X → ℂ)
    (hf : ∀ i ∈ s, f i ∈ H) :
    (fun x ↦ ∑ i ∈ s, f i x) ∈ H := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using hH.1
  | @insert i s hi ih =>
      have hm := mem_add M H hH (hf i (by simp))
        (ih fun j hj ↦ hf j (by simp [hj]))
      convert hm using 1
      funext x
      simp [Finset.sum_insert, hi]

theorem mem_pow
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H)
    (hmul : ∀ f ∈ H, ∀ g ∈ H, (fun x ↦ f x * g x) ∈ H)
    {f : M.X → ℂ} (hf : f ∈ H) :
    ∀ n : ℕ, (fun x ↦ (f x) ^ n) ∈ H := by
  intro n
  induction n with
  | zero => simpa using hone
  | succ n ih =>
      simpa [pow_succ] using hmul (fun x ↦ (f x) ^ n) ih f hf

theorem polynomial_eval_mem
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hH : IsClosedL2FunctionSubspace M H)
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H)
    (hmul : ∀ f ∈ H, ∀ g ∈ H, (fun x ↦ f x * g x) ∈ H)
    {h : M.X → ℝ} (hh : (fun x ↦ (h x : ℂ)) ∈ H)
    (p : Polynomial ℝ) :
    (fun x ↦ Complex.ofReal (p.eval (h x))) ∈ H := by
  have hterm : ∀ n ∈ p.support,
      (fun x ↦ ((p.coeff n : ℝ) : ℂ) * (h x : ℂ) ^ n) ∈ H := by
    intro n hn
    exact mem_smul M H hH
      (mem_pow M H hone hmul hh n) (p.coeff n : ℂ)
  have hsum := mem_finset_sum M H hH p.support
    (fun n x ↦ ((p.coeff n : ℝ) : ℂ) * (h x : ℂ) ^ n) hterm
  convert hsum using 1
  funext x
  rw [Polynomial.eval_eq_sum]
  simp only [Polynomial.sum, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow]

theorem continuous_real_function_mem
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hH : IsClosedL2FunctionSubspace M H)
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H)
    (hmul : ∀ f ∈ H, ∀ g ∈ H, (fun x ↦ f x * g x) ∈ H)
    {h : M.X → ℝ} (hhmeas : Measurable h)
    (hh : (fun x ↦ (h x : ℂ)) ∈ H)
    (a b : ℝ) (hab : ∀ x, h x ∈ Set.Icc a b)
    (F : ℝ → ℝ) (hF : Continuous F)
    (C : ℝ) (hC : ∀ t ∈ Set.Icc a b, |F t| ≤ C) :
    (fun x ↦ Complex.ofReal (F (h x))) ∈ H := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  choose p hp using fun n : ℕ ↦
    exists_polynomial_near_of_continuousOn a b F hF.continuousOn
      ((1 : ℝ) / (n + 1)) (by positivity)
  let q : ℕ → M.X → ℂ := fun n x ↦ Complex.ofReal ((p n).eval (h x))
  have hq : ∀ n, q n ∈ H := fun n ↦
    polynomial_eval_mem M H hH hone hmul hh (p n)
  apply hH.2.2.2.2 q hq (fun x ↦ Complex.ofReal (F (h x)))
  · exact MemLp.of_bound
      (Complex.continuous_ofReal.measurable.comp
        (hF.measurable.comp hhmeas)).aestronglyMeasurable C
      (Eventually.of_forall fun x ↦ by
        simpa [Complex.norm_real, Real.norm_eq_abs] using hC (h x) (hab x))
  · have hu : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((1 : ℝ) / (n + 1)))
        atTop (nhds (0 : ENNReal)) := by
      simpa using ENNReal.tendsto_ofReal
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (nhds 0))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    · exact fun _ ↦ zero_le _
    · intro n
      calc
        eLpNorm (fun x ↦ q n x - Complex.ofReal (F (h x))) 2 M.μ
            ≤ eLpNorm (fun _ : M.X ↦
                Complex.ofReal ((1 : ℝ) / (n + 1))) 2 M.μ := by
              apply eLpNorm_mono
              intro x
              have hnear := hp n (h x) (hab x)
              have heps : 0 ≤ (1 : ℝ) / (n + 1) := by positivity
              change ‖Complex.ofReal ((p n).eval (h x)) -
                Complex.ofReal (F (h x))‖ ≤
                ‖Complex.ofReal ((1 : ℝ) / (n + 1))‖
              rw [← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
                Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg heps]
              exact hnear.le
        _ = ENNReal.ofReal ((1 : ℝ) / (n + 1)) := by
              have heps : 0 ≤ (1 : ℝ) / (n + 1) := by positivity
              rw [eLpNorm_const' (p := (2 : ENNReal)) _ (by norm_num) (by norm_num)]
              rw [measure_univ, ENNReal.one_rpow, mul_one]
              rw [enorm_eq_nnnorm, ENNReal.ofReal_eq_coe_nnreal heps]
              norm_cast
              apply NNReal.eq
              simp [Real.norm_eq_abs]
              positivity

def ramp (c : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  min 1 (max 0 (((n + 1 : ℕ) : ℝ) * (t - c)))

theorem ramp_continuous (c : ℝ) (n : ℕ) :
    Continuous (ramp c n) := by
  exact continuous_const.min
    (continuous_const.max
      (continuous_const.mul (continuous_id.sub continuous_const)))

theorem ramp_mem_Icc (c : ℝ) (n : ℕ) (t : ℝ) :
    ramp c n t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

theorem ramp_tendsto_indicator (c t : ℝ) :
    Tendsto (fun n : ℕ ↦ ramp c n t) atTop
      (nhds (if c < t then 1 else 0)) := by
  by_cases hct : c < t
  · have hd : 0 < t - c := sub_pos.mpr hct
    have ht : Tendsto
        (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) * (t - c)) atTop atTop := by
      convert
        (tendsto_natCast_atTop_atTop.comp
          (tendsto_add_atTop_nat 1)).const_mul_atTop hd using 1
      funext n
      simp [mul_comm]
    have hev : ∀ᶠ n : ℕ in atTop,
        ((n + 1 : ℕ) : ℝ) * (t - c) ≥ 1 :=
      ht.eventually (eventually_ge_atTop 1)
    rw [if_pos hct]
    refine (tendsto_congr' (hev.mono fun n hn ↦ ?_)).2 tendsto_const_nhds
    unfold ramp
    have hz : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * (t - c) :=
      le_trans (by norm_num) hn
    rw [max_eq_right hz, min_eq_left hn]
  · have htc : t - c ≤ 0 := sub_nonpos.mpr (not_lt.mp hct)
    rw [if_neg hct]
    convert tendsto_const_nhds using 1
    funext n
    have hn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    unfold ramp
    rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos hn htc)]
    norm_num

/-- The analytic part of the upper-level-set construction only needs the ramp
approximants to lie in the closed `L²` subspace.  Their production may come
from a local bounded functional calculus rather than a global algebra
structure on the whole subspace. -/
theorem upper_level_indicator_mem_of_ramps
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hH : IsClosedL2FunctionSubspace M H)
    {h : M.X → ℝ} (hhmeas : Measurable h) (c : ℝ)
    (hq : ∀ n : ℕ,
      (fun x ↦ Complex.ofReal (ramp c n (h x))) ∈ H) :
    indicatorOne {x | c < h x} ∈ H := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let A : Set M.X := {x | c < h x}
  have hA : MeasurableSet A := hhmeas measurableSet_Ioi
  let q : ℕ → M.X → ℂ := fun n x ↦ Complex.ofReal (ramp c n (h x))
  apply hH.2.2.2.2 q hq (indicatorOne A)
  · exact memLp_indicator_const 2 hA 1 (Or.inr (by finiteness))
  · have htarget : Measurable (indicatorOne A) :=
      Measurable.indicator measurable_const hA
    have hqmeas : ∀ n, Measurable (q n) := fun n ↦
      Complex.continuous_ofReal.measurable.comp
        ((ramp_continuous c n).measurable.comp hhmeas)
    let F : ℕ → M.X → ℝ≥0∞ := fun n x ↦
      ‖q n x - indicatorOne A x‖ₑ ^ (2 : ℝ)
    have hFmeas : ∀ n, Measurable (F n) := fun n ↦
      ((hqmeas n).sub htarget).enorm.pow_const 2
    have hFbound : ∀ n, F n ≤ᵐ[M.μ] (fun _ ↦ (4 : ℝ≥0∞)) := by
      intro n
      filter_upwards [] with x
      have hqnorm : ‖q n x‖ ≤ 1 := by
        simp only [q, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (ramp_mem_Icc c n (h x)).1]
        exact (ramp_mem_Icc c n (h x)).2
      have htnorm : ‖indicatorOne A x‖ ≤ 1 := by
        by_cases hx : x ∈ A <;> simp [indicatorOne, hx]
      have hnorm : ‖q n x - indicatorOne A x‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by linarith)
      have henorm : ‖q n x - indicatorOne A x‖ₑ ≤ (2 : ℝ≥0∞) := by
        rw [enorm_eq_nnnorm]
        exact ENNReal.coe_le_coe.mpr (by exact_mod_cast hnorm)
      exact (ENNReal.rpow_le_rpow henorm (by norm_num)).trans_eq (by norm_num)
    have hFfin : (∫⁻ _ : M.X, (4 : ℝ≥0∞) ∂M.μ) ≠ ∞ := by
      simp
    have hFlim : ∀ᵐ x : M.X ∂M.μ,
        Tendsto (fun n ↦ F n x) atTop (nhds 0) := by
      filter_upwards [] with x
      have hr := ramp_tendsto_indicator c (h x)
      have hpoint :
          Tendsto (fun n ↦ q n x - indicatorOne A x) atTop (nhds 0) := by
        have hc := (Complex.continuous_ofReal.tendsto
          (if c < h x then 1 else 0)).comp hr
        have heq : ((if c < h x then 1 else 0 : ℝ) : ℂ) =
            indicatorOne A x := by
          by_cases hx : c < h x <;> simp [A, indicatorOne, hx]
        have hconst : Tendsto (fun _ : ℕ ↦ indicatorOne A x) atTop
            (nhds (indicatorOne A x)) := tendsto_const_nhds
        simpa only [q, Function.comp_apply, heq, sub_self] using
          hc.sub hconst
      have he : Tendsto
          (fun n ↦ ‖q n x - indicatorOne A x‖ₑ) atTop (nhds 0) := by
        simpa using (continuous_enorm.tendsto 0).comp hpoint
      have hp : Tendsto
          (fun n ↦ ‖q n x - indicatorOne A x‖ₑ ^ (2 : ℝ))
          atTop (nhds 0) := by
        simpa using
          ((ENNReal.continuous_rpow_const :
            Continuous (fun z : ℝ≥0∞ ↦ z ^ (2 : ℝ))).tendsto 0).comp he
      simpa [F] using hp
    have hint : Tendsto (fun n ↦ ∫⁻ x, F n x ∂M.μ) atTop (nhds 0) := by
      simpa using tendsto_lintegral_of_dominated_convergence
        (fun _ : M.X ↦ (4 : ℝ≥0∞)) hFmeas hFbound hFfin hFlim
    have hrpow : Tendsto
        (fun n ↦ (∫⁻ x, F n x ∂M.μ) ^ (1 / (2 : ℝ)))
        atTop (nhds 0) := by
      simpa using
        ((ENNReal.continuous_rpow_const :
          Continuous (fun z : ℝ≥0∞ ↦ z ^ (1 / (2 : ℝ)))).tendsto 0).comp hint
    convert hrpow using 1
    · funext n
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      simp only [ENNReal.toReal_ofNat]
      rfl

theorem upper_level_indicator_mem
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hH : IsClosedL2FunctionSubspace M H)
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H)
    (hmul : ∀ f ∈ H, ∀ g ∈ H, (fun x ↦ f x * g x) ∈ H)
    {h : M.X → ℝ} (hhmeas : Measurable h)
    (hh : (fun x ↦ (h x : ℂ)) ∈ H)
    (a b : ℝ) (hab : ∀ x, h x ∈ Set.Icc a b) (c : ℝ) :
    indicatorOne {x | c < h x} ∈ H := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let A : Set M.X := {x | c < h x}
  have hA : MeasurableSet A := hhmeas measurableSet_Ioi
  let q : ℕ → M.X → ℂ := fun n x ↦ Complex.ofReal (ramp c n (h x))
  have hq : ∀ n, q n ∈ H := fun n ↦
    continuous_real_function_mem M H hM hH hone hmul hhmeas hh a b hab
      (ramp c n) (ramp_continuous c n) 1
      (fun t _ ↦ by
        rw [abs_of_nonneg (ramp_mem_Icc c n t).1]
        exact (ramp_mem_Icc c n t).2)
  apply hH.2.2.2.2 q hq (indicatorOne A)
  · exact memLp_indicator_const 2 hA 1 (Or.inr (by finiteness))
  · have htarget : Measurable (indicatorOne A) :=
      Measurable.indicator measurable_const hA
    have hqmeas : ∀ n, Measurable (q n) := fun n ↦
      Complex.continuous_ofReal.measurable.comp
        ((ramp_continuous c n).measurable.comp hhmeas)
    let F : ℕ → M.X → ℝ≥0∞ := fun n x ↦
      ‖q n x - indicatorOne A x‖ₑ ^ (2 : ℝ)
    have hFmeas : ∀ n, Measurable (F n) := fun n ↦
      ((hqmeas n).sub htarget).enorm.pow_const 2
    have hFbound : ∀ n, F n ≤ᵐ[M.μ] (fun _ ↦ (4 : ℝ≥0∞)) := by
      intro n
      filter_upwards [] with x
      have hqnorm : ‖q n x‖ ≤ 1 := by
        simp only [q, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (ramp_mem_Icc c n (h x)).1]
        exact (ramp_mem_Icc c n (h x)).2
      have htnorm : ‖indicatorOne A x‖ ≤ 1 := by
        by_cases hx : x ∈ A <;> simp [indicatorOne, hx]
      have hnorm : ‖q n x - indicatorOne A x‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by linarith)
      have henorm : ‖q n x - indicatorOne A x‖ₑ ≤ (2 : ℝ≥0∞) := by
        rw [enorm_eq_nnnorm]
        exact ENNReal.coe_le_coe.mpr (by exact_mod_cast hnorm)
      exact (ENNReal.rpow_le_rpow henorm (by norm_num)).trans_eq (by norm_num)
    have hFfin : (∫⁻ _ : M.X, (4 : ℝ≥0∞) ∂M.μ) ≠ ∞ := by
      simp
    have hFlim : ∀ᵐ x : M.X ∂M.μ,
        Tendsto (fun n ↦ F n x) atTop (nhds 0) := by
      filter_upwards [] with x
      have hr := ramp_tendsto_indicator c (h x)
      have hpoint :
          Tendsto (fun n ↦ q n x - indicatorOne A x) atTop (nhds 0) := by
        have hc := (Complex.continuous_ofReal.tendsto
          (if c < h x then 1 else 0)).comp hr
        have heq : ((if c < h x then 1 else 0 : ℝ) : ℂ) =
            indicatorOne A x := by
          by_cases hx : c < h x <;> simp [A, indicatorOne, hx]
        have hconst : Tendsto (fun _ : ℕ ↦ indicatorOne A x) atTop
            (nhds (indicatorOne A x)) := tendsto_const_nhds
        simpa only [q, Function.comp_apply, heq, sub_self] using
          hc.sub hconst
      have he : Tendsto
          (fun n ↦ ‖q n x - indicatorOne A x‖ₑ) atTop (nhds 0) := by
        simpa using (continuous_enorm.tendsto 0).comp hpoint
      have hp : Tendsto
          (fun n ↦ ‖q n x - indicatorOne A x‖ₑ ^ (2 : ℝ))
          atTop (nhds 0) := by
        simpa using
          ((ENNReal.continuous_rpow_const :
            Continuous (fun z : ℝ≥0∞ ↦ z ^ (2 : ℝ))).tendsto 0).comp he
      simpa [F] using hp
    have hint : Tendsto (fun n ↦ ∫⁻ x, F n x ∂M.μ) atTop (nhds 0) := by
      simpa using tendsto_lintegral_of_dominated_convergence
        (fun _ : M.X ↦ (4 : ℝ≥0∞)) hFmeas hFbound hFfin hFlim
    have hrpow : Tendsto
        (fun n ↦ (∫⁻ x, F n x ∂M.μ) ^ (1 / (2 : ℝ)))
        atTop (nhds 0) := by
      simpa using
        ((ENNReal.continuous_rpow_const :
          Continuous (fun z : ℝ≥0∞ ↦ z ^ (1 / (2 : ℝ)))).tendsto 0).comp hint
    convert hrpow using 1
    · funext n
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      simp only [ENNReal.toReal_ofNat]
      rfl

theorem exists_bounded_measurable_representative_of_memLp_top
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hH : IsClosedL2FunctionSubspace M H)
    {f : M.X → ℂ} (hf : f ∈ H) (hftop : M.lpMember ⊤ f) :
    ∃ g : M.X → ℂ, ∃ C : ℝ,
      Measurable g ∧ f =ᵐ[M.μ] g ∧ (∀ x, ‖g x‖ ≤ C) ∧ g ∈ H := by
  have hess : eLpNormEssSup f M.μ < ⊤ := by
    simpa only [eLpNorm_exponent_top] using hftop.2
  obtain ⟨C, hC⟩ :=
    eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hess
  let m : M.X → ℂ := hftop.1.mk f
  have hmmeas : Measurable m := hftop.1.measurable_mk
  have hfm : f =ᵐ[M.μ] m := hftop.1.ae_eq_mk
  have hmC : ∀ᵐ x ∂M.μ, ‖m x‖₊ ≤ C := by
    filter_upwards [hC, hfm] with x hx hxeq
    rw [← hxeq]
    exact hx
  let g : M.X → ℂ := fun x ↦ if ‖m x‖₊ ≤ C then m x else 0
  have hgmeas : Measurable g := by
    exact Measurable.ite
      (measurableSet_le hmmeas.nnnorm measurable_const) hmmeas measurable_const
  have hfg : f =ᵐ[M.μ] g := by
    filter_upwards [hfm, hmC] with x hxeq hxC
    simp [g, hxC, hxeq]
  refine ⟨g, C, hgmeas, hfg, ?_, hH.2.2.2.1 f hf g hfg⟩
  intro x
  by_cases hx : ‖m x‖₊ ≤ C
  · change ‖if ‖m x‖₊ ≤ C then m x else 0‖ ≤ (C : ℝ)
    rw [if_pos hx]
    exact_mod_cast hx
  · simp [g, hx]

theorem exists_bounded_measurable_representative
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hH : IsClosedL2FunctionSubspace M H)
    (htop : ∀ f ∈ H, M.lpMember ⊤ f)
    {f : M.X → ℂ} (hf : f ∈ H) :
    ∃ g : M.X → ℂ, ∃ C : ℝ,
      Measurable g ∧ f =ᵐ[M.μ] g ∧ (∀ x, ‖g x‖ ≤ C) ∧ g ∈ H :=
  exists_bounded_measurable_representative_of_memLp_top
    M H hH hf (htop f hf)

theorem real_part_mem
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hH : IsClosedL2FunctionSubspace M H)
    (hstar : ∀ f ∈ H, (fun x ↦ star (f x)) ∈ H)
    {f : M.X → ℂ} (hf : f ∈ H) :
    (fun x ↦ ((f x).re : ℂ)) ∈ H := by
  have hs := hstar f hf
  have ha := mem_add M H hH hf hs
  have hr := mem_smul M H hH ha ((1 : ℂ) / 2)
  convert hr using 1
  funext x
  apply Complex.ext
  · simp
    ring
  · simp

theorem imag_part_mem
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hH : IsClosedL2FunctionSubspace M H)
    (hstar : ∀ f ∈ H, (fun x ↦ star (f x)) ∈ H)
    {f : M.X → ℂ} (hf : f ∈ H) :
    (fun x ↦ ((f x).im : ℂ)) ∈ H := by
  have hs := hstar f hf
  have hd := mem_sub M H hH hf hs
  have hi := mem_smul M H hH hd (-Complex.I / 2)
  convert hi using 1
  funext x
  apply Complex.ext
  · simp
    ring
  · simp

theorem measurableSpace_indicatorFamily
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hH : IsClosedL2FunctionSubspace M H)
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H)
    (hmul : ∀ f ∈ H, ∀ g ∈ H, (fun x ↦ f x * g x) ∈ H) :
    ∃ mH : MeasurableSpace M.X,
      mH = MeasurableSpace.generateFrom (indicatorFamily M H) ∧
      ∀ A : Set M.X, @MeasurableSet M.X mH A ↔ A ∈ indicatorFamily M H := by
  let mH := MeasurableSpace.generateFrom (indicatorFamily M H)
  refine ⟨mH, rfl, ?_⟩
  intro A
  constructor
  · intro hA
    exact MeasurableSpace.generateFrom_induction
      (indicatorFamily M H)
      (fun B _ ↦ B ∈ indicatorFamily M H)
      (fun _ hB _ ↦ hB)
      (by
        have hu := indicatorFamily_univ M H hone
        simpa using indicatorFamily_compl M H hH hone hu)
      (fun _ _ hB ↦ indicatorFamily_compl M H hH hone hB)
      (fun B _ hB ↦ indicatorFamily_iUnion M H hM hH hmul B hB)
      A hA
  · intro hA
    exact MeasurableSpace.measurableSet_generateFrom hA

theorem measurableSet_generateFrom_indicatorFamily_iff
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hH : IsClosedL2FunctionSubspace M H)
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H)
    (hmul : ∀ f ∈ H, ∀ g ∈ H, (fun x ↦ f x * g x) ∈ H)
    (A : Set M.X) :
    @MeasurableSet M.X
      (MeasurableSpace.generateFrom (indicatorFamily M H)) A ↔
      A ∈ indicatorFamily M H := by
  obtain ⟨mH, hmH, hall⟩ :=
    measurableSpace_indicatorFamily M H hM hH hone hmul
  subst mH
  exact hall A

theorem simpleFunc_mem_of_indicatorFamily
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hH : IsClosedL2FunctionSubspace M H)
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H)
    (hmul : ∀ f ∈ H, ∀ g ∈ H, (fun x ↦ f x * g x) ∈ H)
    (s : @SimpleFunc M.X
      (MeasurableSpace.generateFrom (indicatorFamily M H)) ℂ) :
    (fun x ↦ s x) ∈ H := by
  induction s using SimpleFunc.induction with
  | const c hs =>
      have hsFam :=
        (measurableSet_generateFrom_indicatorFamily_iff
          M H hM hH hone hmul _).mp hs
      have hc := mem_smul M H hH hsFam.2 c
      convert hc using 1
      funext x
      by_cases hx : x ∈ ‹Set M.X› <;> simp [indicatorOne, hx]
  | add _ hf hg =>
      exact mem_add M H hH hf hg

theorem member_has_indicatorFamily_measurable_representative
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hH : IsClosedL2FunctionSubspace M H)
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H)
    (htop : ∀ f ∈ H, M.lpMember ⊤ f)
    (hstar : ∀ f ∈ H, (fun x ↦ star (f x)) ∈ H)
    (hmul : ∀ f ∈ H, ∀ g ∈ H, (fun x ↦ f x * g x) ∈ H)
    {f : M.X → ℂ} (hf : f ∈ H) :
    HasMeasurableRepresentativeForFamily M (indicatorFamily M H) f := by
  obtain ⟨g, C, hgmeas, hfg, hgbound, hgH⟩ :=
    exists_bounded_measurable_representative M H hH htop hf
  let mH : MeasurableSpace M.X :=
    MeasurableSpace.generateFrom (indicatorFamily M H)
  have hreH : (fun x ↦ ((g x).re : ℂ)) ∈ H :=
    real_part_mem M H hH hstar hgH
  have himH : (fun x ↦ ((g x).im : ℂ)) ∈ H :=
    imag_part_mem M H hH hstar hgH
  have hreBound : ∀ x, (g x).re ∈ Set.Icc (-|C|) |C| := by
    intro x
    have hx : |(g x).re| ≤ |C| :=
      (RCLike.abs_re_le_norm (g x)).trans ((hgbound x).trans (le_abs_self C))
    exact (abs_le.mp hx)
  have himBound : ∀ x, (g x).im ∈ Set.Icc (-|C|) |C| := by
    intro x
    have hx : |(g x).im| ≤ |C| :=
      (RCLike.abs_im_le_norm (g x)).trans ((hgbound x).trans (le_abs_self C))
    exact (abs_le.mp hx)
  have hre_mH : @Measurable M.X ℝ mH inferInstance (fun x ↦ (g x).re) := by
    apply measurable_of_Ioi
    intro c
    apply MeasurableSpace.measurableSet_generateFrom
    exact ⟨hgmeas.re measurableSet_Ioi,
      upper_level_indicator_mem M H hM hH hone hmul hgmeas.re hreH
        (-|C|) |C| hreBound c⟩
  have him_mH : @Measurable M.X ℝ mH inferInstance (fun x ↦ (g x).im) := by
    apply measurable_of_Ioi
    intro c
    apply MeasurableSpace.measurableSet_generateFrom
    exact ⟨hgmeas.im measurableSet_Ioi,
      upper_level_indicator_mem M H hM hH hone hmul hgmeas.im himH
        (-|C|) |C| himBound c⟩
  refine ⟨g, ?_, hfg⟩
  have hreC : @Measurable M.X ℂ mH inferInstance
      (fun x ↦ ((g x).re : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hre_mH
  have himC : @Measurable M.X ℂ mH inferInstance
      (fun x ↦ ((g x).im : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp him_mH
  have hI : @Measurable M.X ℂ mH inferInstance
      (fun _ ↦ Complex.I) := measurable_const
  have hrec : @Measurable M.X ℂ mH inferInstance
      (fun x ↦ ((g x).re : ℂ) + Complex.I * ((g x).im : ℂ)) :=
    hreC.add (hI.mul himC)
  convert hrec using 1
  funext x
  apply Complex.ext <;> simp

set_option maxHeartbeats 800000 in
theorem mem_of_indicatorFamily_measurable_representative
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hH : IsClosedL2FunctionSubspace M H)
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H)
    (hmul : ∀ f ∈ H, ∀ g ∈ H, (fun x ↦ f x * g x) ∈ H)
    {f : M.X → ℂ} (hf2 : M.lpMember 2 f)
    (hfmeas : HasMeasurableRepresentativeForFamily
      M (indicatorFamily M H) f) :
    f ∈ H := by
  obtain ⟨g, hgsub, hfg⟩ := hfmeas
  have hmHle :
      MeasurableSpace.generateFrom (indicatorFamily M H) ≤
        M.measurableSpace := by
    apply MeasurableSpace.generateFrom_le
    intro A hA
    exact hA.1
  have hgmeas : @Measurable M.X ℂ M.measurableSpace inferInstance g :=
    hgsub.mono hmHle le_rfl
  have hg2 : M.lpMember 2 g := (memLp_congr_ae hfg).mp hf2
  let s : ℕ → @SimpleFunc M.X
      (MeasurableSpace.generateFrom (indicatorFamily M H)) ℂ := by
    letI : MeasurableSpace M.X :=
      MeasurableSpace.generateFrom (indicatorFamily M H)
    exact fun n ↦
      SimpleFunc.approxOn g hgsub (Set.range g ∪ {0}) 0 (by simp) n
  have hsH : ∀ n, (fun x ↦ s n x) ∈ H := fun n ↦
    simpleFunc_mem_of_indicatorFamily M H hM hH hone hmul (s n)
  have hconv0 : Tendsto
      (fun n ↦ eLpNorm
        (⇑(SimpleFunc.approxOn g hgmeas
          (Set.range g ∪ {0}) 0 (by simp) n) - g)
        2 M.μ) atTop (nhds 0) := by
    exact SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm
      (p := (2 : ENNReal)) (by norm_num) hgmeas hg2.2
  have hconv : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ s n x - g x) 2 M.μ)
      atTop (nhds 0) := by
    convert hconv0 using 1
  have hgH := hH.2.2.2.2 (fun n x ↦ s n x) hsH g hg2 hconv
  exact hH.2.2.2.1 g hgH f hfg.symm

theorem measurableSet_generateFrom_indicatorFamily_iff_of_indicator_mul
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hH : IsClosedL2FunctionSubspace M H)
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H)
    (hmulIndicator : ∀ {A B : Set M.X},
      indicatorOne A ∈ H → indicatorOne B ∈ H →
        (fun x ↦ indicatorOne A x * indicatorOne B x) ∈ H)
    (A : Set M.X) :
    @MeasurableSet M.X
      (MeasurableSpace.generateFrom (indicatorFamily M H)) A ↔
      A ∈ indicatorFamily M H := by
  constructor
  · intro hA
    exact MeasurableSpace.generateFrom_induction
      (indicatorFamily M H)
      (fun B _ ↦ B ∈ indicatorFamily M H)
      (fun _ hB _ ↦ hB)
      (by
        have hu := indicatorFamily_univ M H hone
        simpa using indicatorFamily_compl M H hH hone hu)
      (fun _ _ hB ↦ indicatorFamily_compl M H hH hone hB)
      (fun B _ hB ↦ indicatorFamily_iUnion_of_indicator_mul
        M H hM hH hmulIndicator B hB)
      A hA
  · intro hA
    exact MeasurableSpace.measurableSet_generateFrom hA

theorem simpleFunc_mem_of_indicatorFamily_of_indicator_mul
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hH : IsClosedL2FunctionSubspace M H)
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H)
    (hmulIndicator : ∀ {A B : Set M.X},
      indicatorOne A ∈ H → indicatorOne B ∈ H →
        (fun x ↦ indicatorOne A x * indicatorOne B x) ∈ H)
    (s : @SimpleFunc M.X
      (MeasurableSpace.generateFrom (indicatorFamily M H)) ℂ) :
    (fun x ↦ s x) ∈ H := by
  induction s using SimpleFunc.induction with
  | const c hs =>
      have hsFam :=
        (measurableSet_generateFrom_indicatorFamily_iff_of_indicator_mul
          M H hM hH hone hmulIndicator _).mp hs
      have hc := mem_smul M H hH hsFam.2 c
      convert hc using 1
      funext x
      by_cases hx : x ∈ ‹Set M.X› <;>
        simp [indicatorOne, hx]
  | add _ hf hg =>
      exact mem_add M H hH hf hg

set_option maxHeartbeats 800000 in
/-- Every `L²` function measurable for the σ-algebra generated by the
indicator members of `H` belongs to `H`; only indicator-local multiplication
closure is needed. -/
theorem mem_of_indicatorFamily_measurable_representative_of_indicator_mul
    (M : System.{u}) (H : Set (M.X → ℂ))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hH : IsClosedL2FunctionSubspace M H)
    (hone : (fun _ : M.X ↦ (1 : ℂ)) ∈ H)
    (hmulIndicator : ∀ {A B : Set M.X},
      indicatorOne A ∈ H → indicatorOne B ∈ H →
        (fun x ↦ indicatorOne A x * indicatorOne B x) ∈ H)
    {f : M.X → ℂ} (hf2 : M.lpMember 2 f)
    (hfmeas : HasMeasurableRepresentativeForFamily
      M (indicatorFamily M H) f) :
    f ∈ H := by
  obtain ⟨g, hgsub, hfg⟩ := hfmeas
  have hmHle :
      MeasurableSpace.generateFrom (indicatorFamily M H) ≤
        M.measurableSpace := by
    apply MeasurableSpace.generateFrom_le
    intro A hA
    exact hA.1
  have hgmeas : @Measurable M.X ℂ M.measurableSpace inferInstance g :=
    hgsub.mono hmHle le_rfl
  have hg2 : M.lpMember 2 g := (memLp_congr_ae hfg).mp hf2
  let s : ℕ → @SimpleFunc M.X
      (MeasurableSpace.generateFrom (indicatorFamily M H)) ℂ := by
    letI : MeasurableSpace M.X :=
      MeasurableSpace.generateFrom (indicatorFamily M H)
    exact fun n ↦
      SimpleFunc.approxOn g hgsub (Set.range g ∪ {0}) 0 (by simp) n
  have hsH : ∀ n, (fun x ↦ s n x) ∈ H := fun n ↦
    simpleFunc_mem_of_indicatorFamily_of_indicator_mul
      M H hM hH hone hmulIndicator (s n)
  have hconv0 : Tendsto
      (fun n ↦ eLpNorm
        (⇑(SimpleFunc.approxOn g hgmeas
          (Set.range g ∪ {0}) 0 (by simp) n) - g)
        2 M.μ) atTop (nhds 0) := by
    exact SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm
      (p := (2 : ENNReal)) (by norm_num) hgmeas hg2.2
  have hconv : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ s n x - g x) 2 M.μ)
      atTop (nhds 0) := by
    convert hconv0 using 1
  have hgH := hH.2.2.2.2 (fun n x ↦ s n x) hsH g hg2 hconv
  exact hH.2.2.2.1 g hgH f hfg.symm

/-- Having a representative measurable for a fixed generated σ-algebra is
closed under `L²` convergence. -/
theorem hasMeasurableRepresentativeForFamily_closed
    (M : System.{u}) (A : SetFamily M.X)
    (fseq : ℕ → M.X → ℂ)
    (hfseq2 : ∀ n, M.lpMember 2 (fseq n))
    (hfseqA : ∀ n,
      HasMeasurableRepresentativeForFamily M A (fseq n))
    (f : M.X → ℂ) (hf2 : M.lpMember 2 f)
    (hconv : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ fseq n x - f x) 2 M.μ)
      atTop (nhds 0)) :
    HasMeasurableRepresentativeForFamily M A f := by
  choose g hgmeas hfg using hfseqA
  have hinMeasure : TendstoInMeasure M.μ fseq atTop f := by
    apply tendstoInMeasure_of_tendsto_eLpNorm
      (p := (2 : ENNReal)) (by norm_num)
      (fun n ↦ (hfseq2 n).1) hf2.1
    simpa only [Pi.sub_apply] using hconv
  obtain ⟨ns, _hns, hsub⟩ := hinMeasure.exists_seq_tendsto_ae
  have hfgAll : ∀ᵐ x ∂M.μ, ∀ n, fseq n x = g n x :=
    ae_all_iff.mpr hfg
  have hsubg : ∀ᵐ x ∂M.μ,
      Tendsto (fun i ↦ g (ns i) x) atTop (nhds (f x)) := by
    filter_upwards [hsub, hfgAll] with x hx heq
    have heqfun :
        (fun i ↦ g (ns i) x) = fun i ↦ fseq (ns i) x := by
      funext i
      exact (heq (ns i)).symm
    rw [heqfun]
    exact hx
  let mA : MeasurableSpace M.X := MeasurableSpace.generateFrom A
  letI : MeasurableSpace M.X := mA
  let gLim : M.X → ℂ :=
    fun x ↦ limUnder atTop (fun i ↦ g (ns i) x)
  have hgLimMeas : StronglyMeasurable gLim := by
    exact StronglyMeasurable.limUnder
      (fun i ↦ (hgmeas (ns i)).stronglyMeasurable)
  refine ⟨gLim, hgLimMeas.measurable, ?_⟩
  filter_upwards [hsubg] with x hx
  exact hx.limUnder_eq.symm

theorem algebraOfBoundedFunctions
    (M : System.{u}) :
    AlgebraOfBoundedFunctionsStatement M := by
  intro hM H hH hone htop hstar hmul
  let A : SetFamily M.X := indicatorFamily M H
  refine ⟨A, indicatorFamily_isSigmaAlgebra M H hM hH hone hmul, ?_, ?_, ?_⟩
  · intro B hB
    exact hB.1
  · intro f
    constructor
    · intro hf
      exact ⟨hH.2.1 f hf,
        member_has_indicatorFamily_measurable_representative
          M H hM hH hone htop hstar hmul hf⟩
    · rintro ⟨hf2, hfmeas⟩
      exact mem_of_indicatorFamily_measurable_representative
        M H hM hH hone hmul hf2 hfmeas
  · rintro ⟨hinv, hcomp⟩
    obtain ⟨S, hT, hS, _hleft, hright⟩ := hinv
    intro B
    change
      @MeasurableSet M.X
          (MeasurableSpace.generateFrom (indicatorFamily M H)) B ↔
        @MeasurableSet M.X
          (MeasurableSpace.generateFrom (indicatorFamily M H))
          (M.T ⁻¹' B)
    rw [measurableSet_generateFrom_indicatorFamily_iff
          M H hM hH hone hmul B,
      measurableSet_generateFrom_indicatorFamily_iff
          M H hM hH hone hmul (M.T ⁻¹' B)]
    constructor
    · intro hB
      refine ⟨hT.1 B hB.1, ?_⟩
      have hc := (hcomp (indicatorOne B)).mp hB.2
      convert hc using 1
    · intro hpre
      have hBset : S ⁻¹' (M.T ⁻¹' B) = B := by
        ext x
        simp only [mem_preimage]
        rw [hright x]
      have hBmeas : MeasurableSet B := by
        rw [← hBset]
        exact hS.1 (M.T ⁻¹' B) hpre.1
      refine ⟨hBmeas, ?_⟩
      apply (hcomp (indicatorOne B)).mpr
      convert hpre.2 using 1

end Chapter02.AlgebraSubSigma
