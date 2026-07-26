import Chapter02.Ergodic.CorrelationSemiAlgebra
import Chapter02.Ergodic.FiniteMarkov
import Chapter01.Coding.MarkovCoding
import Chapter00.PerronFrobenius.PrimitiveAsymptotics
import Chapter02.Ergodic.BernoulliMixing

noncomputable section

open Classical Filter
open scoped BigOperators ENNReal

namespace Chapter02
namespace MarkovErgodic

universe u

private lemma cesaroTendsTo_const_mul (c : ℝ) {a : ℕ → ℝ} {l : ℝ}
    (ha : cesaroTendsTo a l) : cesaroTendsTo (fun n ↦ c * a n) (c * l) := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at ha ⊢
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ c) atTop (nhds c)).mul ha
  convert h using 1
  · funext N
    calc
      (((N + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1), c * a n) =
          ∑ n ∈ Finset.range (N + 1),
            (((N + 1 : ℕ) : ℝ)⁻¹ * c) * a n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ = (((N + 1 : ℕ) : ℝ)⁻¹ * c) *
          ∑ n ∈ Finset.range (N + 1), a n := by rw [Finset.mul_sum]
      _ = c * (((N + 1 : ℕ) : ℝ)⁻¹ *
          ∑ n ∈ Finset.range (N + 1), a n) := by ring

private lemma cesaroTendsTo_finset_sum {I : Type*} (s : Finset I)
    (a : I → ℕ → ℝ) (ha : ∀ i ∈ s, cesaroTendsTo (a i) 0) :
    cesaroTendsTo (fun n ↦ ∑ i ∈ s, a i n) 0 := by
  classical
  unfold cesaroTendsTo seqTendsTo cesaroAverage at ha ⊢
  have hsum := tendsto_finset_sum s (fun i hi ↦ ha i hi)
  convert hsum using 1
  · funext N
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  · simp

private lemma cesaroTendsTo_of_succ {a : ℕ → ℝ} {l C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n, |a n| ≤ C)
    (hsucc : cesaroTendsTo (fun n ↦ a (n + 1)) l) :
    cesaroTendsTo a l := by
  have hinv : Tendsto (fun N : ℕ ↦ (((N + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have herr : Tendsto
      (fun N : ℕ ↦ (((N + 1 : ℕ) : ℝ))⁻¹ * (a 0 - a (N + 1)))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (g := fun N : ℕ ↦
      (((N + 1 : ℕ) : ℝ))⁻¹ * (2 * C))
    · intro N
      exact norm_nonneg _
    · intro N
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity :
        0 ≤ (((N + 1 : ℕ) : ℝ))⁻¹)]
      have hsub : |a 0 - a (N + 1)| ≤ 2 * C := by
        calc
          |a 0 - a (N + 1)| ≤ |a 0| + |a (N + 1)| := abs_sub _ _
          _ ≤ C + C := add_le_add (ha 0) (ha (N + 1))
          _ = 2 * C := by ring
      exact mul_le_mul_of_nonneg_left hsub (by positivity)
    · simpa using hinv.mul_const (2 * C)
  unfold cesaroTendsTo seqTendsTo at hsucc ⊢
  have hadd := hsucc.add herr
  simpa only [add_zero] using hadd.congr' (Filter.Eventually.of_forall fun N ↦ by
    have hid : a 0 + ∑ n ∈ Finset.range (N + 1), a (n + 1) =
        (∑ n ∈ Finset.range (N + 1), a n) + a (N + 1) := by
      rw [add_comm, ← Finset.sum_range_succ', Finset.sum_range_succ]
    have hshiftSum : (∑ n ∈ Finset.range (N + 1), a (n + 1)) =
        (∑ n ∈ Finset.range (N + 1), a n) + a (N + 1) - a 0 := by
      linarith
    unfold cesaroAverage
    rw [hshiftSum]
    ring)

private lemma cesaroTendsTo_of_add_shift {a : ℕ → ℝ} {l C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n, |a n| ≤ C) (k : ℕ)
    (hshift : cesaroTendsTo (fun n ↦ a (n + k)) l) : cesaroTendsTo a l := by
  induction k generalizing a with
  | zero => simpa using hshift
  | succ k ih =>
      apply cesaroTendsTo_of_succ hC ha
      apply ih (a := fun n ↦ a (n + 1)) (fun n ↦ ha (n + 1))
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hshift

private theorem oneSided_map_eq {M : System.{u}} (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1)
    (h : Chapter01.IsOneSidedMarkovShiftWith M k p P) :
    ∃ e : M.X ≃ (ℕ → Fin k),
      Measurable e ∧ Measurable e.symm ∧
      MeasureTheory.Measure.map e M.μ =
        Chapter01.oneSidedMarkovMeasure k p P hP0 hP1 ∧
      (∀ x n, e (M.T x) n = e x (n + 1)) := by
  rcases h with ⟨hM, e, he, heinv, hT, hp, hsum, hP, hPsum, hstationary, hcyl⟩
  let μ := Chapter01.oneSidedMarkovMeasure k p P hP0 hP1
  refine ⟨e, he, heinv, ?_, hT⟩
  let ν := MeasureTheory.Measure.map e M.μ
  have hfin : ∀ n : ℕ,
      MeasureTheory.Measure.map (Chapter01.finitePrefix n) ν =
        MeasureTheory.Measure.map (Chapter01.finitePrefix n) μ := by
    intro n
    apply MeasureTheory.Measure.ext_of_singleton
    intro a
    have hfiber : MeasurableSet
        (Chapter01.finitePrefix n ⁻¹' ({a} : Set (Fin (n + 1) → Fin k))) :=
      (Chapter01.finitePrefix_measurable n) (MeasurableSet.singleton a)
    rw [MeasureTheory.Measure.map_apply (Chapter01.finitePrefix_measurable n)
      (MeasurableSet.singleton a)]
    change MeasureTheory.Measure.map e M.μ
      (Chapter01.finitePrefix n ⁻¹' {a}) = _
    rw [MeasureTheory.Measure.map_apply he hfiber]
    have hsource : e ⁻¹' (Chapter01.finitePrefix n ⁻¹' {a}) =
        {x | ∀ i : Fin (n + 1), e x i = a i} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      exact ⟨fun hx i ↦ congrFun hx i, fun hx ↦ funext hx⟩
    rw [hsource, hcyl n a]
    rw [MeasureTheory.Measure.map_apply (Chapter01.finitePrefix_measurable n)
      (MeasurableSet.singleton a)]
    have htarget : Chapter01.finitePrefix n ⁻¹' {a} =
        Chapter01.markovPrefixCylinder a := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff,
        Chapter01.markovPrefixCylinder, Set.mem_setOf_eq]
      exact ⟨fun hx i ↦ congrFun hx i, fun hx ↦ funext hx⟩
    rw [htarget]
    exact (Chapter01.oneSidedMarkovMeasure_prefix k p P hp hsum hP0 hP1 n a).symm
  apply MeasureTheory.Measure.ext_of_generateFrom_of_cover_subset
    (Chapter01.markovPrefixSetFamily_generate k)
    (Chapter01.markovPrefixSetFamily_piSystem k) (T := {Set.univ})
  · intro C hC
    subst C
    exact ⟨0, Set.univ, by simp⟩
  · exact Set.countable_singleton _
  · simp
  · intro C hC
    subst C
    rw [MeasureTheory.Measure.map_apply he MeasurableSet.univ]
    simp only [Set.preimage_univ]
    change (Chapter01.MeasurePreservingSystemData.toProbabilitySpace M).μ Set.univ ≠ ∞
    rw [hM.1.measure_univ]
    norm_num
  · rintro C ⟨n, A, rfl⟩
    rw [← MeasureTheory.Measure.map_apply (Chapter01.finitePrefix_measurable n)
        (Set.toFinite A).measurableSet,
      ← MeasureTheory.Measure.map_apply (Chapter01.finitePrefix_measurable n)
        (Set.toFinite A).measurableSet, hfin n]

def listPrefixCylinder {k : ℕ} (word : List (Fin k)) : Set (ℕ → Fin k) :=
  {x | ∀ i : Fin word.length, x i = word.get i}

def separatedListCylinders {k : ℕ} (left right : List (Fin k))
    (gap : ℕ) : Set (ℕ → Fin k) :=
  {x | (∀ i : Fin left.length, x i = left.get i) ∧
    ∀ j : Fin right.length,
      x (left.length - 1 + gap + j) = right.get j}

def listTransitionWeight {k : ℕ} (P : Matrix (Fin k) (Fin k) ℝ) :
    List (Fin k) → ℝ
  | [] => 1
  | _a :: [] => 1
  | a :: b :: tail => P a b * listTransitionWeight P (b :: tail)

private theorem listTransitionWeight_cons_eq_markovPathWeight
    {k : ℕ} (P : Matrix (Fin k) (Fin k) ℝ)
    (a : Fin k) (tail : List (Fin k)) :
    listTransitionWeight P (a :: tail) =
      Chapter01.markovPathWeight P a (fun i ↦ tail.get i) := by
  induction tail generalizing a with
  | nil => simp [listTransitionWeight, Chapter01.markovPathWeight_zero]
  | cons b tail ih =>
      rw [listTransitionWeight]
      have hfun : (fun i : Fin (tail.length + 1) ↦ (b :: tail).get i) =
          Fin.cases b (fun i : Fin tail.length ↦ tail.get i) := by
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
      calc
        P a b * listTransitionWeight P (b :: tail) =
            P a b * Chapter01.markovPathWeight P b (fun i ↦ tail.get i) := by
              rw [ih]
        _ = Chapter01.markovPathWeight P a
            (Fin.cases b (fun i : Fin tail.length ↦ tail.get i)) := by
              rw [Chapter01.markovPathWeight_cons]
        _ = Chapter01.markovPathWeight P a
            (fun i : Fin (tail.length + 1) ↦ (b :: tail).get i) := by
              rw [hfun]

private theorem listTransitionWeight_append_singleton
    {k : ℕ} (P : Matrix (Fin k) (Fin k) ℝ)
    (a : Fin k) (tail : List (Fin k)) (b : Fin k) :
    listTransitionWeight P ((a :: tail) ++ [b]) =
      listTransitionWeight P (a :: tail) *
        P ((a :: tail).getLast (by simp)) b := by
  induction tail generalizing a with
  | nil => simp [listTransitionWeight]
  | cons c tail ih =>
      change P a c * listTransitionWeight P ((c :: tail) ++ [b]) = _
      rw [ih]
      simp only [List.getLast_cons (by simp : c :: tail ≠ [])]
      rw [show listTransitionWeight P (a :: c :: tail) =
        P a c * listTransitionWeight P (c :: tail) by rfl]
      ring

private theorem listTransitionWeight_nonneg {k : ℕ}
    (P : Matrix (Fin k) (Fin k) ℝ) (hP : ∀ i j, 0 ≤ P i j) :
    ∀ word : List (Fin k), 0 ≤ listTransitionWeight P word := by
  intro word
  induction word with
  | nil => simp [listTransitionWeight]
  | cons a tail ih =>
      cases tail with
      | nil => simp [listTransitionWeight]
      | cons b rest =>
          change 0 ≤ P a b * listTransitionWeight P (b :: rest)
          exact mul_nonneg (hP a b) ih

private theorem listTransitionWeight_append_nonempty {k : ℕ}
    (P : Matrix (Fin k) (Fin k) ℝ)
    (a : Fin k) (tail : List (Fin k)) (b : Fin k) (right : List (Fin k)) :
    listTransitionWeight P ((a :: tail) ++ (b :: right)) =
      listTransitionWeight P (a :: tail) *
        P ((a :: tail).getLast (by simp)) b *
          listTransitionWeight P (b :: right) := by
  induction tail generalizing a with
  | nil => simp [listTransitionWeight]
  | cons c tail ih =>
      change P a c * listTransitionWeight P ((c :: tail) ++ (b :: right)) = _
      rw [ih]
      simp only [List.getLast_cons (by simp : c :: tail ≠ [])]
      rw [show listTransitionWeight P (a :: c :: tail) =
        P a c * listTransitionWeight P (c :: tail) by rfl]
      ring

private theorem listPrefixCylinder_cons_measure
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (a : Fin k) (tail : List (Fin k)) :
    Chapter01.oneSidedMarkovMeasure k p P hP hPsum
        (listPrefixCylinder (a :: tail)) =
      ENNReal.ofReal (p a * listTransitionWeight P (a :: tail)) := by
  let f : Fin (tail.length + 1) → Fin k := fun i ↦ (a :: tail).get i
  have hset : listPrefixCylinder (a :: tail) = Chapter01.markovPrefixCylinder f := by
    ext x
    simp only [listPrefixCylinder, Set.mem_setOf_eq,
      Chapter01.markovPrefixCylinder]
    rfl
  rw [hset, Chapter01.oneSidedMarkovMeasure_prefix k p P hp hsum hP hPsum]
  have hf : f = Fin.cases a (fun i : Fin tail.length ↦ tail.get i) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [f]
    · simp [f]
  rw [hf]
  simp only [Fin.cases_zero, Fin.cases_succ]
  change ENNReal.ofReal
      (p a * Chapter01.markovPathWeight P a (fun i ↦ tail.get i)) = _
  rw [← listTransitionWeight_cons_eq_markovPathWeight]

private theorem listPrefixCylinder_append_singleton {k : ℕ}
    (word : List (Fin k)) (c : Fin k) :
    listPrefixCylinder (word ++ [c]) =
      listPrefixCylinder word ∩ {x | x word.length = c} := by
  ext x
  simp only [listPrefixCylinder, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    constructor
    · intro i
      have hi := h ⟨i, by simp⟩
      simpa [List.get_eq_getElem] using hi
    · have hi := h ⟨word.length, by simp⟩
      simpa [List.get_eq_getElem] using hi
  · rintro ⟨hword, hc⟩ i
    by_cases hi : (i : ℕ) < word.length
    · let j : Fin word.length := ⟨(i : ℕ), hi⟩
      have hjval : (j : ℕ) = (i : ℕ) := by simp [j]
      calc
        x i = x j := (congrArg x hjval).symm
        _ = word.get j := hword j
        _ = (word ++ [c]).get i := by
          simp [List.get_eq_getElem, hi, hjval]
    · have hieq : (i : ℕ) = word.length := by
        have hibound : (i : ℕ) < word.length + 1 := by simpa using i.isLt
        omega
      calc
        x i = x word.length := congrArg x hieq
        _ = c := hc
        _ = (word ++ [c]).get i := by
          rw [List.get_eq_getElem]
          simp [hieq]

private theorem listPrefixCylinder_append {k : ℕ}
    (left right : List (Fin k)) :
    listPrefixCylinder (left ++ right) =
      listPrefixCylinder left ∩
        {x | ∀ j : Fin right.length, x (left.length + j) = right.get j} := by
  ext x
  simp only [listPrefixCylinder, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    constructor
    · intro i
      have hi := h ⟨(i : ℕ), by simp; omega⟩
      simpa [List.get_eq_getElem] using hi
    · intro j
      let i : Fin (left ++ right).length :=
        ⟨left.length + (j : ℕ), by simp⟩
      have hival : (i : ℕ) = left.length + (j : ℕ) := by simp [i]
      calc
        x (left.length + (j : ℕ)) = x i := congrArg x hival.symm
        _ = (left ++ right).get i := h i
        _ = right.get j := by
          simp [List.get_eq_getElem, i]
  · rintro ⟨hleft, hright⟩ i
    by_cases hi : (i : ℕ) < left.length
    · let j : Fin left.length := ⟨(i : ℕ), hi⟩
      have hjval : (j : ℕ) = (i : ℕ) := by simp [j]
      calc
        x i = x j := (congrArg x hjval).symm
        _ = left.get j := hleft j
        _ = (left ++ right).get i := by
          simp [List.get_eq_getElem, hi, hjval]
    · have hle : left.length ≤ (i : ℕ) := Nat.le_of_not_gt hi
      let j : Fin right.length :=
        ⟨(i : ℕ) - left.length, by
          have hibound : (i : ℕ) < left.length + right.length := by
            simpa using i.isLt
          omega⟩
      have hjval : left.length + (j : ℕ) = (i : ℕ) := by
        simp [j]
        omega
      calc
        x i = x (left.length + (j : ℕ)) := congrArg x hjval.symm
        _ = right.get j := hright j
        _ = (left ++ right).get i := by
          simp [List.get_eq_getElem, j, hle]

private theorem separatedListCylinders_one_gap {k : ℕ}
    (a : Fin k) (tail right : List (Fin k)) :
    separatedListCylinders (a :: tail) right 1 =
      listPrefixCylinder ((a :: tail) ++ right) := by
  rw [listPrefixCylinder_append]
  ext x
  simp only [separatedListCylinders, listPrefixCylinder,
    Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hleft, hright⟩
    exact ⟨hleft, fun j ↦ by simpa using hright j⟩
  · rintro ⟨hleft, hright⟩
    exact ⟨hleft, fun j ↦ by simpa using hright j⟩

private theorem separatedListCylinders_succ_gap {k : ℕ}
    (a : Fin k) (tail right : List (Fin k)) (gap : ℕ) :
    separatedListCylinders (a :: tail) right (gap + 1) =
      ⋃ c : Fin k, separatedListCylinders ((a :: tail) ++ [c]) right gap := by
  ext x
  simp only [separatedListCylinders, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨hleft, hright⟩
    refine ⟨x (a :: tail).length, ?_⟩
    constructor
    · have hx : x ∈ listPrefixCylinder
          ((a :: tail) ++ [x (a :: tail).length]) := by
          rw [listPrefixCylinder_append_singleton]
          exact ⟨hleft, rfl⟩
      exact hx
    · intro j
      have hidx :
          ((a :: tail) ++ [x (a :: tail).length]).length - 1 + gap + (j : ℕ) =
            (a :: tail).length - 1 + (gap + 1) + (j : ℕ) := by
        simp
        omega
      rw [hidx]
      exact hright j
  · rintro ⟨c, hleft, hright⟩
    constructor
    · have hx : x ∈ listPrefixCylinder ((a :: tail) ++ [c]) := hleft
      rw [listPrefixCylinder_append_singleton] at hx
      exact hx.1
    · intro j
      have hidx :
          ((a :: tail) ++ [c]).length - 1 + gap + (j : ℕ) =
            (a :: tail).length - 1 + (gap + 1) + (j : ℕ) := by
        simp
        omega
      rw [← hidx]
      exact hright j

private theorem separatedListCylinders_measurable {k : ℕ}
    (left right : List (Fin k)) (gap : ℕ) :
    MeasurableSet (separatedListCylinders left right gap) := by
  change MeasurableSet
    ({x : ℕ → Fin k | ∀ i : Fin left.length, x i = left.get i} ∩
      {x : ℕ → Fin k | ∀ j : Fin right.length,
        x (left.length - 1 + gap + (j : ℕ)) = right.get j})
  apply MeasurableSet.inter
  · convert MeasurableSet.iInter (fun i : Fin left.length ↦
        measurableSet_eq_fun
          (measurable_pi_apply (i : ℕ) :
            Measurable (fun x : ℕ → Fin k ↦ x i))
          (measurable_const :
            Measurable (fun _x : ℕ → Fin k ↦ left.get i))) using 1
    ext x
    simp
  · convert MeasurableSet.iInter (fun j : Fin right.length ↦
        measurableSet_eq_fun
          (measurable_pi_apply (left.length - 1 + gap + (j : ℕ)) :
            Measurable (fun x : ℕ → Fin k ↦
              x (left.length - 1 + gap + (j : ℕ))))
          (measurable_const :
            Measurable (fun _x : ℕ → Fin k ↦ right.get j))) using 1
    ext x
    simp

private theorem separatedListCylinders_append_pairwise_disjoint {k : ℕ}
    (a : Fin k) (tail right : List (Fin k)) (gap : ℕ) :
    Pairwise (Function.onFun Disjoint
      (fun c : Fin k ↦ separatedListCylinders ((a :: tail) ++ [c]) right gap)) := by
  intro c d hcd
  change Disjoint (separatedListCylinders ((a :: tail) ++ [c]) right gap)
    (separatedListCylinders ((a :: tail) ++ [d]) right gap)
  rw [Set.disjoint_left]
  intro x hxc hxd
  have hxc' : x ∈ listPrefixCylinder ((a :: tail) ++ [c]) := hxc.1
  have hxd' : x ∈ listPrefixCylinder ((a :: tail) ++ [d]) := hxd.1
  rw [listPrefixCylinder_append_singleton] at hxc' hxd'
  exact hcd (hxc'.2.symm.trans hxd'.2)

private theorem separatedListCylinders_succ_gap_measure
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (a : Fin k) (tail right : List (Fin k)) (gap : ℕ) :
    Chapter01.oneSidedMarkovMeasure k p P hP hPsum
        (separatedListCylinders (a :: tail) right (gap + 1)) =
      ∑ c : Fin k, Chapter01.oneSidedMarkovMeasure k p P hP hPsum
        (separatedListCylinders ((a :: tail) ++ [c]) right gap) := by
  rw [separatedListCylinders_succ_gap]
  rw [MeasureTheory.measure_iUnion
    (separatedListCylinders_append_pairwise_disjoint a tail right gap)
    (fun c ↦ separatedListCylinders_measurable _ _ _), tsum_fintype]

theorem separatedListCylinders_measure
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (a : Fin k) (tail : List (Fin k)) (b : Fin k) (right : List (Fin k)) :
    ∀ gap : ℕ,
      Chapter01.oneSidedMarkovMeasure k p P hP hPsum
          (separatedListCylinders (a :: tail) (b :: right) (gap + 1)) =
        ENNReal.ofReal
          (p a * listTransitionWeight P (a :: tail) *
            (P ^ (gap + 1)) ((a :: tail).getLast (by simp)) b *
              listTransitionWeight P (b :: right)) := by
  intro gap
  induction gap generalizing a tail with
  | zero =>
      rw [separatedListCylinders_one_gap]
      change Chapter01.oneSidedMarkovMeasure k p P hP hPsum
        (listPrefixCylinder (a :: (tail ++ (b :: right)))) = _
      rw [listPrefixCylinder_cons_measure k p P hp hsum hP hPsum
        a (tail ++ (b :: right))]
      congr 1
      change p a * listTransitionWeight P ((a :: tail) ++ (b :: right)) = _
      rw [listTransitionWeight_append_nonempty]
      simp
      ring
  | succ gap ih =>
      rw [show gap + 1 + 1 = (gap + 1) + 1 by omega]
      rw [separatedListCylinders_succ_gap_measure]
      have hrewrite :
          (∑ c : Fin k, Chapter01.oneSidedMarkovMeasure k p P hP hPsum
            (separatedListCylinders ((a :: tail) ++ [c])
              (b :: right) (gap + 1))) =
          ∑ c : Fin k, ENNReal.ofReal
            (p a * listTransitionWeight P ((a :: tail) ++ [c]) *
              (P ^ (gap + 1))
                (((a :: tail) ++ [c]).getLast (by simp)) b *
                listTransitionWeight P (b :: right)) := by
        apply Finset.sum_congr rfl
        intro c _
        exact ih (a := a) (tail := tail ++ [c])
      rw [hrewrite]
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · congr 1
        have hlast : ∀ c : Fin k,
            ((a :: tail) ++ [c]).getLast (by simp) = c := by
          intro c
          simp
        simp_rw [listTransitionWeight_append_singleton, hlast]
        calc
          ∑ c, p a *
                (listTransitionWeight P (a :: tail) *
                  P ((a :: tail).getLast (by simp)) c) *
                (P ^ (gap + 1)) c b * listTransitionWeight P (b :: right) =
              (p a * listTransitionWeight P (a :: tail) *
                listTransitionWeight P (b :: right)) *
                ∑ c, P ((a :: tail).getLast (by simp)) c *
                  (P ^ (gap + 1)) c b := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c _
            ring
          _ = p a * listTransitionWeight P (a :: tail) *
                (P ^ (gap + 1 + 1)) ((a :: tail).getLast (by simp)) b *
                  listTransitionWeight P (b :: right) := by
            rw [← Matrix.mul_apply, ← pow_succ']
            ring
      · intro c _
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (hp a)
              (listTransitionWeight_nonneg P hP ((a :: tail) ++ [c])))
            (FiniteMarkov.pow_nonnegative P hP (gap + 1)
              (((a :: tail) ++ [c]).getLast (by simp)) b))
          (listTransitionWeight_nonneg P hP (b :: right))

private theorem markovPrefixSetFamily_isAlgebra (k : ℕ) :
    Chapter00.IsAlgebra (Chapter01.markovPrefixSetFamily k) := by
  constructor
  · exact ⟨0, ∅, by simp⟩
  constructor
  · rintro C ⟨n, A, rfl⟩ D ⟨m, B, rfl⟩
    let N := max n m
    let rn : (Fin (N + 1) → Fin k) → (Fin (n + 1) → Fin k) :=
      fun z i ↦ z ⟨i, by
        have hi := i.isLt
        have hn : n ≤ N := le_max_left _ _
        omega⟩
    let rm : (Fin (N + 1) → Fin k) → (Fin (m + 1) → Fin k) :=
      fun z i ↦ z ⟨i, by
        have hi := i.isLt
        have hm : m ≤ N := le_max_right _ _
        omega⟩
    let E : Set (Fin (N + 1) → Fin k) := {z | rn z ∈ A ∧ rm z ∉ B}
    refine ⟨N, E, ?_⟩
    ext x
    simp only [Set.mem_diff, Set.mem_preimage, E, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hxA, hxB⟩
      exact ⟨by simpa only [rn, Chapter01.finitePrefix] using hxA,
        by simpa only [rm, Chapter01.finitePrefix] using hxB⟩
    · rintro ⟨hxA, hxB⟩
      exact ⟨by simpa only [rn, Chapter01.finitePrefix] using hxA,
        by simpa only [rm, Chapter01.finitePrefix] using hxB⟩
  · rintro C ⟨n, A, rfl⟩
    refine ⟨n, Aᶜ, ?_⟩
    ext x
    simp

private theorem markovPrefixSetFamily_isSemiAlgebra (k : ℕ) :
    Chapter00.IsSemiAlgebra (Chapter01.markovPrefixSetFamily k) := by
  have hAlg := markovPrefixSetFamily_isAlgebra k
  constructor
  · refine MeasureTheory.IsSetSemiring.mk hAlg.1 ?_ ?_
    · intro s hs t ht
      have hdiff := hAlg.2.1 s hs tᶜ (hAlg.2.2 t ht)
      convert hdiff using 1
      ext x
      simp
    · intro s hs t ht
      let I : Finset (Set (ℕ → Fin k)) := {s \ t}
      refine ⟨I, ?_, ?_, ?_⟩
      · intro E hE
        have : E = s \ t := by simpa [I] using hE
        subst E
        exact hAlg.2.1 s hs t ht
      · intro E hEI F hFI hEF
        simp [I] at hEI hFI
        exact (hEF (hEI.trans hFI.symm)).elim
      · simp [I]
  · let B : Fin 1 → Set (ℕ → Fin k) := fun _ ↦ Set.univ
    refine ⟨1, B, ?_, ?_, ?_⟩
    · intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
    · intro i
      refine ⟨0, Set.univ, ?_⟩
      simp [B]
    · ext x
      simp [B]

private theorem markovPrefixSetFamily_generate (k : ℕ) :
    Chapter00.generatedSigmaAlgebra (Chapter01.markovPrefixSetFamily k) =
      {E : Set (ℕ → Fin k) | MeasurableSet E} := by
  apply Set.ext
  intro E
  change @MeasurableSet (ℕ → Fin k)
      (MeasurableSpace.generateFrom (Chapter01.markovPrefixSetFamily k)) E ↔
    MeasurableSet E
  rw [← Chapter01.markovPrefixSetFamily_generate k]

private lemma correlation_fintype_iUnion (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : ι → Set M.X) (D : κ → Set M.X)
    (hCdisj : Pairwise (Function.onFun Disjoint C))
    (hDdisj : Pairwise (Function.onFun Disjoint D))
    (hCmeas : ∀ i, MeasurableSet (C i)) (hDmeas : ∀ j, MeasurableSet (D j))
    (n : ℕ) :
    correlation M (⋃ i, C i) (⋃ j, D j) n =
      ∑ i, ∑ j, correlation M (C i) (D j) n := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let E : ι → κ → Set M.X := fun i j ↦ C i ∩ preimageIter M n (D j)
  have hset : (⋃ i, C i) ∩ preimageIter M n (⋃ j, D j) =
      ⋃ i, ⋃ j, E i j := by
    ext x
    simp [E, preimageIter, Chapter01.iterateMap]
  have hEmeas : ∀ i j, MeasurableSet (E i j) := fun i j ↦
    (hCmeas i).inter ((hDmeas j).preimage (hM.2.measurable.iterate n))
  have hEdisjJ : ∀ i, Pairwise (Function.onFun Disjoint (E i)) := by
    intro i j l hjl
    apply Set.disjoint_left.2
    intro x hxj hxl
    exact Set.disjoint_left.1 (hDdisj hjl) hxj.2 hxl.2
  have hEdisjI : Pairwise (Function.onFun Disjoint (fun i ↦ ⋃ j, E i j)) := by
    intro i l hil
    apply Set.disjoint_left.2
    intro x hxi hxl
    simp only [Set.mem_iUnion] at hxi hxl
    exact Set.disjoint_left.1 (hCdisj hil)
      (Classical.choose_spec hxi).1 (Classical.choose_spec hxl).1
  unfold correlation realMeasure
  rw [hset, MeasureTheory.measure_iUnion hEdisjI
    (fun i ↦ MeasurableSet.iUnion (fun j ↦ hEmeas i j))]
  have hinner (i : ι) : M.μ (⋃ j, E i j) = ∑ j, M.μ (E i j) := by
    simpa only [tsum_fintype] using
      MeasureTheory.measure_iUnion (hEdisjJ i) (hEmeas i)
  simp_rw [hinner]
  simp only [tsum_fintype]
  rw [ENNReal.toReal_sum (fun _ _ ↦ by simp)]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.toReal_sum (fun _ _ ↦ by simp)]

private lemma productMeasureValue_fintype_iUnion (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : ι → Set M.X) (D : κ → Set M.X)
    (hCdisj : Pairwise (Function.onFun Disjoint C))
    (hDdisj : Pairwise (Function.onFun Disjoint D))
    (hCmeas : ∀ i, MeasurableSet (C i)) (hDmeas : ∀ j, MeasurableSet (D j)) :
    productMeasureValue M (⋃ i, C i) (⋃ j, D j) =
      ∑ i, ∑ j, productMeasureValue M (C i) (D j) := by
  unfold productMeasureValue
  have hrealC : realMeasure M (⋃ i, C i) = ∑ i, realMeasure M (C i) := by
    letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
    unfold realMeasure
    rw [MeasureTheory.measure_iUnion hCdisj hCmeas, tsum_fintype,
      ENNReal.toReal_sum (fun _ _ ↦ by simp)]
  have hrealD : realMeasure M (⋃ j, D j) = ∑ j, realMeasure M (D j) := by
    letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
    unfold realMeasure
    rw [MeasureTheory.measure_iUnion hDdisj hDmeas, tsum_fintype,
      ENNReal.toReal_sum (fun _ _ ↦ by simp)]
  rw [hrealC, hrealD, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

private lemma seq_fintype_iUnion (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : ι → Set M.X) (D : κ → Set M.X)
    (hCdisj : Pairwise (Function.onFun Disjoint C))
    (hDdisj : Pairwise (Function.onFun Disjoint D))
    (hCmeas : ∀ i, MeasurableSet (C i)) (hDmeas : ∀ j, MeasurableSet (D j))
    (hlim : ∀ i j, Tendsto (fun n ↦ correlation M (C i) (D j) n) atTop
      (nhds (productMeasureValue M (C i) (D j)))) :
    Tendsto (fun n ↦ correlation M (⋃ i, C i) (⋃ j, D j) n) atTop
      (nhds (productMeasureValue M (⋃ i, C i) (⋃ j, D j))) := by
  have hsum : Tendsto
      (fun n ↦ ∑ i, ∑ j, correlation M (C i) (D j) n) atTop
      (nhds (∑ i, ∑ j, productMeasureValue M (C i) (D j))) := by
    apply tendsto_finset_sum
    intro i _
    apply tendsto_finset_sum
    intro j _
    exact hlim i j
  convert hsum using 1
  · funext n
    exact correlation_fintype_iUnion M hM C D hCdisj hDdisj hCmeas hDmeas n
  · congr 1
    exact productMeasureValue_fintype_iUnion M hM C D hCdisj hDdisj hCmeas hDmeas

private lemma cesaro_fintype_iUnion (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : ι → Set M.X) (D : κ → Set M.X)
    (hCdisj : Pairwise (Function.onFun Disjoint C))
    (hDdisj : Pairwise (Function.onFun Disjoint D))
    (hCmeas : ∀ i, MeasurableSet (C i)) (hDmeas : ∀ j, MeasurableSet (D j))
    (hlim : ∀ i j, cesaroTendsTo (fun n ↦ correlation M (C i) (D j) n)
      (productMeasureValue M (C i) (D j))) :
    cesaroTendsTo (fun n ↦ correlation M (⋃ i, C i) (⋃ j, D j) n)
      (productMeasureValue M (⋃ i, C i) (⋃ j, D j)) := by
  unfold cesaroTendsTo seqTendsTo at hlim ⊢
  have hsum : Tendsto
      (fun N ↦ ∑ i, ∑ j, cesaroAverage (fun n ↦ correlation M (C i) (D j) n) N)
      atTop (nhds (∑ i, ∑ j, productMeasureValue M (C i) (D j))) := by
    apply tendsto_finset_sum
    intro i hi
    apply tendsto_finset_sum
    intro j hj
    exact hlim i j
  convert hsum using 1
  · funext N
    rw [show (fun n ↦ correlation M (⋃ i, C i) (⋃ j, D j) n) =
        (fun n ↦ ∑ i, ∑ j, correlation M (C i) (D j) n) by
      funext n
      exact correlation_fintype_iUnion M hM C D hCdisj hDdisj hCmeas hDmeas n]
    unfold cesaroAverage
    calc
      (((N + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
          ∑ i, ∑ j, correlation M (C i) (D j) n) =
          ∑ n ∈ Finset.range (N + 1), ∑ i, ∑ j,
            (((N + 1 : ℕ) : ℝ)⁻¹ * correlation M (C i) (D j) n) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = ∑ i, ∑ n ∈ Finset.range (N + 1), ∑ j,
          (((N + 1 : ℕ) : ℝ)⁻¹ * correlation M (C i) (D j) n) :=
        Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ n ∈ Finset.range (N + 1),
          (((N + 1 : ℕ) : ℝ)⁻¹ * correlation M (C i) (D j) n) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, (((N + 1 : ℕ) : ℝ)⁻¹ *
          ∑ n ∈ Finset.range (N + 1), correlation M (C i) (D j) n) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
  · congr 1
    exact productMeasureValue_fintype_iUnion M hM C D hCdisj hDdisj hCmeas hDmeas

private def prefixAtom {k n : ℕ} (A : Set (Fin (n + 1) → Fin k))
    (a : Fin (n + 1) → Fin k) : Set (ℕ → Fin k) :=
  if a ∈ A then Chapter01.markovPrefixCylinder a else ∅

private theorem prefixAtom_iUnion {k n : ℕ}
    (A : Set (Fin (n + 1) → Fin k)) :
    (⋃ a, prefixAtom A a) = Chapter01.finitePrefix n ⁻¹' A := by
  ext x
  simp only [prefixAtom, Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨a, ha⟩
    split at ha
    · have hxa : Chapter01.finitePrefix n x = a := by
        funext i
        exact ha i
      simpa [hxa] using ‹a ∈ A›
    · exact ha.elim
  · intro hx
    refine ⟨Chapter01.finitePrefix n x, ?_⟩
    simp only [hx, ↓reduceIte, Chapter01.markovPrefixCylinder,
      Set.mem_setOf_eq, Chapter01.finitePrefix]
    intro i
    trivial

private theorem prefixAtom_pairwise_disjoint {k n : ℕ}
    (A : Set (Fin (n + 1) → Fin k)) :
    Pairwise (Function.onFun Disjoint (prefixAtom A)) := by
  intro a b hab
  change Disjoint (prefixAtom A a) (prefixAtom A b)
  rw [Set.disjoint_left]
  intro x hxa hxb
  by_cases ha : a ∈ A <;> by_cases hb : b ∈ A
  · simp only [prefixAtom, ha, hb, ↓reduceIte,
      Chapter01.markovPrefixCylinder, Set.mem_setOf_eq] at hxa hxb
    apply hab
    funext i
    exact (hxa i).symm.trans (hxb i)
  · simpa [prefixAtom, hb] using hxb
  · simpa [prefixAtom, ha] using hxa
  · simpa [prefixAtom, ha] using hxa

private theorem prefixAtom_measurable {k n : ℕ}
    (A : Set (Fin (n + 1) → Fin k)) (a : Fin (n + 1) → Fin k) :
    MeasurableSet (prefixAtom A a) := by
  by_cases ha : a ∈ A
  · simpa [prefixAtom, ha] using Chapter01.markovPrefixCylinder_measurable a
  · simp [prefixAtom, ha]

private theorem oneSidedShift_iterate (k n : ℕ) (x : ℕ → Fin k) (i : ℕ) :
    ((Chapter01.oneSidedShift^[n]) x) i = x (i + n) := by
  induction n generalizing x i with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      simp only [Chapter01.oneSidedShift]
      congr 1

private theorem list_get_ofFn_cast {α : Type*} {n : ℕ}
    (f : Fin n → α) (i : Fin (List.ofFn f).length) (j : Fin n)
    (hij : (i : ℕ) = (j : ℕ)) :
    (List.ofFn f).get i = f j := by
  rw [List.get_ofFn]
  congr 1
  apply Fin.ext
  exact hij

private theorem prefixCylinder_inter_shift_eq_separated
    {k n m : ℕ} (a : Fin (n + 1) → Fin k) (b : Fin (m + 1) → Fin k)
    (gap : ℕ) :
    Chapter01.markovPrefixCylinder a ∩
        (Chapter01.oneSidedShift^[n + gap]) ⁻¹'
          Chapter01.markovPrefixCylinder b =
      separatedListCylinders (List.ofFn a) (List.ofFn b) gap := by
  ext x
  simp only [Chapter01.markovPrefixCylinder, Set.mem_inter_iff,
    Set.mem_setOf_eq, Set.mem_preimage, separatedListCylinders]
  constructor
  · rintro ⟨ha, hb⟩
    constructor
    · intro i
      let i' : Fin (n + 1) := ⟨(i : ℕ), by simpa using i.isLt⟩
      have hval : (i : ℕ) = (i' : ℕ) := by simp [i']
      calc
        x i = x i' := congrArg x hval
        _ = a i' := ha i'
        _ = (List.ofFn a).get i :=
          (list_get_ofFn_cast a i i' hval).symm
    · intro j
      rw [show (List.ofFn a).length - 1 + gap + (j : ℕ) =
          (j : ℕ) + (n + gap) by simp; omega]
      rw [← oneSidedShift_iterate k (n + gap) x (j : ℕ)]
      let j' : Fin (m + 1) := ⟨(j : ℕ), by simpa using j.isLt⟩
      have hval : (j : ℕ) = (j' : ℕ) := by simp [j']
      calc
        (Chapter01.oneSidedShift^[n + gap]) x j =
            (Chapter01.oneSidedShift^[n + gap]) x j' :=
          congrArg ((Chapter01.oneSidedShift^[n + gap]) x) hval
        _ = b j' := hb j'
        _ = (List.ofFn b).get j :=
          (list_get_ofFn_cast b j j' hval).symm
  · rintro ⟨ha, hb⟩
    constructor
    · intro i
      let i' : Fin (List.ofFn a).length := ⟨(i : ℕ), by simpa using i.isLt⟩
      have hval : (i' : ℕ) = (i : ℕ) := by simp [i']
      calc
        x i = x i' := (congrArg x hval).symm
        _ = (List.ofFn a).get i' := ha i'
        _ = a i := list_get_ofFn_cast a i' i hval
    · intro j
      rw [oneSidedShift_iterate]
      rw [show (j : ℕ) + (n + gap) =
          (List.ofFn a).length - 1 + gap + (j : ℕ) by simp; omega]
      let j' : Fin (List.ofFn b).length := ⟨(j : ℕ), by simpa using j.isLt⟩
      have hval : (j' : ℕ) = (j : ℕ) := by simp [j']
      calc
        x ((List.ofFn a).length - 1 + gap + (j : ℕ)) =
            x ((List.ofFn a).length - 1 + gap + (j' : ℕ)) := by rw [hval]
        _ = (List.ofFn b).get j' := hb j'
        _ = b j := list_get_ofFn_cast b j' j hval

private theorem markovPrefixCylinder_eq_listPrefixCylinder
    {k n : ℕ} (a : Fin (n + 1) → Fin k) :
    Chapter01.markovPrefixCylinder a = listPrefixCylinder (List.ofFn a) := by
  ext x
  simp only [Chapter01.markovPrefixCylinder, listPrefixCylinder,
    Set.mem_setOf_eq]
  constructor
  · intro ha i
    let i' : Fin (n + 1) := ⟨(i : ℕ), by simpa using i.isLt⟩
    have hval : (i : ℕ) = (i' : ℕ) := by simp [i']
    calc
      x i = x i' := congrArg x hval
      _ = a i' := ha i'
      _ = (List.ofFn a).get i := (list_get_ofFn_cast a i i' hval).symm
  · intro ha i
    let i' : Fin (List.ofFn a).length := ⟨(i : ℕ), by simpa using i.isLt⟩
    have hval : (i' : ℕ) = (i : ℕ) := by simp [i']
    calc
      x i = x i' := (congrArg x hval).symm
      _ = (List.ofFn a).get i' := ha i'
      _ = a i := list_get_ofFn_cast a i' i hval

private theorem canonicalOneSided_prefixCylinder_tendsto
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hlim : ∀ i j, Tendsto (fun n ↦ (P ^ n) i j) atTop (nhds (p j)))
    {n m : ℕ} (a : Fin (n + 1) → Fin k) (b : Fin (m + 1) → Fin k) :
    let M := Chapter01.oneSidedMarkovSystem k p P hP hPsum
    Tendsto (fun q ↦ correlation M (Chapter01.markovPrefixCylinder a)
      (Chapter01.markovPrefixCylinder b) q) atTop
      (nhds (productMeasureValue M (Chapter01.markovPrefixCylinder a)
        (Chapter01.markovPrefixCylinder b))) := by
  let M := Chapter01.oneSidedMarkovSystem k p P hP hPsum
  let ta : List (Fin k) := List.ofFn (fun i : Fin n ↦ a i.succ)
  let tb : List (Fin k) := List.ofFn (fun i : Fin m ↦ b i.succ)
  have hwa : List.ofFn a = a 0 :: ta := by
    simp [ta, List.ofFn_succ]
  have hwb : List.ofFn b = b 0 :: tb := by
    simp [tb, List.ofFn_succ]
  let lastA : Fin k := (a 0 :: ta).getLast (by simp)
  let wa : ℝ := listTransitionWeight P (a 0 :: ta)
  let wb : ℝ := listTransitionWeight P (b 0 :: tb)
  have hwa0 : 0 ≤ wa := listTransitionWeight_nonneg P hP _
  have hwb0 : 0 ≤ wb := listTransitionWeight_nonneg P hP _
  have hM : Chapter01.IsMeasurePreservingSystem M :=
    Chapter01.oneSidedMarkovSystem_mps k p P hp hsum hP hPsum hstationary
  have hmeasureA : M.μ (Chapter01.markovPrefixCylinder a) =
      ENNReal.ofReal (p (a 0) * wa) := by
    rw [markovPrefixCylinder_eq_listPrefixCylinder, hwa]
    exact listPrefixCylinder_cons_measure k p P hp hsum hP hPsum _ _
  have hmeasureB : M.μ (Chapter01.markovPrefixCylinder b) =
      ENNReal.ofReal (p (b 0) * wb) := by
    rw [markovPrefixCylinder_eq_listPrefixCylinder, hwb]
    exact listPrefixCylinder_cons_measure k p P hp hsum hP hPsum _ _
  have hproduct : productMeasureValue M (Chapter01.markovPrefixCylinder a)
      (Chapter01.markovPrefixCylinder b) =
      (p (a 0) * wa) * (p (b 0) * wb) := by
    have hAprod : 0 ≤ p (a 0) * wa := mul_nonneg (hp _) hwa0
    have hBprod : 0 ≤ p (b 0) * wb := mul_nonneg (hp _) hwb0
    unfold productMeasureValue realMeasure
    rw [hmeasureA, hmeasureB, ENNReal.toReal_ofReal hAprod,
      ENNReal.toReal_ofReal hBprod]
  apply (Filter.tendsto_add_atTop_iff_nat
    (f := fun q ↦ correlation M (Chapter01.markovPrefixCylinder a)
      (Chapter01.markovPrefixCylinder b) q) (n + 1)).mp
  have hentry : Tendsto (fun q ↦ (P ^ (q + 1)) lastA (b 0)) atTop
      (nhds (p (b 0))) :=
    (hlim lastA (b 0)).comp (tendsto_add_atTop_nat 1)
  have hscaled := ((hentry.const_mul (p (a 0) * wa)).mul_const wb)
  rw [hproduct]
  convert hscaled using 1
  · funext q
    unfold correlation realMeasure
    have hset : Chapter01.markovPrefixCylinder a ∩
        preimageIter M (q + (n + 1)) (Chapter01.markovPrefixCylinder b) =
        separatedListCylinders (a 0 :: ta) (b 0 :: tb) (q + 1) := by
      change Chapter01.markovPrefixCylinder a ∩
          (Chapter01.oneSidedShift^[q + (n + 1)]) ⁻¹'
            Chapter01.markovPrefixCylinder b = _
      rw [show q + (n + 1) = n + (q + 1) by omega]
      rw [prefixCylinder_inter_shift_eq_separated, hwa, hwb]
    rw [hset]
    change (Chapter01.oneSidedMarkovMeasure k p P hP hPsum
      (separatedListCylinders (a 0 :: ta) (b 0 :: tb) (q + 1))).toReal = _
    rw [separatedListCylinders_measure k p P hp hsum hP hPsum
      (a 0) ta (b 0) tb q]
    have hnonneg : 0 ≤
        p (a 0) * listTransitionWeight P (a 0 :: ta) *
          (P ^ (q + 1)) ((a 0 :: ta).getLast (by simp)) (b 0) *
            listTransitionWeight P (b 0 :: tb) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (hp _) hwa0)
          (FiniteMarkov.pow_nonnegative P hP (q + 1) lastA (b 0))) hwb0
    rw [ENNReal.toReal_ofReal hnonneg]
  · congr 1
    ring

private theorem canonicalOneSided_prefixSet_tendsto
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hlim : ∀ i j, Tendsto (fun n ↦ (P ^ n) i j) atTop (nhds (p j)))
    {n m : ℕ} (A : Set (Fin (n + 1) → Fin k))
    (B : Set (Fin (m + 1) → Fin k)) :
    let M := Chapter01.oneSidedMarkovSystem k p P hP hPsum
    Tendsto (fun q ↦ correlation M (Chapter01.finitePrefix n ⁻¹' A)
      (Chapter01.finitePrefix m ⁻¹' B) q) atTop
      (nhds (productMeasureValue M (Chapter01.finitePrefix n ⁻¹' A)
        (Chapter01.finitePrefix m ⁻¹' B))) := by
  let M := Chapter01.oneSidedMarkovSystem k p P hP hPsum
  have hM : Chapter01.IsMeasurePreservingSystem M :=
    Chapter01.oneSidedMarkovSystem_mps k p P hp hsum hP hPsum hstationary
  change Tendsto (fun q ↦ correlation M (Chapter01.finitePrefix n ⁻¹' A)
      (Chapter01.finitePrefix m ⁻¹' B) q) atTop
    (nhds (productMeasureValue M (Chapter01.finitePrefix n ⁻¹' A)
      (Chapter01.finitePrefix m ⁻¹' B)))
  rw [← prefixAtom_iUnion A, ← prefixAtom_iUnion B]
  apply seq_fintype_iUnion M hM (prefixAtom A) (prefixAtom B)
    (prefixAtom_pairwise_disjoint A) (prefixAtom_pairwise_disjoint B)
    (prefixAtom_measurable A) (prefixAtom_measurable B)
  intro a b
  by_cases ha : a ∈ A <;> by_cases hb : b ∈ B
  · simpa [prefixAtom, ha, hb] using
      canonicalOneSided_prefixCylinder_tendsto k p P hp hsum hP hPsum
        hstationary hlim a b
  · simpa [prefixAtom, ha, hb, correlation, productMeasureValue, realMeasure,
      preimageIter, Chapter01.iterateMap] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
  · simpa [prefixAtom, ha, correlation, productMeasureValue, realMeasure,
      preimageIter, Chapter01.iterateMap] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
  · simpa [prefixAtom, ha, correlation, productMeasureValue, realMeasure,
      preimageIter, Chapter01.iterateMap] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))

theorem canonicalOneSidedStrongMixing
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hlim : ∀ i j, Tendsto (fun n ↦ (P ^ n) i j) atTop (nhds (p j))) :
    IsStrongMixing (Chapter01.oneSidedMarkovSystem k p P hP hPsum) := by
  let M := Chapter01.oneSidedMarkovSystem k p P hP hPsum
  have hM : Chapter01.IsMeasurePreservingSystem M :=
    Chapter01.oneSidedMarkovSystem_mps k p P hp hsum hP hPsum hstationary
  refine ⟨hM, ?_⟩
  apply CorrelationSemiAlgebra.seq_on_all_measurable M hM
    (Chapter01.markovPrefixSetFamily k) (markovPrefixSetFamily_generate k)
  intro A B hA hB
  have hsub : Chapter00.generatedAlgebra (Chapter01.markovPrefixSetFamily k) ⊆
      Chapter01.markovPrefixSetFamily k := by
    intro E hE
    exact hE _ ⟨markovPrefixSetFamily_isAlgebra k, Set.Subset.rfl⟩
  rcases hsub hA with ⟨n, C, rfl⟩
  rcases hsub hB with ⟨m, D, rfl⟩
  exact canonicalOneSided_prefixSet_tendsto k p P hp hsum hP hPsum
    hstationary hlim C D

theorem primitive_iff_entrywise_stationary_limit
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    (IsIrreducibleStochasticMatrix P ∧
        Chapter00.IsAperiodicNonnegativeMatrix k P) ↔
      ∀ i j, Tendsto (fun n ↦ (P ^ n) i j) atTop (nhds (p j)) := by
  have hk : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    simpa using hsum
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  constructor
  · rintro ⟨hirr, haper⟩
    let π : stdSimplex ℝ (Fin k) := ⟨p, ⟨fun i ↦ (hp i).le, hsum⟩⟩
    have hstoch : MCMC.Finite.IsStochastic P := ⟨hP, hPsum⟩
    have hstat : MCMC.Finite.IsStationary P π := by
      ext j
      change ∑ i, P i j * p i = p j
      simpa [mul_comm] using hstationary j
    have hprim : P.IsPrimitive := haper.toMatrixIsPrimitive
    have hirred : P.IsIrreducible := Matrix.IsPrimitive.isIrreducible hprim
    let hchain : MCMC.Finite.IsMCMC P π :=
      { stochastic := hstoch
        stationary := hstat
        irreducible := hirred
        primitive := hprim }
    have hconv : Tendsto (fun n : ℕ ↦ P ^ n) atTop
        (nhds (MCMC.Finite.LimitMatrix π)) :=
      MCMC.Finite.convergence_to_stationarity P π hchain
    intro i j
    have heval : Continuous (fun Q : Matrix (Fin k) (Fin k) ℝ ↦ Q i j) :=
      (continuous_apply j).comp (continuous_apply i)
    simpa [MCMC.Finite.LimitMatrix, π] using (heval.tendsto _).comp hconv
  · intro hlim
    have hev' : ∀ᶠ n : ℕ in atTop, ∀ i j, 0 < (P ^ n) i j := by
      simp only [Filter.eventually_all]
      intro i j
      have hopen : Set.Ioi (0 : ℝ) ∈ nhds (p j) :=
        isOpen_Ioi.mem_nhds (hp j)
      exact (hlim i j).eventually hopen
    have hlarge : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
    rcases (hev'.and hlarge).exists with ⟨n, hnpos, hn⟩
    exact ⟨⟨hP, hPsum, fun i j ↦ ⟨n, hnpos i j⟩⟩,
      ⟨hP, n, hn, hnpos⟩⟩

theorem oneSidedStrongMixing_of_entrywise_limit {M : System.{u}}
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (h : Chapter01.IsOneSidedMarkovShiftWith M k p P)
    (hlim : ∀ i j, Tendsto (fun n ↦ (P ^ n) i j) atTop (nhds (p j))) :
    IsStrongMixing M := by
  have h' := h
  rcases h with ⟨hM, _e, _he, _heinv, _hT, hp, hsum, hP, hPsum,
    hstationary, _hcyl⟩
  rcases oneSided_map_eq k p P hP hPsum h' with
    ⟨e, he, heinv, hmap, hT⟩
  apply BernoulliMixing.strongMixing_of_measurable_conjugacy hM
    (canonicalOneSidedStrongMixing k p P hp hsum hP hPsum hstationary hlim)
    e he heinv hmap
  intro x
  funext n
  exact hT x n

private theorem cesaro_shifted_matrix_power
    (k : ℕ) (P Q : Matrix (Fin k) (Fin k) ℝ)
    (hlim : ∀ i j, Tendsto
      (fun N : ℕ ↦ if N = 0 then 0 else
        ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N, (P ^ n) i j)
      atTop (nhds (Q i j)))
    (hPQ : P * Q = Q) (i j : Fin k) :
    cesaroTendsTo (fun n ↦ (P ^ (n + 1)) i j) (Q i j) := by
  have hterms : ∀ l : Fin k, Tendsto
      (fun N : ℕ ↦ P i l *
        (if N + 1 = 0 then 0 else
          (((N + 1 : ℕ) : ℝ)⁻¹) *
            ∑ n ∈ Finset.range (N + 1), (P ^ n) l j))
      atTop (nhds (P i l * Q l j)) := by
    intro l
    exact tendsto_const_nhds.mul
      ((hlim l j).comp (tendsto_add_atTop_nat 1))
  have hsum := tendsto_finset_sum Finset.univ (fun l hl ↦ hterms l)
  unfold cesaroTendsTo seqTendsTo cesaroAverage
  convert hsum using 1
  · funext N
    simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte]
    rw [Finset.mul_sum]
    calc
      (∑ n ∈ Finset.range (N + 1),
          (((N + 1 : ℕ) : ℝ)⁻¹ * (P ^ (n + 1)) i j)) =
          ∑ n ∈ Finset.range (N + 1), ∑ l,
            P i l * (((N + 1 : ℕ) : ℝ)⁻¹ * (P ^ n) l j) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [pow_succ', Matrix.mul_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ = ∑ l, ∑ n ∈ Finset.range (N + 1),
          P i l * (((N + 1 : ℕ) : ℝ)⁻¹ * (P ^ n) l j) := Finset.sum_comm
      _ = ∑ l, P i l * (((N + 1 : ℕ) : ℝ)⁻¹ *
          ∑ n ∈ Finset.range (N + 1), (P ^ n) l j) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mul_sum, Finset.mul_sum]
  · rw [← Matrix.mul_apply, hPQ]

private theorem canonicalOneSided_prefixCylinder_cesaro
    (k : ℕ) (p : Fin k → ℝ) (P Q : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hlim : ∀ i j, Tendsto
      (fun N : ℕ ↦ if N = 0 then 0 else
        ((N : ℝ)⁻¹) * ∑ r ∈ Finset.range N, (P ^ r) i j)
      atTop (nhds (Q i j)))
    (hPQ : P * Q = Q) (hQ : ∀ i j, Q i j = p j)
    {n m : ℕ} (a : Fin (n + 1) → Fin k) (b : Fin (m + 1) → Fin k) :
    let M := Chapter01.oneSidedMarkovSystem k p P hP hPsum
    cesaroTendsTo (fun q ↦ correlation M (Chapter01.markovPrefixCylinder a)
      (Chapter01.markovPrefixCylinder b) q)
      (productMeasureValue M (Chapter01.markovPrefixCylinder a)
        (Chapter01.markovPrefixCylinder b)) := by
  let M := Chapter01.oneSidedMarkovSystem k p P hP hPsum
  let ta : List (Fin k) := List.ofFn (fun i : Fin n ↦ a i.succ)
  let tb : List (Fin k) := List.ofFn (fun i : Fin m ↦ b i.succ)
  have hwa : List.ofFn a = a 0 :: ta := by simp [ta, List.ofFn_succ]
  have hwb : List.ofFn b = b 0 :: tb := by simp [tb, List.ofFn_succ]
  let lastA : Fin k := (a 0 :: ta).getLast (by simp)
  let wa : ℝ := listTransitionWeight P (a 0 :: ta)
  let wb : ℝ := listTransitionWeight P (b 0 :: tb)
  have hwa0 : 0 ≤ wa := listTransitionWeight_nonneg P hP _
  have hwb0 : 0 ≤ wb := listTransitionWeight_nonneg P hP _
  have hM : Chapter01.IsMeasurePreservingSystem M :=
    Chapter01.oneSidedMarkovSystem_mps k p P hp hsum hP hPsum hstationary
  have hmeasureA : M.μ (Chapter01.markovPrefixCylinder a) =
      ENNReal.ofReal (p (a 0) * wa) := by
    rw [markovPrefixCylinder_eq_listPrefixCylinder, hwa]
    exact listPrefixCylinder_cons_measure k p P hp hsum hP hPsum _ _
  have hmeasureB : M.μ (Chapter01.markovPrefixCylinder b) =
      ENNReal.ofReal (p (b 0) * wb) := by
    rw [markovPrefixCylinder_eq_listPrefixCylinder, hwb]
    exact listPrefixCylinder_cons_measure k p P hp hsum hP hPsum _ _
  have hproduct : productMeasureValue M (Chapter01.markovPrefixCylinder a)
      (Chapter01.markovPrefixCylinder b) =
      (p (a 0) * wa) * (p (b 0) * wb) := by
    unfold productMeasureValue realMeasure
    rw [hmeasureA, hmeasureB, ENNReal.toReal_ofReal (mul_nonneg (hp _) hwa0),
      ENNReal.toReal_ofReal (mul_nonneg (hp _) hwb0)]
  have hentry := cesaro_shifted_matrix_power k P Q hlim hPQ lastA (b 0)
  rw [hQ lastA (b 0)] at hentry
  have hscaled := cesaroTendsTo_const_mul wb
    (cesaroTendsTo_const_mul (p (a 0) * wa) hentry)
  have htail : cesaroTendsTo
      (fun q ↦ correlation M (Chapter01.markovPrefixCylinder a)
        (Chapter01.markovPrefixCylinder b) (q + (n + 1)))
      (productMeasureValue M (Chapter01.markovPrefixCylinder a)
        (Chapter01.markovPrefixCylinder b)) := by
    rw [hproduct]
    convert hscaled using 1
    · funext q
      unfold correlation realMeasure
      have hset : Chapter01.markovPrefixCylinder a ∩
          preimageIter M (q + (n + 1)) (Chapter01.markovPrefixCylinder b) =
          separatedListCylinders (a 0 :: ta) (b 0 :: tb) (q + 1) := by
        change Chapter01.markovPrefixCylinder a ∩
            (Chapter01.oneSidedShift^[q + (n + 1)]) ⁻¹'
              Chapter01.markovPrefixCylinder b = _
        rw [show q + (n + 1) = n + (q + 1) by omega]
        rw [prefixCylinder_inter_shift_eq_separated, hwa, hwb]
      rw [hset]
      change (Chapter01.oneSidedMarkovMeasure k p P hP hPsum
        (separatedListCylinders (a 0 :: ta) (b 0 :: tb) (q + 1))).toReal = _
      rw [separatedListCylinders_measure k p P hp hsum hP hPsum
        (a 0) ta (b 0) tb q]
      rw [ENNReal.toReal_ofReal]
      · ring
      · exact mul_nonneg
          (mul_nonneg (mul_nonneg (hp _) hwa0)
            (FiniteMarkov.pow_nonnegative P hP (q + 1) lastA (b 0))) hwb0
    · ring
  apply cesaroTendsTo_of_add_shift (C := 1) (by norm_num) _ (n + 1) htail
  intro q
  unfold correlation realMeasure
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  change M.μ.real
    (Chapter01.markovPrefixCylinder a ∩
      preimageIter M q (Chapter01.markovPrefixCylinder b)) ≤ 1
  calc
    _ ≤ M.μ.real Set.univ :=
      MeasureTheory.measureReal_mono (Set.subset_univ _) (by simp)
    _ = 1 := by simp [MeasureTheory.Measure.real]

set_option maxHeartbeats 800000 in
private theorem canonicalOneSided_prefixSet_cesaro
    (k : ℕ) (p : Fin k → ℝ) (P Q : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hlim : ∀ i j, Tendsto
      (fun N : ℕ ↦ if N = 0 then 0 else
        ((N : ℝ)⁻¹) * ∑ r ∈ Finset.range N, (P ^ r) i j)
      atTop (nhds (Q i j)))
    (hPQ : P * Q = Q) (hQ : ∀ i j, Q i j = p j)
    {n m : ℕ} (A : Set (Fin (n + 1) → Fin k))
    (B : Set (Fin (m + 1) → Fin k)) :
    let M := Chapter01.oneSidedMarkovSystem k p P hP hPsum
    cesaroTendsTo (fun q ↦ correlation M (Chapter01.finitePrefix n ⁻¹' A)
      (Chapter01.finitePrefix m ⁻¹' B) q)
      (productMeasureValue M (Chapter01.finitePrefix n ⁻¹' A)
        (Chapter01.finitePrefix m ⁻¹' B)) := by
  let M := Chapter01.oneSidedMarkovSystem k p P hP hPsum
  have hM : Chapter01.IsMeasurePreservingSystem M :=
    Chapter01.oneSidedMarkovSystem_mps k p P hp hsum hP hPsum hstationary
  change cesaroTendsTo (fun q ↦ correlation M (Chapter01.finitePrefix n ⁻¹' A)
      (Chapter01.finitePrefix m ⁻¹' B) q)
    (productMeasureValue M (Chapter01.finitePrefix n ⁻¹' A)
      (Chapter01.finitePrefix m ⁻¹' B))
  rw [← prefixAtom_iUnion A, ← prefixAtom_iUnion B]
  apply cesaro_fintype_iUnion M hM (prefixAtom A)
    (prefixAtom B) (prefixAtom_pairwise_disjoint A) (prefixAtom_pairwise_disjoint B)
    (prefixAtom_measurable A) (prefixAtom_measurable B)
  intro a b
  by_cases ha : a ∈ A <;> by_cases hb : b ∈ B
  · simpa [prefixAtom, ha, hb] using
      canonicalOneSided_prefixCylinder_cesaro k p P Q hp hsum hP hPsum
        hstationary hlim hPQ hQ a b
  · unfold cesaroTendsTo seqTendsTo cesaroAverage
    simp [prefixAtom, ha, hb, correlation, productMeasureValue, realMeasure,
      preimageIter, Chapter01.iterateMap]
  · unfold cesaroTendsTo seqTendsTo cesaroAverage
    simp [prefixAtom, ha, correlation, productMeasureValue, realMeasure,
      preimageIter, Chapter01.iterateMap]
  · unfold cesaroTendsTo seqTendsTo cesaroAverage
    simp [prefixAtom, ha, correlation, productMeasureValue, realMeasure,
      preimageIter, Chapter01.iterateMap]

theorem canonicalOneSidedCesaroCorrelations_of_irreducible
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hirr : IsIrreducibleStochasticMatrix P) :
    let M := Chapter01.oneSidedMarkovSystem k p P hP hPsum
    ∀ A B : Set M.X, MeasurableSet A → MeasurableSet B →
      cesaroTendsTo (fun q ↦ correlation M A B q) (productMeasureValue M A B) := by
  let M := Chapter01.oneSidedMarkovSystem k p P hP hPsum
  obtain ⟨Q, hlim, hPQ, hQP, hQQ⟩ :=
    StochasticCesaro.stochasticMatrixCesaroLimit k P hP hPsum
  have hrows : StochasticMatrixRowsEqual Q :=
    FiniteMarkov.irreducible_implies_rows_equal hirr hPQ
  have hstat := FiniteMarkov.stationary_cesaro_limit p P Q hstationary hlim
  have hQ : ∀ i j, Q i j = p j := by
    intro i j
    calc
      Q i j = (∑ l, p l) * Q i j := by rw [hsum, one_mul]
      _ = ∑ l, p l * Q i j := Finset.sum_mul _ _ _
      _ = ∑ l, p l * Q l j := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [hrows l i j]
      _ = p j := hstat j
  have hM : Chapter01.IsMeasurePreservingSystem M :=
    Chapter01.oneSidedMarkovSystem_mps k p P (fun i ↦ (hp i).le) hsum
      hP hPsum hstationary
  have hgen := markovPrefixSetFamily_generate k
  have hAlg := CorrelationSemiAlgebra.cesaro_on_generatedAlgebra M hM
    (Chapter01.markovPrefixSetFamily k) (markovPrefixSetFamily_isSemiAlgebra k)
    hgen (fun A B hA hB ↦ by
      rcases hA with ⟨n, C, rfl⟩
      rcases hB with ⟨m, D, rfl⟩
      exact canonicalOneSided_prefixSet_cesaro k p P Q (fun i ↦ (hp i).le)
        hsum hP hPsum hstationary hlim hPQ hQ C D)
  exact CorrelationSemiAlgebra.cesaro_on_all_measurable M hM
    (Chapter01.markovPrefixSetFamily k) hgen hAlg

private theorem ergodic_of_cesaroCorrelations {M : System.{u}}
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hcorr : ∀ A B : Set M.X, MeasurableSet A → MeasurableSet B →
      cesaroTendsTo (fun n ↦ correlation M A B n) (productMeasureValue M A B)) :
    IsErgodic M := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  refine ⟨hM, ?_⟩
  intro A hA hnull
  have hstep : M.T ⁻¹' A =ᵐ[M.μ] A := by
    rw [← MeasureTheory.measure_symmDiff_eq_zero_iff]
    simpa [Chapter00.symmDiff, Set.symmDiff_def] using hnull
  have hiter : ∀ n, preimageIter M n A =ᵐ[M.μ] A := by
    intro n
    induction n with
    | zero => simp [preimageIter, Chapter01.iterateMap]
    | succ n ih =>
        have hpre := hM.2.quasiMeasurePreserving.ae_eq_comp ih
        simpa only [preimageIter, Chapter01.iterateMap, Set.preimage_preimage,
          Function.iterate_succ_apply] using hpre.trans hstep
  have hconst : cesaroTendsTo (fun n ↦ correlation M A A n) (realMeasure M A) := by
    unfold cesaroTendsTo seqTendsTo
    convert tendsto_const_nhds using 1
    funext N
    have heach : ∀ n, correlation M A A n = realMeasure M A := by
      intro n
      unfold correlation
      apply congrArg ENNReal.toReal
      apply MeasureTheory.measure_congr
      filter_upwards [hiter n] with x hx
      change (x ∈ A ∧ x ∈ preimageIter M n A) = (x ∈ A)
      change (x ∈ preimageIter M n A) = (x ∈ A) at hx
      rw [hx]
      simp
    simp only [cesaroAverage, heach, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    field_simp
  have heq : realMeasure M A = productMeasureValue M A A :=
    tendsto_nhds_unique hconst (hcorr A A hA hA)
  have hidem : realMeasure M A * (realMeasure M A - 1) = 0 := by
    unfold productMeasureValue at heq
    nlinarith
  rcases mul_eq_zero.mp hidem with hzero | hone
  · left
    apply (ENNReal.toReal_eq_toReal (by simp : M.μ A ≠ ⊤)
      (by simp : (0 : ENNReal) ≠ ⊤)).mp
    simpa [realMeasure] using hzero
  · right
    have hrealone : realMeasure M A = 1 := by nlinarith
    apply (ENNReal.toReal_eq_toReal (by simp : M.μ A ≠ ⊤)
      (by simp : (1 : ENNReal) ≠ ⊤)).mp
    simpa [realMeasure] using hrealone

private theorem isErgodic_to_mathlibErgodic {M : System.{u}}
    (hM : IsErgodic M) : Ergodic M.T M.μ := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  refine Ergodic.mk hM.1.2 (PreErgodic.mk ?_)
  intro s hs hinv
  have hsymm : M.μ (Chapter00.symmDiff (M.T ⁻¹' s) s) = 0 := by
    simp [hinv, Chapter00.symmDiff]
  rcases hM.2 s hs hsymm with hzero | hone
  · unfold Filter.EventuallyConst
    refine ⟨{False}, ?_⟩
    constructor
    · change ∀ᵐ x ∂M.μ, s x ∈ ({False} : Set Prop)
      filter_upwards [MeasureTheory.ae_eq_empty.mpr hzero] with x hx
      change s x = False
      exact hx
    · simp
  · have hfin : M.μ s ≠ ⊤ := by simp [hone]
    have hcompl : M.μ sᶜ = 0 := by
      rw [MeasureTheory.measure_compl hs hfin]
      simp [hone]
    unfold Filter.EventuallyConst
    refine ⟨{True}, ?_⟩
    constructor
    · change ∀ᵐ x ∂M.μ, s x ∈ ({True} : Set Prop)
      filter_upwards [MeasureTheory.ae_eq_univ.mpr hcompl] with x hx
      change s x = True
      exact hx
    · simp

private theorem ergodic_exists_positive_return {M : System.{u}}
    (hM : IsErgodic M) (A B : Set M.X) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hposA : 0 < M.μ A) (hposB : 0 < M.μ B) :
    ∃ n : ℕ, 0 < n ∧ 0 < M.μ (A ∩ preimageIter M n B) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  let U : Set M.X := ⋃ n : ℕ, preimageIter M (n + 1) B
  have hUmeas : MeasurableSet U := by
    apply MeasurableSet.iUnion
    intro n
    exact (hM.1.2.iterate (n + 1)).measurable hB
  have hpre : M.T ⁻¹' U ⊆ U := by
    intro x hx
    simp only [U, Set.mem_preimage, Set.mem_iUnion] at hx ⊢
    obtain ⟨n, hn⟩ := hx
    refine ⟨n + 1, ?_⟩
    simpa [preimageIter, Function.iterate_succ_apply] using hn
  have hzero_or_full :=
    (isErgodic_to_mathlibErgodic hM).ae_empty_or_univ_of_preimage_ae_le
      hUmeas.nullMeasurableSet (Filter.Eventually.of_forall hpre)
  have hUfull : M.μ U = 1 := by
    rcases hzero_or_full with hzero | hfull
    · have hUzero : M.μ U = 0 := MeasureTheory.ae_eq_empty.mp hzero
      have hsub : preimageIter M 1 B ⊆ U := by
        intro x hx
        simp only [U, Set.mem_iUnion]
        exact ⟨0, by simpa using hx⟩
      have hprezero : M.μ (preimageIter M 1 B) = 0 :=
        nonpos_iff_eq_zero.mp (hUzero ▸ MeasureTheory.measure_mono hsub)
      have hmeasure : M.μ (preimageIter M 1 B) = M.μ B :=
        (hM.1.2.iterate 1).measure_preimage hB.nullMeasurableSet
      rw [hmeasure] at hprezero
      exact (ne_of_gt hposB hprezero).elim
    · calc
        M.μ U = M.μ Set.univ := MeasureTheory.measure_congr hfull
        _ = 1 := hM.1.1.measure_univ
  have hAU : M.μ (A ∩ U) = M.μ A := by
    have hcompl : M.μ Uᶜ = 0 := by
      rw [MeasureTheory.measure_compl hUmeas (by simp [hUfull])]
      simp [hUfull]
    apply MeasureTheory.measure_congr
    filter_upwards [MeasureTheory.ae_eq_univ.mpr hcompl] with x hx
    change (x ∈ A ∩ U) = (x ∈ A)
    have hxU : x ∈ U := hx.mpr trivial
    simp [hxU]
  by_contra hnone
  push_neg at hnone
  have hallzero : ∀ n : ℕ, M.μ (A ∩ preimageIter M (n + 1) B) = 0 := by
    intro n
    exact nonpos_iff_eq_zero.mp (hnone (n + 1) (by omega))
  have hunionzero : M.μ (⋃ n : ℕ, A ∩ preimageIter M (n + 1) B) = 0 :=
    MeasureTheory.measure_iUnion_null hallzero
  have hset : A ∩ U = ⋃ n : ℕ, A ∩ preimageIter M (n + 1) B := by
    ext x
    simp [U]
  have : M.μ A = 0 := by rw [← hAU, hset, hunionzero]
  exact (ne_of_gt hposA) this

theorem canonicalOneSidedErgodic_of_irreducible
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hirr : IsIrreducibleStochasticMatrix P) :
    IsErgodic (Chapter01.oneSidedMarkovSystem k p P hP hPsum) := by
  apply ergodic_of_cesaroCorrelations
    (Chapter01.oneSidedMarkovSystem_mps k p P (fun i ↦ (hp i).le) hsum
      hP hPsum hstationary)
  exact canonicalOneSidedCesaroCorrelations_of_irreducible k p P hp hsum
    hP hPsum hstationary hirr

def nonnegativeRestriction {k : ℕ} (x : ℤ → Fin k) : ℕ → Fin k :=
  fun n ↦ x n

private theorem nonnegativeRestriction_measurable {k : ℕ} :
    Measurable (@nonnegativeRestriction k) := by
  exact measurable_pi_lambda _ fun n ↦ measurable_pi_apply (n : ℤ)

private theorem twoSided_map_nonnegativeRestriction
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    MeasureTheory.Measure.map nonnegativeRestriction
        (Chapter01.twoSidedMarkovMeasure k p P hp hsum hP hPsum hstationary) =
      Chapter01.oneSidedMarkovMeasure k p P hP hPsum := by
  let ν := MeasureTheory.Measure.map nonnegativeRestriction
    (Chapter01.twoSidedMarkovMeasure k p P hp hsum hP hPsum hstationary)
  let μ := Chapter01.oneSidedMarkovMeasure k p P hP hPsum
  have hfin : ∀ n : ℕ,
      MeasureTheory.Measure.map (Chapter01.finitePrefix n) ν =
        MeasureTheory.Measure.map (Chapter01.finitePrefix n) μ := by
    intro n
    apply MeasureTheory.Measure.ext_of_singleton
    intro a
    rw [MeasureTheory.Measure.map_apply (Chapter01.finitePrefix_measurable n)
      (MeasurableSet.singleton a)]
    change MeasureTheory.Measure.map nonnegativeRestriction
      (Chapter01.twoSidedMarkovMeasure k p P hp hsum hP hPsum hstationary)
      (Chapter01.finitePrefix n ⁻¹' {a}) = _
    rw [MeasureTheory.Measure.map_apply nonnegativeRestriction_measurable
      ((Chapter01.finitePrefix_measurable n) (MeasurableSet.singleton a))]
    have hleft : nonnegativeRestriction ⁻¹'
        (Chapter01.finitePrefix n ⁻¹' {a}) =
        {x : ℤ → Fin k | ∀ i : Fin (n + 1), x (i : ℤ) = a i} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      exact ⟨fun hx i ↦ congrFun hx i, fun hx ↦ funext hx⟩
    rw [hleft, Chapter01.twoSidedMarkovMeasure_nonnegative_prefix k p P hp hsum
      hP hPsum hstationary n a]
    rw [MeasureTheory.Measure.map_apply (Chapter01.finitePrefix_measurable n)
      (MeasurableSet.singleton a)]
    have hright : Chapter01.finitePrefix n ⁻¹' {a} =
        Chapter01.markovPrefixCylinder a := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff,
        Chapter01.markovPrefixCylinder, Set.mem_setOf_eq]
      exact ⟨fun hx i ↦ congrFun hx i, fun hx ↦ funext hx⟩
    rw [hright, Chapter01.oneSidedMarkovMeasure_prefix k p P hp hsum hP hPsum]
  apply MeasureTheory.Measure.ext_of_generateFrom_of_cover_subset
    (Chapter01.markovPrefixSetFamily_generate k)
    (Chapter01.markovPrefixSetFamily_piSystem k) (T := {Set.univ})
  · intro C hC
    subst C
    exact ⟨0, Set.univ, by simp⟩
  · exact Set.countable_singleton _
  · simp
  · intro C hC
    subst C
    rw [MeasureTheory.Measure.map_apply nonnegativeRestriction_measurable
      MeasurableSet.univ]
    simp only [Set.preimage_univ]
    rw [(Chapter01.twoSidedMarkovMeasure_isProbability k p P hp hsum hP hPsum
      hstationary).measure_univ]
    norm_num
  · rintro C ⟨n, A, rfl⟩
    rw [← MeasureTheory.Measure.map_apply (Chapter01.finitePrefix_measurable n)
        (Set.toFinite A).measurableSet,
      ← MeasureTheory.Measure.map_apply (Chapter01.finitePrefix_measurable n)
        (Set.toFinite A).measurableSet, hfin n]

private theorem bilateralShift_iterate (k n : ℕ) (x : ℤ → Fin k) (z : ℤ) :
    ((Chapter01.bilateralShift^[n]) x) z = x (z + n) := by
  induction n generalizing x z with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      simp only [Chapter01.bilateralShift]
      congr 1
      omega

private theorem nonnegativeRestriction_iterate (k n : ℕ) (x : ℤ → Fin k) :
    nonnegativeRestriction ((Chapter01.bilateralShift^[n]) x) =
      (Chapter01.oneSidedShift^[n]) (nonnegativeRestriction x) := by
  funext i
  change ((Chapter01.bilateralShift^[n]) x) (i : ℤ) =
    ((Chapter01.oneSidedShift^[n]) (nonnegativeRestriction x)) i
  rw [bilateralShift_iterate, oneSidedShift_iterate]
  rfl

def nonnegativeExtension {k : ℕ} (d : Fin k) (x : ℕ → Fin k) : ℤ → Fin k :=
  fun z ↦ if hz : 0 ≤ z then x z.toNat else d

private theorem nonnegativeExtension_measurable {k : ℕ} (d : Fin k) :
    Measurable (nonnegativeExtension d) := by
  apply measurable_pi_lambda
  intro z
  by_cases hz : 0 ≤ z
  · simp only [nonnegativeExtension, hz, ↓reduceDIte]
    exact measurable_pi_apply z.toNat
  · simp [nonnegativeExtension, hz]

private theorem shifted_finite_event_from_nonnegative
    {k : ℕ} (d : Fin k) (A : Set (ℤ → Fin k)) (s : Finset ℤ)
    (hA : ∀ x y, (∀ z ∈ s, x z = y z) → (x ∈ A ↔ y ∈ A))
    (r : ℕ) (hr : ∀ z ∈ s, Int.natAbs z ≤ r) :
    let Ashift := (Chapter01.bilateralShift^[r]) ⁻¹' A
    let Aone := nonnegativeExtension d ⁻¹' Ashift
    nonnegativeRestriction ⁻¹' Aone = Ashift := by
  dsimp only
  ext x
  simp only [Set.mem_preimage]
  apply hA
  intro z hz
  rw [bilateralShift_iterate, bilateralShift_iterate]
  have hzr : 0 ≤ z + (r : ℤ) := by
    cases z with
    | ofNat q =>
        have hq : (0 : ℤ) ≤ (q : ℤ) := by exact_mod_cast Nat.zero_le q
        have hr0 : (0 : ℤ) ≤ (r : ℤ) := by exact_mod_cast Nat.zero_le r
        exact add_nonneg hq hr0
    | negSucc q =>
        have hzupper := hr (Int.negSucc q) hz
        simp at hzupper ⊢
        omega
  simp only [nonnegativeExtension, hzr, ↓reduceDIte, nonnegativeRestriction]
  congr 1
  exact Int.toNat_of_nonneg hzr

theorem canonicalTwoSidedStrongMixing
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hlim : ∀ i j, Tendsto (fun n ↦ (P ^ n) i j) atTop (nhds (p j))) :
    IsStrongMixing
      (Chapter01.twoSidedMarkovSystem k p P hp hsum hP hPsum hstationary) := by
  let M₂ := Chapter01.twoSidedMarkovSystem k p P hp hsum hP hPsum hstationary
  let M₁ := Chapter01.oneSidedMarkovSystem k p P hP hPsum
  have hM₂ : Chapter01.IsMeasurePreservingSystem M₂ :=
    Chapter01.twoSidedMarkovSystem_mps k p P hp hsum hP hPsum hstationary
  have hM₁ : Chapter01.IsMeasurePreservingSystem M₁ :=
    Chapter01.oneSidedMarkovSystem_mps k p P hp hsum hP hPsum hstationary
  have hOne : IsStrongMixing M₁ :=
    canonicalOneSidedStrongMixing k p P hp hsum hP hPsum hstationary hlim
  have hmap := twoSided_map_nonnegativeRestriction k p P hp hsum hP hPsum hstationary
  have hk : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    simpa using hsum
  let d : Fin k := ⟨0, hk⟩
  refine ⟨hM₂, ?_⟩
  have hgen : Chapter00.generatedSigmaAlgebra
      (BernoulliMixing.coordinateSetFamily ℤ k) =
      {E : Set (ℤ → Fin k) | MeasurableSet E} :=
    BernoulliMixing.coordinateSetFamily_generate (ι := ℤ) k
  apply CorrelationSemiAlgebra.seq_on_all_measurable M₂ hM₂
    (BernoulliMixing.coordinateSetFamily ℤ k) hgen
  intro A B hAAlg hBAlg
  rcases BernoulliMixing.generatedAlgebra_dependsOnFiniteCoordinates hAAlg with
    ⟨s, hAs⟩
  rcases BernoulliMixing.generatedAlgebra_dependsOnFiniteCoordinates hBAlg with
    ⟨t, hBt⟩
  let r : ℕ := ∑ z ∈ s ∪ t, (Int.natAbs z + 1)
  have hrs : ∀ z ∈ s, Int.natAbs z ≤ r := by
    intro z hz
    have hz' : z ∈ s ∪ t := Finset.mem_union_left t hz
    have hle : Int.natAbs z + 1 ≤ r := by
      dsimp [r]
      exact Finset.single_le_sum
        (fun q _ ↦ Nat.zero_le (Int.natAbs q + 1)) hz'
    omega
  have hrt : ∀ z ∈ t, Int.natAbs z ≤ r := by
    intro z hz
    have hz' : z ∈ s ∪ t := Finset.mem_union_right s hz
    have hle : Int.natAbs z + 1 ≤ r := by
      dsimp [r]
      exact Finset.single_le_sum
        (fun q _ ↦ Nat.zero_le (Int.natAbs q + 1)) hz'
    omega
  let Ashift : Set (ℤ → Fin k) := (Chapter01.bilateralShift^[r]) ⁻¹' A
  let Bshift : Set (ℤ → Fin k) := (Chapter01.bilateralShift^[r]) ⁻¹' B
  let Aone : Set (ℕ → Fin k) := nonnegativeExtension d ⁻¹' Ashift
  let Bone : Set (ℕ → Fin k) := nonnegativeExtension d ⁻¹' Bshift
  have hAmeas : MeasurableSet A := by
    have h := CorrelationSemiAlgebra.generatedAlgebra_subset_generatedSigmaAlgebra
      (BernoulliMixing.coordinateSetFamily ℤ k) hAAlg
    simpa [BernoulliMixing.coordinateSetFamily_generate (ι := ℤ) k] using h
  have hBmeas : MeasurableSet B := by
    have h := CorrelationSemiAlgebra.generatedAlgebra_subset_generatedSigmaAlgebra
      (BernoulliMixing.coordinateSetFamily ℤ k) hBAlg
    simpa [BernoulliMixing.coordinateSetFamily_generate (ι := ℤ) k] using h
  have hAshiftMeas : MeasurableSet Ashift :=
    hAmeas.preimage (Chapter01.bilateralShift_measurable.iterate r)
  have hBshiftMeas : MeasurableSet Bshift :=
    hBmeas.preimage (Chapter01.bilateralShift_measurable.iterate r)
  have hAoneMeas : MeasurableSet Aone :=
    hAshiftMeas.preimage (nonnegativeExtension_measurable d)
  have hBoneMeas : MeasurableSet Bone :=
    hBshiftMeas.preimage (nonnegativeExtension_measurable d)
  have hAfac : nonnegativeRestriction ⁻¹' Aone = Ashift :=
    shifted_finite_event_from_nonnegative d A s hAs r hrs
  have hBfac : nonnegativeRestriction ⁻¹' Bone = Bshift :=
    shifted_finite_event_from_nonnegative d B t hBt r hrt
  have hmeasureFactor : ∀ C : Set (ℕ → Fin k), MeasurableSet C →
      M₂.μ (nonnegativeRestriction ⁻¹' C) = M₁.μ C := by
    intro C hC
    calc
      M₂.μ (nonnegativeRestriction ⁻¹' C) =
          MeasureTheory.Measure.map nonnegativeRestriction M₂.μ C := by
        exact (MeasureTheory.Measure.map_apply
          nonnegativeRestriction_measurable hC).symm
      _ = M₁.μ C := by
        change MeasureTheory.Measure.map nonnegativeRestriction
          (Chapter01.twoSidedMarkovMeasure k p P hp hsum hP hPsum hstationary) C =
          Chapter01.oneSidedMarkovMeasure k p P hP hPsum C
        rw [hmap]
  have hmeasureA : realMeasure M₂ A = realMeasure M₁ Aone := by
    unfold realMeasure
    rw [← (hM₂.2.iterate r).measure_preimage hAmeas.nullMeasurableSet]
    change (M₂.μ Ashift).toReal = _
    rw [← hAfac, hmeasureFactor Aone hAoneMeas]
  have hmeasureB : realMeasure M₂ B = realMeasure M₁ Bone := by
    unfold realMeasure
    rw [← (hM₂.2.iterate r).measure_preimage hBmeas.nullMeasurableSet]
    change (M₂.μ Bshift).toReal = _
    rw [← hBfac, hmeasureFactor Bone hBoneMeas]
  have hcorr : ∀ q, correlation M₂ A B q = correlation M₁ Aone Bone q := by
    intro q
    have hjointMeas : MeasurableSet (A ∩ preimageIter M₂ q B) :=
      hAmeas.inter (hBmeas.preimage (hM₂.2.measurable.iterate q))
    have hshiftJoint : Ashift ∩ preimageIter M₂ q Bshift =
        (Chapter01.bilateralShift^[r]) ⁻¹' (A ∩ preimageIter M₂ q B) := by
      ext x
      simp only [Ashift, Bshift, Set.mem_inter_iff, Set.mem_preimage,
        preimageIter, Chapter01.iterateMap]
      constructor
      · rintro ⟨hA, hB⟩
        exact ⟨hA, by
          change (Chapter01.bilateralShift^[r])
            ((Chapter01.bilateralShift^[q]) x) ∈ B at hB
          change (Chapter01.bilateralShift^[q])
            ((Chapter01.bilateralShift^[r]) x) ∈ B
          simpa [← Function.iterate_add_apply, add_comm] using hB⟩
      · rintro ⟨hA, hB⟩
        exact ⟨hA, by
          change (Chapter01.bilateralShift^[q])
            ((Chapter01.bilateralShift^[r]) x) ∈ B at hB
          change (Chapter01.bilateralShift^[r])
            ((Chapter01.bilateralShift^[q]) x) ∈ B
          simpa [← Function.iterate_add_apply, add_comm] using hB⟩
    have hfactorJoint : Ashift ∩ preimageIter M₂ q Bshift =
        nonnegativeRestriction ⁻¹' (Aone ∩ preimageIter M₁ q Bone) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, preimageIter,
        Chapter01.iterateMap]
      rw [← hAfac, ← hBfac]
      simp only [Set.mem_preimage]
      change nonnegativeRestriction x ∈ Aone ∧
          nonnegativeRestriction ((Chapter01.bilateralShift^[q]) x) ∈ Bone ↔
        nonnegativeRestriction x ∈ Aone ∧
          (Chapter01.oneSidedShift^[q]) (nonnegativeRestriction x) ∈ Bone
      rw [nonnegativeRestriction_iterate]
    unfold correlation realMeasure
    rw [← (hM₂.2.iterate r).measure_preimage hjointMeas.nullMeasurableSet]
    change (M₂.μ ((Chapter01.bilateralShift^[r]) ⁻¹'
      (A ∩ preimageIter M₂ q B))).toReal = _
    rw [← hshiftJoint, hfactorJoint]
    exact congrArg ENNReal.toReal
      (hmeasureFactor _ (hAoneMeas.inter
        (hBoneMeas.preimage (hM₁.2.measurable.iterate q))))
  have hprod : productMeasureValue M₂ A B = productMeasureValue M₁ Aone Bone := by
    unfold productMeasureValue
    rw [hmeasureA, hmeasureB]
  rw [hprod]
  exact (hOne.2 Aone Bone hAoneMeas hBoneMeas).congr'
    (Filter.Eventually.of_forall fun q ↦ (hcorr q).symm)

theorem canonicalTwoSidedCesaroCorrelations_of_irreducible
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hirr : IsIrreducibleStochasticMatrix P) :
    let M₂ := Chapter01.twoSidedMarkovSystem k p P (fun i ↦ (hp i).le)
      hsum hP hPsum hstationary
    ∀ A B : Set M₂.X, MeasurableSet A → MeasurableSet B →
      cesaroTendsTo (fun q ↦ correlation M₂ A B q) (productMeasureValue M₂ A B) := by
  let hp0 : ∀ i, 0 ≤ p i := fun i ↦ (hp i).le
  let M₂ := Chapter01.twoSidedMarkovSystem k p P hp0 hsum hP hPsum hstationary
  let M₁ := Chapter01.oneSidedMarkovSystem k p P hP hPsum
  have hM₂ : Chapter01.IsMeasurePreservingSystem M₂ :=
    Chapter01.twoSidedMarkovSystem_mps k p P hp0 hsum hP hPsum hstationary
  have hM₁ : Chapter01.IsMeasurePreservingSystem M₁ :=
    Chapter01.oneSidedMarkovSystem_mps k p P hp0 hsum hP hPsum hstationary
  have hOne := canonicalOneSidedCesaroCorrelations_of_irreducible k p P hp
    hsum hP hPsum hstationary hirr
  have hmap := twoSided_map_nonnegativeRestriction k p P hp0 hsum hP hPsum hstationary
  have hk : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    simpa using hsum
  let d : Fin k := ⟨0, hk⟩
  have hgen : Chapter00.generatedSigmaAlgebra
      (BernoulliMixing.coordinateSetFamily ℤ k) =
      {E : Set (ℤ → Fin k) | MeasurableSet E} :=
    BernoulliMixing.coordinateSetFamily_generate (ι := ℤ) k
  apply CorrelationSemiAlgebra.cesaro_on_all_measurable M₂ hM₂
    (BernoulliMixing.coordinateSetFamily ℤ k) hgen
  intro A B hAAlg hBAlg
  rcases BernoulliMixing.generatedAlgebra_dependsOnFiniteCoordinates hAAlg with
    ⟨s, hAs⟩
  rcases BernoulliMixing.generatedAlgebra_dependsOnFiniteCoordinates hBAlg with
    ⟨t, hBt⟩
  let r : ℕ := ∑ z ∈ s ∪ t, (Int.natAbs z + 1)
  have hrs : ∀ z ∈ s, Int.natAbs z ≤ r := by
    intro z hz
    have hz' : z ∈ s ∪ t := Finset.mem_union_left t hz
    have hle : Int.natAbs z + 1 ≤ r := by
      dsimp [r]
      exact Finset.single_le_sum
        (fun q _ ↦ Nat.zero_le (Int.natAbs q + 1)) hz'
    omega
  have hrt : ∀ z ∈ t, Int.natAbs z ≤ r := by
    intro z hz
    have hz' : z ∈ s ∪ t := Finset.mem_union_right s hz
    have hle : Int.natAbs z + 1 ≤ r := by
      dsimp [r]
      exact Finset.single_le_sum
        (fun q _ ↦ Nat.zero_le (Int.natAbs q + 1)) hz'
    omega
  let Ashift : Set (ℤ → Fin k) := (Chapter01.bilateralShift^[r]) ⁻¹' A
  let Bshift : Set (ℤ → Fin k) := (Chapter01.bilateralShift^[r]) ⁻¹' B
  let Aone : Set (ℕ → Fin k) := nonnegativeExtension d ⁻¹' Ashift
  let Bone : Set (ℕ → Fin k) := nonnegativeExtension d ⁻¹' Bshift
  have hAmeas : MeasurableSet A := by
    have h := CorrelationSemiAlgebra.generatedAlgebra_subset_generatedSigmaAlgebra
      (BernoulliMixing.coordinateSetFamily ℤ k) hAAlg
    simpa [BernoulliMixing.coordinateSetFamily_generate (ι := ℤ) k] using h
  have hBmeas : MeasurableSet B := by
    have h := CorrelationSemiAlgebra.generatedAlgebra_subset_generatedSigmaAlgebra
      (BernoulliMixing.coordinateSetFamily ℤ k) hBAlg
    simpa [BernoulliMixing.coordinateSetFamily_generate (ι := ℤ) k] using h
  have hAshiftMeas : MeasurableSet Ashift :=
    hAmeas.preimage (Chapter01.bilateralShift_measurable.iterate r)
  have hBshiftMeas : MeasurableSet Bshift :=
    hBmeas.preimage (Chapter01.bilateralShift_measurable.iterate r)
  have hAoneMeas : MeasurableSet Aone :=
    hAshiftMeas.preimage (nonnegativeExtension_measurable d)
  have hBoneMeas : MeasurableSet Bone :=
    hBshiftMeas.preimage (nonnegativeExtension_measurable d)
  have hAfac : nonnegativeRestriction ⁻¹' Aone = Ashift :=
    shifted_finite_event_from_nonnegative d A s hAs r hrs
  have hBfac : nonnegativeRestriction ⁻¹' Bone = Bshift :=
    shifted_finite_event_from_nonnegative d B t hBt r hrt
  have hmeasureFactor : ∀ C : Set (ℕ → Fin k), MeasurableSet C →
      M₂.μ (nonnegativeRestriction ⁻¹' C) = M₁.μ C := by
    intro C hC
    calc
      M₂.μ (nonnegativeRestriction ⁻¹' C) =
          MeasureTheory.Measure.map nonnegativeRestriction M₂.μ C := by
        exact (MeasureTheory.Measure.map_apply nonnegativeRestriction_measurable hC).symm
      _ = M₁.μ C := by
        change MeasureTheory.Measure.map nonnegativeRestriction
          (Chapter01.twoSidedMarkovMeasure k p P hp0 hsum hP hPsum hstationary) C =
          Chapter01.oneSidedMarkovMeasure k p P hP hPsum C
        rw [hmap]
  have hmeasureA : realMeasure M₂ A = realMeasure M₁ Aone := by
    unfold realMeasure
    rw [← (hM₂.2.iterate r).measure_preimage hAmeas.nullMeasurableSet]
    change (M₂.μ Ashift).toReal = _
    rw [← hAfac, hmeasureFactor Aone hAoneMeas]
  have hmeasureB : realMeasure M₂ B = realMeasure M₁ Bone := by
    unfold realMeasure
    rw [← (hM₂.2.iterate r).measure_preimage hBmeas.nullMeasurableSet]
    change (M₂.μ Bshift).toReal = _
    rw [← hBfac, hmeasureFactor Bone hBoneMeas]
  have hcorr : ∀ q, correlation M₂ A B q = correlation M₁ Aone Bone q := by
    intro q
    have hjointMeas : MeasurableSet (A ∩ preimageIter M₂ q B) :=
      hAmeas.inter (hBmeas.preimage (hM₂.2.measurable.iterate q))
    have hshiftJoint : Ashift ∩ preimageIter M₂ q Bshift =
        (Chapter01.bilateralShift^[r]) ⁻¹' (A ∩ preimageIter M₂ q B) := by
      ext x
      simp only [Ashift, Bshift, Set.mem_inter_iff, Set.mem_preimage,
        preimageIter, Chapter01.iterateMap]
      constructor
      · rintro ⟨hA, hB⟩
        exact ⟨hA, by
          change (Chapter01.bilateralShift^[r])
            ((Chapter01.bilateralShift^[q]) x) ∈ B at hB
          change (Chapter01.bilateralShift^[q])
            ((Chapter01.bilateralShift^[r]) x) ∈ B
          simpa [← Function.iterate_add_apply, add_comm] using hB⟩
      · rintro ⟨hA, hB⟩
        exact ⟨hA, by
          change (Chapter01.bilateralShift^[q])
            ((Chapter01.bilateralShift^[r]) x) ∈ B at hB
          change (Chapter01.bilateralShift^[r])
            ((Chapter01.bilateralShift^[q]) x) ∈ B
          simpa [← Function.iterate_add_apply, add_comm] using hB⟩
    have hfactorJoint : Ashift ∩ preimageIter M₂ q Bshift =
        nonnegativeRestriction ⁻¹' (Aone ∩ preimageIter M₁ q Bone) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, preimageIter,
        Chapter01.iterateMap]
      rw [← hAfac, ← hBfac]
      simp only [Set.mem_preimage]
      change nonnegativeRestriction x ∈ Aone ∧
          nonnegativeRestriction ((Chapter01.bilateralShift^[q]) x) ∈ Bone ↔
        nonnegativeRestriction x ∈ Aone ∧
          (Chapter01.oneSidedShift^[q]) (nonnegativeRestriction x) ∈ Bone
      rw [nonnegativeRestriction_iterate]
    unfold correlation realMeasure
    rw [← (hM₂.2.iterate r).measure_preimage hjointMeas.nullMeasurableSet]
    change (M₂.μ ((Chapter01.bilateralShift^[r]) ⁻¹'
      (A ∩ preimageIter M₂ q B))).toReal = _
    rw [← hshiftJoint, hfactorJoint]
    exact congrArg ENNReal.toReal
      (hmeasureFactor _ (hAoneMeas.inter
        (hBoneMeas.preimage (hM₁.2.measurable.iterate q))))
  have hprod : productMeasureValue M₂ A B = productMeasureValue M₁ Aone Bone := by
    unfold productMeasureValue
    rw [hmeasureA, hmeasureB]
  have hseq : (fun q ↦ correlation M₂ A B q) =
      (fun q ↦ correlation M₁ Aone Bone q) := funext hcorr
  rw [hprod, hseq]
  exact hOne Aone Bone hAoneMeas hBoneMeas

theorem canonicalTwoSidedErgodic_of_irreducible
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hirr : IsIrreducibleStochasticMatrix P) :
    IsErgodic (Chapter01.twoSidedMarkovSystem k p P (fun i ↦ (hp i).le)
      hsum hP hPsum hstationary) := by
  apply ergodic_of_cesaroCorrelations
    (Chapter01.twoSidedMarkovSystem_mps k p P (fun i ↦ (hp i).le) hsum
      hP hPsum hstationary)
  exact canonicalTwoSidedCesaroCorrelations_of_irreducible k p P hp hsum
    hP hPsum hstationary hirr

private theorem twoSided_map_eq {M : System.{u}}
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (h : Chapter01.IsTwoSidedMarkovShiftWith M k p P) :
    ∃ e : M.X ≃ (ℤ → Fin k),
      Measurable e ∧ Measurable e.symm ∧
      MeasureTheory.Measure.map e M.μ =
        Chapter01.twoSidedMarkovMeasure k p P hp hsum hP hPsum hstationary ∧
      (∀ x z, e (M.T x) z = e x (z + 1)) := by
  rcases h with ⟨hM, e, he, heinv, hT, _hp, _hsum, _hP, _hPsum,
    _hstationary, hcyl⟩
  let μ₂ := Chapter01.twoSidedMarkovMeasure k p P hp hsum hP hPsum hstationary
  let ν := MeasureTheory.Measure.map e M.μ
  have hcenter : ∀ m n : ℕ, ∀ past : Fin m → Fin k, ∀ center : Fin k,
      ∀ future : Fin n → Fin k,
      ν (Chapter01.centeredCylinder past center future) =
        μ₂ (Chapter01.centeredCylinder past center future) := by
    intro m
    induction m with
    | zero =>
        intro n past center future
        let a : Fin (n + 1) → Fin k := Fin.cases center future
        have hset : e ⁻¹' Chapter01.centeredCylinder past center future =
            {x | ∀ i : Fin (n + 1), e x (i : ℤ) = a i} := by
          ext x
          simp only [Set.mem_preimage, Chapter01.centeredCylinder,
            Set.mem_singleton_iff, Set.mem_setOf_eq]
          constructor
          · intro hx i
            have hrest := congrArg Prod.snd hx
            have hc := congrArg Prod.fst hrest
            have hf := congrArg Prod.snd hrest
            refine Fin.cases ?_ (fun j ↦ ?_) i
            · simpa [Chapter01.centeredObservation, a] using hc
            · have hj := congrFun hf j
              change e x ((j : ℤ) + 1) = future j at hj
              simpa [a] using hj
          · intro hx
            apply Prod.ext
            · funext i
              exact Fin.elim0 i
            · apply Prod.ext
              · simpa [Chapter01.centeredObservation, a] using hx 0
              · funext j
                have hj := hx j.succ
                change e x ((j : ℤ) + 1) = future j
                simpa [a] using hj
        rw [MeasureTheory.Measure.map_apply he
          (Chapter01.centeredCylinder_measurable past center future), hset,
          hcyl n a]
        have htarget : Chapter01.centeredCylinder past center future =
            {x : ℤ → Fin k | ∀ i : Fin (n + 1), x (i : ℤ) = a i} := by
          ext x
          simp only [Chapter01.centeredCylinder, Set.mem_singleton_iff,
            Set.mem_setOf_eq]
          constructor
          · intro hx i
            have hrest := congrArg Prod.snd hx
            have hc := congrArg Prod.fst hrest
            have hf := congrArg Prod.snd hrest
            refine Fin.cases ?_ (fun j ↦ ?_) i
            · simpa [Chapter01.centeredObservation, a] using hc
            · have hj := congrFun hf j
              change x ((j : ℤ) + 1) = future j at hj
              simpa [a] using hj
          · intro hx
            apply Prod.ext
            · funext i
              exact Fin.elim0 i
            · apply Prod.ext
              · simpa [Chapter01.centeredObservation, a] using hx 0
              · funext j
                have hj := hx j.succ
                change x ((j : ℤ) + 1) = future j
                simpa [a] using hj
        rw [htarget, Chapter01.twoSidedMarkovMeasure_nonnegative_prefix
          k p P hp hsum hP hPsum hstationary n a]
    | succ m ih =>
        intro n past center future
        let left : Fin k := past 0
        let rest : Fin m → Fin k := fun i ↦ past i.succ
        have hpast : Fin.cases left rest = past := by
          funext i
          refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
        have hsourceSet : M.T ⁻¹' (e ⁻¹'
            Chapter01.centeredCylinder past center future) =
            e ⁻¹' Chapter01.centeredCylinder rest left
              (Fin.cases center future) := by
          rw [← hpast]
          ext x
          have heq : e (M.T x) = Chapter01.bilateralShift (e x) := by
            funext z
            exact hT x z
          simp only [Set.mem_preimage, heq]
          exact Set.ext_iff.mp
            (Chapter01.bilateralShift_preimage_centeredCylinder_cons
              left rest center future) (e x)
        have hsourceMeas : MeasurableSet (e ⁻¹'
            Chapter01.centeredCylinder past center future) :=
          he (Chapter01.centeredCylinder_measurable past center future)
        rw [MeasureTheory.Measure.map_apply he
          (Chapter01.centeredCylinder_measurable past center future)]
        rw [← hM.2.measure_preimage hsourceMeas.nullMeasurableSet, hsourceSet]
        rw [← MeasureTheory.Measure.map_apply he
          (Chapter01.centeredCylinder_measurable rest left
            (Fin.cases center future))]
        rw [ih (past := rest) (center := left)
          (future := Fin.cases center future)]
        rw [← hpast]
        simpa [Chapter01.bilateralShift_preimage_centeredCylinder_cons] using
          (Chapter01.twoSidedMarkovMeasure_shift_centeredCylinder_cons
            k p P hp hsum hP hPsum hstationary left rest center future)
  refine ⟨e, he, heinv, ?_, hT⟩
  apply MeasureTheory.Measure.ext_of_generateFrom_of_cover_subset
    (Chapter01.centeredSetFamily_generate k)
    (Chapter01.centeredSetFamily_piSystem k) (T := {Set.univ})
  · intro C hC
    subst C
    exact ⟨0, 0, Set.univ, by simp⟩
  · exact Set.countable_singleton _
  · simp
  · intro C hC
    subst C
    rw [MeasureTheory.Measure.map_apply he MeasurableSet.univ]
    simp only [Set.preimage_univ]
    change (Chapter01.MeasurePreservingSystemData.toProbabilitySpace M).μ Set.univ ≠ ∞
    rw [hM.1.measure_univ]
    norm_num
  · rintro C ⟨m, n, A, rfl⟩
    have hobs : MeasureTheory.Measure.map (Chapter01.centeredObservation m n) ν =
        MeasureTheory.Measure.map (Chapter01.centeredObservation m n) μ₂ := by
      apply MeasureTheory.Measure.ext_of_singleton
      rintro ⟨past, center, future⟩
      rw [MeasureTheory.Measure.map_apply
          (Chapter01.centeredObservation_measurable m n) (MeasurableSet.singleton _),
        MeasureTheory.Measure.map_apply
          (Chapter01.centeredObservation_measurable m n) (MeasurableSet.singleton _)]
      exact hcenter m n past center future
    rw [← MeasureTheory.Measure.map_apply (Chapter01.centeredObservation_measurable m n)
        (Set.toFinite A).measurableSet,
      ← MeasureTheory.Measure.map_apply (Chapter01.centeredObservation_measurable m n)
        (Set.toFinite A).measurableSet, hobs]

theorem markovShiftStrongMixing_of_entrywise_limit {M : System.{u}}
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (h : Chapter01.IsMarkovShiftWith M k p P)
    (hlim : ∀ i j, Tendsto (fun n ↦ (P ^ n) i j) atTop (nhds (p j))) :
    IsStrongMixing M := by
  rcases h with hone | htwo
  · exact oneSidedStrongMixing_of_entrywise_limit k p P hone hlim
  · have htwo' := htwo
    rcases htwo with ⟨hM, _e, _he, _heinv, _hT, hp, hsum, hP, hPsum,
      hstationary, _hcyl⟩
    rcases twoSided_map_eq k p P hp hsum hP hPsum hstationary htwo' with
      ⟨e, he, heinv, hmap, hT⟩
    apply BernoulliMixing.strongMixing_of_measurable_conjugacy hM
      (canonicalTwoSidedStrongMixing k p P hp hsum hP hPsum hstationary hlim)
      e he heinv hmap
    intro x
    funext z
    exact hT x z

theorem markovShiftStrongMixing_of_primitive {M : System.{u}}
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (h : Chapter01.IsMarkovShiftWith M k p P) (hp : ∀ i, 0 < p i)
    (hprimitive : IsIrreducibleStochasticMatrix P ∧
      Chapter00.IsAperiodicNonnegativeMatrix k P) :
    IsStrongMixing M := by
  have h' := h
  rcases h with hone | htwo
  · rcases hone with ⟨_hM, _e, _he, _heinv, _hT, _hp0, hsum, hP, hPsum,
      hstationary, _hcyl⟩
    have hlim := (primitive_iff_entrywise_stationary_limit k p P hp hsum hP
      hPsum hstationary).mp hprimitive
    exact markovShiftStrongMixing_of_entrywise_limit k p P h' hlim
  · rcases htwo with ⟨_hM, _e, _he, _heinv, _hT, _hp0, hsum, hP, hPsum,
      hstationary, _hcyl⟩
    have hlim := (primitive_iff_entrywise_stationary_limit k p P hp hsum hP
      hPsum hstationary).mp hprimitive
    exact markovShiftStrongMixing_of_entrywise_limit k p P h' hlim

private theorem canonicalOneSided_entrywise_limit_of_strongMixing
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hmix : IsStrongMixing (Chapter01.oneSidedMarkovSystem k p P hP hPsum)) :
    ∀ i j, Tendsto (fun n ↦ (P ^ n) i j) atTop (nhds (p j)) := by
  let M := Chapter01.oneSidedMarkovSystem k p P hP hPsum
  intro i j
  let ai : Fin 1 → Fin k := fun _ ↦ i
  let aj : Fin 1 → Fin k := fun _ ↦ j
  let Ci := Chapter01.markovPrefixCylinder ai
  let Cj := Chapter01.markovPrefixCylinder aj
  have hCi : MeasurableSet Ci := Chapter01.markovPrefixCylinder_measurable ai
  have hCj : MeasurableSet Cj := Chapter01.markovPrefixCylinder_measurable aj
  have hcorr := hmix.2 Ci Cj hCi hCj
  have hmeasurei : realMeasure M Ci = p i := by
    unfold realMeasure
    change (Chapter01.oneSidedMarkovMeasure k p P hP hPsum Ci).toReal = p i
    rw [show Ci = listPrefixCylinder [i] by
      change Chapter01.markovPrefixCylinder ai = listPrefixCylinder [i]
      rw [markovPrefixCylinder_eq_listPrefixCylinder]
      ext x
      simp [ai, listPrefixCylinder],
      listPrefixCylinder_cons_measure k p P (fun q ↦ (hp q).le) hsum hP hPsum]
    simp [listTransitionWeight, (hp i).le]
  have hmeasurej : realMeasure M Cj = p j := by
    unfold realMeasure
    change (Chapter01.oneSidedMarkovMeasure k p P hP hPsum Cj).toReal = p j
    rw [show Cj = listPrefixCylinder [j] by
      change Chapter01.markovPrefixCylinder aj = listPrefixCylinder [j]
      rw [markovPrefixCylinder_eq_listPrefixCylinder]
      ext x
      simp [aj, listPrefixCylinder],
      listPrefixCylinder_cons_measure k p P (fun q ↦ (hp q).le) hsum hP hPsum]
    simp [listTransitionWeight, (hp j).le]
  have hprod : productMeasureValue M Ci Cj = p i * p j := by
    unfold productMeasureValue
    rw [hmeasurei, hmeasurej]
  rw [hprod] at hcorr
  apply (Filter.tendsto_add_atTop_iff_nat
    (f := fun n ↦ (P ^ n) i j) 1).mp
  have hscaled := (hcorr.comp (tendsto_add_atTop_nat 1)).const_mul (p i)⁻¹
  convert hscaled using 1
  · funext q
    symm
    unfold correlation realMeasure
    have hset : Ci ∩ preimageIter M (q + 1) Cj =
        separatedListCylinders [i] [j] (q + 1) := by
      change Chapter01.markovPrefixCylinder ai ∩
          (Chapter01.oneSidedShift^[q + 1]) ⁻¹'
            Chapter01.markovPrefixCylinder aj = _
      simpa [ai, aj] using
        (prefixCylinder_inter_shift_eq_separated ai aj (q + 1))
    change (p i)⁻¹ * (M.μ (Ci ∩ preimageIter M (q + 1) Cj)).toReal = _
    rw [hset]
    change (p i)⁻¹ * (Chapter01.oneSidedMarkovMeasure k p P hP hPsum
      (separatedListCylinders [i] [j] (q + 1))).toReal = _
    rw [separatedListCylinders_measure k p P (fun q ↦ (hp q).le) hsum
      hP hPsum i [] j [] q]
    have hnonneg : 0 ≤ p i * (P ^ (q + 1)) i j :=
      mul_nonneg (hp i).le (FiniteMarkov.pow_nonnegative P hP _ _ _)
    rw [ENNReal.toReal_ofReal]
    · simp [listTransitionWeight]
      field_simp [(hp i).ne']
    · simpa [listTransitionWeight] using hnonneg
  · congr 1
    field_simp [(hp i).ne']

private theorem strongMixing_of_conjugacy_inverse {M : System.{u}} {N : System.{v}}
    (hN : Chapter01.IsMeasurePreservingSystem N) (hM : IsStrongMixing M)
    (e : M.X ≃ N.X) (he : Measurable e) (heinv : Measurable e.symm)
    (hmap : MeasureTheory.Measure.map e M.μ = N.μ)
    (hT : ∀ x, e (M.T x) = N.T (e x)) : IsStrongMixing N := by
  have hmapinv : MeasureTheory.Measure.map e.symm N.μ = M.μ := by
    rw [← hmap, MeasureTheory.Measure.map_map heinv he]
    simpa using (MeasureTheory.Measure.map_id :
      MeasureTheory.Measure.map (id : M.X → M.X) M.μ = M.μ)
  apply BernoulliMixing.strongMixing_of_measurable_conjugacy hN hM
    e.symm heinv he hmapinv
  intro y
  apply e.injective
  simpa using (hT (e.symm y)).symm

private theorem iterate_conjugacy {M : System.{u}} {N : System.{v}}
    (e : M.X ≃ N.X) (hT : ∀ x, e (M.T x) = N.T (e x))
    (n : ℕ) (x : M.X) : e ((M.T^[n]) x) = (N.T^[n]) (e x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hT]

private theorem correlation_eq_of_measurable_conjugacy
    {M : System.{u}} {N : System.{v}}
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (e : M.X ≃ N.X) (he : Measurable e)
    (hmap : MeasureTheory.Measure.map e M.μ = N.μ)
    (hT : ∀ x, e (M.T x) = N.T (e x))
    (A B : Set N.X) (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    correlation M (e ⁻¹' A) (e ⁻¹' B) n = correlation N A B n := by
  have hset : (e ⁻¹' A) ∩ preimageIter M n (e ⁻¹' B) =
      e ⁻¹' (A ∩ preimageIter N n B) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, preimageIter,
      Chapter01.iterateMap]
    rw [iterate_conjugacy e hT n x]
  have htarget : MeasurableSet (A ∩ preimageIter N n B) :=
    hA.inter (hB.preimage (hN.2.measurable.iterate n))
  unfold correlation realMeasure
  rw [hset]
  exact congrArg ENNReal.toReal (by
    calc
      M.μ (e ⁻¹' (A ∩ preimageIter N n B)) =
          MeasureTheory.Measure.map e M.μ (A ∩ preimageIter N n B) :=
        (MeasureTheory.Measure.map_apply he htarget).symm
      _ = N.μ (A ∩ preimageIter N n B) := by rw [hmap])

private theorem cesaroCorrelations_of_measurable_conjugacy
    {M : System.{u}} {N : System.{v}}
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (hNcorr : ∀ A B : Set N.X, MeasurableSet A → MeasurableSet B →
      cesaroTendsTo (fun n ↦ correlation N A B n) (productMeasureValue N A B))
    (e : M.X ≃ N.X) (he : Measurable e) (heinv : Measurable e.symm)
    (hmap : MeasureTheory.Measure.map e M.μ = N.μ)
    (hT : ∀ x, e (M.T x) = N.T (e x)) :
    ∀ A B : Set M.X, MeasurableSet A → MeasurableSet B →
      cesaroTendsTo (fun n ↦ correlation M A B n) (productMeasureValue M A B) := by
  intro A B hA hB
  let A' : Set N.X := e.symm ⁻¹' A
  let B' : Set N.X := e.symm ⁻¹' B
  have hA' : MeasurableSet A' := heinv hA
  have hB' : MeasurableSet B' := heinv hB
  have hmeasure : ∀ C : Set N.X, MeasurableSet C → M.μ (e ⁻¹' C) = N.μ C := by
    intro C hC
    calc
      M.μ (e ⁻¹' C) = MeasureTheory.Measure.map e M.μ C := by
        rw [MeasureTheory.Measure.map_apply he hC]
      _ = N.μ C := by rw [hmap]
  have hpreA : e ⁻¹' A' = A := by ext x; simp [A']
  have hpreB : e ⁻¹' B' = B := by ext x; simp [B']
  have hcorr : ∀ n, correlation M A B n = correlation N A' B' n := by
    intro n
    have hset : A ∩ preimageIter M n B =
        e ⁻¹' (A' ∩ preimageIter N n B') := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, preimageIter,
        Chapter01.iterateMap]
      rw [← hpreA, ← hpreB]
      simp only [Set.mem_preimage]
      rw [iterate_conjugacy e hT n x]
    have htarget : MeasurableSet (A' ∩ preimageIter N n B') :=
      hA'.inter (hB'.preimage (hN.2.measurable.iterate n))
    unfold correlation realMeasure
    rw [hset, hmeasure _ htarget]
  have hprod : productMeasureValue M A B = productMeasureValue N A' B' := by
    unfold productMeasureValue realMeasure
    rw [← hpreA, ← hpreB, hmeasure A' hA', hmeasure B' hB']
  have hseq : (fun n ↦ correlation M A B n) =
      (fun n ↦ correlation N A' B' n) := funext hcorr
  rw [hprod, hseq]
  exact hNcorr A' B' hA' hB'

private theorem weakMixing_of_measurable_conjugacy {M : System.{u}} {N : System.{v}}
    (hM : Chapter01.IsMeasurePreservingSystem M) (hN : IsWeakMixing N)
    (e : M.X ≃ N.X) (he : Measurable e) (heinv : Measurable e.symm)
    (hmap : MeasureTheory.Measure.map e M.μ = N.μ)
    (hT : ∀ x, e (M.T x) = N.T (e x)) : IsWeakMixing M := by
  refine ⟨hM, ?_⟩
  intro A B hA hB
  let A' : Set N.X := e.symm ⁻¹' A
  let B' : Set N.X := e.symm ⁻¹' B
  have hA' : MeasurableSet A' := heinv hA
  have hB' : MeasurableSet B' := heinv hB
  have hmeasure : ∀ C : Set N.X, MeasurableSet C → M.μ (e ⁻¹' C) = N.μ C := by
    intro C hC
    calc
      M.μ (e ⁻¹' C) = MeasureTheory.Measure.map e M.μ C := by
        rw [MeasureTheory.Measure.map_apply he hC]
      _ = N.μ C := by rw [hmap]
  have hpreA : e ⁻¹' A' = A := by
    ext x
    simp [A']
  have hpreB : e ⁻¹' B' = B := by
    ext x
    simp [B']
  have hcorr : ∀ n, correlation M A B n = correlation N A' B' n := by
    intro n
    have hset : A ∩ preimageIter M n B =
        e ⁻¹' (A' ∩ preimageIter N n B') := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, preimageIter,
        Chapter01.iterateMap]
      rw [← hpreA, ← hpreB]
      simp only [Set.mem_preimage]
      rw [iterate_conjugacy e hT n x]
    have htarget : MeasurableSet (A' ∩ preimageIter N n B') :=
      hA'.inter (hB'.preimage (hN.1.2.iterate n).measurable)
    unfold correlation realMeasure
    rw [hset, hmeasure _ htarget]
  have hprod : productMeasureValue M A B = productMeasureValue N A' B' := by
    unfold productMeasureValue realMeasure
    rw [← hpreA, ← hpreB, hmeasure A' hA', hmeasure B' hB']
  have hseq : (fun n ↦ |correlation M A B n - productMeasureValue M A B|) =
      fun n ↦ |correlation N A' B' n - productMeasureValue N A' B'| := by
    funext n
    rw [hcorr n, hprod]
  rw [hseq]
  exact hN.2 A' B' hA' hB'

private theorem weakMixing_of_conjugacy_inverse {M : System.{u}} {N : System.{v}}
    (hN : Chapter01.IsMeasurePreservingSystem N) (hM : IsWeakMixing M)
    (e : M.X ≃ N.X) (he : Measurable e) (heinv : Measurable e.symm)
    (hmap : MeasureTheory.Measure.map e M.μ = N.μ)
    (hT : ∀ x, e (M.T x) = N.T (e x)) : IsWeakMixing N := by
  have hmapinv : MeasureTheory.Measure.map e.symm N.μ = M.μ := by
    rw [← hmap, MeasureTheory.Measure.map_map heinv he]
    simpa using (MeasureTheory.Measure.map_id :
      MeasureTheory.Measure.map (id : M.X → M.X) M.μ = M.μ)
  apply weakMixing_of_measurable_conjugacy hN hM e.symm heinv he hmapinv
  intro y
  apply e.injective
  simpa using (hT (e.symm y)).symm

private theorem canonicalOneSidedStrongMixing_of_twoSided
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hmix : IsStrongMixing
      (Chapter01.twoSidedMarkovSystem k p P hp hsum hP hPsum hstationary)) :
    IsStrongMixing (Chapter01.oneSidedMarkovSystem k p P hP hPsum) := by
  let M₂ := Chapter01.twoSidedMarkovSystem k p P hp hsum hP hPsum hstationary
  let M₁ := Chapter01.oneSidedMarkovSystem k p P hP hPsum
  have hM₁ : Chapter01.IsMeasurePreservingSystem M₁ :=
    Chapter01.oneSidedMarkovSystem_mps k p P hp hsum hP hPsum hstationary
  have hmap := twoSided_map_nonnegativeRestriction k p P hp hsum hP hPsum hstationary
  refine ⟨hM₁, ?_⟩
  intro A B hA hB
  have hA' : MeasurableSet A := hA
  have hB' : MeasurableSet B := hB
  have hpreA : MeasurableSet (nonnegativeRestriction ⁻¹' A) :=
    hA'.preimage nonnegativeRestriction_measurable
  have hpreB : MeasurableSet (nonnegativeRestriction ⁻¹' B) :=
    hB'.preimage nonnegativeRestriction_measurable
  have hcorr₂ := hmix.2 (nonnegativeRestriction ⁻¹' A)
    (nonnegativeRestriction ⁻¹' B) hpreA hpreB
  have hmeasure : ∀ C : Set (ℕ → Fin k), MeasurableSet C →
      M₂.μ (nonnegativeRestriction ⁻¹' C) = M₁.μ C := by
    intro C hC
    calc
      M₂.μ (nonnegativeRestriction ⁻¹' C) =
          MeasureTheory.Measure.map nonnegativeRestriction M₂.μ C :=
        (MeasureTheory.Measure.map_apply nonnegativeRestriction_measurable hC).symm
      _ = M₁.μ C := by
        change MeasureTheory.Measure.map nonnegativeRestriction
          (Chapter01.twoSidedMarkovMeasure k p P hp hsum hP hPsum hstationary) C =
          Chapter01.oneSidedMarkovMeasure k p P hP hPsum C
        rw [hmap]
  have hcorr : ∀ n, correlation M₂ (nonnegativeRestriction ⁻¹' A)
      (nonnegativeRestriction ⁻¹' B) n = correlation M₁ A B n := by
    intro n
    unfold correlation realMeasure
    have hset : (nonnegativeRestriction ⁻¹' A) ∩
        preimageIter M₂ n (nonnegativeRestriction ⁻¹' B) =
        nonnegativeRestriction ⁻¹' (A ∩ preimageIter M₁ n B) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, preimageIter,
        Chapter01.iterateMap]
      change nonnegativeRestriction x ∈ A ∧
          nonnegativeRestriction ((Chapter01.bilateralShift^[n]) x) ∈ B ↔
        nonnegativeRestriction x ∈ A ∧
          (Chapter01.oneSidedShift^[n]) (nonnegativeRestriction x) ∈ B
      rw [nonnegativeRestriction_iterate]
    rw [hset]
    exact congrArg ENNReal.toReal (hmeasure _ (hA'.inter
      (hB'.preimage (hM₁.2.measurable.iterate n))))
  have hprod : productMeasureValue M₂ (nonnegativeRestriction ⁻¹' A)
      (nonnegativeRestriction ⁻¹' B) = productMeasureValue M₁ A B := by
    unfold productMeasureValue realMeasure
    rw [hmeasure A hA', hmeasure B hB']
  rw [← hprod]
  exact hcorr₂.congr'
    (Filter.Eventually.of_forall fun n ↦ hcorr n)

private theorem canonicalOneSidedWeakMixing_of_twoSided
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hmix : IsWeakMixing
      (Chapter01.twoSidedMarkovSystem k p P hp hsum hP hPsum hstationary)) :
    IsWeakMixing (Chapter01.oneSidedMarkovSystem k p P hP hPsum) := by
  let M₂ := Chapter01.twoSidedMarkovSystem k p P hp hsum hP hPsum hstationary
  let M₁ := Chapter01.oneSidedMarkovSystem k p P hP hPsum
  have hM₁ : Chapter01.IsMeasurePreservingSystem M₁ :=
    Chapter01.oneSidedMarkovSystem_mps k p P hp hsum hP hPsum hstationary
  have hmap := twoSided_map_nonnegativeRestriction k p P hp hsum hP hPsum hstationary
  refine ⟨hM₁, ?_⟩
  intro A B hA hB
  have hA' : MeasurableSet A := hA
  have hB' : MeasurableSet B := hB
  have hpreA : MeasurableSet (nonnegativeRestriction ⁻¹' A) :=
    hA'.preimage nonnegativeRestriction_measurable
  have hpreB : MeasurableSet (nonnegativeRestriction ⁻¹' B) :=
    hB'.preimage nonnegativeRestriction_measurable
  have hweak₂ := hmix.2 (nonnegativeRestriction ⁻¹' A)
    (nonnegativeRestriction ⁻¹' B) hpreA hpreB
  have hmeasure : ∀ C : Set (ℕ → Fin k), MeasurableSet C →
      M₂.μ (nonnegativeRestriction ⁻¹' C) = M₁.μ C := by
    intro C hC
    calc
      M₂.μ (nonnegativeRestriction ⁻¹' C) =
          MeasureTheory.Measure.map nonnegativeRestriction M₂.μ C :=
        (MeasureTheory.Measure.map_apply nonnegativeRestriction_measurable hC).symm
      _ = M₁.μ C := by
        change MeasureTheory.Measure.map nonnegativeRestriction
          (Chapter01.twoSidedMarkovMeasure k p P hp hsum hP hPsum hstationary) C =
          Chapter01.oneSidedMarkovMeasure k p P hP hPsum C
        rw [hmap]
  have hcorr : ∀ n, correlation M₂ (nonnegativeRestriction ⁻¹' A)
      (nonnegativeRestriction ⁻¹' B) n = correlation M₁ A B n := by
    intro n
    unfold correlation realMeasure
    have hset : (nonnegativeRestriction ⁻¹' A) ∩
        preimageIter M₂ n (nonnegativeRestriction ⁻¹' B) =
        nonnegativeRestriction ⁻¹' (A ∩ preimageIter M₁ n B) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, preimageIter,
        Chapter01.iterateMap]
      change nonnegativeRestriction x ∈ A ∧
          nonnegativeRestriction ((Chapter01.bilateralShift^[n]) x) ∈ B ↔
        nonnegativeRestriction x ∈ A ∧
          (Chapter01.oneSidedShift^[n]) (nonnegativeRestriction x) ∈ B
      rw [nonnegativeRestriction_iterate]
    rw [hset]
    exact congrArg ENNReal.toReal (hmeasure _ (hA'.inter
      (hB'.preimage (hM₁.2.measurable.iterate n))))
  have hprod : productMeasureValue M₂ (nonnegativeRestriction ⁻¹' A)
      (nonnegativeRestriction ⁻¹' B) = productMeasureValue M₁ A B := by
    unfold productMeasureValue realMeasure
    rw [hmeasure A hA', hmeasure B hB']
  have hseq : (fun n ↦ |correlation M₁ A B n - productMeasureValue M₁ A B|) =
      fun n ↦ |correlation M₂ (nonnegativeRestriction ⁻¹' A)
        (nonnegativeRestriction ⁻¹' B) n -
          productMeasureValue M₂ (nonnegativeRestriction ⁻¹' A)
            (nonnegativeRestriction ⁻¹' B)| := by
    funext n
    rw [hcorr n, hprod]
  rw [hseq]
  exact hweak₂

private theorem canonicalOneSided_aperiodic_of_weakMixing
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hmix : IsWeakMixing (Chapter01.oneSidedMarkovSystem k p P hP hPsum)) :
    Chapter00.IsAperiodicNonnegativeMatrix k P := by
  let M := Chapter01.oneSidedMarkovSystem k p P hP hPsum
  let C : Fin k → Set (ℕ → Fin k) := fun i ↦
    Chapter01.markovPrefixCylinder (fun _ : Fin 1 ↦ i)
  have hCmeas (i : Fin k) : MeasurableSet (C i) :=
    Chapter01.markovPrefixCylinder_measurable (fun _ : Fin 1 ↦ i)
  have hmeasure (i : Fin k) : realMeasure M (C i) = p i := by
    unfold realMeasure
    change (Chapter01.oneSidedMarkovMeasure k p P hP hPsum (C i)).toReal = p i
    rw [show C i = listPrefixCylinder [i] by
      change Chapter01.markovPrefixCylinder (fun _ : Fin 1 ↦ i) =
        listPrefixCylinder [i]
      rw [markovPrefixCylinder_eq_listPrefixCylinder]
      ext x
      simp [listPrefixCylinder],
      listPrefixCylinder_cons_measure k p P (fun q ↦ (hp q).le) hsum hP hPsum]
    simp [listTransitionWeight, (hp i).le]
  have hprod (i j : Fin k) : productMeasureValue M (C i) (C j) = p i * p j := by
    unfold productMeasureValue
    rw [hmeasure i, hmeasure j]
  have hcorr (i j : Fin k) (n : ℕ) (hn : 0 < n) :
      correlation M (C i) (C j) n = p i * (P ^ n) i j := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    unfold correlation realMeasure
    have hset : C i ∩ preimageIter M (q + 1) (C j) =
        separatedListCylinders [i] [j] (q + 1) := by
      change Chapter01.markovPrefixCylinder (fun _ : Fin 1 ↦ i) ∩
          (Chapter01.oneSidedShift^[q + 1]) ⁻¹'
            Chapter01.markovPrefixCylinder (fun _ : Fin 1 ↦ j) = _
      simpa using (prefixCylinder_inter_shift_eq_separated
        (fun _ : Fin 1 ↦ i) (fun _ : Fin 1 ↦ j) (q + 1))
    rw [hset]
    change (Chapter01.oneSidedMarkovMeasure k p P hP hPsum
      (separatedListCylinders [i] [j] (q + 1))).toReal = _
    rw [separatedListCylinders_measure k p P (fun r ↦ (hp r).le) hsum
      hP hPsum i [] j [] q]
    rw [ENNReal.toReal_ofReal]
    · simp [listTransitionWeight]
    · simpa [listTransitionWeight] using
        mul_nonneg (hp i).le (FiniteMarkov.pow_nonnegative P hP _ _ _)
  let d : ℕ → ℝ := fun n ↦ ∑ i, ∑ j,
    (p i * p j)⁻¹ *
      |correlation M (C i) (C j) n - productMeasureValue M (C i) (C j)|
  have hterm (i j : Fin k) : cesaroTendsTo
      (fun n ↦ (p i * p j)⁻¹ *
        |correlation M (C i) (C j) n - productMeasureValue M (C i) (C j)|) 0 := by
    have hw := hmix.2 (C i) (C j) (hCmeas i) (hCmeas j)
    simpa using cesaroTendsTo_const_mul (p i * p j)⁻¹ hw
  have hdlim : cesaroTendsTo d 0 := by
    apply cesaroTendsTo_finset_sum Finset.univ
    intro i hi
    apply cesaroTendsTo_finset_sum Finset.univ
    intro j hj
    exact hterm i j
  have hdnonneg (n : ℕ) : 0 ≤ d n := by
    dsimp [d]
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (hp i).le (hp j).le)) (abs_nonneg _)
  refine ⟨hP, ?_⟩
  by_contra hprimitive
  push_neg at hprimitive
  have hd_ge_one (n : ℕ) (hn : 0 < n) : 1 ≤ d n := by
    rcases hprimitive n hn with ⟨i, j, hij⟩
    have hzero : (P ^ n) i j = 0 :=
      le_antisymm hij (FiniteMarkov.pow_nonnegative P hP n i j)
    have heq : (p i * p j)⁻¹ *
        |correlation M (C i) (C j) n - productMeasureValue M (C i) (C j)| = 1 := by
      rw [hcorr i j n hn, hprod i j, hzero]
      simp only [mul_zero, zero_sub, abs_neg, abs_of_pos (mul_pos (hp i) (hp j))]
      exact inv_mul_cancel₀ (mul_ne_zero (hp i).ne' (hp j).ne')
    have hjle : (p i * p j)⁻¹ *
        |correlation M (C i) (C j) n - productMeasureValue M (C i) (C j)| ≤
        ∑ j', (p i * p j')⁻¹ *
          |correlation M (C i) (C j') n - productMeasureValue M (C i) (C j')| := by
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun j' ↦ (p i * p j')⁻¹ *
          |correlation M (C i) (C j') n - productMeasureValue M (C i) (C j')|)
        (fun j' hj' ↦
        mul_nonneg (inv_nonneg.mpr (mul_nonneg (hp i).le (hp j').le))
          (abs_nonneg _)) (Finset.mem_univ j)
    have hile : (∑ j', (p i * p j')⁻¹ *
          |correlation M (C i) (C j') n - productMeasureValue M (C i) (C j')|) ≤ d n := by
      dsimp [d]
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun i' ↦ ∑ j', (p i' * p j')⁻¹ *
          |correlation M (C i') (C j') n - productMeasureValue M (C i') (C j')|)
        (fun i' hi' ↦
        Finset.sum_nonneg fun j' hj' ↦
          mul_nonneg (inv_nonneg.mpr (mul_nonneg (hp i').le (hp j').le))
            (abs_nonneg _)) (Finset.mem_univ i)
    rw [← heq]
    exact hjle.trans hile
  have hsumlower : ∀ N : ℕ, (N : ℝ) ≤ ∑ n ∈ Finset.range (N + 1), d n := by
    intro N
    induction N with
    | zero =>
        simpa only [Nat.zero_add, Finset.sum_range_succ, Finset.sum_range_zero,
          zero_add, Nat.cast_zero] using hdnonneg 0
    | succ N ih =>
        rw [show N.succ + 1 = (N + 1) + 1 by omega, Finset.sum_range_succ]
        have hone := hd_ge_one (N + 1) (by omega)
        norm_num only [Nat.cast_succ]
        exact add_le_add ih hone
  unfold cesaroTendsTo seqTendsTo at hdlim
  have hsmall : ∀ᶠ N : ℕ in atTop, cesaroAverage d N < (1 / 2 : ℝ) :=
    hdlim.eventually (Iio_mem_nhds (by norm_num))
  rcases (hsmall.and (eventually_ge_atTop 1)).exists with ⟨N, hNsmall, hN⟩
  unfold cesaroAverage at hNsmall
  have hden : 0 < (N : ℝ) + 1 := by positivity
  have hhalf : (1 / 2 : ℝ) ≤ (N : ℝ) / ((N : ℝ) + 1) := by
    apply (le_div_iff₀ hden).2
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have havglower : (N : ℝ) / ((N : ℝ) + 1) ≤
      (((N + 1 : ℕ) : ℝ))⁻¹ * ∑ n ∈ Finset.range (N + 1), d n := by
    rw [Nat.cast_add, Nat.cast_one, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hsumlower N) (inv_nonneg.mpr hden.le)
  exact (not_lt_of_ge (hhalf.trans havglower)) hNsmall

theorem markovShift_entrywise_limit_of_strongMixing {M : System.{u}}
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (h : Chapter01.IsMarkovShiftWith M k p P) (hp : ∀ i, 0 < p i)
    (hmix : IsStrongMixing M) :
    ∀ i j, Tendsto (fun n ↦ (P ^ n) i j) atTop (nhds (p j)) := by
  rcases h with hone | htwo
  · have hone' := hone
    rcases hone with ⟨hM, _e, _he, _heinv, _hT, _hp0, hsum, hP, hPsum,
      hstationary, _hcyl⟩
    rcases oneSided_map_eq k p P hP hPsum hone' with ⟨e, he, heinv, hmap, hT⟩
    have hcanonical := strongMixing_of_conjugacy_inverse
      (Chapter01.oneSidedMarkovSystem_mps k p P (fun i ↦ (hp i).le) hsum
        hP hPsum hstationary) hmix e he heinv hmap (fun x ↦ by
          funext n
          exact hT x n)
    exact canonicalOneSided_entrywise_limit_of_strongMixing k p P hp hsum
      hP hPsum hstationary hcanonical
  · have htwo' := htwo
    rcases htwo with ⟨hM, _e, _he, _heinv, _hT, _hp0, hsum, hP, hPsum,
      hstationary, _hcyl⟩
    rcases twoSided_map_eq k p P (fun i ↦ (hp i).le) hsum hP hPsum
      hstationary htwo' with ⟨e, he, heinv, hmap, hT⟩
    have hcanonical₂ := strongMixing_of_conjugacy_inverse
      (Chapter01.twoSidedMarkovSystem_mps k p P (fun i ↦ (hp i).le) hsum
        hP hPsum hstationary) hmix e he heinv hmap (fun x ↦ by
          funext z
          exact hT x z)
    have hcanonical₁ := canonicalOneSidedStrongMixing_of_twoSided k p P
      (fun i ↦ (hp i).le) hsum hP hPsum hstationary hcanonical₂
    exact canonicalOneSided_entrywise_limit_of_strongMixing k p P hp hsum
      hP hPsum hstationary hcanonical₁

theorem markovShiftStrongMixing_iff_primitive {M : System.{u}}
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (h : Chapter01.IsMarkovShiftWith M k p P) (hp : ∀ i, 0 < p i) :
    IsStrongMixing M ↔
      IsIrreducibleStochasticMatrix P ∧
        Chapter00.IsAperiodicNonnegativeMatrix k P := by
  constructor
  · intro hmix
    have hlim := markovShift_entrywise_limit_of_strongMixing k p P h hp hmix
    rcases h with hone | htwo
    · rcases hone with ⟨_hM, _e, _he, _heinv, _hT, _hp0, hsum, hP, hPsum,
        hstationary, _hcyl⟩
      exact (primitive_iff_entrywise_stationary_limit k p P hp hsum hP hPsum
        hstationary).mpr hlim
    · rcases htwo with ⟨_hM, _e, _he, _heinv, _hT, _hp0, hsum, hP, hPsum,
        hstationary, _hcyl⟩
      exact (primitive_iff_entrywise_stationary_limit k p P hp hsum hP hPsum
        hstationary).mpr hlim
  · exact markovShiftStrongMixing_of_primitive k p P h hp

theorem markovShiftPrimitive_iff_entrywise_limit {M : System.{u}}
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (h : Chapter01.IsMarkovShiftWith M k p P) (hp : ∀ i, 0 < p i) :
    (IsIrreducibleStochasticMatrix P ∧
        Chapter00.IsAperiodicNonnegativeMatrix k P) ↔
      ∀ i j, Tendsto (fun n ↦ (P ^ n) i j) atTop (nhds (p j)) := by
  rcases h with hone | htwo
  · rcases hone with ⟨_hM, _e, _he, _heinv, _hT, _hp0, hsum, hP, hPsum,
      hstationary, _hcyl⟩
    exact primitive_iff_entrywise_stationary_limit k p P hp hsum hP hPsum
      hstationary
  · rcases htwo with ⟨_hM, _e, _he, _heinv, _hT, _hp0, hsum, hP, hPsum,
      hstationary, _hcyl⟩
    exact primitive_iff_entrywise_stationary_limit k p P hp hsum hP hPsum
      hstationary

theorem markovShiftPrimitive_of_weakMixing {M : System.{u}}
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (h : Chapter01.IsMarkovShiftWith M k p P) (hp : ∀ i, 0 < p i)
    (hweak : IsWeakMixing M) :
    IsIrreducibleStochasticMatrix P ∧
      Chapter00.IsAperiodicNonnegativeMatrix k P := by
  have h' := h
  have haper : Chapter00.IsAperiodicNonnegativeMatrix k P := by
    rcases h with hone | htwo
    · have hone' := hone
      rcases hone with ⟨_hM, _e, _he, _heinv, _hT, _hp0, hsum, hP, hPsum,
        hstationary, _hcyl⟩
      rcases oneSided_map_eq k p P hP hPsum hone' with ⟨e, he, heinv, hmap, hT⟩
      have hcanonical := weakMixing_of_conjugacy_inverse
        (Chapter01.oneSidedMarkovSystem_mps k p P (fun i ↦ (hp i).le) hsum
          hP hPsum hstationary) hweak e he heinv hmap (fun x ↦ by
            funext n
            exact hT x n)
      exact canonicalOneSided_aperiodic_of_weakMixing k p P hp hsum hP hPsum
        hstationary hcanonical
    · have htwo' := htwo
      rcases htwo with ⟨_hM, _e, _he, _heinv, _hT, _hp0, hsum, hP, hPsum,
        hstationary, _hcyl⟩
      rcases twoSided_map_eq k p P (fun i ↦ (hp i).le) hsum hP hPsum
        hstationary htwo' with ⟨e, he, heinv, hmap, hT⟩
      have hcanonical₂ := weakMixing_of_conjugacy_inverse
        (Chapter01.twoSidedMarkovSystem_mps k p P (fun i ↦ (hp i).le) hsum
          hP hPsum hstationary) hweak e he heinv hmap (fun x ↦ by
            funext z
            exact hT x z)
      have hcanonical₁ := canonicalOneSidedWeakMixing_of_twoSided k p P
        (fun i ↦ (hp i).le) hsum hP hPsum hstationary hcanonical₂
      exact canonicalOneSided_aperiodic_of_weakMixing k p P hp hsum hP hPsum
        hstationary hcanonical₁
  rcases haper.2 with ⟨n, hn, hpos⟩
  rcases h' with hone | htwo
  · rcases hone with ⟨_hM, _e, _he, _heinv, _hT, _hp0, _hsum, hP, hPsum,
      _hstationary, _hcyl⟩
    exact ⟨⟨hP, hPsum, fun i j ↦ ⟨n, hpos i j⟩⟩, haper⟩
  · rcases htwo with ⟨_hM, _e, _he, _heinv, _hT, _hp0, _hsum, hP, hPsum,
      _hstationary, _hcyl⟩
    exact ⟨⟨hP, hPsum, fun i j ↦ ⟨n, hpos i j⟩⟩, haper⟩

private theorem strongMixing_implies_weakMixing {M : System.{u}}
    (hstrong : IsStrongMixing M) : IsWeakMixing M := by
  refine ⟨hstrong.1, ?_⟩
  intro A B hA hB
  have hcorr := hstrong.2 A B hA hB
  have habs : Tendsto
      (fun n ↦ |correlation M A B n - productMeasureValue M A B|)
      atTop (nhds 0) := by
    convert (hcorr.sub tendsto_const_nhds).abs using 1 <;> simp
  unfold cesaroTendsTo seqTendsTo cesaroAverage
  exact habs.cesaro.comp (tendsto_add_atTop_nat 1)

theorem markovShiftWeakMixing_iff_strongMixing {M : System.{u}}
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (h : Chapter01.IsMarkovShiftWith M k p P) (hp : ∀ i, 0 < p i) :
    IsWeakMixing M ↔ IsStrongMixing M := by
  constructor
  · intro hweak
    exact markovShiftStrongMixing_of_primitive k p P h hp
      (markovShiftPrimitive_of_weakMixing k p P h hp hweak)
  · exact strongMixing_implies_weakMixing

theorem markovShiftErgodic_of_irreducible {M : System.{u}}
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (h : Chapter01.IsMarkovShiftWith M k p P) (hp : ∀ i, 0 < p i)
    (hirr : IsIrreducibleStochasticMatrix P) : IsErgodic M := by
  rcases h with hone | htwo
  · have hone' := hone
    rcases hone with ⟨hM, _e, _he, _heinv, _hT, _hp0, hsum, hP, hPsum,
      hstationary, _hcyl⟩
    rcases oneSided_map_eq k p P hP hPsum hone' with ⟨e, he, heinv, hmap, hT⟩
    have hN := Chapter01.oneSidedMarkovSystem_mps k p P (fun i ↦ (hp i).le)
      hsum hP hPsum hstationary
    apply ergodic_of_cesaroCorrelations hM
    apply cesaroCorrelations_of_measurable_conjugacy hM hN
      (canonicalOneSidedCesaroCorrelations_of_irreducible k p P hp hsum
        hP hPsum hstationary hirr) e he heinv hmap
    intro x
    funext n
    exact hT x n
  · have htwo' := htwo
    rcases htwo with ⟨hM, _e, _he, _heinv, _hT, _hp0, hsum, hP, hPsum,
      hstationary, _hcyl⟩
    rcases twoSided_map_eq k p P (fun i ↦ (hp i).le) hsum hP hPsum
      hstationary htwo' with ⟨e, he, heinv, hmap, hT⟩
    have hN := Chapter01.twoSidedMarkovSystem_mps k p P (fun i ↦ (hp i).le)
      hsum hP hPsum hstationary
    apply ergodic_of_cesaroCorrelations hM
    apply cesaroCorrelations_of_measurable_conjugacy hM hN
      (canonicalTwoSidedCesaroCorrelations_of_irreducible k p P hp hsum
        hP hPsum hstationary hirr) e he heinv hmap
    intro x
    funext z
    exact hT x z

private theorem canonicalOneSided_singleton_correlation
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (i j : Fin k) (n : ℕ) (hn : 0 < n) :
    let M := Chapter01.oneSidedMarkovSystem k p P hP hPsum
    let Ci := Chapter01.markovPrefixCylinder (fun _ : Fin 1 ↦ i)
    let Cj := Chapter01.markovPrefixCylinder (fun _ : Fin 1 ↦ j)
    correlation M Ci Cj n = p i * (P ^ n) i j := by
  let M := Chapter01.oneSidedMarkovSystem k p P hP hPsum
  let Ci := Chapter01.markovPrefixCylinder (fun _ : Fin 1 ↦ i)
  let Cj := Chapter01.markovPrefixCylinder (fun _ : Fin 1 ↦ j)
  dsimp only
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  unfold correlation realMeasure
  have hset : Ci ∩ preimageIter M (q + 1) Cj =
      separatedListCylinders [i] [j] (q + 1) := by
    change Chapter01.markovPrefixCylinder (fun _ : Fin 1 ↦ i) ∩
        (Chapter01.oneSidedShift^[q + 1]) ⁻¹'
          Chapter01.markovPrefixCylinder (fun _ : Fin 1 ↦ j) = _
    simpa using (prefixCylinder_inter_shift_eq_separated
      (fun _ : Fin 1 ↦ i) (fun _ : Fin 1 ↦ j) (q + 1))
  rw [hset]
  change (Chapter01.oneSidedMarkovMeasure k p P hP hPsum
    (separatedListCylinders [i] [j] (q + 1))).toReal = _
  rw [separatedListCylinders_measure k p P hp hsum hP hPsum i [] j [] q]
  rw [ENNReal.toReal_ofReal]
  · simp [listTransitionWeight]
  · simpa [listTransitionWeight] using
      mul_nonneg (hp i) (FiniteMarkov.pow_nonnegative P hP _ _ _)

private theorem canonicalTwoSided_future_correlation
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (A B : Set (ℕ → Fin k)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (n : ℕ) :
    let M₂ := Chapter01.twoSidedMarkovSystem k p P hp hsum hP hPsum hstationary
    let M₁ := Chapter01.oneSidedMarkovSystem k p P hP hPsum
    correlation M₂ (nonnegativeRestriction ⁻¹' A)
      (nonnegativeRestriction ⁻¹' B) n = correlation M₁ A B n := by
  let M₂ := Chapter01.twoSidedMarkovSystem k p P hp hsum hP hPsum hstationary
  let M₁ := Chapter01.oneSidedMarkovSystem k p P hP hPsum
  dsimp only
  have hM₁ : Chapter01.IsMeasurePreservingSystem M₁ :=
    Chapter01.oneSidedMarkovSystem_mps k p P hp hsum hP hPsum hstationary
  have hmap := twoSided_map_nonnegativeRestriction k p P hp hsum hP hPsum hstationary
  have hmeasure : ∀ C : Set (ℕ → Fin k), MeasurableSet C →
      M₂.μ (nonnegativeRestriction ⁻¹' C) = M₁.μ C := by
    intro C hC
    calc
      M₂.μ (nonnegativeRestriction ⁻¹' C) =
          MeasureTheory.Measure.map nonnegativeRestriction M₂.μ C :=
        (MeasureTheory.Measure.map_apply nonnegativeRestriction_measurable hC).symm
      _ = M₁.μ C := by
        change MeasureTheory.Measure.map nonnegativeRestriction
          (Chapter01.twoSidedMarkovMeasure k p P hp hsum hP hPsum hstationary) C =
          Chapter01.oneSidedMarkovMeasure k p P hP hPsum C
        rw [hmap]
  unfold correlation realMeasure
  have hset : (nonnegativeRestriction ⁻¹' A) ∩
      preimageIter M₂ n (nonnegativeRestriction ⁻¹' B) =
      nonnegativeRestriction ⁻¹' (A ∩ preimageIter M₁ n B) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, preimageIter,
      Chapter01.iterateMap]
    change nonnegativeRestriction x ∈ A ∧
        nonnegativeRestriction ((Chapter01.bilateralShift^[n]) x) ∈ B ↔
      nonnegativeRestriction x ∈ A ∧
        (Chapter01.oneSidedShift^[n]) (nonnegativeRestriction x) ∈ B
    rw [nonnegativeRestriction_iterate]
  rw [hset]
  exact congrArg ENNReal.toReal (hmeasure _
    (hA.inter (hB.preimage (hM₁.2.measurable.iterate n))))

theorem markovShiftIrreducible_of_ergodic {M : System.{u}}
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (h : Chapter01.IsMarkovShiftWith M k p P) (hp : ∀ i, 0 < p i)
    (herg : IsErgodic M) : IsIrreducibleStochasticMatrix P := by
  rcases h with hone | htwo
  · have hone' := hone
    rcases hone with ⟨hM, _e, _he, _heinv, _hT, _hp0, hsum, hP, hPsum,
      hstationary, _hcyl⟩
    rcases oneSided_map_eq k p P hP hPsum hone' with ⟨e, he, heinv, hmap, hT⟩
    let N := Chapter01.oneSidedMarkovSystem k p P hP hPsum
    have hN : Chapter01.IsMeasurePreservingSystem N :=
      Chapter01.oneSidedMarkovSystem_mps k p P (fun i ↦ (hp i).le) hsum
        hP hPsum hstationary
    refine ⟨hP, hPsum, ?_⟩
    intro i j
    let Ci : Set (ℕ → Fin k) :=
      Chapter01.markovPrefixCylinder (fun _ : Fin 1 ↦ i)
    let Cj : Set (ℕ → Fin k) :=
      Chapter01.markovPrefixCylinder (fun _ : Fin 1 ↦ j)
    have hCi : MeasurableSet Ci :=
      Chapter01.markovPrefixCylinder_measurable (fun _ : Fin 1 ↦ i)
    have hCj : MeasurableSet Cj :=
      Chapter01.markovPrefixCylinder_measurable (fun _ : Fin 1 ↦ j)
    have hmeasureCi : M.μ (e ⁻¹' Ci) = ENNReal.ofReal (p i) := by
      rw [← MeasureTheory.Measure.map_apply he hCi, hmap]
      exact Chapter01.oneSidedMarkovMeasure_prefix_zero k p P hP hPsum _
    have hmeasureCj : M.μ (e ⁻¹' Cj) = ENNReal.ofReal (p j) := by
      rw [← MeasureTheory.Measure.map_apply he hCj, hmap]
      exact Chapter01.oneSidedMarkovMeasure_prefix_zero k p P hP hPsum _
    obtain ⟨n, hn, hret⟩ := ergodic_exists_positive_return herg
      (e ⁻¹' Ci) (e ⁻¹' Cj) (hCi.preimage he) (hCj.preimage he)
      (by rw [hmeasureCi]; exact ENNReal.ofReal_pos.mpr (hp i))
      (by rw [hmeasureCj]; exact ENNReal.ofReal_pos.mpr (hp j))
    refine ⟨n, ?_⟩
    have hcorrM : 0 < correlation M (e ⁻¹' Ci) (e ⁻¹' Cj) n := by
      letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
      unfold correlation realMeasure
      exact ENNReal.toReal_pos hret.ne' (MeasureTheory.measure_ne_top M.μ _)
    have hcorrEq := correlation_eq_of_measurable_conjugacy hM hN e he hmap
      (fun x ↦ by funext q; exact hT x q) Ci Cj hCi hCj n
    have hformula := canonicalOneSided_singleton_correlation k p P
      (fun q ↦ (hp q).le) hsum hP hPsum i j n hn
    change correlation N Ci Cj n = p i * (P ^ n) i j at hformula
    have hcorrN : 0 < correlation N Ci Cj n := lt_of_lt_of_eq hcorrM hcorrEq
    have hprodpos : 0 < p i * (P ^ n) i j := lt_of_lt_of_eq hcorrN hformula
    rcases (mul_pos_iff.mp hprodpos) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge (hp i).le hneg.1).elim
  · have htwo' := htwo
    rcases htwo with ⟨hM, _e, _he, _heinv, _hT, _hp0, hsum, hP, hPsum,
      hstationary, _hcyl⟩
    rcases twoSided_map_eq k p P (fun i ↦ (hp i).le) hsum hP hPsum
      hstationary htwo' with ⟨e, he, heinv, hmap, hT⟩
    let N₂ := Chapter01.twoSidedMarkovSystem k p P (fun i ↦ (hp i).le)
      hsum hP hPsum hstationary
    let N₁ := Chapter01.oneSidedMarkovSystem k p P hP hPsum
    have hN₂ : Chapter01.IsMeasurePreservingSystem N₂ :=
      Chapter01.twoSidedMarkovSystem_mps k p P (fun i ↦ (hp i).le) hsum
        hP hPsum hstationary
    have hfactor := twoSided_map_nonnegativeRestriction k p P (fun i ↦ (hp i).le)
      hsum hP hPsum hstationary
    refine ⟨hP, hPsum, ?_⟩
    intro i j
    let Ci : Set (ℕ → Fin k) :=
      Chapter01.markovPrefixCylinder (fun _ : Fin 1 ↦ i)
    let Cj : Set (ℕ → Fin k) :=
      Chapter01.markovPrefixCylinder (fun _ : Fin 1 ↦ j)
    let Di : Set (ℤ → Fin k) := nonnegativeRestriction ⁻¹' Ci
    let Dj : Set (ℤ → Fin k) := nonnegativeRestriction ⁻¹' Cj
    have hCi : MeasurableSet Ci :=
      Chapter01.markovPrefixCylinder_measurable (fun _ : Fin 1 ↦ i)
    have hCj : MeasurableSet Cj :=
      Chapter01.markovPrefixCylinder_measurable (fun _ : Fin 1 ↦ j)
    have hDi : MeasurableSet Di := hCi.preimage nonnegativeRestriction_measurable
    have hDj : MeasurableSet Dj := hCj.preimage nonnegativeRestriction_measurable
    have hmeasureDiN : N₂.μ Di = ENNReal.ofReal (p i) := by
      calc
        N₂.μ Di = MeasureTheory.Measure.map nonnegativeRestriction N₂.μ Ci :=
          (MeasureTheory.Measure.map_apply nonnegativeRestriction_measurable hCi).symm
        _ = N₁.μ Ci := by
          simpa [N₂, N₁] using congrArg (fun μ : MeasureTheory.Measure (ℕ → Fin k) ↦ μ Ci) hfactor
        _ = ENNReal.ofReal (p i) :=
          Chapter01.oneSidedMarkovMeasure_prefix_zero k p P hP hPsum _
    have hmeasureDjN : N₂.μ Dj = ENNReal.ofReal (p j) := by
      calc
        N₂.μ Dj = MeasureTheory.Measure.map nonnegativeRestriction N₂.μ Cj :=
          (MeasureTheory.Measure.map_apply nonnegativeRestriction_measurable hCj).symm
        _ = N₁.μ Cj := by
          simpa [N₂, N₁] using congrArg (fun μ : MeasureTheory.Measure (ℕ → Fin k) ↦ μ Cj) hfactor
        _ = ENNReal.ofReal (p j) :=
          Chapter01.oneSidedMarkovMeasure_prefix_zero k p P hP hPsum _
    have hmeasureDi : M.μ (e ⁻¹' Di) = ENNReal.ofReal (p i) := by
      calc
        M.μ (e ⁻¹' Di) = MeasureTheory.Measure.map e M.μ Di :=
          (MeasureTheory.Measure.map_apply he hDi).symm
        _ = N₂.μ Di := by
          simpa [N₂] using congrArg (fun μ : MeasureTheory.Measure (ℤ → Fin k) ↦ μ Di) hmap
        _ = ENNReal.ofReal (p i) := hmeasureDiN
    have hmeasureDj : M.μ (e ⁻¹' Dj) = ENNReal.ofReal (p j) := by
      calc
        M.μ (e ⁻¹' Dj) = MeasureTheory.Measure.map e M.μ Dj :=
          (MeasureTheory.Measure.map_apply he hDj).symm
        _ = N₂.μ Dj := by
          simpa [N₂] using congrArg (fun μ : MeasureTheory.Measure (ℤ → Fin k) ↦ μ Dj) hmap
        _ = ENNReal.ofReal (p j) := hmeasureDjN
    obtain ⟨n, hn, hret⟩ := ergodic_exists_positive_return herg
      (e ⁻¹' Di) (e ⁻¹' Dj) (hDi.preimage he) (hDj.preimage he)
      (by rw [hmeasureDi]; exact ENNReal.ofReal_pos.mpr (hp i))
      (by rw [hmeasureDj]; exact ENNReal.ofReal_pos.mpr (hp j))
    refine ⟨n, ?_⟩
    have hcorrM : 0 < correlation M (e ⁻¹' Di) (e ⁻¹' Dj) n := by
      letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
      unfold correlation realMeasure
      exact ENNReal.toReal_pos hret.ne' (MeasureTheory.measure_ne_top M.μ _)
    have hcorrEq := correlation_eq_of_measurable_conjugacy hM hN₂ e he hmap
      (fun x ↦ by funext z; exact hT x z) Di Dj hDi hDj n
    have hfuture := canonicalTwoSided_future_correlation k p P
      (fun q ↦ (hp q).le) hsum hP hPsum hstationary Ci Cj hCi hCj n
    change correlation N₂ Di Dj n = correlation N₁ Ci Cj n at hfuture
    have hformula := canonicalOneSided_singleton_correlation k p P
      (fun q ↦ (hp q).le) hsum hP hPsum i j n hn
    change correlation N₁ Ci Cj n = p i * (P ^ n) i j at hformula
    have hcorrN₂ : 0 < correlation N₂ Di Dj n := lt_of_lt_of_eq hcorrM hcorrEq
    have hcorrN₁ : 0 < correlation N₁ Ci Cj n := lt_of_lt_of_eq hcorrN₂ hfuture
    have hprodpos : 0 < p i * (P ^ n) i j := lt_of_lt_of_eq hcorrN₁ hformula
    rcases (mul_pos_iff.mp hprodpos) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge (hp i).le hneg.1).elim

theorem markovShiftErgodic_iff_irreducible {M : System.{u}}
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (h : Chapter01.IsMarkovShiftWith M k p P) (hp : ∀ i, 0 < p i) :
    IsErgodic M ↔ IsIrreducibleStochasticMatrix P := by
  constructor
  · exact markovShiftIrreducible_of_ergodic k p P h hp
  · exact markovShiftErgodic_of_irreducible k p P h hp

end MarkovErgodic
end Chapter02
