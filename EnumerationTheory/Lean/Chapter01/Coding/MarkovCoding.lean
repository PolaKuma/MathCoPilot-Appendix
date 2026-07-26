import Chapter01.Common
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

noncomputable section

open Classical
open scoped BigOperators ENNReal

namespace Chapter01

noncomputable def finiteStateMeasure (k : ℕ) (q : Fin k → ℝ) :
    MeasureTheory.Measure (Fin k) :=
  ∑ i : Fin k, ENNReal.ofReal (q i) • MeasureTheory.Measure.dirac i

theorem finiteStateMeasure_singleton (k : ℕ) (q : Fin k → ℝ)
    (i : Fin k) : finiteStateMeasure k q {i} = ENNReal.ofReal (q i) := by
  rw [finiteStateMeasure, MeasureTheory.Measure.finset_sum_apply]
  simp only [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply,
    Set.indicator, Set.mem_singleton_iff, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

theorem finiteStateMeasure_univ (k : ℕ) (q : Fin k → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, q i = 1) :
    finiteStateMeasure k q Set.univ = 1 := by
  rw [finiteStateMeasure, MeasureTheory.Measure.finset_sum_apply]
  simp_rw [MeasureTheory.Measure.smul_apply]
  simp only [MeasureTheory.Measure.dirac_apply, Set.indicator_of_mem,
    Set.mem_univ, smul_eq_mul, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hq i), hsum]
  norm_num

noncomputable def finiteMarkovKernel (k : ℕ)
    (P : Matrix (Fin k) (Fin k) ℝ) (n : ℕ) :
    ProbabilityTheory.Kernel
      ((i : Finset.Iic n) → Fin k) (Fin k) :=
  ProbabilityTheory.Kernel.mk
    (fun x => finiteStateMeasure k (P (x ⟨n, by simp⟩)))
    (measurable_of_finite _)

theorem finiteMarkovKernel_apply (k : ℕ)
    (P : Matrix (Fin k) (Fin k) ℝ) (n : ℕ)
    (x : (i : Finset.Iic n) → Fin k) :
    finiteMarkovKernel k P n x =
      finiteStateMeasure k (P (x ⟨n, by simp⟩)) := rfl

theorem finiteMarkovKernel_isMarkov (k : ℕ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (n : ℕ) : ProbabilityTheory.IsMarkovKernel (finiteMarkovKernel k P n) := by
  constructor
  intro x
  constructor
  rw [finiteMarkovKernel_apply]
  exact finiteStateMeasure_univ k _ (hP _) (hPsum _)

noncomputable def oneSidedMarkovMeasure (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1) :
    MeasureTheory.Measure (ℕ → Fin k) := by
  letI : ∀ n, ProbabilityTheory.IsMarkovKernel (finiteMarkovKernel k P n) :=
    fun n => finiteMarkovKernel_isMarkov k P hP hPsum n
  exact ProbabilityTheory.Kernel.trajMeasure (finiteStateMeasure k p)
    (finiteMarkovKernel k P)

theorem oneSidedMarkovMeasure_map_frestrict_zero (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1) :
    MeasureTheory.Measure.map (Preorder.frestrictLe 0)
        (oneSidedMarkovMeasure k p P hP hPsum) =
      MeasureTheory.Measure.map
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Fin k)).symm
        (finiteStateMeasure k p) := by
  letI : ∀ n, ProbabilityTheory.IsMarkovKernel (finiteMarkovKernel k P n) :=
    fun n => finiteMarkovKernel_isMarkov k P hP hPsum n
  unfold oneSidedMarkovMeasure ProbabilityTheory.Kernel.trajMeasure
  rw [MeasureTheory.Measure.map_comp _ _ (by fun_prop),
    ProbabilityTheory.Kernel.traj_map_frestrictLe,
    ProbabilityTheory.Kernel.partialTraj_self]
  simp

def markovPrefixCylinder {k : ℕ} {n : ℕ} (a : Fin (n + 1) → Fin k) :
    Set (ℕ → Fin k) := {x | ∀ i : Fin (n + 1), x i = a i}

theorem markovPrefixCylinder_measurable {k : ℕ} {n : ℕ}
    (a : Fin (n + 1) → Fin k) : MeasurableSet (markovPrefixCylinder a) := by
  rw [show markovPrefixCylinder a = ⋂ i, {x | x (i : ℕ) = a i} by
    ext x
    simp [markovPrefixCylinder]]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_eq_fun (measurable_pi_apply (i : ℕ)) measurable_const

theorem oneSidedMarkovMeasure_prefix_zero (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (a : Fin 1 → Fin k) :
    oneSidedMarkovMeasure k p P hP hPsum (markovPrefixCylinder a) =
      ENNReal.ofReal (p (a 0)) := by
  let b : (i : Finset.Iic 0) → Fin k := fun _ => a 0
  have hpre : Preorder.frestrictLe 0 ⁻¹' ({b} : Set ((i : Finset.Iic 0) → Fin k)) =
      markovPrefixCylinder a := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, markovPrefixCylinder,
      Set.mem_setOf_eq]
    constructor
    · intro h i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact congrFun h ⟨0, by simp⟩
    · intro h
      funext i
      have hi : i.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property)
      have hi' : i = ⟨0, by simp⟩ := Subtype.ext hi
      subst i
      exact h 0
  rw [← hpre, ← MeasureTheory.Measure.map_apply (by fun_prop)
    (MeasurableSet.singleton b),
    oneSidedMarkovMeasure_map_frestrict_zero]
  rw [MeasureTheory.Measure.map_apply
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Fin k)).symm.measurable
    (MeasurableSet.singleton b)]
  have hpre0 :
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Fin k)).symm ⁻¹'
          ({b} : Set ((i : Finset.Iic 0) → Fin k)) = ({a 0} : Set (Fin k)) := by
    ext i
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact congrFun h ⟨0, by simp⟩
    · intro h
      subst i
      funext j
      have hj : j.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp j.property)
      have hj' : j = ⟨0, by simp⟩ := Subtype.ext hj
      subst j
      rfl
  rw [hpre0, finiteStateMeasure_singleton]

theorem oneSidedMarkovMeasure_prefix_succ (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (n : ℕ) (a : Fin (n + 2) → Fin k) :
    oneSidedMarkovMeasure k p P hP hPsum (markovPrefixCylinder a) =
      oneSidedMarkovMeasure k p P hP hPsum
          (markovPrefixCylinder (fun i : Fin (n + 1) => a i.castSucc)) *
        ENNReal.ofReal (P (a ⟨n, by omega⟩) (a (Fin.last (n + 1)))) := by
  letI : ∀ m, ProbabilityTheory.IsMarkovKernel (finiteMarkovKernel k P m) :=
    fun m => finiteMarkovKernel_isMarkov k P hP hPsum m
  letI : MeasureTheory.IsProbabilityMeasure (finiteStateMeasure k p) :=
    ⟨finiteStateMeasure_univ k p hp hpsum⟩
  let μ := oneSidedMarkovMeasure k p P hP hPsum
  let b : (i : Finset.Iic n) → Fin k := fun i => a ⟨i.1, by
    have hi := Finset.mem_Iic.mp i.property
    omega⟩
  let c : Fin k := a (Fin.last (n + 1))
  have hpre0 : Preorder.frestrictLe n ⁻¹' ({b} : Set ((i : Finset.Iic n) → Fin k)) =
      markovPrefixCylinder (fun i : Fin (n + 1) => a i.castSucc) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, markovPrefixCylinder,
      Set.mem_setOf_eq]
    constructor
    · intro h i
      exact congrFun h ⟨i.1, Finset.mem_Iic.mpr (by omega)⟩
    · intro h
      funext i
      exact h ⟨i.1, by
        have hi := Finset.mem_Iic.mp i.property
        omega⟩
  have hpre1 :
      (fun x : ℕ → Fin k => (Preorder.frestrictLe n x, x (n + 1))) ⁻¹'
          (({b} : Set ((i : Finset.Iic n) → Fin k)) ×ˢ ({c} : Set (Fin k))) =
        markovPrefixCylinder a := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
      markovPrefixCylinder, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hb, hc⟩ i
      by_cases hi : i.1 ≤ n
      · exact congrFun hb ⟨i.1, Finset.mem_Iic.mpr hi⟩
      · have hilast : i = Fin.last (n + 1) := by
          apply Fin.eq_last_of_not_lt
          omega
        subst i
        exact hc
    · intro h
      constructor
      · funext i
        exact h ⟨i.1, by
          have hi := Finset.mem_Iic.mp i.property
          omega⟩
      · exact h (Fin.last (n + 1))
  have hjoint := ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => Fin k) (κ := finiteMarkovKernel k P)
    (μ₀ := finiteStateMeasure k p) (a := n)
  have happ := congrArg
    (fun ν : MeasureTheory.Measure (((i : Finset.Iic n) → Fin k) × Fin k) =>
      ν (({b} : Set ((i : Finset.Iic n) → Fin k)) ×ˢ ({c} : Set (Fin k)))) hjoint
  dsimp only at happ
  rw [MeasureTheory.Measure.compProd_apply_prod (MeasurableSet.singleton b)
      (MeasurableSet.singleton c)] at happ
  rw [MeasureTheory.Measure.map_apply (by fun_prop)
    ((MeasurableSet.singleton b).prod (MeasurableSet.singleton c)), hpre1] at happ
  change
    (∫⁻ x in ({b} : Set ((i : Finset.Iic n) → Fin k)),
        finiteMarkovKernel k P n x ({c} : Set (Fin k))
      ∂MeasureTheory.Measure.map (Preorder.frestrictLe n) μ) =
      μ (markovPrefixCylinder a) at happ
  have hint :
      (∫⁻ x in ({b} : Set ((i : Finset.Iic n) → Fin k)),
          finiteMarkovKernel k P n x ({c} : Set (Fin k))
        ∂MeasureTheory.Measure.map (Preorder.frestrictLe n) μ) =
        ENNReal.ofReal (P (a ⟨n, by omega⟩) c) *
          MeasureTheory.Measure.map (Preorder.frestrictLe n) μ {b} := by
    have heq : ∀ x ∈ ({b} : Set ((i : Finset.Iic n) → Fin k)),
        finiteMarkovKernel k P n x ({c} : Set (Fin k)) =
          ENNReal.ofReal (P (a ⟨n, by omega⟩) c) := by
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      rw [finiteMarkovKernel_apply, finiteStateMeasure_singleton]
    calc
      (∫⁻ x in ({b} : Set ((i : Finset.Iic n) → Fin k)),
          finiteMarkovKernel k P n x ({c} : Set (Fin k))
        ∂MeasureTheory.Measure.map (Preorder.frestrictLe n) μ) =
          ∫⁻ _x in ({b} : Set ((i : Finset.Iic n) → Fin k)),
            ENNReal.ofReal (P (a ⟨n, by omega⟩) c)
          ∂MeasureTheory.Measure.map (Preorder.frestrictLe n) μ := by
            apply MeasureTheory.setLIntegral_congr_fun (MeasurableSet.singleton b)
            exact heq
      _ = _ := MeasureTheory.setLIntegral_const _ _
  rw [hint] at happ
  rw [MeasureTheory.Measure.map_apply (by fun_prop) (MeasurableSet.singleton b), hpre0] at happ
  change μ (markovPrefixCylinder a) =
    μ (markovPrefixCylinder (fun i : Fin (n + 1) => a i.castSucc)) *
      ENNReal.ofReal (P (a ⟨n, by omega⟩) (a (Fin.last (n + 1))))
  rw [← happ]
  change ENNReal.ofReal (P (a ⟨n, by omega⟩) c) * _ =
    _ * ENNReal.ofReal (P (a ⟨n, by omega⟩) (a (Fin.last (n + 1))))
  rw [show c = a (Fin.last (n + 1)) by rfl, mul_comm]

theorem oneSidedMarkovMeasure_prefix (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (n : ℕ) (a : Fin (n + 1) → Fin k) :
    oneSidedMarkovMeasure k p P hP hPsum (markovPrefixCylinder a) =
      ENNReal.ofReal
        (p (a 0) * ∏ i : Fin n, P (a i.castSucc) (a i.succ)) := by
  induction n with
  | zero =>
      simpa using oneSidedMarkovMeasure_prefix_zero k p P hP hPsum a
  | succ n ih =>
      rw [oneSidedMarkovMeasure_prefix_succ k p P hp hpsum hP hPsum n a,
        ih (fun i : Fin (n + 1) => a i.castSucc)]
      have hprod : 0 ≤ ∏ i : Fin n,
          P (a i.castSucc.castSucc) (a i.succ.castSucc) :=
        Finset.prod_nonneg fun i _ => hP _ _
      rw [← ENNReal.ofReal_mul (mul_nonneg (hp _) hprod)]
      apply congrArg ENNReal.ofReal
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.castSucc_zero, Fin.succ_castSucc, Fin.succ_last]
      have hidx0 : (⟨n, by omega⟩ : Fin (n + 2)) = (Fin.last n).castSucc := by
        apply Fin.ext
        simp
      have hidx1 : Fin.last (n + 1) = Fin.last n.succ := by
        apply Fin.ext
        simp
      rw [hidx0, hidx1]
      ring

theorem oneSidedMarkovMeasure_isProbability (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1) :
    MeasureTheory.IsProbabilityMeasure (oneSidedMarkovMeasure k p P hP hPsum) := by
  letI : ∀ n, ProbabilityTheory.IsMarkovKernel (finiteMarkovKernel k P n) :=
    fun n => finiteMarkovKernel_isMarkov k P hP hPsum n
  letI : MeasureTheory.IsProbabilityMeasure (finiteStateMeasure k p) :=
    ⟨finiteStateMeasure_univ k p hp hpsum⟩
  unfold oneSidedMarkovMeasure
  infer_instance

theorem oneSidedMarkovMeasure_shift_prefix (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (n : ℕ) (a : Fin (n + 1) → Fin k) :
    oneSidedMarkovMeasure k p P hP hPsum
        (oneSidedShift ⁻¹' markovPrefixCylinder a) =
      oneSidedMarkovMeasure k p P hP hPsum (markovPrefixCylinder a) := by
  let μ := oneSidedMarkovMeasure k p P hP hPsum
  let C : Fin k → Set (ℕ → Fin k) := fun j =>
    markovPrefixCylinder (Fin.cases j a)
  have hpre : oneSidedShift ⁻¹' markovPrefixCylinder a = ⋃ j, C j := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, markovPrefixCylinder,
      Set.mem_setOf_eq, oneSidedShift]
    constructor
    · intro hx
      refine ⟨x 0, ?_⟩
      intro i
      refine Fin.cases ?_ (fun q => ?_) i
      · rfl
      · exact hx q
    · rintro ⟨j, hj⟩ i
      exact hj i.succ
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro i j hij
    change Disjoint (C i) (C j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    apply hij
    have hi : x 0 = i := by simpa [C] using hxi (0 : Fin (n + 2))
    have hj : x 0 = j := by simpa [C] using hxj (0 : Fin (n + 2))
    exact hi.symm.trans hj
  rw [hpre, MeasureTheory.measure_iUnion hdisj
    (fun j => markovPrefixCylinder_measurable (Fin.cases j a)), tsum_fintype]
  simp_rw [show C = fun j => markovPrefixCylinder (Fin.cases j a) by rfl,
    oneSidedMarkovMeasure_prefix k p P hp hpsum hP hPsum (n + 1)]
  rw [oneSidedMarkovMeasure_prefix k p P hp hpsum hP hPsum n]
  simp_rw [Fin.prod_univ_succ]
  have hhead : ∀ j : Fin k, Fin.cases j a (Fin.castSucc 0) = j := by
    intro j
    rw [Fin.castSucc_zero]
    rfl
  have htail : ∀ (j : Fin k) (i : Fin n),
      Fin.cases j a i.succ.castSucc = a i.castSucc := by
    intro j i
    rw [← Fin.succ_castSucc]
    rfl
  simp_rw [hhead, htail]
  simp only [Fin.cases_zero, Fin.cases_succ]
  simp_rw [← mul_assoc]
  have hterm : ∀ j : Fin k,
      0 ≤ p j * P j (a 0) *
        ∏ i : Fin n, P (a i.castSucc) (a i.succ) := by
    intro j
    exact mul_nonneg (mul_nonneg (hp _) (hP _ _))
      (Finset.prod_nonneg fun i _ => hP _ _)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hterm j)]
  apply congrArg ENNReal.ofReal
  rw [← Finset.sum_mul, hstationary]

def finitePrefix {k : ℕ} (n : ℕ) (x : ℕ → Fin k) : Fin (n + 1) → Fin k :=
  fun i => x i

theorem finitePrefix_measurable {k : ℕ} (n : ℕ) :
    Measurable (@finitePrefix k n) := by
  exact measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)

def markovPrefixSetFamily (k : ℕ) : Set (Set (ℕ → Fin k)) :=
  {C | ∃ n : ℕ, ∃ A : Set (Fin (n + 1) → Fin k), C = finitePrefix n ⁻¹' A}

theorem markovPrefixSetFamily_generate (k : ℕ) :
    (inferInstance : MeasurableSpace (ℕ → Fin k)) =
      MeasurableSpace.generateFrom (markovPrefixSetFamily k) := by
  apply le_antisymm
  · rw [MeasurableSpace.pi_eq_generateFrom_projections]
    apply MeasurableSpace.generateFrom_mono
    rintro _ ⟨i, B, hB, rfl⟩
    let A : Set (Fin (i + 1) → Fin k) :=
      {a | a ⟨i, by omega⟩ ∈ B}
    refine ⟨i, A, ?_⟩
    ext x
    simp [finitePrefix, A]
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨n, A, rfl⟩
    exact (finitePrefix_measurable n) (Set.toFinite A).measurableSet

theorem markovPrefixSetFamily_piSystem (k : ℕ) :
    IsPiSystem (markovPrefixSetFamily k) := by
  rintro C ⟨n, A, rfl⟩ D ⟨m, B, rfl⟩ hne
  let N := max n m
  let rn : (Fin (N + 1) → Fin k) → (Fin (n + 1) → Fin k) :=
    fun z i => z ⟨i, by
      have hi := i.isLt
      have hn : n ≤ N := le_max_left _ _
      omega⟩
  let rm : (Fin (N + 1) → Fin k) → (Fin (m + 1) → Fin k) :=
    fun z i => z ⟨i, by
      have hi := i.isLt
      have hm : m ≤ N := le_max_right _ _
      omega⟩
  let E : Set (Fin (N + 1) → Fin k) := {z | rn z ∈ A ∧ rm z ∈ B}
  refine ⟨N, E, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, E, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxA, hxB⟩
    constructor
    · simpa only [rn, finitePrefix] using hxA
    · simpa only [rm, finitePrefix] using hxB
  · rintro ⟨hxA, hxB⟩
    constructor
    · simpa only [rn, finitePrefix] using hxA
    · simpa only [rm, finitePrefix] using hxB

theorem oneSidedMarkovMeasure_shiftPreserving (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    MeasureTheory.MeasurePreserving (@oneSidedShift k)
      (oneSidedMarkovMeasure k p P hP hPsum)
      (oneSidedMarkovMeasure k p P hP hPsum) := by
  let μ := oneSidedMarkovMeasure k p P hP hPsum
  have hshift : Measurable (@oneSidedShift k) := by
    exact measurable_pi_lambda _ fun n => measurable_pi_apply (n + 1)
  refine ⟨hshift, ?_⟩
  have hfin : ∀ n : ℕ,
      MeasureTheory.Measure.map (finitePrefix n)
          (MeasureTheory.Measure.map oneSidedShift μ) =
        MeasureTheory.Measure.map (finitePrefix n) μ := by
    intro n
    apply MeasureTheory.Measure.ext_of_singleton
    intro a
    have hC : finitePrefix n ⁻¹' ({a} : Set (Fin (n + 1) → Fin k)) =
        markovPrefixCylinder a := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, markovPrefixCylinder,
        Set.mem_setOf_eq]
      constructor
      · intro h i
        exact congrFun h i
      · intro h
        funext i
        exact h i
    rw [MeasureTheory.Measure.map_apply (finitePrefix_measurable n)
      (MeasurableSet.singleton a),
      MeasureTheory.Measure.map_apply hshift
        ((finitePrefix_measurable n) (MeasurableSet.singleton a)), hC,
      MeasureTheory.Measure.map_apply (finitePrefix_measurable n)
        (MeasurableSet.singleton a), hC]
    exact oneSidedMarkovMeasure_shift_prefix k p P hp hpsum hP hPsum
      hstationary n a
  apply MeasureTheory.Measure.ext_of_generateFrom_of_cover_subset
    (markovPrefixSetFamily_generate k) (markovPrefixSetFamily_piSystem k)
    (T := {Set.univ})
  · intro C hC
    subst C
    exact ⟨0, Set.univ, by simp⟩
  · exact Set.countable_singleton _
  · simp
  · intro C hC
    have hCu : C = Set.univ := Set.mem_singleton_iff.mp hC
    subst C
    rw [MeasureTheory.Measure.map_apply hshift MeasurableSet.univ]
    have hprob := oneSidedMarkovMeasure_isProbability k p P hp hpsum hP hPsum
    simp only [Set.preimage_univ]
    rw [hprob.measure_univ]
    simp
  · rintro C ⟨n, A, rfl⟩
    rw [← MeasureTheory.Measure.map_apply (finitePrefix_measurable n)
        (Set.toFinite A).measurableSet,
      ← MeasureTheory.Measure.map_apply (finitePrefix_measurable n)
        (Set.toFinite A).measurableSet, hfin n]

noncomputable def oneSidedMarkovSystem (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1) :
    MeasurePreservingSystemData where
  X := ℕ → Fin k
  measurableSpace := inferInstance
  μ := oneSidedMarkovMeasure k p P hP hPsum
  T := oneSidedShift

theorem oneSidedMarkovSystem_mps (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    IsMeasurePreservingSystem (oneSidedMarkovSystem k p P hP hPsum) := by
  constructor
  · exact oneSidedMarkovMeasure_isProbability k p P hp hpsum hP hPsum
  · exact oneSidedMarkovMeasure_shiftPreserving k p P hp hpsum hP hPsum hstationary

def reverseTransition {k : ℕ} (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun j i => if p j = 0 then p i else p i * P i j / p j

theorem reverseTransition_nonneg {k : ℕ} (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ) (hp : ∀ i, 0 ≤ p i)
    (hP : ∀ i j, 0 ≤ P i j) :
    ∀ i j, 0 ≤ reverseTransition p P i j := by
  intro i j
  simp only [reverseTransition]
  split_ifs with hi
  · exact hp j
  · exact div_nonneg (mul_nonneg (hp _) (hP _ _)) (hp _)

theorem stationary_term_eq_zero_of_weight_zero {k : ℕ} (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ) (hp : ∀ i, 0 ≤ p i)
    (hP : ∀ i j, 0 ≤ P i j)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    {i j : Fin k} (hj : p j = 0) : p i * P i j = 0 := by
  have hnonneg : ∀ l : Fin k, 0 ≤ p l * P l j :=
    fun l => mul_nonneg (hp l) (hP l j)
  have hle : p i * P i j ≤ ∑ l : Fin k, p l * P l j := by
    exact Finset.single_le_sum (fun l _ => hnonneg l) (Finset.mem_univ i)
  have hsum : ∑ l : Fin k, p l * P l j = 0 := by
    rw [hstationary, hj]
  exact le_antisymm (by simpa [hsum] using hle) (hnonneg i)

theorem reverseTransition_balance {k : ℕ} (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ) (hp : ∀ i, 0 ≤ p i)
    (hP : ∀ i j, 0 ≤ P i j)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    ∀ i j, p i * reverseTransition p P i j = p j * P j i := by
  intro i j
  simp only [reverseTransition]
  by_cases hi : p i = 0
  · rw [if_pos hi, hi, zero_mul]
    exact (stationary_term_eq_zero_of_weight_zero p P hp hP hstationary
      (i := j) (j := i) hi).symm
  · rw [if_neg hi]
    field_simp

theorem reverseTransition_rowsum {k : ℕ} (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (hP : ∀ i j, 0 ≤ P i j)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    ∀ i, ∑ j, reverseTransition p P i j = 1 := by
  intro i
  simp only [reverseTransition]
  by_cases hi : p i = 0
  · simp_rw [if_pos hi]
    exact hpsum
  · simp_rw [if_neg hi]
    rw [← Finset.sum_div, hstationary, div_self hi]

theorem reverseTransition_stationary {k : ℕ} (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ) (hp : ∀ i, 0 ≤ p i)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    ∀ j, ∑ i, p i * reverseTransition p P i j = p j := by
  intro j
  simp_rw [reverseTransition_balance p P hp hP hstationary]
  rw [← Finset.mul_sum, hPsum, mul_one]

def conditionalInitial {k : ℕ} (i : Fin k) : Fin k → ℝ :=
  fun j => if j = i then 1 else 0

theorem conditionalInitial_nonneg {k : ℕ} (i : Fin k) :
    ∀ j, 0 ≤ conditionalInitial i j := by
  intro j
  simp only [conditionalInitial]
  split_ifs <;> norm_num

theorem conditionalInitial_sum {k : ℕ} (i : Fin k) :
    ∑ j, conditionalInitial i j = 1 := by
  simp [conditionalInitial]

def twoSidedGlue {k : ℕ} (paths : (ℕ → Fin k) × (ℕ → Fin k)) :
    ℤ → Fin k := fun z =>
  if 0 ≤ z then paths.2 z.toNat else paths.1 z.natAbs

theorem twoSidedGlue_measurable {k : ℕ} : Measurable (@twoSidedGlue k) := by
  apply measurable_pi_lambda
  intro z
  by_cases hz : 0 ≤ z
  · simp only [twoSidedGlue, hz, ↓reduceIte]
    exact (measurable_pi_apply z.toNat).comp measurable_snd
  · simp only [twoSidedGlue, hz, ↓reduceIte]
    exact (measurable_pi_apply z.natAbs).comp measurable_fst

noncomputable def twoSidedMarkovComponent (k : ℕ) (i : Fin k)
    (Q P : Matrix (Fin k) (Fin k) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hQsum : ∀ i, ∑ j, Q i j = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1) :
    MeasureTheory.Measure (ℤ → Fin k) :=
  MeasureTheory.Measure.map twoSidedGlue
    (MeasureTheory.Measure.prod
      (oneSidedMarkovMeasure k (conditionalInitial i) Q hQ hQsum)
      (oneSidedMarkovMeasure k (conditionalInitial i) P hP hPsum))

theorem twoSidedMarkovComponent_isProbability (k : ℕ) (i : Fin k)
    (Q P : Matrix (Fin k) (Fin k) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hQsum : ∀ i, ∑ j, Q i j = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1) :
    MeasureTheory.IsProbabilityMeasure
      (twoSidedMarkovComponent k i Q P hQ hQsum hP hPsum) := by
  let μb := oneSidedMarkovMeasure k (conditionalInitial i) Q hQ hQsum
  let μf := oneSidedMarkovMeasure k (conditionalInitial i) P hP hPsum
  have hb := oneSidedMarkovMeasure_isProbability k (conditionalInitial i) Q
    (conditionalInitial_nonneg i) (conditionalInitial_sum i) hQ hQsum
  have hf := oneSidedMarkovMeasure_isProbability k (conditionalInitial i) P
    (conditionalInitial_nonneg i) (conditionalInitial_sum i) hP hPsum
  letI : MeasureTheory.IsProbabilityMeasure μb := hb
  letI : MeasureTheory.IsProbabilityMeasure μf := hf
  constructor
  rw [twoSidedMarkovComponent,
    MeasureTheory.Measure.map_apply twoSidedGlue_measurable MeasurableSet.univ]
  simp only [Set.preimage_univ]
  rw [MeasureTheory.Measure.prod_apply MeasurableSet.univ]
  simp only [Set.preimage_univ, hf.measure_univ]
  rw [MeasureTheory.lintegral_const, hb.measure_univ]
  norm_num

noncomputable def twoSidedMarkovMeasure (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    MeasureTheory.Measure (ℤ → Fin k) :=
  let Q := reverseTransition p P
  let hQ := reverseTransition_nonneg p P hp hP
  let hQsum := reverseTransition_rowsum p P hp hpsum hP hstationary
  ∑ i : Fin k, ENNReal.ofReal (p i) •
    twoSidedMarkovComponent k i Q P hQ hQsum hP hPsum

theorem twoSidedMarkovMeasure_isProbability (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    MeasureTheory.IsProbabilityMeasure
      (twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary) := by
  let Q := reverseTransition p P
  let hQ := reverseTransition_nonneg p P hp hP
  let hQsum := reverseTransition_rowsum p P hp hpsum hP hstationary
  constructor
  rw [twoSidedMarkovMeasure, MeasureTheory.Measure.finset_sum_apply]
  simp_rw [MeasureTheory.Measure.smul_apply]
  change (∑ i : Fin k, ENNReal.ofReal (p i) *
    (twoSidedMarkovComponent k i Q P hQ hQsum hP hPsum) Set.univ) = 1
  have hcomp : ∀ i : Fin k,
      (twoSidedMarkovComponent k i Q P hQ hQsum hP hPsum) Set.univ = 1 := by
    intro i
    exact (twoSidedMarkovComponent_isProbability k i Q P hQ hQsum hP hPsum).measure_univ
  simp_rw [hcomp, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), hpsum]
  norm_num

def tailObservation {k : ℕ} (m : ℕ) (x : ℕ → Fin k) : Fin m → Fin k :=
  fun i => x ((i : ℕ) + 1)

def tailCylinder {k : ℕ} {m : ℕ} (word : Fin m → Fin k) :
    Set (ℕ → Fin k) := tailObservation m ⁻¹' {word}

theorem tailCylinder_measurable {k : ℕ} {m : ℕ} (word : Fin m → Fin k) :
    MeasurableSet (tailCylinder word) := by
  apply MeasurableSet.preimage (MeasurableSet.singleton word)
  exact measurable_pi_lambda _ fun i => measurable_pi_apply ((i : ℕ) + 1)

def markovPathWeight {k m : ℕ} (R : Matrix (Fin k) (Fin k) ℝ)
    (start : Fin k) (word : Fin m → Fin k) : ℝ :=
  let a : Fin (m + 1) → Fin k := Fin.cases start word
  ∏ r : Fin m, R (a r.castSucc) (word r)

theorem markovPathWeight_nonneg {k m : ℕ}
    (R : Matrix (Fin k) (Fin k) ℝ) (hR : ∀ i j, 0 ≤ R i j)
    (start : Fin k) (word : Fin m → Fin k) :
    0 ≤ markovPathWeight R start word := by
  exact Finset.prod_nonneg fun i _ => hR _ _

theorem markovPathWeight_cons {k m : ℕ}
    (R : Matrix (Fin k) (Fin k) ℝ) (start next : Fin k)
    (word : Fin m → Fin k) :
    markovPathWeight R start (Fin.cases next word) =
      R start next * markovPathWeight R next word := by
  rw [markovPathWeight, Fin.prod_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cases_zero, Fin.cases_succ,
    markovPathWeight]
  congr 1

theorem markovPathWeight_zero {k : ℕ} (R : Matrix (Fin k) (Fin k) ℝ)
    (start : Fin k) (word : Fin 0 → Fin k) :
    markovPathWeight R start word = 1 := by
  simp [markovPathWeight]

theorem conditionalMarkovMeasure_tail (k : ℕ) (i : Fin k)
    (R : Matrix (Fin k) (Fin k) ℝ)
    (hR : ∀ i j, 0 ≤ R i j) (hRsum : ∀ i, ∑ j, R i j = 1)
    (m : ℕ) (word : Fin m → Fin k) :
    oneSidedMarkovMeasure k (conditionalInitial i) R hR hRsum
        (tailCylinder word) =
      ENNReal.ofReal (markovPathWeight R i word) := by
  let μ := oneSidedMarkovMeasure k (conditionalInitial i) R hR hRsum
  let C : Fin k → Set (ℕ → Fin k) := fun j =>
    markovPrefixCylinder (Fin.cases j word)
  have htail : tailCylinder word = ⋃ j, C j := by
    ext x
    simp only [tailCylinder, tailObservation, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_iUnion, markovPrefixCylinder,
      Set.mem_setOf_eq]
    constructor
    · intro hx
      refine ⟨x 0, ?_⟩
      intro r
      refine Fin.cases ?_ (fun q => ?_) r
      · rfl
      · exact congrFun hx q
    · rintro ⟨j, hj⟩
      funext q
      exact hj q.succ
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro a b hab
    change Disjoint (C a) (C b)
    rw [Set.disjoint_left]
    intro x hxa hxb
    apply hab
    have ha : x 0 = a := by simpa [C] using hxa (0 : Fin (m + 1))
    have hb : x 0 = b := by simpa [C] using hxb (0 : Fin (m + 1))
    exact ha.symm.trans hb
  rw [htail, MeasureTheory.measure_iUnion hdisj
      (fun j => markovPrefixCylinder_measurable (Fin.cases j word)), tsum_fintype]
  simp_rw [show C = fun j => markovPrefixCylinder (Fin.cases j word) by rfl,
    oneSidedMarkovMeasure_prefix k (conditionalInitial i) R
      (conditionalInitial_nonneg i) (conditionalInitial_sum i) hR hRsum m]
  rw [Finset.sum_eq_single i]
  · simp [conditionalInitial, markovPathWeight]
  · intro j hj hji
    simp [conditionalInitial, hji]
  · simp

def centeredObservation {k : ℕ} (m n : ℕ) (x : ℤ → Fin k) :
    (Fin m → Fin k) × Fin k × (Fin n → Fin k) :=
  (fun i => x (-((i : ℤ) + 1)), x 0, fun i => x ((i : ℤ) + 1))

def centeredCylinder {k m n : ℕ} (past : Fin m → Fin k) (center : Fin k)
    (future : Fin n → Fin k) : Set (ℤ → Fin k) :=
  centeredObservation m n ⁻¹' {(past, center, future)}

theorem centeredObservation_measurable {k : ℕ} (m n : ℕ) :
    Measurable (@centeredObservation k m n) := by
  have hpast : Measurable
      (fun x : ℤ → Fin k => fun i : Fin m => x (-((i : ℤ) + 1))) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (-((i : ℤ) + 1))
  have hcenter : Measurable (fun x : ℤ → Fin k => x 0) := measurable_pi_apply 0
  have hfuture : Measurable
      (fun x : ℤ → Fin k => fun i : Fin n => x ((i : ℤ) + 1)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply ((i : ℤ) + 1)
  change Measurable (fun x : ℤ → Fin k =>
    ((fun i : Fin m => x (-((i : ℤ) + 1))),
      (x 0, fun i : Fin n => x ((i : ℤ) + 1))))
  exact hpast.prod (hcenter.prod hfuture)

theorem centeredCylinder_measurable {k m n : ℕ} (past : Fin m → Fin k)
    (center : Fin k) (future : Fin n → Fin k) :
    MeasurableSet (centeredCylinder past center future) :=
  (centeredObservation_measurable m n) (MeasurableSet.singleton _)

theorem twoSidedGlue_preimage_centeredCylinder {k m n : ℕ}
    (past : Fin m → Fin k) (center : Fin k) (future : Fin n → Fin k) :
    twoSidedGlue ⁻¹' centeredCylinder past center future =
      tailCylinder past ×ˢ markovPrefixCylinder (Fin.cases center future) := by
  ext paths
  simp only [Set.mem_preimage, centeredCylinder, Set.mem_singleton_iff,
    Set.mem_prod, tailCylinder, markovPrefixCylinder, Set.mem_setOf_eq]
  have hneg : ∀ i : Fin m,
      twoSidedGlue paths (-((i : ℤ) + 1)) = paths.1 ((i : ℕ) + 1) := by
    intro i
    rw [twoSidedGlue, if_neg (by omega)]
    congr 1
  have hzero : twoSidedGlue paths 0 = paths.2 0 := by
    simp [twoSidedGlue]
  have hpos : ∀ i : Fin n,
      twoSidedGlue paths ((i : ℤ) + 1) = paths.2 ((i : ℕ) + 1) := by
    intro i
    rw [twoSidedGlue, if_pos (by omega)]
    congr 1
  constructor
  · intro h
    have hpast := congrArg Prod.fst h
    have hrest := congrArg Prod.snd h
    have hcenter := congrArg Prod.fst hrest
    have hfuture := congrArg Prod.snd hrest
    constructor
    · funext i
      simpa only [centeredObservation, tailObservation, hneg] using congrFun hpast i
    · intro r
      refine Fin.cases ?_ (fun i => ?_) r
      · simpa only [hzero] using hcenter
      · simpa only [hpos] using congrFun hfuture i
  · rintro ⟨hpast, hforward⟩
    apply Prod.ext
    · funext i
      change twoSidedGlue paths (-((i : ℤ) + 1)) = past i
      rw [hneg]
      exact congrFun hpast i
    · apply Prod.ext
      · change twoSidedGlue paths 0 = center
        rw [hzero]
        exact hforward 0
      · funext i
        change twoSidedGlue paths ((i : ℤ) + 1) = future i
        rw [hpos]
        exact hforward i.succ

theorem twoSidedMarkovComponent_centeredCylinder (k : ℕ) (i : Fin k)
    (Q P : Matrix (Fin k) (Fin k) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hQsum : ∀ i, ∑ j, Q i j = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    {m n : ℕ} (past : Fin m → Fin k) (center : Fin k)
    (future : Fin n → Fin k) :
    twoSidedMarkovComponent k i Q P hQ hQsum hP hPsum
        (centeredCylinder past center future) =
      ENNReal.ofReal (markovPathWeight Q i past) *
        ENNReal.ofReal
          (conditionalInitial i center * markovPathWeight P center future) := by
  let μb := oneSidedMarkovMeasure k (conditionalInitial i) Q hQ hQsum
  let μf := oneSidedMarkovMeasure k (conditionalInitial i) P hP hPsum
  letI : MeasureTheory.IsProbabilityMeasure μb :=
    oneSidedMarkovMeasure_isProbability k (conditionalInitial i) Q
      (conditionalInitial_nonneg i) (conditionalInitial_sum i) hQ hQsum
  letI : MeasureTheory.IsProbabilityMeasure μf :=
    oneSidedMarkovMeasure_isProbability k (conditionalInitial i) P
      (conditionalInitial_nonneg i) (conditionalInitial_sum i) hP hPsum
  rw [twoSidedMarkovComponent,
    MeasureTheory.Measure.map_apply twoSidedGlue_measurable
      (centeredCylinder_measurable past center future),
    twoSidedGlue_preimage_centeredCylinder,
    MeasureTheory.Measure.prod_prod,
    conditionalMarkovMeasure_tail k i Q hQ hQsum m past,
    oneSidedMarkovMeasure_prefix k (conditionalInitial i) P
      (conditionalInitial_nonneg i) (conditionalInitial_sum i) hP hPsum n]
  simp only [Fin.cases_zero]
  congr 2

theorem twoSidedMarkovMeasure_centeredCylinder (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    {m n : ℕ} (past : Fin m → Fin k) (center : Fin k)
    (future : Fin n → Fin k) :
    twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary
        (centeredCylinder past center future) =
      ENNReal.ofReal (p center) *
        ENNReal.ofReal (markovPathWeight (reverseTransition p P) center past) *
        ENNReal.ofReal (markovPathWeight P center future) := by
  let Q := reverseTransition p P
  let hQ := reverseTransition_nonneg p P hp hP
  let hQsum := reverseTransition_rowsum p P hp hpsum hP hstationary
  rw [twoSidedMarkovMeasure, MeasureTheory.Measure.finset_sum_apply]
  simp_rw [MeasureTheory.Measure.smul_apply]
  change (∑ i : Fin k, ENNReal.ofReal (p i) *
    twoSidedMarkovComponent k i Q P hQ hQsum hP hPsum
      (centeredCylinder past center future)) = _
  simp_rw [twoSidedMarkovComponent_centeredCylinder k _ Q P hQ hQsum hP hPsum
    past center future]
  rw [Finset.sum_eq_single center]
  · simp [conditionalInitial, Q, mul_assoc]
  · intro i hi hic
    have hci : center ≠ i := Ne.symm hic
    simp [conditionalInitial, hci]
  · simp

theorem twoSidedMarkovMeasure_centeredCylinder_real (k : ℕ)
    (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    {m n : ℕ} (past : Fin m → Fin k) (center : Fin k)
    (future : Fin n → Fin k) :
    twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary
        (centeredCylinder past center future) =
      ENNReal.ofReal
        (p center * markovPathWeight (reverseTransition p P) center past *
          markovPathWeight P center future) := by
  rw [twoSidedMarkovMeasure_centeredCylinder k p P hp hpsum hP hPsum
    hstationary past center future]
  rw [← ENNReal.ofReal_mul (hp center),
    ← ENNReal.ofReal_mul (mul_nonneg (hp center)
      (markovPathWeight_nonneg _ (reverseTransition_nonneg p P hp hP) _ _))]

def bilateralShift {k : ℕ} (x : ℤ → Fin k) : ℤ → Fin k :=
  fun z => x (z + 1)

theorem bilateralShift_measurable {k : ℕ} : Measurable (@bilateralShift k) := by
  exact measurable_pi_lambda _ fun z => measurable_pi_apply (z + 1)

theorem bilateralShift_preimage_centeredCylinder_cons {k m n : ℕ}
    (left : Fin k) (past : Fin m → Fin k) (center : Fin k)
    (future : Fin n → Fin k) :
    bilateralShift ⁻¹' centeredCylinder (Fin.cases left past) center future =
      centeredCylinder past left (Fin.cases center future) := by
  ext x
  simp only [Set.mem_preimage, centeredCylinder, Set.mem_singleton_iff]
  constructor
  · intro h
    have hpast := congrArg Prod.fst h
    have hrest := congrArg Prod.snd h
    have hcenter := congrArg Prod.fst hrest
    have hfuture := congrArg Prod.snd hrest
    apply Prod.ext
    · funext i
      have hi := congrFun hpast i.succ
      change x (-((i : ℤ) + 1)) = past i
      simpa [centeredObservation, bilateralShift] using hi
    · apply Prod.ext
      · have hi := congrFun hpast 0
        change x 0 = left
        simpa [centeredObservation, bilateralShift] using hi
      · funext i
        refine Fin.cases ?_ (fun q => ?_) i
        · change x 1 = center
          simpa [centeredObservation, bilateralShift] using hcenter
        · have hi := congrFun hfuture q
          change x ((q : ℤ) + 2) = future q
          simpa [centeredObservation, bilateralShift] using hi
  · intro h
    have hpast := congrArg Prod.fst h
    have hrest := congrArg Prod.snd h
    have hcenter := congrArg Prod.fst hrest
    have hfuture := congrArg Prod.snd hrest
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun q => ?_) i
      · change x 0 = left at hcenter
        change bilateralShift x (-(((0 : Fin (m + 1)) : ℤ) + 1)) = left
        simpa [bilateralShift] using hcenter
      · have hi := congrFun hpast q
        change x (-((q : ℤ) + 1)) = past q at hi
        change bilateralShift x (-(((q.succ : Fin (m + 1)) : ℤ) + 1)) = past q
        simpa [bilateralShift] using hi
    · apply Prod.ext
      · have hi := congrFun hfuture 0
        change x 1 = center at hi
        change bilateralShift x 0 = center
        simpa [bilateralShift] using hi
      · funext i
        have hi := congrFun hfuture i.succ
        change x ((i : ℤ) + 2) = future i at hi
        change bilateralShift x ((i : ℤ) + 1) = future i
        simpa [bilateralShift] using hi

theorem twoSidedMarkovMeasure_shift_centeredCylinder_cons (k : ℕ)
    (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    {m n : ℕ} (left : Fin k) (past : Fin m → Fin k) (center : Fin k)
    (future : Fin n → Fin k) :
    twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary
        (bilateralShift ⁻¹'
          centeredCylinder (Fin.cases left past) center future) =
      twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary
        (centeredCylinder (Fin.cases left past) center future) := by
  rw [bilateralShift_preimage_centeredCylinder_cons]
  rw [twoSidedMarkovMeasure_centeredCylinder_real k p P hp hpsum hP hPsum
      hstationary past left (Fin.cases center future),
    twoSidedMarkovMeasure_centeredCylinder_real k p P hp hpsum hP hPsum
      hstationary (Fin.cases left past) center future,
    markovPathWeight_cons, markovPathWeight_cons]
  apply congrArg ENNReal.ofReal
  have hbalance := reverseTransition_balance p P hp hP hstationary center left
  calc
    p left * markovPathWeight (reverseTransition p P) left past *
        (P left center * markovPathWeight P center future) =
      (p left * P left center) *
        markovPathWeight (reverseTransition p P) left past *
        markovPathWeight P center future := by ring
    _ = (p center * reverseTransition p P center left) *
        markovPathWeight (reverseTransition p P) left past *
        markovPathWeight P center future := by rw [hbalance]
    _ = p center *
        (reverseTransition p P center left *
          markovPathWeight (reverseTransition p P) left past) *
        markovPathWeight P center future := by ring

theorem bilateralShift_preimage_centeredCylinder_zero {k n : ℕ}
    (past : Fin 0 → Fin k) (center : Fin k) (future : Fin n → Fin k) :
    bilateralShift ⁻¹' centeredCylinder past center future =
      ⋃ left : Fin k, centeredCylinder past left (Fin.cases center future) := by
  ext x
  simp only [Set.mem_preimage, centeredCylinder, Set.mem_singleton_iff,
    Set.mem_iUnion]
  constructor
  · intro h
    have hrest := congrArg Prod.snd h
    have hcenter := congrArg Prod.fst hrest
    have hfuture := congrArg Prod.snd hrest
    refine ⟨x 0, ?_⟩
    apply Prod.ext
    · funext i
      exact Fin.elim0 i
    · apply Prod.ext
      · rfl
      · funext i
        refine Fin.cases ?_ (fun q => ?_) i
        · change x 1 = center
          simpa [centeredObservation, bilateralShift] using hcenter
        · have hi := congrFun hfuture q
          change x ((q : ℤ) + 2) = future q
          simpa [centeredObservation, bilateralShift] using hi
  · rintro ⟨left, h⟩
    have hrest := congrArg Prod.snd h
    have hfuture := congrArg Prod.snd hrest
    apply Prod.ext
    · funext i
      exact Fin.elim0 i
    · apply Prod.ext
      · have hi := congrFun hfuture 0
        change x 1 = center at hi
        change bilateralShift x 0 = center
        simpa [bilateralShift] using hi
      · funext i
        have hi := congrFun hfuture i.succ
        change x ((i : ℤ) + 2) = future i at hi
        change bilateralShift x ((i : ℤ) + 1) = future i
        simpa [bilateralShift] using hi

theorem twoSidedMarkovMeasure_shift_centeredCylinder_zero (k : ℕ)
    (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    {n : ℕ} (past : Fin 0 → Fin k) (center : Fin k)
    (future : Fin n → Fin k) :
    twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary
        (bilateralShift ⁻¹' centeredCylinder past center future) =
      twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary
        (centeredCylinder past center future) := by
  let μ := twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary
  let C : Fin k → Set (ℤ → Fin k) := fun left =>
    centeredCylinder past left (Fin.cases center future)
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro i j hij
    change Disjoint (C i) (C j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    apply hij
    have hi : x 0 = i := by
      change centeredObservation 0 (n + 1) x =
        (past, i, Fin.cases center future) at hxi
      have h := congrArg (fun y => y.2.1) hxi
      simpa [centeredObservation] using h
    have hj : x 0 = j := by
      change centeredObservation 0 (n + 1) x =
        (past, j, Fin.cases center future) at hxj
      have h := congrArg (fun y => y.2.1) hxj
      simpa [centeredObservation] using h
    exact hi.symm.trans hj
  rw [bilateralShift_preimage_centeredCylinder_zero,
    MeasureTheory.measure_iUnion hdisj
      (fun i => centeredCylinder_measurable past i (Fin.cases center future)),
    tsum_fintype]
  simp only [C]
  simp_rw [twoSidedMarkovMeasure_centeredCylinder_real k p P hp hpsum hP hPsum
    hstationary past _ (Fin.cases center future)]
  rw [twoSidedMarkovMeasure_centeredCylinder_real k p P hp hpsum hP hPsum
    hstationary past center future]
  simp_rw [markovPathWeight_cons]
  simp_rw [markovPathWeight_zero]
  simp only [mul_one]
  have hfuture : 0 ≤ markovPathWeight P center future :=
    markovPathWeight_nonneg P hP center future
  simp_rw [← mul_assoc]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (hp i) (hP i center)) hfuture)]
  apply congrArg ENNReal.ofReal
  rw [← Finset.sum_mul, hstationary]

def centeredSetFamily (k : ℕ) : Set (Set (ℤ → Fin k)) :=
  {C | ∃ m n : ℕ,
    ∃ A : Set ((Fin m → Fin k) × Fin k × (Fin n → Fin k)),
      C = centeredObservation m n ⁻¹' A}

theorem centeredSetFamily_generate (k : ℕ) :
    (inferInstance : MeasurableSpace (ℤ → Fin k)) =
      MeasurableSpace.generateFrom (centeredSetFamily k) := by
  apply le_antisymm
  · rw [MeasurableSpace.pi_eq_generateFrom_projections]
    apply MeasurableSpace.generateFrom_mono
    rintro _ ⟨z, B, hB, rfl⟩
    cases z with
    | ofNat r =>
        cases r with
        | zero =>
            let A : Set ((Fin 0 → Fin k) × Fin k × (Fin 0 → Fin k)) :=
              {t | t.2.1 ∈ B}
            refine ⟨0, 0, A, ?_⟩
            ext x
            simp [centeredObservation, A]
        | succ r =>
            let A : Set ((Fin 0 → Fin k) × Fin k × (Fin (r + 1) → Fin k)) :=
              {t | t.2.2 ⟨r, by omega⟩ ∈ B}
            refine ⟨0, r + 1, A, ?_⟩
            ext x
            simp [centeredObservation, A]
    | negSucc r =>
        let A : Set ((Fin (r + 1) → Fin k) × Fin k × (Fin 0 → Fin k)) :=
          {t | t.1 ⟨r, by omega⟩ ∈ B}
        refine ⟨r + 1, 0, A, ?_⟩
        ext x
        have hz : Int.negSucc r = -1 + -(r : ℤ) := by omega
        simp [centeredObservation, A, hz]
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨m, n, A, rfl⟩
    exact (centeredObservation_measurable m n) (Set.toFinite A).measurableSet

theorem centeredSetFamily_piSystem (k : ℕ) :
    IsPiSystem (centeredSetFamily k) := by
  rintro C ⟨m, n, A, rfl⟩ D ⟨m', n', B, rfl⟩ hne
  let M := max m m'
  let N := max n n'
  let rm : ((Fin M → Fin k) × Fin k × (Fin N → Fin k)) →
      ((Fin m → Fin k) × Fin k × (Fin n → Fin k)) := fun t =>
    (fun i => t.1 ⟨i, by
      have hi := i.isLt
      have hm : m ≤ M := le_max_left _ _
      omega⟩,
      t.2.1,
      fun i => t.2.2 ⟨i, by
        have hi := i.isLt
        have hn : n ≤ N := le_max_left _ _
        omega⟩)
  let rm' : ((Fin M → Fin k) × Fin k × (Fin N → Fin k)) →
      ((Fin m' → Fin k) × Fin k × (Fin n' → Fin k)) := fun t =>
    (fun i => t.1 ⟨i, by
      have hi := i.isLt
      have hm : m' ≤ M := le_max_right _ _
      omega⟩,
      t.2.1,
      fun i => t.2.2 ⟨i, by
        have hi := i.isLt
        have hn : n' ≤ N := le_max_right _ _
        omega⟩)
  let E : Set ((Fin M → Fin k) × Fin k × (Fin N → Fin k)) :=
    {t | rm t ∈ A ∧ rm' t ∈ B}
  refine ⟨M, N, E, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, E, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxA, hxB⟩
    constructor
    · simpa only [rm, centeredObservation] using hxA
    · simpa only [rm', centeredObservation] using hxB
  · rintro ⟨hxA, hxB⟩
    constructor
    · simpa only [rm, centeredObservation] using hxA
    · simpa only [rm', centeredObservation] using hxB

theorem twoSidedMarkovMeasure_shift_centeredCylinder (k : ℕ)
    (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    {m n : ℕ} (past : Fin m → Fin k) (center : Fin k)
    (future : Fin n → Fin k) :
    twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary
        (bilateralShift ⁻¹' centeredCylinder past center future) =
      twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary
        (centeredCylinder past center future) := by
  cases m with
  | zero =>
      exact twoSidedMarkovMeasure_shift_centeredCylinder_zero k p P hp hpsum
        hP hPsum hstationary past center future
  | succ m =>
      let left : Fin k := past 0
      let rest : Fin m → Fin k := fun i => past i.succ
      have hpast : past = Fin.cases left rest := by
        funext i
        refine Fin.cases ?_ (fun q => ?_) i
        · rfl
        · rfl
      rw [hpast]
      exact twoSidedMarkovMeasure_shift_centeredCylinder_cons k p P hp hpsum
        hP hPsum hstationary left rest center future

theorem twoSidedMarkovMeasure_shiftPreserving (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    MeasureTheory.MeasurePreserving (@bilateralShift k)
      (twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary)
      (twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary) := by
  let μ := twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary
  have hshift : Measurable (@bilateralShift k) := bilateralShift_measurable
  refine ⟨hshift, ?_⟩
  have hfin : ∀ m n : ℕ,
      MeasureTheory.Measure.map (centeredObservation m n)
          (MeasureTheory.Measure.map bilateralShift μ) =
        MeasureTheory.Measure.map (centeredObservation m n) μ := by
    intro m n
    apply MeasureTheory.Measure.ext_of_singleton
    rintro ⟨past, center, future⟩
    have hC : centeredObservation m n ⁻¹' ({(past, center, future)} :
        Set ((Fin m → Fin k) × Fin k × (Fin n → Fin k))) =
        centeredCylinder past center future := rfl
    rw [MeasureTheory.Measure.map_apply (centeredObservation_measurable m n)
        (MeasurableSet.singleton (past, center, future)),
      MeasureTheory.Measure.map_apply hshift
        ((centeredObservation_measurable m n)
          (MeasurableSet.singleton (past, center, future))), hC,
      MeasureTheory.Measure.map_apply (centeredObservation_measurable m n)
        (MeasurableSet.singleton (past, center, future)), hC]
    exact twoSidedMarkovMeasure_shift_centeredCylinder k p P hp hpsum hP hPsum
      hstationary past center future
  apply MeasureTheory.Measure.ext_of_generateFrom_of_cover_subset
    (centeredSetFamily_generate k) (centeredSetFamily_piSystem k)
    (T := {Set.univ})
  · intro C hC
    subst C
    exact ⟨0, 0, Set.univ, by simp⟩
  · exact Set.countable_singleton _
  · simp
  · intro C hC
    have hCu : C = Set.univ := Set.mem_singleton_iff.mp hC
    subst C
    rw [MeasureTheory.Measure.map_apply hshift MeasurableSet.univ]
    have hprob := twoSidedMarkovMeasure_isProbability k p P hp hpsum hP hPsum
      hstationary
    simp only [Set.preimage_univ]
    rw [hprob.measure_univ]
    simp
  · rintro C ⟨m, n, A, rfl⟩
    rw [← MeasureTheory.Measure.map_apply (centeredObservation_measurable m n)
        (Set.toFinite A).measurableSet,
      ← MeasureTheory.Measure.map_apply (centeredObservation_measurable m n)
        (Set.toFinite A).measurableSet, hfin m n]

noncomputable def twoSidedMarkovSystem (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    MeasurePreservingSystemData where
  X := ℤ → Fin k
  measurableSpace := inferInstance
  μ := twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary
  T := bilateralShift

theorem twoSidedMarkovSystem_mps (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    IsMeasurePreservingSystem
      (twoSidedMarkovSystem k p P hp hpsum hP hPsum hstationary) := by
  constructor
  · exact twoSidedMarkovMeasure_isProbability k p P hp hpsum hP hPsum hstationary
  · exact twoSidedMarkovMeasure_shiftPreserving k p P hp hpsum hP hPsum hstationary

theorem twoSidedMarkovMeasure_nonnegative_prefix (k : ℕ) (p : Fin k → ℝ)
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (n : ℕ) (a : Fin (n + 1) → Fin k) :
    twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary
        {x | ∀ i : Fin (n + 1), x (i : ℤ) = a i} =
      ENNReal.ofReal
        (p (a 0) * ∏ i : Fin n, P (a i.castSucc) (a i.succ)) := by
  let past : Fin 0 → Fin k := fun i => Fin.elim0 i
  let future : Fin n → Fin k := fun i => a i.succ
  have hset : {x : ℤ → Fin k | ∀ i : Fin (n + 1), x (i : ℤ) = a i} =
      centeredCylinder past (a 0) future := by
    ext x
    simp only [centeredCylinder, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_setOf_eq]
    constructor
    · intro h
      apply Prod.ext
      · funext i
        exact Fin.elim0 i
      · apply Prod.ext
        · exact h 0
        · funext i
          change x ((i : ℤ) + 1) = a i.succ
          simpa using h i.succ
    · intro h i
      have hrest := congrArg Prod.snd h
      have hcenter := congrArg Prod.fst hrest
      have hfuture := congrArg Prod.snd hrest
      refine Fin.cases ?_ (fun q => ?_) i
      · simpa [centeredObservation] using hcenter
      · have hi := congrFun hfuture q
        change x ((q : ℤ) + 1) = a q.succ at hi
        simpa using hi
  have hcases : Fin.cases (a 0) future = a := by
    funext i
    refine Fin.cases ?_ (fun q => ?_) i
    · rfl
    · rfl
  have hweight : markovPathWeight P (a 0) future =
      ∏ i : Fin n, P (a i.castSucc) (a i.succ) := by
    unfold markovPathWeight
    apply Finset.prod_congr rfl
    intro i hi
    dsimp only
    rw [congrFun hcases i.castSucc]
  rw [hset, twoSidedMarkovMeasure_centeredCylinder_real k p P hp hpsum hP hPsum
    hstationary past (a 0) future, markovPathWeight_zero, mul_one, hweight]

end Chapter01
