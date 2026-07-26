import Chapter00.Common
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! Construction used by Section 01's finite-alphabet Daniell--Kolmogorov theorem. -/

open scoped BigOperators ENNReal
open Set MeasureTheory
open ProbabilityTheory

namespace Chapter00

abbrev Hist (k n : ℕ) := (i : Finset.Iic n) → Fin k

private def histSplitEquiv (k n : ℕ) : Hist k (n + 1) ≃ Hist k n × Fin k where
  toFun x :=
    (fun i => x ⟨i.1, Finset.mem_Iic.mpr (by
      have hi := Finset.mem_Iic.mp i.2
      omega)⟩,
     x ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)
  invFun y i := if hi : i.1 ≤ n then y.1 ⟨i.1, Finset.mem_Iic.mpr hi⟩ else y.2
  left_inv x := by
    funext i
    dsimp
    split_ifs with hi
    · rfl
    · have hi' := Finset.mem_Iic.mp i.2
      have : i.1 = n + 1 := by omega
      exact congrArg x (Subtype.ext this.symm)
  right_inv y := by
    apply Prod.ext
    · funext i
      simp [Finset.mem_Iic.mp i.2]
    · simp

private def snocEquiv (k n : ℕ) :
    ((Fin n → Fin k) × Fin k) ≃ (Fin (n + 1) → Fin k) where
  toFun y := Fin.snoc y.1 y.2
  invFun f := (Fin.init f, f (Fin.last n))
  left_inv y := by
    apply Prod.ext
    · funext i
      simp [Fin.init, Fin.snoc]
    · simp [Fin.snoc]
  right_inv f := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.snoc]
    · simp [Fin.snoc, Fin.init]

private def consEquiv (k n : ℕ) :
    ((Fin n → Fin k) × Fin k) ≃ (Fin (n + 1) → Fin k) where
  toFun y := Fin.cons y.2 y.1
  invFun f := (Fin.tail f, f 0)
  left_inv y := by
    apply Prod.ext
    · funext i
      simp [Fin.tail, Fin.cons]
    · simp [Fin.cons]
  right_inv f := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Fin.cons]
    · simp [Fin.cons, Fin.tail]

private def spatialEquiv (k : ℕ) :
    (n : ℕ) → Hist k n ≃ (Fin (n + 1) → Fin k)
  | 0 =>
      { toFun := fun x _ => x ⟨0, by simp⟩
        invFun := fun f _ => f 0
        left_inv := by
          intro x
          funext i
          have hi : i = ⟨0, by simp⟩ := Subtype.ext
            (Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2))
          subst i
          rfl
        right_inv := by intro f; funext i; exact Fin.eq_zero i ▸ rfl }
  | n + 1 =>
      (histSplitEquiv k n).trans
        (((spatialEquiv k n).prodCongr (Equiv.refl (Fin k))).trans
          (if Even n then snocEquiv k (n + 1) else consEquiv k (n + 1)))

#check spatialEquiv
#check List.ofFn_succ
#check List.ofFn_zero

private lemma ofFn_snoc {α : Type*} {n : ℕ} (f : Fin n → α) (a : α) :
    List.ofFn (Fin.snoc f a) = List.ofFn f ++ [a] := by
  induction n with
  | zero => rw [List.ofFn_succ, List.ofFn_zero]; rfl
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      congr 1
      simpa [Fin.snoc] using ih (fun i => f i.succ)

private def finOneFunEquiv (k : ℕ) : (Fin 1 → Fin k) ≃ Fin k where
  toFun f := f 0
  invFun a := fun _ => a
  left_inv f := by funext i; exact Fin.eq_zero i ▸ rfl
  right_inv _ := rfl

private theorem block_total (k : ℕ) (p : ℕ → List (Fin k) → ℝ)
    (hsum : ∑ a : Fin k, p 0 [a] = 1)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word)) :
    ∀ n, ∑ f : Fin (n + 1) → Fin k, p n (List.ofFn f) = 1 := by
  intro n
  induction n with
  | zero =>
      calc
        (∑ f : Fin 1 → Fin k, p 0 (List.ofFn f)) =
            ∑ a : Fin k, p 0 [a] := by
              exact Fintype.sum_equiv (finOneFunEquiv k)
                (fun f => p 0 (List.ofFn f)) (fun a => p 0 [a]) (by
                  intro f
                  simp [finOneFunEquiv])
        _ = 1 := hsum
  | succ n ih =>
      by_cases hn : Even n
      · calc
          (∑ f : Fin (n + 2) → Fin k, p (n + 1) (List.ofFn f)) =
              ∑ y : (Fin (n + 1) → Fin k) × Fin k,
                p (n + 1) (List.ofFn ((snocEquiv k (n + 1)) y)) := by
                exact ((snocEquiv k (n + 1)).sum_comp
                  (fun f => p (n + 1) (List.ofFn f))).symm
          _ = ∑ f : Fin (n + 1) → Fin k,
                ∑ a : Fin k, p (n + 1) (List.ofFn f ++ [a]) := by
                rw [Fintype.sum_prod_type]
                apply Fintype.sum_congr
                intro f
                apply Fintype.sum_congr
                intro a
                change p (n + 1) (List.ofFn (Fin.snoc f a)) = _
                rw [ofFn_snoc]
          _ = ∑ f : Fin (n + 1) → Fin k, p n (List.ofFn f) := by
                apply Fintype.sum_congr
                intro f
                exact (hright n (List.ofFn f) (by simp)).symm
          _ = 1 := ih

      · calc
          (∑ f : Fin (n + 2) → Fin k, p (n + 1) (List.ofFn f)) =
              ∑ y : (Fin (n + 1) → Fin k) × Fin k,
                p (n + 1) (List.ofFn ((consEquiv k (n + 1)) y)) := by
                exact ((consEquiv k (n + 1)).sum_comp
                  (fun f => p (n + 1) (List.ofFn f))).symm
          _ = ∑ f : Fin (n + 1) → Fin k,
                ∑ a : Fin k, p (n + 1) (a :: List.ofFn f) := by
                rw [Fintype.sum_prod_type]
                apply Fintype.sum_congr
                intro f
                apply Fintype.sum_congr
                intro a
                change p (n + 1) (List.ofFn (Fin.cons a f)) = _
                rw [List.ofFn_cons]
          _ = ∑ f : Fin (n + 1) → Fin k, p n (List.ofFn f) := by
                apply Fintype.sum_congr
                intro f
                exact (hleft n (List.ofFn f) (by simp)).symm
          _ = 1 := ih

private noncomputable def blockMeasure (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) (n : ℕ) : Measure (Hist k n) :=
  ∑ x : Hist k n,
    ENNReal.ofReal (p n (List.ofFn (spatialEquiv k n x))) • Measure.dirac x

private theorem blockMeasure_singleton (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) (n : ℕ) (x : Hist k n) :
    blockMeasure k p n {x} =
      ENNReal.ofReal (p n (List.ofFn (spatialEquiv k n x))) := by
  rw [blockMeasure, Measure.finset_sum_apply]
  simp [Measure.smul_apply, Pi.single_apply]

private theorem blockMeasure_isProbability (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hsum : ∑ a : Fin k, p 0 [a] = 1)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word)) (n : ℕ) :
    IsProbabilityMeasure (blockMeasure k p n) := by
  constructor
  rw [blockMeasure, Measure.finset_sum_apply]
  simp_rw [Measure.smul_apply, Measure.dirac_apply]
  simp only [Set.indicator_of_mem, Set.mem_univ, smul_eq_mul, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · calc
      ENNReal.ofReal (∑ i, p n (List.ofFn (spatialEquiv k n i))) =
          ENNReal.ofReal (∑ f, p n (List.ofFn f)) := by
            exact congrArg ENNReal.ofReal
              ((spatialEquiv k n).sum_comp (fun f => p n (List.ofFn f)))
      _ = 1 := by rw [block_total k p hsum hright hleft n]; norm_num
  · intro x _hx
    exact hp n _ (by simp)

private def histRestrict (k n : ℕ) : Hist k (n + 1) → Hist k n :=
  fun x i => x ⟨i.1, Finset.mem_Iic.mpr (by
    have hi := Finset.mem_Iic.mp i.2
    omega)⟩

private lemma histSplitEquiv_fst (k n : ℕ) (x : Hist k (n + 1)) :
    (histSplitEquiv k n x).1 = histRestrict k n x := rfl

private theorem blockMeasure_consistent (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word)) (n : ℕ) :
    Measure.map (histRestrict k n) (blockMeasure k p (n + 1)) =
      blockMeasure k p n := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton x),
    blockMeasure_singleton]
  rw [blockMeasure, Measure.finset_sum_apply]
  simp_rw [Measure.smul_apply, Measure.dirac_apply]
  simp_rw [Set.indicator]
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Pi.one_apply,
    smul_eq_mul]
  simp_rw [mul_ite]
  simp only [mul_one, mul_zero]
  change (∑ y : Hist k (n + 1),
    if histRestrict k n y = x then
      ENNReal.ofReal (p (n + 1) (List.ofFn (spatialEquiv k (n + 1) y))) else 0) = _
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  rw [Finset.sum_subtype (p := fun y : Hist k (n + 1) => histRestrict k n y = x)
    (Finset.univ.filter (fun y : Hist k (n + 1) => histRestrict k n y = x)) (by simp)]
  let e : Fin k ≃ {y : Hist k (n + 1) // histRestrict k n y = x} :=
    { toFun := fun a => ⟨(histSplitEquiv k n).symm (x, a), by
          rw [← histSplitEquiv_fst]
          simp⟩
      invFun := fun y => (histSplitEquiv k n y.1).2
      left_inv := by intro a; simp
      right_inv := by
        intro y
        apply Subtype.ext
        apply (histSplitEquiv k n).injective
        apply Prod.ext
        · simpa [histSplitEquiv_fst] using y.2.symm
        · simp }
  rw [← e.sum_comp]
  by_cases hn : Even n
  · rw [← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [hright n (List.ofFn (spatialEquiv k n x)) (by simp)]
      apply Fintype.sum_congr
      intro a
      dsimp [e]
      change p (n + 1) (List.ofFn
        (spatialEquiv k (n + 1) ((histSplitEquiv k n).symm (x, a)))) = _
      apply congrArg (p (n + 1))
      rw [show spatialEquiv k (n + 1) ((histSplitEquiv k n).symm (x, a)) =
          Fin.snoc (spatialEquiv k n x) a by
        simp [spatialEquiv, snocEquiv, hn]]
      exact ofFn_snoc _ _
    · intro a _ha
      exact hp (n + 1) _ (by simp)

  · rw [← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [hleft n (List.ofFn (spatialEquiv k n x)) (by simp)]
      apply Fintype.sum_congr
      intro a
      dsimp [e]
      change p (n + 1) (List.ofFn
        (spatialEquiv k (n + 1) ((histSplitEquiv k n).symm (x, a)))) = _
      apply congrArg (p (n + 1))
      rw [show spatialEquiv k (n + 1) ((histSplitEquiv k n).symm (x, a)) =
          Fin.cons a (spatialEquiv k n x) by
        simp [spatialEquiv, consEquiv, hn]]
      exact List.ofFn_cons _ _
    · intro a _ha
      exact hp (n + 1) _ (by simp)

private noncomputable def initialMeasure (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) : Measure (Fin k) :=
  ∑ a : Fin k, ENNReal.ofReal (p 0 [a]) • Measure.dirac a

private theorem initialMeasure_singleton (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) (a : Fin k) :
    initialMeasure k p {a} = ENNReal.ofReal (p 0 [a]) := by
  rw [initialMeasure, Measure.finset_sum_apply]
  simp [Measure.smul_apply, Measure.dirac_apply, Pi.single_apply]

private theorem initialMeasure_isProbability (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hsum : ∑ a : Fin k, p 0 [a] = 1) :
    IsProbabilityMeasure (initialMeasure k p) := by
  constructor
  rw [initialMeasure, Measure.finset_sum_apply]
  simp_rw [Measure.smul_apply, Measure.dirac_apply]
  simp only [Set.indicator_of_mem, Set.mem_univ, smul_eq_mul, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [hsum]
    norm_num
  · intro a _ha
    exact hp 0 [a] (by simp)

private def histNew (k n : ℕ) : Hist k (n + 1) → Fin k :=
  fun x => x ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩

private lemma histSplitEquiv_pair (k n : ℕ) (x : Hist k (n + 1)) :
    histSplitEquiv k n x = (histRestrict k n x, histNew k n x) := rfl

private noncomputable def dkKernel (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ)
    (hk : 0 < k)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hsum : ∑ a : Fin k, p 0 [a] = 1)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word))
    (n : ℕ) : ProbabilityTheory.Kernel (Hist k n) (Fin k) := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  letI := blockMeasure_isProbability k p hp hsum hright hleft (n + 1)
  exact ProbabilityTheory.condDistrib (histNew k n) (histRestrict k n)
    (blockMeasure k p (n + 1))

private theorem blockMeasure_compProd_dkKernel (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ)
    (hk : 0 < k)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hsum : ∑ a : Fin k, p 0 [a] = 1)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word)) (n : ℕ) :
    (blockMeasure k p n) ⊗ₘ (dkKernel k p hk hp hsum hright hleft n) =
      Measure.map (histSplitEquiv k n) (blockMeasure k p (n + 1)) := by
  letI := blockMeasure_isProbability k p hp hsum hright hleft (n + 1)
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [dkKernel]
  rw [← blockMeasure_consistent k p hp hright hleft n]
  exact ProbabilityTheory.compProd_map_condDistrib
    (X := histRestrict k n) (Y := histNew k n)
    (μ := blockMeasure k p (n + 1)) (measurable_of_finite _).aemeasurable

private theorem dkKernel_isMarkov (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) (hk : 0 < k)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hsum : ∑ a : Fin k, p 0 [a] = 1)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word)) (n : ℕ) :
    IsMarkovKernel (dkKernel k p hk hp hsum hright hleft n) := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  unfold dkKernel
  infer_instance

private theorem initialPrefix_eq_blockMeasure_zero (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) :
    Measure.map
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Fin k)).symm
        (initialMeasure k p) =
      blockMeasure k p 0 := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton x),
    blockMeasure_singleton]
  have hpre :
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Fin k)).symm ⁻¹'
          ({x} : Set (Hist k 0)) = ({x ⟨0, by simp⟩} : Set (Fin k)) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact congrFun h ⟨0, by simp⟩
    · intro h
      funext i
      have hi : i = ⟨0, by simp⟩ := Subtype.ext
        (Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2))
      subst i
      simpa using h
  rw [hpre, initialMeasure_singleton]
  congr 2

private noncomputable def dkOneSidedMeasure (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) (hk : 0 < k)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hsum : ∑ a : Fin k, p 0 [a] = 1)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word)) :
    Measure (ℕ → Fin k) := by
  letI : ∀ n, IsMarkovKernel (dkKernel k p hk hp hsum hright hleft n) :=
    fun n => dkKernel_isMarkov k p hk hp hsum hright hleft n
  exact Kernel.trajMeasure (initialMeasure k p)
    (dkKernel k p hk hp hsum hright hleft)

private theorem dkOneSidedMeasure_marginal (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) (hk : 0 < k)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hsum : ∑ a : Fin k, p 0 [a] = 1)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word)) :
    ∀ n, Measure.map (Preorder.frestrictLe n)
        (dkOneSidedMeasure k p hk hp hsum hright hleft) = blockMeasure k p n := by
  letI : ∀ n, IsMarkovKernel (dkKernel k p hk hp hsum hright hleft n) :=
    fun n => dkKernel_isMarkov k p hk hp hsum hright hleft n
  letI : IsProbabilityMeasure (initialMeasure k p) :=
    initialMeasure_isProbability k p hp hsum
  intro n
  induction n with
  | zero =>
      unfold dkOneSidedMeasure Kernel.trajMeasure
      rw [Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
        Kernel.partialTraj_self]
      simpa using initialPrefix_eq_blockMeasure_zero k p
  | succ n ih =>
      have hjoint := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ => Fin k)
        (κ := dkKernel k p hk hp hsum hright hleft)
        (μ₀ := initialMeasure k p) (a := n)
      change
        (Measure.map (Preorder.frestrictLe n)
            (dkOneSidedMeasure k p hk hp hsum hright hleft)) ⊗ₘ
              dkKernel k p hk hp hsum hright hleft n = _ at hjoint
      rw [ih, blockMeasure_compProd_dkKernel k p hk hp hsum hright hleft n] at hjoint
      let e : Hist k (n + 1) ≃ᵐ Hist k n × Fin k :=
        { toEquiv := histSplitEquiv k n
          measurable_toFun := measurable_of_finite _
          measurable_invFun := measurable_of_finite _ }
      apply MeasurableEmbedding.map_injective e.measurableEmbedding
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rw [show Measure.map (e : Hist k (n + 1) → Hist k n × Fin k)
          (blockMeasure k p (n + 1)) =
            Measure.map (fun x : ℕ → Fin k =>
              (Preorder.frestrictLe n x, x (n + 1)))
              (Kernel.trajMeasure (initialMeasure k p)
                (dkKernel k p hk hp hsum hright hleft)) by
        exact hjoint]
      apply Measure.map_congr
      filter_upwards
      intro x
      rfl

private def spatialIndex : ℤ → ℕ
  | Int.ofNat 0 => 0
  | Int.ofNat (r + 1) => 2 * r + 1
  | Int.negSucc r => 2 * r + 2

private def decodeSpatial {k : ℕ} (x : ℕ → Fin k) : ℤ → Fin k :=
  fun z => x (spatialIndex z)

private theorem decodeSpatial_measurable {k : ℕ} :
    Measurable (decodeSpatial : (ℕ → Fin k) → (ℤ → Fin k)) := by
  apply measurable_pi_lambda
  intro z
  exact measurable_pi_apply (spatialIndex z)

private theorem spatialEquiv_restrict (k : ℕ) (x : ℕ → Fin k) :
    ∀ n (i : Fin (n + 1)),
      spatialEquiv k n (Preorder.frestrictLe n x) i =
        decodeSpatial x (-Int.ofNat (n / 2) + (i : ℕ)) := by
  intro n
  induction n with
  | zero =>
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl
  | succ n ih =>
      by_cases hn : Even n
      · rcases hn with ⟨r, hr⟩
        subst n
        have hd0 : (r + r) / 2 = r := by omega
        have hd1 : (r + r + 1) / 2 = r := by omega
        intro i
        simp only [spatialEquiv,
          if_pos (show Even (r + r) from ⟨r, rfl⟩), Equiv.trans_apply]
        change (Fin.snoc
          (spatialEquiv k (r + r) (Preorder.frestrictLe (r + r) x))
          (x (r + r + 1)) : Fin (r + r + 1 + 1) → Fin k) i = _
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Fin.snoc_last, decodeSpatial, hd1]
          change x (r + r + 1) =
            x (spatialIndex (-Int.ofNat r + Int.ofNat (r + r + 1)))
          rw [show -Int.ofNat r + Int.ofNat (r + r + 1) =
            Int.ofNat (r + 1) by
              change -(r : ℤ) + ((r + r + 1 : ℕ) : ℤ) = ((r + 1 : ℕ) : ℤ)
              push_cast
              ring]
          simp [spatialIndex]
          congr 1 <;> omega
        · rw [Fin.snoc_castSucc]
          rw [ih j]
          simp only [hd0, hd1]
          rfl
      · obtain ⟨r, hr⟩ : ∃ r, n = 2 * r + 1 := by
          rcases Nat.even_or_odd n with he | ho
          · exact False.elim (hn he)
          · rcases ho with ⟨r, hr⟩
            exact ⟨r, by omega⟩
        subst n
        have hd0 : (2 * r + 1) / 2 = r := by omega
        have hd1 : (2 * r + 1 + 1) / 2 = r + 1 := by omega
        intro i
        simp only [spatialEquiv, if_neg hn, Equiv.trans_apply]
        change (Fin.cons (x (2 * r + 1 + 1))
          (spatialEquiv k (2 * r + 1) (Preorder.frestrictLe (2 * r + 1) x)) :
            Fin (2 * r + 1 + 1 + 1) → Fin k) i = _
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero, decodeSpatial, hd1]
          change x (2 * r + 1 + 1) = x (spatialIndex (-Int.ofNat (r + 1)))
          rw [show -Int.ofNat (r + 1) = Int.negSucc r by rfl]
          simp [spatialIndex]
        · rw [Fin.cons_succ]
          rw [ih j]
          simp only [hd0, hd1]
          change decodeSpatial x (-Int.ofNat r + Int.ofNat j.1) =
            decodeSpatial x (-Int.ofNat (r + 1) + Int.ofNat j.succ.1)
          apply congrArg (decodeSpatial x)
          push_cast
          simp
          ring

private theorem sum_right_extensions (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (n : ℕ) (word : List (Fin k)) (hlen : word.length = n + 1) :
    ∀ r, p n word = ∑ f : Fin r → Fin k,
      p (n + r) (word ++ List.ofFn f) := by
  intro r
  induction r generalizing n word with
  | zero => simp [List.ofFn_zero]
  | succ r ih =>
      rw [hright n word hlen]
      simp_rw [ih (n := n + 1) (word := word ++ [_]) (by simp [hlen])]
      rw [Finset.sum_comm]
      calc
        (∑ f : Fin r → Fin k, ∑ a : Fin k,
            p (n + 1 + r) ((word ++ [a]) ++ List.ofFn f)) =
            ∑ y : (Fin r → Fin k) × Fin k,
              p (n + (r + 1)) (word ++ List.ofFn ((consEquiv k r) y)) := by
                rw [Fintype.sum_prod_type]
                apply Fintype.sum_congr
                intro f
                apply Fintype.sum_congr
                intro a
                change p (n + 1 + r) ((word ++ [a]) ++ List.ofFn f) =
                  p (n + (r + 1)) (word ++ List.ofFn (Fin.cons a f))
                rw [List.ofFn_cons]
                rw [show n + 1 + r = n + (r + 1) by omega]
                simp [List.append_assoc]
        _ = ∑ g : Fin (r + 1) → Fin k,
              p (n + (r + 1)) (word ++ List.ofFn g) := by
                exact (consEquiv k r).sum_comp
                  (fun g => p (n + (r + 1)) (word ++ List.ofFn g))

private theorem sum_left_extensions (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ)
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word))
    (n : ℕ) (word : List (Fin k)) (hlen : word.length = n + 1) :
    ∀ l, p n word = ∑ f : Fin l → Fin k,
      p (n + l) (List.ofFn f ++ word) := by
  intro l
  induction l generalizing n word with
  | zero => simp [List.ofFn_zero]
  | succ l ih =>
      rw [hleft n word hlen]
      simp_rw [ih (n := n + 1) (word := _ :: word) (by simp [hlen])]
      rw [Finset.sum_comm]
      calc
        (∑ f : Fin l → Fin k, ∑ a : Fin k,
            p (n + 1 + l) (List.ofFn f ++ a :: word)) =
            ∑ y : (Fin l → Fin k) × Fin k,
              p (n + (l + 1)) (List.ofFn ((snocEquiv k l) y) ++ word) := by
                rw [Fintype.sum_prod_type]
                apply Fintype.sum_congr
                intro f
                apply Fintype.sum_congr
                intro a
                change p (n + 1 + l) (List.ofFn f ++ a :: word) =
                  p (n + (l + 1)) (List.ofFn (Fin.snoc f a) ++ word)
                rw [ofFn_snoc]
                rw [show n + 1 + l = n + (l + 1) by omega]
                simp [List.append_assoc]
        _ = ∑ g : Fin (l + 1) → Fin k,
              p (n + (l + 1)) (List.ofFn g ++ word) := by
                exact (snocEquiv k l).sum_comp
                  (fun g => p (n + (l + 1)) (List.ofFn g ++ word))

private theorem sum_both_extensions (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word))
    (n l r : ℕ) (word : List (Fin k)) (hlen : word.length = n + 1) :
    p n word = ∑ a : Fin l → Fin k, ∑ b : Fin r → Fin k,
      p (n + l + r) (List.ofFn a ++ word ++ List.ofFn b) := by
  rw [sum_left_extensions k p hleft n word hlen l]
  apply Fintype.sum_congr
  intro a
  have hlen' : (List.ofFn a ++ word).length = (n + l) + 1 := by
    simp [hlen]
    omega
  rw [sum_right_extensions k p hright (n + l) (List.ofFn a ++ word) hlen' r]

private theorem mem_twoSidedCylinder_ofFn {k m : ℕ}
    (h : ℤ) (f : Fin m → Fin k) (x : ℤ → Fin k) :
    x ∈ twoSidedCylinder h (List.ofFn f) ↔
      ∀ i : Fin m, x (h + (i : ℕ)) = f i := by
  constructor
  · intro hx i
    let j : Fin (List.ofFn f).length := Fin.cast (by simp) i
    have hj := hx j
    rw [getElem?_pos (List.ofFn f) j j.2] at hj
    simp only [Option.some.injEq] at hj
    change (List.ofFn f).get j = x (h + (j : ℕ)) at hj
    rw [List.get_ofFn] at hj
    simpa [j] using hj.symm
  · intro hx j
    let i : Fin m := Fin.cast (by simp) j
    rw [getElem?_pos (List.ofFn f) j j.2]
    simp only [Option.some.injEq]
    change (List.ofFn f).get j = x (h + (j : ℕ))
    rw [List.get_ofFn]
    simpa [i] using (hx i).symm

private theorem twoSidedCylinder_ofFn_measurable (k m : ℕ)
    (h : ℤ) (f : Fin m → Fin k) :
    MeasurableSet (twoSidedCylinder h (List.ofFn f)) := by
  rw [show twoSidedCylinder h (List.ofFn f) =
      ⋂ i : Fin m, {x : ℤ → Fin k | x (h + (i : ℕ)) = f i} by
    ext x
    simpa only [Set.mem_iInter, Set.mem_setOf_eq] using
      (mem_twoSidedCylinder_ofFn h f x)]
  exact MeasurableSet.iInter fun i =>
    measurableSet_eq_fun (measurable_pi_apply (h + (i : ℕ))) measurable_const

private lemma decodeSpatial_center_preimage (k n : ℕ)
    (f : Fin (n + 1) → Fin k) :
    decodeSpatial ⁻¹'
        twoSidedCylinder (-Int.ofNat (n / 2)) (List.ofFn f) =
      Preorder.frestrictLe n ⁻¹' ({(spatialEquiv k n).symm f} : Set (Hist k n)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hx
    apply (spatialEquiv k n).injective
    funext i
    rw [Equiv.apply_symm_apply, spatialEquiv_restrict]
    exact (mem_twoSidedCylinder_ofFn _ _ _).mp hx i
  · intro hx
    apply (mem_twoSidedCylinder_ofFn _ _ _).mpr
    intro i
    have hxi := congrFun (congrArg (spatialEquiv k n) hx) i
    rw [Equiv.apply_symm_apply, spatialEquiv_restrict] at hxi
    exact hxi

private noncomputable def dkTwoSidedMeasure (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) (hk : 0 < k)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hsum : ∑ a : Fin k, p 0 [a] = 1)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word)) :
    Measure (ℤ → Fin k) :=
  Measure.map decodeSpatial (dkOneSidedMeasure k p hk hp hsum hright hleft)

private theorem dkTwoSidedMeasure_center (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) (hk : 0 < k)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hsum : ∑ a : Fin k, p 0 [a] = 1)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word))
    (n : ℕ) (f : Fin (n + 1) → Fin k) :
    dkTwoSidedMeasure k p hk hp hsum hright hleft
        (twoSidedCylinder (-Int.ofNat (n / 2)) (List.ofFn f)) =
      ENNReal.ofReal (p n (List.ofFn f)) := by
  rw [dkTwoSidedMeasure, Measure.map_apply decodeSpatial_measurable
    (twoSidedCylinder_ofFn_measurable k (n + 1) _ f), decodeSpatial_center_preimage]
  rw [← Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  rw [dkOneSidedMeasure_marginal k p hk hp hsum hright hleft n,
    blockMeasure_singleton]
  simp

private def prependFn {k l m : ℕ} (a : Fin l → Fin k) (f : Fin m → Fin k) :
    Fin (l + m) → Fin k := Fin.addCases a f

private def appendFn {k l m : ℕ} (f : Fin m → Fin k) (a : Fin l → Fin k) :
    Fin (m + l) → Fin k := Fin.addCases f a

@[simp] private lemma prependFn_castAdd {k l m : ℕ} (a : Fin l → Fin k)
    (f : Fin m → Fin k) (i : Fin l) : prependFn a f (Fin.castAdd m i) = a i := by
  simp [prependFn, Fin.addCases]

@[simp] private lemma prependFn_natAdd {k l m : ℕ} (a : Fin l → Fin k)
    (f : Fin m → Fin k) (i : Fin m) : prependFn a f (Fin.natAdd l i) = f i := by
  simp [prependFn, Fin.addCases]

@[simp] private lemma appendFn_castAdd {k l m : ℕ} (f : Fin m → Fin k)
    (a : Fin l → Fin k) (i : Fin m) : appendFn f a (Fin.castAdd l i) = f i := by
  simp [appendFn, Fin.addCases]

@[simp] private lemma appendFn_natAdd {k l m : ℕ} (f : Fin m → Fin k)
    (a : Fin l → Fin k) (i : Fin l) : appendFn f a (Fin.natAdd m i) = a i := by
  simp [appendFn, Fin.addCases]

private lemma ofFn_prependFn {k l m : ℕ} (a : Fin l → Fin k) (f : Fin m → Fin k) :
    List.ofFn (prependFn a f) = List.ofFn a ++ List.ofFn f := by
  rw [List.ofFn_add]
  apply congrArg₂ (· ++ ·)
  · congr 1
    funext i
    change prependFn a f (Fin.castLE (by omega) i) = a i
    rw [show Fin.castLE (by omega) i = Fin.castAdd m i by apply Fin.ext; rfl,
      prependFn_castAdd]
  · congr 1
    funext i
    simp [prependFn, Fin.addCases]

private lemma ofFn_appendFn {k l m : ℕ} (f : Fin m → Fin k) (a : Fin l → Fin k) :
    List.ofFn (appendFn f a) = List.ofFn f ++ List.ofFn a :=
  ofFn_prependFn f a

private theorem twoSidedCylinder_prepend_iUnion {k l m : ℕ}
    (h : ℤ) (f : Fin m → Fin k) :
    twoSidedCylinder (h + l) (List.ofFn f) =
      ⋃ a : Fin l → Fin k, twoSidedCylinder h (List.ofFn (prependFn a f)) := by
  ext x
  constructor
  · intro hx
    let a : Fin l → Fin k := fun i => x (h + (i : ℕ))
    apply Set.mem_iUnion.mpr
    refine ⟨a, (mem_twoSidedCylinder_ofFn h (prependFn a f) x).mpr ?_⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [prependFn, a, Fin.addCases]
    · have hj := (mem_twoSidedCylinder_ofFn (h + l) f x).mp hx j
      convert hj using 1 <;> simp [prependFn, Fin.addCases] <;> push_cast <;> ring
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨a, ha⟩
    apply (mem_twoSidedCylinder_ofFn (h + l) f x).mpr
    intro i
    have hi := (mem_twoSidedCylinder_ofFn h (prependFn a f) x).mp ha
      (Fin.natAdd l i)
    convert hi using 1 <;> simp [prependFn, Fin.addCases] <;> push_cast <;> ring

private theorem twoSidedCylinder_append_iUnion {k l m : ℕ}
    (h : ℤ) (f : Fin m → Fin k) :
    twoSidedCylinder h (List.ofFn f) =
      ⋃ a : Fin l → Fin k, twoSidedCylinder h (List.ofFn (appendFn f a)) := by
  ext x
  constructor
  · intro hx
    let a : Fin l → Fin k := fun i => x (h + m + (i : ℕ))
    apply Set.mem_iUnion.mpr
    refine ⟨a, (mem_twoSidedCylinder_ofFn h (appendFn f a) x).mpr ?_⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [appendFn, Fin.addCases] using
        (mem_twoSidedCylinder_ofFn h f x).mp hx j
    · rw [appendFn_natAdd]
      simp only [a]
      congr 1
      change h + (((m + j.1 : ℕ)) : ℤ) = h + (m : ℤ) + (j.1 : ℤ)
      push_cast
      ring
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨a, ha⟩
    apply (mem_twoSidedCylinder_ofFn h f x).mpr
    intro i
    have hi := (mem_twoSidedCylinder_ofFn h (appendFn f a) x).mp ha
      (Fin.castAdd l i)
    simpa [appendFn, Fin.addCases] using hi

private theorem pairwise_disjoint_prepend {k l m : ℕ} (h : ℤ) (f : Fin m → Fin k) :
    Pairwise (Function.onFun Disjoint
      (fun a : Fin l → Fin k => twoSidedCylinder h (List.ofFn (prependFn a f)))) := by
  intro a b hab
  change Disjoint (twoSidedCylinder h (List.ofFn (prependFn a f)))
    (twoSidedCylinder h (List.ofFn (prependFn b f)))
  rw [Set.disjoint_left]
  intro x hxa hxb
  apply hab
  funext i
  have ha := (mem_twoSidedCylinder_ofFn h (prependFn a f) x).mp hxa
    (Fin.castAdd m i)
  have hb := (mem_twoSidedCylinder_ofFn h (prependFn b f) x).mp hxb
    (Fin.castAdd m i)
  simpa [prependFn, Fin.addCases] using ha.symm.trans hb

private theorem pairwise_disjoint_append {k l m : ℕ} (h : ℤ) (f : Fin m → Fin k) :
    Pairwise (Function.onFun Disjoint
      (fun a : Fin l → Fin k => twoSidedCylinder h (List.ofFn (appendFn f a)))) := by
  intro a b hab
  change Disjoint (twoSidedCylinder h (List.ofFn (appendFn f a)))
    (twoSidedCylinder h (List.ofFn (appendFn f b)))
  rw [Set.disjoint_left]
  intro x hxa hxb
  apply hab
  funext i
  have ha := (mem_twoSidedCylinder_ofFn h (appendFn f a) x).mp hxa
    (Fin.natAdd m i)
  have hb := (mem_twoSidedCylinder_ofFn h (appendFn f b) x).mp hxb
    (Fin.natAdd m i)
  simpa [appendFn, Fin.addCases] using ha.symm.trans hb

private lemma ofFn_cast {α : Type*} {m q : ℕ} (f : Fin m → α) (h : m = q) :
    List.ofFn (fun i : Fin q => f (Fin.cast h.symm i)) = List.ofFn f := by
  subst q
  rfl

private theorem dkTwoSidedMeasure_center_cast (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) (hk : 0 < k)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hsum : ∑ a : Fin k, p 0 [a] = 1)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word))
    (n m : ℕ) (hm : m = n + 1) (f : Fin m → Fin k) :
    dkTwoSidedMeasure k p hk hp hsum hright hleft
        (twoSidedCylinder (-Int.ofNat (n / 2)) (List.ofFn f)) =
      ENNReal.ofReal (p n (List.ofFn f)) := by
  let g : Fin (n + 1) → Fin k := fun i => f (Fin.cast hm.symm i)
  have hfg : List.ofFn g = List.ofFn f := ofFn_cast f hm
  rw [← hfg]
  exact dkTwoSidedMeasure_center k p hk hp hsum hright hleft n g

private theorem dkTwoSidedMeasure_prepend (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) (hk : 0 < k)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hsum : ∑ a : Fin k, p 0 [a] = 1)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word))
    (n l : ℕ) (f : Fin (n + 1) → Fin k) :
    dkTwoSidedMeasure k p hk hp hsum hright hleft
        (twoSidedCylinder (-Int.ofNat ((n + l) / 2) + l) (List.ofFn f)) =
      ENNReal.ofReal (p n (List.ofFn f)) := by
  rw [twoSidedCylinder_prepend_iUnion]
  rw [measure_iUnion (pairwise_disjoint_prepend _ f)
    (fun a => twoSidedCylinder_ofFn_measurable k (l + (n + 1)) _ (prependFn a f)),
    tsum_fintype]
  simp_rw [dkTwoSidedMeasure_center_cast k p hk hp hsum hright hleft
    (n + l) (l + (n + 1)) (by omega) (prependFn _ f)]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    rw [sum_left_extensions k p hleft n (List.ofFn f) (by simp) l]
    apply Fintype.sum_congr
    intro a
    rw [ofFn_prependFn]
  · intro a _ha
    apply hp (n + l) _
    simp
    omega

private theorem dkTwoSidedMeasure_append (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) (hk : 0 < k)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hsum : ∑ a : Fin k, p 0 [a] = 1)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word))
    (n l : ℕ) (f : Fin (n + 1) → Fin k) :
    dkTwoSidedMeasure k p hk hp hsum hright hleft
        (twoSidedCylinder (-Int.ofNat ((n + l) / 2)) (List.ofFn f)) =
      ENNReal.ofReal (p n (List.ofFn f)) := by
  rw [twoSidedCylinder_append_iUnion]
  rw [measure_iUnion (pairwise_disjoint_append _ f)
    (fun a => twoSidedCylinder_ofFn_measurable k ((n + 1) + l) _ (appendFn f a)),
    tsum_fintype]
  simp_rw [dkTwoSidedMeasure_center_cast k p hk hp hsum hright hleft
    (n + l) ((n + 1) + l) (by omega) (appendFn f _)]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    rw [sum_right_extensions k p hright n (List.ofFn f) (by simp) l]
    apply Fintype.sum_congr
    intro a
    rw [ofFn_appendFn]
  · intro a _ha
    apply hp (n + l) _
    simp
    omega

private theorem dkOneSidedMeasure_isProbability (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) (hk : 0 < k)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hsum : ∑ a : Fin k, p 0 [a] = 1)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word)) :
    IsProbabilityMeasure (dkOneSidedMeasure k p hk hp hsum hright hleft) := by
  letI : ∀ n, IsMarkovKernel (dkKernel k p hk hp hsum hright hleft n) :=
    fun n => dkKernel_isMarkov k p hk hp hsum hright hleft n
  letI : IsProbabilityMeasure (initialMeasure k p) :=
    initialMeasure_isProbability k p hp hsum
  unfold dkOneSidedMeasure
  infer_instance

private theorem dkTwoSidedMeasure_isProbability (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) (hk : 0 < k)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hsum : ∑ a : Fin k, p 0 [a] = 1)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word)) :
    IsProbabilityMeasure (dkTwoSidedMeasure k p hk hp hsum hright hleft) := by
  unfold dkTwoSidedMeasure
  letI := dkOneSidedMeasure_isProbability k p hk hp hsum hright hleft
  exact Measure.isProbabilityMeasure_map decodeSpatial_measurable.aemeasurable

private theorem dkTwoSidedMeasure_cylinder (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) (hk : 0 < k)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hsum : ∑ a : Fin k, p 0 [a] = 1)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word))
    (h : ℤ) (n : ℕ) (word : List (Fin k)) (hlen : word.length = n + 1) :
    dkTwoSidedMeasure k p hk hp hsum hright hleft (twoSidedCylinder h word) =
      ENNReal.ofReal (p n word) := by
  let f : Fin (n + 1) → Fin k := fun i => word.get (Fin.cast hlen.symm i)
  have hfw : List.ofFn f = word := by
    calc
      List.ofFn f = List.ofFn word.get := ofFn_cast word.get hlen
      _ = word := List.ofFn_get word
  rw [← hfw]
  cases h with
  | ofNat q =>
      have hd : (n + (2 * q + n)) / 2 = q + n := by omega
      have hh : (Int.ofNat q) =
          -Int.ofNat ((n + (2 * q + n)) / 2) + (2 * q + n : ℕ) := by
        rw [hd]
        change (q : ℤ) = -((q + n : ℕ) : ℤ) + ((2 * q + n : ℕ) : ℤ)
        push_cast
        ring
      rw [hh]
      exact dkTwoSidedMeasure_prepend k p hk hp hsum hright hleft
        n (2 * q + n) f
  | negSucc q =>
      by_cases hn : n ≤ 2 * (q + 1)
      · let l := 2 * (q + 1) - n
        have hnl : n + l = 2 * (q + 1) := by dsimp [l]; omega
        have hd : (n + l) / 2 = q + 1 := by rw [hnl]; omega
        have hh : Int.negSucc q = -Int.ofNat ((n + l) / 2) := by
          rw [hd]
          rfl
        rw [hh]
        exact dkTwoSidedMeasure_append k p hk hp hsum hright hleft n l f
      · let l := n - 2 * (q + 1)
        have hnl : n + l = 2 * (n - (q + 1)) := by dsimp [l]; omega
        have hd : (n + l) / 2 = n - (q + 1) := by rw [hnl]; omega
        have hh : Int.negSucc q = -Int.ofNat ((n + l) / 2) + (l : ℕ) := by
          rw [hd]
          dsimp [l]
          change Int.negSucc q =
            -((n - (q + 1) : ℕ) : ℤ) + ((n - 2 * (q + 1) : ℕ) : ℤ)
          have hq : q + 1 ≤ n := by omega
          rw [Int.ofNat_sub hq, Int.ofNat_sub (by omega : 2 * (q + 1) ≤ n)]
          change Int.negSucc q = -(((n : ℕ) : ℤ) - ((q + 1 : ℕ) : ℤ)) +
            (((n : ℕ) : ℤ) - ((2 * (q + 1) : ℕ) : ℤ))
          push_cast
          omega
        rw [hh]
        exact dkTwoSidedMeasure_prepend k p hk hp hsum hright hleft n l f

private def encodeSpatial {k : ℕ} (x : ℤ → Fin k) : ℕ → Fin k
  | 0 => x 0
  | n + 1 => if Even n then x (Int.ofNat (n / 2 + 1)) else x (Int.negSucc (n / 2))

private theorem encodeSpatial_measurable {k : ℕ} :
    Measurable (encodeSpatial : (ℤ → Fin k) → (ℕ → Fin k)) := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_pi_apply 0
  | succ n =>
      by_cases hn : Even n
      · simpa [encodeSpatial, hn] using measurable_pi_apply (Int.ofNat (n / 2 + 1))
      · simpa [encodeSpatial, hn] using measurable_pi_apply (Int.negSucc (n / 2))

private theorem decode_encodeSpatial {k : ℕ} (x : ℤ → Fin k) :
    decodeSpatial (encodeSpatial x) = x := by
  funext z
  cases z with
  | ofNat n =>
      cases n with
      | zero => rfl
      | succ r =>
          have he : Even (2 * r) := ⟨r, by omega⟩
          simp [decodeSpatial, spatialIndex, encodeSpatial, he]
  | negSucc r =>
      have ho : ¬Even (2 * r + 1) := by
        rintro ⟨s, hs⟩
        omega
      have hd : (2 * r + 1) / 2 = r := by omega
      simp [decodeSpatial, spatialIndex, encodeSpatial, ho, hd]

private theorem encode_decodeSpatial {k : ℕ} (x : ℕ → Fin k) :
    encodeSpatial (decodeSpatial x) = x := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      by_cases hn : Even n
      · rcases hn with ⟨r, hr⟩
        subst n
        have hd : (r + r) / 2 = r := by omega
        simp [encodeSpatial, decodeSpatial, spatialIndex, hd, show Even (r + r) from ⟨r, rfl⟩]
        congr 1 <;> omega
      · obtain ⟨r, hr⟩ : ∃ r, n = 2 * r + 1 := by
          rcases Nat.even_or_odd n with he | ho
          · exact False.elim (hn he)
          · rcases ho with ⟨r, hr⟩
            exact ⟨r, by omega⟩
        subst n
        have hd : (2 * r + 1) / 2 = r := by omega
        simp [encodeSpatial, decodeSpatial, spatialIndex, hd, hn]

private def spatialMeasurableEquiv (k : ℕ) :
    (ℤ → Fin k) ≃ᵐ (ℕ → Fin k) where
  toFun := encodeSpatial
  invFun := decodeSpatial
  left_inv := decode_encodeSpatial
  right_inv := encode_decodeSpatial
  measurable_toFun := encodeSpatial_measurable
  measurable_invFun := decodeSpatial_measurable

private def prefixCylinderFamily (k : ℕ) : Set (Set (ℕ → Fin k)) :=
  {C | ∃ n : ℕ, ∃ x : Hist k n,
    C = Preorder.frestrictLe n ⁻¹' ({x} : Set (Hist k n))}

private theorem prefixCylinderFamily_isPiSystem (k : ℕ) :
    IsPiSystem (prefixCylinderFamily k) := by
  rintro A ⟨n, x, rfl⟩ B ⟨m, y, rfl⟩ hne
  rcases hne with ⟨z, hzA, hzB⟩
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hzA hzB
  by_cases hnm : n ≤ m
  · refine ⟨m, y, ?_⟩
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · exact fun h => h.2
    · intro hw
      refine ⟨?_, hw⟩
      funext i
      have hi : i.1 ≤ m := by
        have := Finset.mem_Iic.mp i.2
        omega
      have hzi := congrFun hzA i
      have hzy := congrFun hzB ⟨i.1, Finset.mem_Iic.mpr hi⟩
      have hwy := congrFun hw ⟨i.1, Finset.mem_Iic.mpr hi⟩
      simpa [Preorder.frestrictLe] using (hzi.symm.trans (hzy.trans hwy.symm)).symm
  · have hmn : m ≤ n := by omega
    refine ⟨n, x, ?_⟩
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · intro hw
      refine ⟨hw, ?_⟩
      funext i
      have hi : i.1 ≤ n := by
        have := Finset.mem_Iic.mp i.2
        omega
      have hzi := congrFun hzB i
      have hzx := congrFun hzA ⟨i.1, Finset.mem_Iic.mpr hi⟩
      have hwx := congrFun hw ⟨i.1, Finset.mem_Iic.mpr hi⟩
      simpa [Preorder.frestrictLe] using (hzi.symm.trans (hzx.trans hwx.symm)).symm

private theorem prefixCylinderFamily_generate (k : ℕ) :
    (inferInstance : MeasurableSpace (ℕ → Fin k)) =
      MeasurableSpace.generateFrom (prefixCylinderFamily k) := by
  apply le_antisymm
  · let G : Set (Set (ℕ → Fin k)) :=
      {C | ∃ i : ℕ, ∃ A : Set (Fin k),
        MeasurableSet A ∧ Function.eval i ⁻¹' A = C}
    have hpi : (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom G := by
      calc
        (inferInstance : MeasurableSpace (ℕ → Fin k)) = MeasurableSpace.pi := rfl
        _ = MeasurableSpace.generateFrom G := MeasurableSpace.pi_eq_generateFrom_projections
    rw [hpi]
    refine MeasurableSpace.generateFrom_le ?_
    rintro C ⟨i, A, _hA, rfl⟩
    letI : MeasurableSpace (ℕ → Fin k) :=
      MeasurableSpace.generateFrom (prefixCylinderFamily k)
    have hsingle (a : Fin k) : MeasurableSet {w : ℕ → Fin k | w i = a} := by
      have heq : {w : ℕ → Fin k | w i = a} =
          ⋃ x : {x : Hist k i // x ⟨i, by simp⟩ = a},
            Preorder.frestrictLe i ⁻¹' ({x.1} : Set (Hist k i)) := by
        ext w
        constructor
        · intro hw
          apply Set.mem_iUnion.mpr
          refine ⟨⟨Preorder.frestrictLe i w, ?_⟩, rfl⟩
          change w i = a
          exact hw
        · intro hw
          rcases Set.mem_iUnion.mp hw with ⟨x, hx⟩
          change w i = a
          calc
            w i = Preorder.frestrictLe i w ⟨i, by simp⟩ := rfl
            _ = x.1 ⟨i, by simp⟩ := congrFun hx ⟨i, by simp⟩
            _ = a := x.2
      rw [heq]
      apply MeasurableSet.iUnion
      intro x
      exact MeasurableSpace.measurableSet_generateFrom ⟨i, x.1, rfl⟩
    have hEq : Function.eval i ⁻¹' A =
        ⋃ a : {a : Fin k // a ∈ A}, {w : ℕ → Fin k | w i = a.1} := by
      ext w
      constructor
      · intro hw
        exact Set.mem_iUnion.mpr ⟨⟨w i, hw⟩, rfl⟩
      · intro hw
        rcases Set.mem_iUnion.mp hw with ⟨a, ha⟩
        change w i ∈ A
        rw [ha]
        exact a.2
    rw [hEq]
    exact MeasurableSet.iUnion fun a => hsingle a.1
  · refine MeasurableSpace.generateFrom_le ?_
    rintro C ⟨n, x, rfl⟩
    exact (by fun_prop : Measurable (Preorder.frestrictLe n)) (measurableSet_singleton x)

private lemma encodeSpatial_prefix_preimage (k n : ℕ) (x : Hist k n) :
    encodeSpatial ⁻¹' (Preorder.frestrictLe n ⁻¹' ({x} : Set (Hist k n))) =
      twoSidedCylinder (-Int.ofNat (n / 2))
        (List.ofFn (spatialEquiv k n x)) := by
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hy
    apply (mem_twoSidedCylinder_ofFn _ _ _).mpr
    intro i
    have hs := spatialEquiv_restrict k (encodeSpatial y) n i
    rw [hy, decode_encodeSpatial] at hs
    exact hs.symm
  · intro hy
    apply (spatialEquiv k n).injective
    funext i
    have hs := spatialEquiv_restrict k (encodeSpatial y) n i
    rw [decode_encodeSpatial] at hs
    have hc := (mem_twoSidedCylinder_ofFn _ _ _).mp hy i
    exact hs.trans hc

private theorem dkTwoSidedMeasure_unique (k : ℕ)
    (p : ℕ → List (Fin k) → ℝ) (hk : 0 < k)
    (hp : ∀ n word, word.length = n + 1 → 0 ≤ p n word)
    (hsum : ∑ a : Fin k, p 0 [a] = 1)
    (hright : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (word ++ [a]))
    (hleft : ∀ n word, word.length = n + 1 →
      p n word = ∑ a : Fin k, p (n + 1) (a :: word))
    (ν : Measure (ℤ → Fin k)) (hνprob : IsProbabilityMeasure ν)
    (hν : ∀ h : ℤ, ∀ n : ℕ, ∀ word : List (Fin k), word.length = n + 1 →
      ν (twoSidedCylinder h word) = ENNReal.ofReal (p n word)) :
    ν = dkTwoSidedMeasure k p hk hp hsum hright hleft := by
  let μ0 := dkOneSidedMeasure k p hk hp hsum hright hleft
  let μ1 := Measure.map encodeSpatial ν
  letI : IsProbabilityMeasure ν := hνprob
  letI : IsProbabilityMeasure μ0 :=
    dkOneSidedMeasure_isProbability k p hk hp hsum hright hleft
  letI : IsProbabilityMeasure μ1 := by
    dsimp [μ1]
    exact Measure.isProbabilityMeasure_map encodeSpatial_measurable.aemeasurable
  have hμ : μ1 = μ0 := by
    apply Measure.ext_of_generateFrom_of_cover (prefixCylinderFamily_generate k)
      (Set.countable_singleton Set.univ) (prefixCylinderFamily_isPiSystem k)
      (T := {Set.univ})
    · simp
    · intro t ht
      rw [Set.mem_singleton_iff.mp ht]
      simp
    · intro t ht s hs
      rw [Set.mem_singleton_iff.mp ht, Set.inter_univ]
      rcases hs with ⟨n, x, rfl⟩
      change (Measure.map encodeSpatial ν)
        (Preorder.frestrictLe n ⁻¹' ({x} : Set (Hist k n))) =
          μ0 (Preorder.frestrictLe n ⁻¹' ({x} : Set (Hist k n)))
      rw [Measure.map_apply encodeSpatial_measurable
        ((by fun_prop : Measurable (Preorder.frestrictLe n))
          (measurableSet_singleton x)), encodeSpatial_prefix_preimage]
      rw [hν (-Int.ofNat (n / 2)) n (List.ofFn (spatialEquiv k n x)) (by simp)]
      rw [← Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
      change _ = Measure.map (Preorder.frestrictLe n)
        (dkOneSidedMeasure k p hk hp hsum hright hleft) {x}
      rw [dkOneSidedMeasure_marginal k p hk hp hsum hright hleft n,
        blockMeasure_singleton]
    · intro t ht
      rw [Set.mem_singleton_iff.mp ht]
      simp
  apply MeasurableEmbedding.map_injective
    (spatialMeasurableEquiv k).measurableEmbedding
  change Measure.map encodeSpatial ν =
    Measure.map encodeSpatial
      (Measure.map decodeSpatial (dkOneSidedMeasure k p hk hp hsum hright hleft))
  rw [Measure.map_map encodeSpatial_measurable decodeSpatial_measurable]
  rw [show encodeSpatial ∘ decodeSpatial = id by
    funext x
    exact encode_decodeSpatial x]
  rw [Measure.map_id]
  exact hμ

theorem daniellKolmogorovTheoremAux
    (k : ℕ) (p : ℕ → List (Fin k) → ℝ) :
    HasDaniellKolmogorovMeasure k p := by
  intro hk hp hsum hright hleft
  have hkpos : 0 < k := by omega
  let S : Set (Set (ℤ → Fin k)) :=
    {C | ∃ h : ℤ, ∃ word : List (Fin k), C = twoSidedCylinder h word}
  have hgen : (inferInstance : MeasurableSpace (ℤ → Fin k)) =
      MeasurableSpace.generateFrom S := by
    apply le_antisymm
    · let G : Set (Set (ℤ → Fin k)) :=
        {C | ∃ i : ℤ, ∃ A : Set (Fin k),
          MeasurableSet A ∧ Function.eval i ⁻¹' A = C}
      have hpi : (inferInstance : MeasurableSpace (ℤ → Fin k)) =
          MeasurableSpace.generateFrom G := by
        calc
          (inferInstance : MeasurableSpace (ℤ → Fin k)) = MeasurableSpace.pi := rfl
          _ = MeasurableSpace.generateFrom G :=
            MeasurableSpace.pi_eq_generateFrom_projections
      rw [hpi]
      refine MeasurableSpace.generateFrom_le ?_
      rintro C ⟨i, A, _hA, rfl⟩
      letI : MeasurableSpace (ℤ → Fin k) := MeasurableSpace.generateFrom S
      have hsingle (a : Fin k) : MeasurableSet {x : ℤ → Fin k | x i = a} := by
        have heq : {x : ℤ → Fin k | x i = a} = twoSidedCylinder i [a] := by
          ext x
          simp [twoSidedCylinder, eq_comm]
        rw [heq]
        exact MeasurableSpace.measurableSet_generateFrom ⟨i, [a], rfl⟩
      have hEq : Function.eval i ⁻¹' A =
          ⋃ a : {a : Fin k // a ∈ A}, {x : ℤ → Fin k | x i = a.1} := by
        ext x
        constructor
        · intro hx
          exact Set.mem_iUnion.mpr ⟨⟨x i, hx⟩, rfl⟩
        · intro hx
          rcases Set.mem_iUnion.mp hx with ⟨a, ha⟩
          change x i ∈ A
          rw [ha]
          exact a.2
      rw [hEq]
      exact MeasurableSet.iUnion fun a => hsingle a.1
    · refine MeasurableSpace.generateFrom_le ?_
      intro C hC
      rcases hC with ⟨h, word, rfl⟩
      rw [← List.ofFn_get word]
      exact twoSidedCylinder_ofFn_measurable k word.length h word.get
  refine ⟨inferInstance, ?_, ?_⟩
  · exact hgen
  · let μ := dkTwoSidedMeasure k p hkpos hp hsum hright hleft
    letI : IsProbabilityMeasure μ :=
      dkTwoSidedMeasure_isProbability k p hkpos hp hsum hright hleft
    refine ⟨μ, inferInstance, ?_, ?_⟩
    · exact dkTwoSidedMeasure_cylinder k p hkpos hp hsum hright hleft
    · intro ν hνprob hν
      exact dkTwoSidedMeasure_unique k p hkpos hp hsum hright hleft ν hνprob hν

end Chapter00
