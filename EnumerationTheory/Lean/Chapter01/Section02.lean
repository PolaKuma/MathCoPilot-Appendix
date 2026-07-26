import Chapter01.Section01
import Chapter01.Coding.BinaryCoding
import Chapter01.Coding.CauchyCoding
import Chapter01.Coding.MarkovCoding

noncomputable section

open Classical
open scoped BigOperators

namespace Chapter01
namespace Section02

universe u v w

private noncomputable def trivialExampleSystem.{z} :
    MeasurePreservingSystemData.{z} where
  X := PUnit.{z + 1}
  measurableSpace := ⊤
  μ := MeasureTheory.Measure.dirac PUnit.unit
  T := id

private noncomputable def nPeriodicExampleSystem.{z} (n : ℕ) [NeZero n] :
    MeasurePreservingSystemData.{z} where
  X := ULift.{z} (Fin n)
  measurableSpace := ⊤
  μ := ProbabilityTheory.uniformOn Set.univ
  T := fun x => ULift.up ((Equiv.addRight (1 : Fin n)) x.down)

private noncomputable def circleRotationExampleSystem.{z} (α : ℝ) :
    MeasurePreservingSystemData.{z} where
  X := ULift.{z} (AddCircle (1 : ℝ))
  measurableSpace := inferInstance
  μ := MeasureTheory.Measure.map (MeasurableEquiv.ulift.symm) AddCircle.haarAddCircle
  T := fun x =>
    MeasurableEquiv.ulift.symm
      (MeasurableEquiv.ulift x + (α : AddCircle (1 : ℝ)))

private noncomputable def liftedCircleTimesSystem.{z} (n : ℕ) :
    MeasurePreservingSystemData.{z} where
  X := ULift.{z} (AddCircle (1 : ℝ))
  measurableSpace := inferInstance
  μ := MeasureTheory.Measure.map (MeasurableEquiv.ulift.symm) AddCircle.haarAddCircle
  T := fun x => MeasurableEquiv.ulift.symm
    (circleTimes n (MeasurableEquiv.ulift x))

private noncomputable def liftedOneSidedBernoulliSystem.{z}
    (k : ℕ) (p : Fin k → ℝ) : MeasurePreservingSystemData.{z} where
  X := ULift.{z} (OneSidedSymbolicSpace k)
  measurableSpace := inferInstance
  μ := MeasureTheory.Measure.map MeasurableEquiv.ulift.symm
    (oneSidedBernoulliMeasure k p)
  T := fun x => MeasurableEquiv.ulift.symm
    (oneSidedShift (MeasurableEquiv.ulift x))

private noncomputable def liftedSystem.{z} (S : MeasurePreservingSystemData.{0}) :
    MeasurePreservingSystemData.{z} where
  X := ULift.{z} S.X
  measurableSpace := inferInstance
  μ := MeasureTheory.Measure.map MeasurableEquiv.ulift.symm S.μ
  T := fun x => MeasurableEquiv.ulift.symm (S.T (MeasurableEquiv.ulift x))

private theorem liftedSystem_mps (S : MeasurePreservingSystemData.{0})
    (hS : IsMeasurePreservingSystem S) :
    IsMeasurePreservingSystem (liftedSystem.{z} S) := by
  let e := MeasurableEquiv.ulift (α := S.X)
  let L := liftedSystem.{z} S
  have hup : MeasureTheory.MeasurePreserving e.symm S.μ L.μ :=
    ⟨e.symm.measurable, rfl⟩
  have hdn : MeasureTheory.MeasurePreserving e L.μ S.μ := by
    refine ⟨e.measurable, ?_⟩
    change MeasureTheory.Measure.map e
      (MeasureTheory.Measure.map e.symm S.μ) = S.μ
    rw [MeasureTheory.Measure.map_map e.measurable e.symm.measurable]
    simpa [e] using (MeasureTheory.Measure.map_id :
      MeasureTheory.Measure.map (id : S.X → S.X) S.μ = S.μ)
  constructor
  · constructor
    change MeasureTheory.Measure.map e.symm S.μ Set.univ = 1
    rw [MeasureTheory.Measure.map_apply e.symm.measurable MeasurableSet.univ]
    exact hS.1.measure_univ
  · change MeasureTheory.MeasurePreserving
      (fun x : ULift.{z} S.X => e.symm (S.T (e x))) L.μ L.μ
    exact hup.comp (hS.2.comp hdn)

private theorem liftedCircleTimesSystem_mps (n : ℕ) (hn : 0 < n) :
    IsMeasurePreservingSystem (liftedCircleTimesSystem n) := by
  let e := MeasurableEquiv.ulift (α := AddCircle (1 : ℝ))
  have hup : MeasureTheory.MeasurePreserving e.symm
      AddCircle.haarAddCircle (liftedCircleTimesSystem n).μ := by
    exact MeasureTheory.MeasurePreserving.mk e.symm.measurable rfl
  have hdn : MeasureTheory.MeasurePreserving e
      (liftedCircleTimesSystem n).μ AddCircle.haarAddCircle := by
    refine MeasureTheory.MeasurePreserving.mk e.measurable ?_
    change MeasureTheory.Measure.map e
      (MeasureTheory.Measure.map e.symm AddCircle.haarAddCircle) = _
    rw [MeasureTheory.Measure.map_map e.measurable e.symm.measurable]
    have hid : MeasureTheory.Measure.map
        (id : AddCircle (1 : ℝ) → AddCircle (1 : ℝ))
        (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
          AddCircle.haarAddCircle := MeasureTheory.Measure.map_id
    simpa [e] using hid
  constructor
  · constructor
    change MeasureTheory.Measure.map e.symm AddCircle.haarAddCircle Set.univ = 1
    rw [MeasureTheory.Measure.map_apply e.symm.measurable MeasurableSet.univ]
    simp
  · change MeasureTheory.MeasurePreserving
      (fun x : ULift (AddCircle (1 : ℝ)) => e.symm (n • e x))
      (liftedCircleTimesSystem n).μ (liftedCircleTimesSystem n).μ
    have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    exact hup.comp
      (((AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle (1 : ℝ)))
      ).measurePreserving_zsmul hnz |>.comp hdn)

private theorem alphabetProbabilityMeasure_isProbabilityMeasure
    (k : ℕ) (p : Fin k -> ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    MeasureTheory.IsProbabilityMeasure (alphabetProbabilityMeasure k p) := by
  constructor
  change (∑ i : Fin k, (ENNReal.ofReal (p i) • MeasureTheory.Measure.dirac i)) Set.univ = 1
  rw [MeasureTheory.Measure.finset_sum_apply]
  simp_rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply]
  simp only [Set.indicator_of_mem, Set.mem_univ, smul_eq_mul, Pi.one_apply]
  simp only [mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := p) (by
    intro i hi
    exact hp i)]
  simp [hsum]

private theorem alphabetProbabilityMeasure_singleton
    (k : ℕ) (p : Fin k -> ℝ) (i : Fin k) :
    alphabetProbabilityMeasure k p ({i} : Set (Fin k)) = ENNReal.ofReal (p i) := by
  rw [alphabetProbabilityMeasure]
  rw [MeasureTheory.Measure.finset_sum_apply]
  simp [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply,
    Pi.single_apply]

private theorem twoSidedBernoulli_cylinder
    (k : ℕ) (n : ℕ) (a : Fin (n + 1) -> Fin k)
    (p : Fin k -> ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (MeasureTheory.Measure.infinitePi
      (fun _ : ℤ => alphabetProbabilityMeasure k p))
      {x : ℤ -> Fin k | ∀ i : Fin (n + 1), x (i : ℤ) = a i} =
      ENNReal.ofReal (∏ i, p (a i)) := by
  letI : MeasureTheory.IsProbabilityMeasure (alphabetProbabilityMeasure k p) :=
    alphabetProbabilityMeasure_isProbabilityMeasure k p hp hsum
  have hsingle : ∀ i : Fin k,
      alphabetProbabilityMeasure k p ({i} : Set (Fin k)) = ENNReal.ofReal (p i) := by
    intro i
    exact alphabetProbabilityMeasure_singleton k p i
  let emb : Fin (n + 1) ↪ ℤ :=
    ⟨fun i => (i : ℤ), by
      intro i j hij
      apply Fin.ext
      exact Int.ofNat_injective (by simpa using hij)⟩
  let s : Finset ℤ := Finset.univ.map emb
  let e0 : Fin (n + 1) → {j // j ∈ s} := fun i =>
    ⟨emb i, by simp [s]⟩
  have he0 : Function.Bijective e0 := by
    constructor
    · intro i j hij
      apply emb.injective
      exact congrArg Subtype.val hij
    · intro j
      have hj : j.1 ∈ s := j.2
      change j.1 ∈ Finset.univ.map emb at hj
      rcases Finset.mem_map.1 hj with ⟨i, hi, hije⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hije
  let e : Fin (n + 1) ≃ {j // j ∈ s} := Equiv.ofBijective e0 he0
  let t : ℤ → Set (Fin k) := fun j =>
    if h : j ∈ s then {a (e.symm ⟨j, h⟩)} else Set.univ
  have hC :
      {x : ℤ -> Fin k | ∀ i : Fin (n + 1), x (i : ℤ) = a i} = Set.pi s t := by
    ext x
    constructor
    · intro hx j hj
      change j ∈ Finset.univ.map emb at hj
      rcases Finset.mem_map.1 hj with ⟨i, hi, hije⟩
      have hi_s : emb i ∈ s := by simp [s]
      have hsub : (⟨emb i, hi_s⟩ : {j // j ∈ s}) = e i := by
        apply Subtype.ext
        rfl
      have he : e.symm ⟨emb i, hi_s⟩ = i := by
        rw [hsub, e.symm_apply_apply]
      have hj_eq : j = emb i := hije.symm
      rw [hj_eq]
      rw [show t (emb i) = ({a i} : Set (Fin k)) by simp [t, hi_s, he]]
      exact Set.mem_singleton_iff.mpr (by simpa [emb] using hx i)
    · intro hx i
      have hi : emb i ∈ s := by simp [s]
      have hxi := hx (emb i) hi
      have he : e.symm ⟨emb i, hi⟩ = i := by
        have hsub : (⟨emb i, hi⟩ : {j // j ∈ s}) = e i := by
          apply Subtype.ext
          rfl
        rw [hsub, e.symm_apply_apply]
      simpa [t, hi, he] using hxi
  rw [hC, MeasureTheory.Measure.infinitePi_pi]
  · rw [show s = Finset.univ.map emb by rfl, Finset.prod_map]
    have htmap : ∀ i : Fin (n + 1),
        (alphabetProbabilityMeasure k p) (t (emb i)) =
          ENNReal.ofReal (p (a i)) := by
      intro i
      have hi : emb i ∈ s := by simp [s]
      have hsub : (⟨emb i, hi⟩ : {j // j ∈ s}) = e i := by
        apply Subtype.ext
        rfl
      have he : e.symm ⟨emb i, hi⟩ = i := by
        rw [hsub, e.symm_apply_apply]
      rw [show t (emb i) = ({a i} : Set (Fin k)) by simp [t, hi, he]]
      exact hsingle (a i)
    simp_rw [htmap]
    rw [← ENNReal.ofReal_prod_of_nonneg]
    exact fun i hi => hp (a i)
  · intro j hj
    simp [t, hj]

noncomputable def twoSidedBernoulliExampleSystem (k : ℕ) (p : Fin k -> ℝ) :
    MeasurePreservingSystemData where
  X := ℤ -> Fin k
  measurableSpace := inferInstance
  μ := MeasureTheory.Measure.infinitePi (fun _ : ℤ => alphabetProbabilityMeasure k p)
  T := fun x n => x (n + 1)

theorem twoSidedBernoulliExampleSystem_mps (k : ℕ)
    (p : Fin k -> ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    IsMeasurePreservingSystem (twoSidedBernoulliExampleSystem k p) := by
  letI : MeasureTheory.IsProbabilityMeasure (alphabetProbabilityMeasure k p) :=
    alphabetProbabilityMeasure_isProbabilityMeasure k p hp hsum
  constructor
  · change MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.infinitePi (fun _ : ℤ => alphabetProbabilityMeasure k p))
    infer_instance
  · change MeasureTheory.MeasurePreserving
      (fun x : ℤ -> Fin k => fun n => x (n + 1))
      (MeasureTheory.Measure.infinitePi (fun _ : ℤ => alphabetProbabilityMeasure k p))
      (MeasureTheory.Measure.infinitePi (fun _ : ℤ => alphabetProbabilityMeasure k p))
    let e : ℤ ≃ ℤ := Equiv.addRight (-1)
    let q : (ℤ -> Fin k) ≃ᵐ (ℤ -> Fin k) :=
      MeasurableEquiv.piCongrLeft (fun _ : ℤ => Fin k) e
    have hmap := MeasureTheory.Measure.infinitePi_map_piCongrLeft
      (fun _ : ℤ => alphabetProbabilityMeasure k p) e
    refine ⟨?_, ?_⟩
    · fun_prop
    change MeasureTheory.Measure.map (fun x : ℤ -> Fin k => fun n => x (n + 1))
      (MeasureTheory.Measure.infinitePi (fun _ : ℤ => alphabetProbabilityMeasure k p)) = _
    simpa [q, e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Function.comp_def,
      Equiv.addRight] using hmap

private theorem oneSidedBernoulliShift_measurePreserving
    (k : ℕ) (p : Fin k -> ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    MeasureTheory.MeasurePreserving (@oneSidedShift k)
      (oneSidedBernoulliMeasure k p) (oneSidedBernoulliMeasure k p) := by
  letI : MeasureTheory.IsProbabilityMeasure (alphabetProbabilityMeasure k p) :=
    alphabetProbabilityMeasure_isProbabilityMeasure k p hp hsum
  have hshift_meas : Measurable (@oneSidedShift k) := by
    exact measurable_pi_lambda _ (fun n => measurable_pi_apply (n + 1))
  refine ⟨hshift_meas, ?_⟩
  apply MeasureTheory.Measure.eq_infinitePi
  intro s t ht
  let emb : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩
  let t' : ℕ → Set (Fin k) := fun j => t (j - 1)
  have hpre : oneSidedShift ⁻¹' Set.pi s t = Set.pi (s.map emb) t' := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi]
    constructor
    · intro hx j hj
      change j ∈ s.map emb at hj
      rcases Finset.mem_map.1 hj with ⟨i, hi, rfl⟩
      have hi' : i ∈ (s : Set ℕ) := by simpa using hi
      simpa [oneSidedShift, t', emb] using hx i hi'
    · intro hx i hi
      change i ∈ s at hi
      have him : emb i ∈ s.map emb := Finset.mem_map.mpr ⟨i, hi, rfl⟩
      have him' : emb i ∈ (s.map emb : Set ℕ) := by simpa using him
      have hxi := hx (emb i) him'
      simpa [oneSidedShift, t', emb] using hxi
  rw [MeasureTheory.Measure.map_apply hshift_meas
    (MeasurableSet.pi s.countable_toSet (by simpa using ht))]
  rw [hpre]
  change (MeasureTheory.Measure.infinitePi
    (fun _ : ℕ => alphabetProbabilityMeasure k p)) (Set.pi (s.map emb) t') = _
  rw [MeasureTheory.Measure.infinitePi_pi]
  · simpa [t', emb] using
      (Finset.prod_map s emb (fun i => alphabetProbabilityMeasure k p (t' i)))
  · intro j hj
    simp only [t']
    exact ht (j - 1)

theorem oneSidedBernoulliExampleSystem_mps
    (k : ℕ) (p : Fin k -> ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    IsMeasurePreservingSystem (oneSidedBernoulliSystem k p) := by
  letI : MeasureTheory.IsProbabilityMeasure (alphabetProbabilityMeasure k p) :=
    alphabetProbabilityMeasure_isProbabilityMeasure k p hp hsum
  constructor
  · change MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.infinitePi (fun _ : ℕ => alphabetProbabilityMeasure k p))
    infer_instance
  · exact oneSidedBernoulliShift_measurePreserving k p hp hsum

theorem oneSidedBernoulli_cylinder
    (k : ℕ) (n : ℕ) (a : Fin (n + 1) -> Fin k)
    (p : Fin k -> ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (oneSidedBernoulliMeasure k p)
      {x : ℕ -> Fin k | ∀ i : Fin (n + 1), x i = a i} =
      ENNReal.ofReal (∏ i, p (a i)) := by
  letI : MeasureTheory.IsProbabilityMeasure (alphabetProbabilityMeasure k p) :=
    alphabetProbabilityMeasure_isProbabilityMeasure k p hp hsum
  let emb : Fin (n + 1) ↪ ℕ :=
    ⟨fun i => i, by
      intro i j hij
      exact Fin.ext hij⟩
  let s : Finset ℕ := Finset.univ.map emb
  let e0 : Fin (n + 1) → {j // j ∈ s} := fun i =>
    ⟨emb i, by simp [s]⟩
  have he0 : Function.Bijective e0 := by
    constructor
    · intro i j hij
      apply emb.injective
      exact congrArg Subtype.val hij
    · intro j
      have hj : j.1 ∈ s := j.2
      change j.1 ∈ Finset.univ.map emb at hj
      rcases Finset.mem_map.1 hj with ⟨i, hi, hije⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hije
  let e : Fin (n + 1) ≃ {j // j ∈ s} := Equiv.ofBijective e0 he0
  let t : ℕ → Set (Fin k) := fun j =>
    if h : j ∈ s then {a (e.symm ⟨j, h⟩)} else Set.univ
  have hC : {x : ℕ -> Fin k | ∀ i : Fin (n + 1), x i = a i} = Set.pi s t := by
    ext x
    constructor
    · intro hx j hj
      change j ∈ Finset.univ.map emb at hj
      rcases Finset.mem_map.1 hj with ⟨i, hi, hije⟩
      have hi_s : emb i ∈ s := by simp [s]
      have hsub : (⟨emb i, hi_s⟩ : {j // j ∈ s}) = e i := by
        apply Subtype.ext
        rfl
      have he : e.symm ⟨emb i, hi_s⟩ = i := by
        rw [hsub, e.symm_apply_apply]
      rw [hije.symm]
      rw [show t (emb i) = ({a i} : Set (Fin k)) by simp [t, hi_s, he]]
      exact Set.mem_singleton_iff.mpr (hx i)
    · intro hx i
      have hi : emb i ∈ s := by simp [s]
      have hxi := hx (emb i) hi
      have he : e.symm ⟨emb i, hi⟩ = i := by
        have hsub : (⟨emb i, hi⟩ : {j // j ∈ s}) = e i := by
          apply Subtype.ext
          rfl
        rw [hsub, e.symm_apply_apply]
      have htval : t (emb i) = ({a i} : Set (Fin k)) := by
        simp [t, hi, he]
      rw [htval] at hxi
      exact Set.mem_singleton_iff.mp hxi
  change (MeasureTheory.Measure.infinitePi
    (fun _ : ℕ => alphabetProbabilityMeasure k p)) _ = _
  rw [hC, MeasureTheory.Measure.infinitePi_pi]
  · rw [show s = Finset.univ.map emb by rfl, Finset.prod_map]
    have htmap : ∀ i : Fin (n + 1),
        (alphabetProbabilityMeasure k p) (t (emb i)) =
          ENNReal.ofReal (p (a i)) := by
      intro i
      have hi : emb i ∈ s := by simp [s]
      have hsub : (⟨emb i, hi⟩ : {j // j ∈ s}) = e i := by
        apply Subtype.ext
        rfl
      have he : e.symm ⟨emb i, hi⟩ = i := by
        rw [hsub, e.symm_apply_apply]
      rw [show t (emb i) = ({a i} : Set (Fin k)) by simp [t, hi, he]]
      exact alphabetProbabilityMeasure_singleton k p (a i)
    simp_rw [htmap]
    rw [← ENNReal.ofReal_prod_of_nonneg]
    exact fun i hi => hp (a i)
  · intro j hj
    simp [t, hj]

private theorem liftedOneSidedBernoulliSystem_mps
    (k : ℕ) (p : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    IsMeasurePreservingSystem (liftedOneSidedBernoulliSystem k p) := by
  let e := MeasurableEquiv.ulift (α := OneSidedSymbolicSpace k)
  let B := oneSidedBernoulliSystem k p
  let L := liftedOneSidedBernoulliSystem k p
  have hB : IsMeasurePreservingSystem B :=
    oneSidedBernoulliExampleSystem_mps k p hp hsum
  have hup : MeasureTheory.MeasurePreserving e.symm B.μ L.μ :=
    ⟨e.symm.measurable, rfl⟩
  have hdn : MeasureTheory.MeasurePreserving e L.μ B.μ := by
    refine ⟨e.measurable, ?_⟩
    change MeasureTheory.Measure.map e
      (MeasureTheory.Measure.map e.symm (oneSidedBernoulliMeasure k p)) =
        oneSidedBernoulliMeasure k p
    rw [MeasureTheory.Measure.map_map e.measurable e.symm.measurable]
    simpa [e] using (MeasureTheory.Measure.map_id :
      MeasureTheory.Measure.map (id : OneSidedSymbolicSpace k → OneSidedSymbolicSpace k)
        (oneSidedBernoulliMeasure k p) = oneSidedBernoulliMeasure k p)
  constructor
  · constructor
    change MeasureTheory.Measure.map e.symm B.μ Set.univ = 1
    rw [MeasureTheory.Measure.map_apply e.symm.measurable MeasurableSet.univ]
    exact hB.1.measure_univ
  · change MeasureTheory.MeasurePreserving
      (fun x : ULift (OneSidedSymbolicSpace k) =>
        e.symm (oneSidedShift (e x))) L.μ L.μ
    exact hup.comp (hB.2.comp hdn)

private theorem liftedOneSidedBernoulliSystem_semantics
    (k : ℕ) (p : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    IsOneSidedBernoulliShiftWith (liftedOneSidedBernoulliSystem k p) k p := by
  let e := MeasurableEquiv.ulift (α := OneSidedSymbolicSpace k)
  refine ⟨liftedOneSidedBernoulliSystem_mps k p hp hsum,
    e.toEquiv, e.measurable, e.symm.measurable, hp, hsum, ?_, ?_⟩
  · intro x n
    rfl
  · intro n a
    let C : Set (ULift (OneSidedSymbolicSpace k)) :=
      {x | ∀ i : Fin (n + 1), e x i = a i}
    have hC : MeasurableSet C := by
      rw [show C = ⋂ i : Fin (n + 1), {x | e x (i : ℕ) = a i} by
        ext x
        simp [C]]
      apply MeasurableSet.iInter
      intro i
      exact measurableSet_eq_fun
        (measurable_pi_apply (i : ℕ) |>.comp e.measurable) measurable_const
    change MeasureTheory.Measure.map e.symm (oneSidedBernoulliMeasure k p) C = _
    rw [MeasureTheory.Measure.map_apply e.symm.measurable hC]
    change oneSidedBernoulliMeasure k p
      {x | ∀ i : Fin (n + 1), x i = a i} = _
    exact oneSidedBernoulli_cylinder k n a p hp hsum

private theorem liftedOneSidedMarkovSystem_semantics
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    IsOneSidedMarkovShiftWith
      (liftedSystem.{z} (oneSidedMarkovSystem k p P hP hPsum)) k p P := by
  let B := oneSidedMarkovSystem k p P hP hPsum
  let e := MeasurableEquiv.ulift (α := ℕ → Fin k)
  refine ⟨liftedSystem_mps B
      (oneSidedMarkovSystem_mps k p P hp hpsum hP hPsum hstationary),
    e.toEquiv, e.measurable, e.symm.measurable, ?_, hp, hpsum, hP, hPsum,
    hstationary, ?_⟩
  · intro x n
    rfl
  · intro n a
    let C : Set (ULift.{z} (ℕ → Fin k)) :=
      {x | ∀ i : Fin (n + 1), e x i = a i}
    have hC : MeasurableSet C := by
      rw [show C = ⋂ i : Fin (n + 1), {x | e x (i : ℕ) = a i} by
        ext x
        simp [C]]
      apply MeasurableSet.iInter
      intro i
      exact measurableSet_eq_fun
        (measurable_pi_apply (i : ℕ) |>.comp e.measurable) measurable_const
    change MeasureTheory.Measure.map e.symm
      (oneSidedMarkovMeasure k p P hP hPsum) C = _
    rw [MeasureTheory.Measure.map_apply e.symm.measurable hC]
    change oneSidedMarkovMeasure k p P hP hPsum
      {x | ∀ i : Fin (n + 1), x i = a i} = _
    exact oneSidedMarkovMeasure_prefix k p P hp hpsum hP hPsum n a

private theorem liftedTwoSidedMarkovSystem_semantics
    (k : ℕ) (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    IsTwoSidedMarkovShiftWith
      (liftedSystem.{z}
        (twoSidedMarkovSystem k p P hp hpsum hP hPsum hstationary)) k p P := by
  let B := twoSidedMarkovSystem k p P hp hpsum hP hPsum hstationary
  let e := MeasurableEquiv.ulift (α := ℤ → Fin k)
  refine ⟨liftedSystem_mps B
      (twoSidedMarkovSystem_mps k p P hp hpsum hP hPsum hstationary),
    e.toEquiv, e.measurable, e.symm.measurable, ?_, hp, hpsum, hP, hPsum,
    hstationary, ?_⟩
  · intro x n
    rfl
  · intro n a
    let C : Set (ULift.{z} (ℤ → Fin k)) :=
      {x | ∀ i : Fin (n + 1), e x (i : ℤ) = a i}
    have hC : MeasurableSet C := by
      rw [show C = ⋂ i : Fin (n + 1), {x | e x (i : ℤ) = a i} by
        ext x
        simp [C]]
      apply MeasurableSet.iInter
      intro i
      exact measurableSet_eq_fun
        (measurable_pi_apply (i : ℤ) |>.comp e.measurable) measurable_const
    change MeasureTheory.Measure.map e.symm
      (twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary) C = _
    rw [MeasureTheory.Measure.map_apply e.symm.measurable hC]
    change twoSidedMarkovMeasure k p P hp hpsum hP hPsum hstationary
      {x | ∀ i : Fin (n + 1), x (i : ℤ) = a i} = _
    exact twoSidedMarkovMeasure_nonnegative_prefix k p P hp hpsum hP hPsum
      hstationary n a

private theorem oneSidedCylinder_isClopen (k : ℕ) (hk : 2 ≤ k)
    (word : List (Fin k)) : IsClopen (oneSidedCylinder word) := by
  let z : Fin k := ⟨0, by omega⟩
  let x : ℕ → Fin k := fun n =>
    if h : n < word.length then word.get ⟨n, h⟩ else z
  have heq : oneSidedCylinder word = PiNat.cylinder x word.length := by
    ext y
    simp only [oneSidedCylinder, OneSidedWordOccursAt, Set.mem_setOf_eq,
      PiNat.cylinder]
    constructor
    · intro h i hi
      simpa [x, hi] using h ⟨i, hi⟩
    · intro h i
      simpa [x, i.isLt] using h i i.isLt
  rw [heq, PiNat.cylinder_eq_pi]
  constructor
  · exact isClosed_set_pi (A := fun _ : ℕ => Fin k)
      (fun i hi => isClosed_singleton)
  · exact isOpen_set_pi (A := fun _ : ℕ => Fin k)
      (Finset.range word.length).finite_toSet (fun i hi => isOpen_discrete _)

private theorem oneSidedCylinder_isTopologicalBasis (k : ℕ) (hk : 2 ≤ k) :
    TopologicalSpace.IsTopologicalBasis (oneSidedCylinderFamily k) := by
  have hfamily : oneSidedCylinderFamily k =
      {C : Set (ℕ → Fin k) | ∃ x n, C = PiNat.cylinder x n} := by
    ext C
    constructor
    · rintro ⟨word, rfl⟩
      let z : Fin k := ⟨0, by omega⟩
      let x : ℕ → Fin k := fun n =>
        if h : n < word.length then word.get ⟨n, h⟩ else z
      refine ⟨x, word.length, ?_⟩
      ext y
      simp only [oneSidedCylinder, OneSidedWordOccursAt, Set.mem_setOf_eq,
        PiNat.cylinder]
      constructor
      · intro h i hi
        simpa [x, hi] using h ⟨i, hi⟩
      · intro h i
        simpa [x, i.isLt] using h i i.isLt
    · rintro ⟨x, n, rfl⟩
      refine ⟨List.ofFn (fun i : Fin n => x i), ?_⟩
      ext y
      simp [oneSidedCylinder, OneSidedWordOccursAt, PiNat.cylinder]
      constructor
      · intro h i
        exact h i (by simpa using i.isLt)
      · intro h i hi
        let j : Fin (List.ofFn (fun q : Fin n => x q)).length :=
          ⟨i, by simpa using hi⟩
        exact h j
  rw [hfamily]
  exact PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => Fin k)

private theorem binarySeries_summable (x : OneSidedSymbolicSpace 2) :
    Summable (fun n : ℕ => ((x n).val : ℝ) / (2 : ℝ) ^ (n + 1)) := by
  apply (summable_geometric_two.comp_injective Nat.succ_injective).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hx : ((x n).val : ℝ) ≤ 1 := by
    exact_mod_cast (Nat.le_of_lt_succ (x n).isLt)
  have hden : 0 < (2 : ℝ) ^ (n + 1) := by positivity
  calc
    ((x n).val : ℝ) / 2 ^ (n + 1) ≤ 1 / 2 ^ (n + 1) :=
      (div_le_div_iff_of_pos_right hden).2 hx
    _ = (1 / 2 : ℝ) ^ (n + 1) := by norm_num [div_pow]

private theorem binaryCoding_eq_coe_tsum (x : OneSidedSymbolicSpace 2) :
    binaryCoding x =
      (((∑' n : ℕ, ((x n).val : ℝ) / (2 : ℝ) ^ (n + 1)) : ℝ) :
        AddCircle (1 : ℝ)) := by
  let q : ℝ →+ AddCircle (1 : ℝ) := QuotientAddGroup.mk' (AddSubgroup.zmultiples 1)
  have hmap := (binarySeries_summable x).hasSum.map q (AddCircle.continuous_mk' 1)
  unfold binaryCoding
  change (∑' n : ℕ, q (((x n).val : ℝ) / (2 : ℝ) ^ (n + 1))) = _
  exact hmap.tsum_eq

private theorem binaryCoding_shift (x : OneSidedSymbolicSpace 2) :
    binaryCoding (oneSidedShift x) = circleTimes 2 (binaryCoding x) := by
  rw [binaryCoding_eq_coe_tsum, binaryCoding_eq_coe_tsum]
  let f : ℕ → ℝ := fun n => ((x n).val : ℝ) / (2 : ℝ) ^ (n + 1)
  have hf : Summable f := binarySeries_summable x
  have hsplit := hf.sum_add_tsum_nat_add 1
  have hshift : (∑' n : ℕ, ((x (n + 1)).val : ℝ) / (2 : ℝ) ^ (n + 1)) =
      2 * (∑' n : ℕ, f (n + 1)) := by
    rw [← tsum_mul_left]
    congr 1
    funext n
    dsimp [f]
    field_simp
    ring
  unfold oneSidedShift circleTimes
  rw [hshift]
  have hreal : 2 * (∑' n : ℕ, f (n + 1)) =
      2 * (∑' n : ℕ, f n) - (x 0).val := by
    have hs : f 0 + (∑' n : ℕ, f (n + 1)) = ∑' n : ℕ, f n := by
      simpa using hsplit
    dsimp [f] at hs ⊢
    norm_num at hs
    linarith
  rw [hreal]
  rw [show (2 : ℝ) * (∑' n : ℕ, f n) =
      (∑' n : ℕ, f n) + (∑' n : ℕ, f n) by ring]
  change ((↑) : ℝ → AddCircle (1 : ℝ)) (∑' n : ℕ, f n) +
      ((↑) : ℝ → AddCircle (1 : ℝ)) (∑' n : ℕ, f n) -
      ((↑) : ℝ → AddCircle (1 : ℝ)) ((x 0).val : ℝ) =
    2 • ((↑) : ℝ → AddCircle (1 : ℝ)) (∑' n : ℕ, f n)
  have hdigit : (((x 0).val : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    have hv : (x 0).val = 0 ∨ (x 0).val = 1 := by omega
    rcases hv with hv | hv <;> simp [hv]
  rw [hdigit, sub_zero, two_nsmul]

/-- Source: Example 1.2.1, Chapter 1, Section 2. -/
theorem trivialSystemExample :
    ∃ S : MeasurePreservingSystemData, IsTrivialSystem S := by
  refine ⟨trivialExampleSystem, ?_, ?_, rfl⟩
  · constructor
    · change MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.dirac (PUnit.unit : trivialExampleSystem.X))
      infer_instance
    · change MeasureTheory.MeasurePreserving id
        trivialExampleSystem.μ trivialExampleSystem.μ
      exact MeasureTheory.MeasurePreserving.id _
  · ext A
    simp only [MeasurePreservingSystemData.𝓧, Set.mem_setOf_eq,
      MeasurableSpace.measurableSet_top, Set.mem_insert_iff,
      Set.mem_singleton_iff, true_iff]
    rcases A.eq_empty_or_nonempty with hA | ⟨a, ha⟩
    · exact Or.inr hA
    · left
      apply Set.eq_univ_of_forall
      intro x
      change PUnit at x a
      cases x
      cases a
      exact ha

/-- Source: Example 1.2.2, Chapter 1, Section 2. -/
theorem nPeriodicSystemExample (n : ℕ) (hn : 0 < n) :
    ∃ S : MeasurePreservingSystemData, IsNPeriodicSystem S n := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  refine ⟨nPeriodicExampleSystem n, ?_, ?_⟩
  · constructor
    · change MeasureTheory.IsProbabilityMeasure
        (ProbabilityTheory.uniformOn (Set.univ : Set (ULift (Fin n))))
      exact ProbabilityTheory.isProbabilityMeasure_uniformOn Set.finite_univ
        Set.univ_nonempty
    · change MeasureTheory.MeasurePreserving
        (fun x : ULift (Fin n) => ULift.up (x.down + 1))
        (ProbabilityTheory.uniformOn Set.univ)
        (ProbabilityTheory.uniformOn Set.univ)
      refine MeasureTheory.MeasurePreserving.mk (measurable_of_finite _) ?_
      ext A hA
      rw [MeasureTheory.Measure.map_apply (measurable_of_finite _) hA]
      rw [ProbabilityTheory.uniformOn_univ, ProbabilityTheory.uniformOn_univ]
      rw [MeasureTheory.Measure.count_apply (MeasurableSpace.measurableSet_top),
        MeasureTheory.Measure.count_apply (MeasurableSpace.measurableSet_top)]
      rw [Set.encard_preimage_of_bijective]
      exact Equiv.ulift.symm.bijective.comp
        ((Equiv.addRight (1 : Fin n)).bijective.comp Equiv.ulift.bijective)
  · refine ⟨Equiv.ulift, ?_⟩
    intro x
    change (x.down + 1 : Fin n).val = (x.down.val + 1) % n
    simp [Fin.add_def]

/--
Source: Example 1.2.3, Chapter 1, Section 2.
Circle rotations preserve Haar/Lebesgue measure; irrational rotations are
minimal, and `{nα mod 1}` is dense in `[0,1]`.
-/
theorem circleRotationSystemExample (α : ℝ) :
    ∃ S : MeasurePreservingSystemData,
      IsRotationSystem S α ∧
        (Irrational α ->
          IsTopologicallyMinimal
            (fun x : AddCircle (1 : ℝ) =>
              x + (α : AddCircle (1 : ℝ)))) := by
  refine ⟨circleRotationExampleSystem α, ?_, ?_⟩
  · constructor
    · constructor
      · change MeasureTheory.IsProbabilityMeasure
          (MeasureTheory.Measure.map (MeasurableEquiv.ulift.symm) AddCircle.haarAddCircle)
        constructor
        rw [MeasureTheory.Measure.map_apply (MeasurableEquiv.ulift.symm.measurable)
          MeasurableSet.univ]
        simp
      · let e := MeasurableEquiv.ulift (α := AddCircle (1 : ℝ))
        have hup : MeasureTheory.MeasurePreserving e.symm
            AddCircle.haarAddCircle (circleRotationExampleSystem α).μ := by
          exact MeasureTheory.MeasurePreserving.mk e.symm.measurable rfl
        have hdn : MeasureTheory.MeasurePreserving e
            (circleRotationExampleSystem α).μ AddCircle.haarAddCircle := by
          refine MeasureTheory.MeasurePreserving.mk e.measurable ?_
          change MeasureTheory.Measure.map e
            (MeasureTheory.Measure.map e.symm AddCircle.haarAddCircle) = _
          rw [MeasureTheory.Measure.map_map e.measurable e.symm.measurable]
          simpa [e] using (MeasureTheory.Measure.map_id :
            MeasureTheory.Measure.map id AddCircle.haarAddCircle = AddCircle.haarAddCircle)
        change MeasureTheory.MeasurePreserving
          (fun x : ULift (AddCircle (1 : ℝ)) =>
            e.symm (e x + (α : AddCircle (1 : ℝ))))
          (circleRotationExampleSystem α).μ (circleRotationExampleSystem α).μ
        exact hup.comp
          ((MeasureTheory.MeasurePreserving.add_right AddCircle.haarAddCircle
            (α : AddCircle (1 : ℝ)) (MeasureTheory.MeasurePreserving.id _)).comp hdn)
    · let e := MeasurableEquiv.ulift (α := AddCircle (1 : ℝ))
      change ∃ e' : ULift (AddCircle (1 : ℝ)) ≃ AddCircle (1 : ℝ),
        Measurable e' ∧ Measurable e'.symm ∧
          MeasureTheory.Measure.map e' (circleRotationExampleSystem α).μ =
            AddCircle.haarAddCircle ∧
          ∀ x : ULift (AddCircle (1 : ℝ)),
            e' ((circleRotationExampleSystem α).T x) =
              e' x + (α : AddCircle (1 : ℝ))
      refine ⟨e.toEquiv, e.measurable, e.symm.measurable, ?_, ?_⟩
      · change MeasureTheory.Measure.map e
          (circleRotationExampleSystem α).μ = _
        change MeasureTheory.Measure.map e
          (MeasureTheory.Measure.map e.symm AddCircle.haarAddCircle) = _
        rw [MeasureTheory.Measure.map_map e.measurable e.symm.measurable]
        simpa [e] using (MeasureTheory.Measure.map_id :
          MeasureTheory.Measure.map id AddCircle.haarAddCircle = AddCircle.haarAddCircle)
      · intro x
        rfl
  · intro hα x
    have hz : DenseRange (fun n : ℤ => n • (α : AddCircle (1 : ℝ))) := by
      exact (AddCircle.denseRange_zsmul_coe_iff (a := α) (p := 1)).2
        (by simpa using hα)
    have hn : DenseRange (fun n : ℕ => n • (α : AddCircle (1 : ℝ))) :=
      (denseRange_zsmul_iff_nsmul).1 hz
    have ht : DenseRange (fun y : AddCircle (1 : ℝ) => y + x) :=
      (Homeomorph.addRight x).surjective.denseRange
    have hc := ht.comp hn (Homeomorph.addRight x).continuous
    simpa [Function.comp_def, add_comm] using hc

/-- Source: Example 1.2.4, Chapter 1, Section 2. -/
theorem doublingMapAndNTimesMapExamples (n : ℕ) (hn : 2 ≤ n) :
    (∃ S : MeasurePreservingSystemData, IsDoublingIntervalSystem S) ∧
      IsMeasurePreservingSystem (circleTimesSystem n) ∧
      Continuous (circleTimes n) ∧
      ¬ Continuous doublingIntervalValue := by
  constructor
  · refine ⟨liftedCircleTimesSystem 2,
        liftedCircleTimesSystem_mps 2 (by omega), ?_⟩
    let u := MeasurableEquiv.ulift (α := AddCircle (1 : ℝ))
    let q : AddCircle (1 : ℝ) ≃ᵐ Set.Ioc (0 : ℝ) (0 + 1) :=
      AddCircle.measurableEquivIoc 1 0
    let e : ULift (AddCircle (1 : ℝ)) ≃ᵐ Set.Ioc (0 : ℝ) (0 + 1) :=
      u.trans q
    refine ⟨e.toEquiv, e.measurable, e.symm.measurable, ?_, ?_⟩
    · have hu : MeasureTheory.MeasurePreserving u
          (liftedCircleTimesSystem 2).μ AddCircle.haarAddCircle := by
        refine MeasureTheory.MeasurePreserving.mk u.measurable ?_
        change MeasureTheory.Measure.map u
          (MeasureTheory.Measure.map u.symm AddCircle.haarAddCircle) = _
        rw [MeasureTheory.Measure.map_map u.measurable u.symm.measurable]
        simpa [u] using (MeasureTheory.Measure.map_id :
          MeasureTheory.Measure.map id AddCircle.haarAddCircle = AddCircle.haarAddCircle)
      have hvol :
          (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
            AddCircle.haarAddCircle := by
        simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
      have hq : MeasureTheory.MeasurePreserving q AddCircle.haarAddCircle
          (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) := by
        rw [← hvol]
        simpa [q] using
          (AddCircle.measurePreserving_equivIoc (1 : ℝ) (a := 0))
      exact (hq.comp hu).map_eq
    · intro x
      have hq : (((q (u x) : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) :
          AddCircle (1 : ℝ)) = u x := by
        change q.symm (q (u x)) = u x
        exact q.symm_apply_apply _
      apply Subtype.ext
      simp [doublingIocMap, liftedCircleTimesSystem, e, u, q, circleTimes, hq]
  · constructor
    · constructor
      · change MeasureTheory.IsProbabilityMeasure
          (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle (1 : ℝ)))
        infer_instance
      · change MeasureTheory.MeasurePreserving
          (fun x : AddCircle (1 : ℝ) => n • x)
          AddCircle.haarAddCircle AddCircle.haarAddCircle
        have hnz : (n : ℤ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega) hn))
        simpa only [Int.ofNat_eq_natCast] using
          ((AddCircle.haarAddCircle :
            MeasureTheory.Measure (AddCircle (1 : ℝ))).measurePreserving_zsmul hnz)
    · constructor
      · change Continuous (fun x : AddCircle (1 : ℝ) => n • x)
        fun_prop
      · intro hcont
        let c : Set.Icc (0 : ℝ) 1 :=
          ⟨1 / 2, by constructor <;> norm_num⟩
        let x : ℕ → Set.Icc (0 : ℝ) 1 := fun m =>
          ⟨1 / 2 - 1 / ((m : ℝ) + 2), by
            constructor
            · have hm : (2 : ℝ) ≤ (m : ℝ) + 2 := by
                have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
                linarith
              have hi : 1 / ((m : ℝ) + 2) ≤ 1 / 2 := by
                exact one_div_le_one_div_of_le (by norm_num) hm
              linarith
            · have hi : 0 ≤ 1 / ((m : ℝ) + 2) := by positivity
              linarith⟩
        have hinv : Filter.Tendsto
            (fun m : ℕ => (1 / ((m : ℝ) + 2) : ℝ))
            Filter.atTop (nhds 0) := by
          have htop : Filter.Tendsto (fun m : ℕ => (m : ℝ) + 2)
              Filter.atTop Filter.atTop :=
            tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
          simpa only [one_div] using htop.inv_tendsto_atTop
        have hx : Filter.Tendsto x Filter.atTop (nhds c) := by
          rw [tendsto_subtype_rng]
          change Filter.Tendsto
            (fun m : ℕ => (1 / 2 : ℝ) - 1 / ((m : ℝ) + 2))
            Filter.atTop (nhds ((1 / 2 : ℝ)))
          convert hinv.const_sub (1 / 2 : ℝ) using 1 <;> norm_num
        have hout0 : Filter.Tendsto
            (fun m => doublingIntervalValue (x m)) Filter.atTop
            (nhds (doublingIntervalValue c)) := (hcont.tendsto c).comp hx
        have heq : (fun m => doublingIntervalValue (x m)) =
            (fun m : ℕ => 1 - 2 / ((m : ℝ) + 2)) := by
          funext m
          simp only [doublingIntervalValue, x]
          have hpos : 0 < 1 / ((m : ℝ) + 2) := by positivity
          rw [if_pos (by linarith)]
          ring
        have hout1 : Filter.Tendsto
            (fun m => doublingIntervalValue (x m)) Filter.atTop (nhds 1) := by
          rw [heq]
          have htwo : Filter.Tendsto
              (fun m : ℕ => 2 * (1 / ((m : ℝ) + 2)))
              Filter.atTop (nhds 0) := by
            simpa only [mul_zero] using hinv.const_mul 2
          convert htwo.const_sub 1 using 1 <;> ring
        have hz : doublingIntervalValue c = 0 := by
          simp [doublingIntervalValue, c]
        have hzeroone := tendsto_nhds_unique hout0 hout1
        rw [hz] at hzeroone
        norm_num at hzeroone

/--
Source: Example 1.2.5 and Problem 1.2.6, Chapter 1, Section 2.
Circle endomorphisms are measure-preserving systems; the source record also
states the Furstenberg `×2, ×3` conjecture as an open problem.
-/
theorem circleEndomorphismSystemExample (n : ℕ) (hn : 0 < n) :
    IsCirclePowerSystem (circleTimesSystem n) n := by
  constructor
  · constructor
    · change MeasureTheory.IsProbabilityMeasure
        (AddCircle.haarAddCircle :
          MeasureTheory.Measure (AddCircle (1 : ℝ)))
      infer_instance
    · change MeasureTheory.MeasurePreserving
        (fun x : AddCircle (1 : ℝ) => n • x)
        AddCircle.haarAddCircle AddCircle.haarAddCircle
      have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      simpa only [Int.ofNat_eq_natCast] using
        ((AddCircle.haarAddCircle :
          MeasureTheory.Measure (AddCircle (1 : ℝ))).measurePreserving_zsmul hnz)
  · refine ⟨Equiv.refl _, measurable_id, measurable_id, ?_, ?_⟩
    · exact MeasureTheory.Measure.map_id
    · intro x
      rfl

/--
Source: Problem 1.2.6 embedded in Example 1.2.5, Chapter 1, Section 2.
Furstenberg's `×2, ×3` conjecture: for multiplicatively independent natural
numbers `n,m`, an ergodic Borel probability measure on the circle invariant
under the semigroup generated by `×n` and `×m` is either Lebesgue measure or
uniformly supported on finitely many points.
-/
def furstenbergTimesTwoTimesThreeConjecture : Prop :=
  ∀ n m : ℕ, 1 < n -> 1 < m ->
    (∀ a b : ℕ, 0 < a -> 0 < b -> n ^ a ≠ m ^ b) ->
    ∀ μ : MeasureTheory.Measure (AddCircle (1 : ℝ)),
      MeasureTheory.IsProbabilityMeasure μ ->
      IsInvariantUnderCircleTimes μ n ->
      IsInvariantUnderCircleTimes μ m ->
      IsJointlyErgodicForCircleTimes μ n m ->
        μ = AddCircle.haarAddCircle ∨
          IsUniformMeasureOnFiniteCircleSet μ

/-- Source: Example 1.2.7, Chapter 1, Section 2. -/
theorem torusRotationSystemExample (k : ℕ) (θ : Fin k -> ℝ) :
    IsMeasurePreservingSystem (torusRotationSystem k θ) := by
  constructor
  · change MeasureTheory.IsProbabilityMeasure (torusHaarMeasure k)
    unfold torusHaarMeasure
    infer_instance
  · change MeasureTheory.MeasurePreserving
      (torusRotation k θ) (torusHaarMeasure k) (torusHaarMeasure k)
    unfold torusRotation torusHaarMeasure
    exact MeasureTheory.MeasurePreserving.add_right
      (MeasureTheory.Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle))
      (fun i => (θ i : AddCircle (1 : ℝ)))
      (MeasureTheory.MeasurePreserving.id
        (MeasureTheory.Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)))

private def triangularTorusHom (k : ℕ) : Torus k →+ Torus k where
  toFun x := triangularTorusMap k 0 x
  map_zero' := by
    cases k with
    | zero => rfl
    | succ n =>
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [triangularTorusMap]
  map_add' x y := by
    cases k with
    | zero => rfl
    | succ n =>
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [triangularTorusMap]
        · simp [triangularTorusMap]
          abel

private def triangularPreimageNat (k : ℕ) (y : Torus k) : ℕ → AddCircle (1 : ℝ)
  | 0 => if h : 0 < k then y ⟨0, h⟩ else 0
  | n + 1 => if h : n + 1 < k then y ⟨n + 1, h⟩ - triangularPreimageNat k y n else 0

private def triangularTorusPreimage (k : ℕ) (y : Torus k) : Torus k :=
  fun i => triangularPreimageNat k y i

private theorem triangularTorusHom_surjective (k : ℕ) :
    Function.Surjective (triangularTorusHom k) := by
  intro y
  refine ⟨triangularTorusPreimage k y, ?_⟩
  cases k with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [triangularTorusHom, triangularTorusMap, triangularTorusPreimage,
          triangularPreimageNat]
      · simp [triangularTorusHom, triangularTorusMap, triangularTorusPreimage,
          triangularPreimageNat]
        congr 1

private def subtractOne (x : BinarySequence) : BinarySequence :=
  fun n => if ∀ j < n, x j = 0 then x n + 1 else x n

private theorem finTwo_add_one_add_one (a : Fin 2) : (a + 1) + 1 = a := by
  fin_cases a <;> decide

private theorem finTwo_add_one_eq_zero_iff (a : Fin 2) : a + 1 = 0 ↔ a = 1 := by
  fin_cases a <;> decide

private theorem finTwo_add_one_eq_one_iff (a : Fin 2) : a + 1 = 1 ↔ a = 0 := by
  fin_cases a <;> decide

private theorem addingOne_lower_zero_iff (x : BinarySequence) (n : ℕ) :
    (∀ j < n, addingOne x j = 0) ↔ ∀ j < n, x j = 1 := by
  constructor
  · intro h j hj
    induction j using Nat.strong_induction_on with
    | h j ih =>
        have hprior : ∀ i < j, x i = 1 := by
          intro i hi
          exact ih i hi (lt_trans hi hj)
        have ho := h j hj
        rw [addingOne, if_pos hprior] at ho
        exact (finTwo_add_one_eq_zero_iff (x j)).mp ho
  · intro h j hj
    have hprior : ∀ i < j, x i = 1 := by
      intro i hi
      exact h i (lt_trans hi hj)
    rw [addingOne, if_pos hprior]
    rw [finTwo_add_one_eq_zero_iff]
    exact h j hj

private theorem subtractOne_lower_one_iff (x : BinarySequence) (n : ℕ) :
    (∀ j < n, subtractOne x j = 1) ↔ ∀ j < n, x j = 0 := by
  constructor
  · intro h j hj
    induction j using Nat.strong_induction_on with
    | h j ih =>
        have hprior : ∀ i < j, x i = 0 := by
          intro i hi
          exact ih i hi (lt_trans hi hj)
        have ho := h j hj
        rw [subtractOne, if_pos hprior] at ho
        exact (finTwo_add_one_eq_one_iff (x j)).mp ho
  · intro h j hj
    have hprior : ∀ i < j, x i = 0 := by
      intro i hi
      exact h i (lt_trans hi hj)
    rw [subtractOne, if_pos hprior]
    rw [finTwo_add_one_eq_one_iff]
    exact h j hj

private theorem subtractOne_addingOne (x : BinarySequence) :
    subtractOne (addingOne x) = x := by
  funext n
  by_cases h : ∀ j < n, x j = 1
  · rw [subtractOne, if_pos ((addingOne_lower_zero_iff x n).2 h)]
    rw [addingOne, if_pos h, finTwo_add_one_add_one]
  · rw [subtractOne, if_neg (by simpa [addingOne_lower_zero_iff] using h)]
    rw [addingOne, if_neg h]

private theorem addingOne_subtractOne (x : BinarySequence) :
    addingOne (subtractOne x) = x := by
  funext n
  by_cases h : ∀ j < n, x j = 0
  · rw [addingOne, if_pos ((subtractOne_lower_one_iff x n).2 h)]
    rw [subtractOne, if_pos h, finTwo_add_one_add_one]
  · rw [addingOne, if_neg (by simpa [subtractOne_lower_one_iff] using h)]
    rw [subtractOne, if_neg h]

private theorem addingOne_bijective : Function.Bijective addingOne := by
  exact Function.bijective_iff_has_inverse.mpr
    ⟨subtractOne, subtractOne_addingOne, addingOne_subtractOne⟩

private def carrySet (n : ℕ) : Set BinarySequence :=
  {x | ∀ j < n, x j = 1}

private theorem carrySet_eq_pi (n : ℕ) :
    carrySet n = Set.pi (Finset.range n : Set ℕ) (fun _ => ({1} : Set (Fin 2))) := by
  ext x
  simp [carrySet]

private theorem carrySet_isClopen (n : ℕ) : IsClopen (carrySet n) := by
  rw [carrySet_eq_pi]
  constructor
  · exact isClosed_set_pi (fun i hi => isClosed_singleton)
  · exact isOpen_set_pi (Finset.range n).finite_toSet
      (fun i hi => isOpen_discrete _)

private theorem addingOne_continuous : Continuous addingOne := by
  apply continuous_pi
  intro n
  unfold addingOne
  apply Continuous.if
  · intro x hx
    rw [show {x : BinarySequence | ∀ j < n, x j = 1} = carrySet n by rfl,
      (carrySet_isClopen n).frontier_eq] at hx
    simp at hx
  · fun_prop
  · exact continuous_apply n

private theorem addingOne_prefix_congr {x y : BinarySequence} {n : ℕ}
    (h : ∀ i < n, x i = y i) : ∀ i < n, addingOne x i = addingOne y i := by
  intro i hi
  unfold addingOne
  have hp : (∀ j < i, x j = 1) ↔ ∀ j < i, y j = 1 := by
    constructor <;> intro hj j hjlt
    · rw [← h j (lt_trans hjlt hi)]
      exact hj j hjlt
    · rw [h j (lt_trans hjlt hi)]
      exact hj j hjlt
  by_cases hx : ∀ j < i, x j = 1
  · rw [if_pos hx, if_pos (hp.mp hx), h i hi]
  · rw [if_neg hx, if_neg (by simpa [hp] using hx), h i hi]

private theorem subtractOne_prefix_congr {x y : BinarySequence} {n : ℕ}
    (h : ∀ i < n, x i = y i) : ∀ i < n, subtractOne x i = subtractOne y i := by
  intro i hi
  unfold subtractOne
  have hp : (∀ j < i, x j = 0) ↔ ∀ j < i, y j = 0 := by
    constructor <;> intro hj j hjlt
    · rw [← h j (lt_trans hjlt hi)]
      exact hj j hjlt
    · rw [h j (lt_trans hjlt hi)]
      exact hj j hjlt
  by_cases hx : ∀ j < i, x j = 0
  · rw [if_pos hx, if_pos (hp.mp hx), h i hi]
  · rw [if_neg hx, if_neg (by simpa [hp] using hx), h i hi]

private theorem addingOne_preimage_cylinder (y : BinarySequence) (n : ℕ) :
    addingOne ⁻¹' PiNat.cylinder y n = PiNat.cylinder (subtractOne y) n := by
  ext x
  simp only [Set.mem_preimage, PiNat.cylinder]
  constructor
  · intro h i hi
    calc
      x i = subtractOne (addingOne x) i := by
        rw [subtractOne_addingOne]
      _ = subtractOne y i := subtractOne_prefix_congr h i hi
  · intro h i hi
    calc
      addingOne x i = addingOne (subtractOne y) i := addingOne_prefix_congr h i hi
      _ = y i := by rw [addingOne_subtractOne]

private theorem binaryProductMeasure_cylinder (x : BinarySequence) (n : ℕ) :
    binaryProductMeasure (PiNat.cylinder x n) = (2 : ENNReal)⁻¹ ^ n := by
  rw [binaryProductMeasure, PiNat.cylinder_eq_pi,
    MeasureTheory.Measure.infinitePi_pi]
  · simp [ProbabilityTheory.uniformOn_univ]
  · intro i hi
    exact MeasurableSet.singleton (x i)

private def initialBinaryCylinders : Set (Set BinarySequence) :=
  {C | ∃ x n, C = PiNat.cylinder x n}

private theorem initialBinaryCylinders_basis :
    TopologicalSpace.IsTopologicalBasis initialBinaryCylinders := by
  exact PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => Fin 2)

private theorem initialBinaryCylinders_eq_words :
    initialBinaryCylinders = oneSidedCylinderFamily 2 := by
  ext C
  constructor
  · rintro ⟨x, n, rfl⟩
    refine ⟨List.ofFn (fun i : Fin n => x i), ?_⟩
    ext y
    simp [oneSidedCylinder, OneSidedWordOccursAt, PiNat.cylinder]
    constructor
    · intro h i
      exact h i (by simpa using i.isLt)
    · intro h i hi
      let j : Fin (List.ofFn (fun q : Fin n => x q)).length :=
        ⟨i, by simpa using hi⟩
      exact h j
  · rintro ⟨word, rfl⟩
    let x : BinarySequence := fun n =>
      if h : n < word.length then word.get ⟨n, h⟩ else 0
    refine ⟨x, word.length, ?_⟩
    ext y
    simp only [oneSidedCylinder, OneSidedWordOccursAt, Set.mem_setOf_eq,
      PiNat.cylinder]
    constructor
    · intro h i hi
      simpa [x, hi] using h ⟨i, hi⟩
    · intro h i
      simpa [x, i.isLt] using h i i.isLt

private theorem initialBinaryCylinders_countable :
    initialBinaryCylinders.Countable := by
  rw [initialBinaryCylinders_eq_words]
  have heq : oneSidedCylinderFamily 2 =
      Set.range (fun word : List (Fin 2) => oneSidedCylinder word) := by
    ext C
    simp only [oneSidedCylinderFamily, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨word, rfl⟩
      exact ⟨word, rfl⟩
    · rintro ⟨word, rfl⟩
      exact ⟨word, rfl⟩
  rw [heq]
  exact Set.countable_range _

private theorem binary_measurableSpace_generate :
    (inferInstance : MeasurableSpace BinarySequence) =
      MeasurableSpace.generateFrom initialBinaryCylinders := by
  apply le_antisymm
  · rw [MeasurableSpace.pi_eq_generateFrom_projections]
    apply MeasurableSpace.generateFrom_le
    rintro u ⟨i, A, hA, hu⟩
    subst u
    have heval : Continuous (fun x : BinarySequence => x i) := continuous_apply i
    have hopen : IsOpen ((fun x : BinarySequence => x i) ⁻¹' A) :=
      heval.isOpen_preimage A (isOpen_discrete A)
    rcases initialBinaryCylinders_basis.open_eq_sUnion hopen with ⟨S, hS, heq⟩
    have hgen : MeasurableSpace.GenerateMeasurable initialBinaryCylinders
        ((fun x : BinarySequence => x i) ⁻¹' A) := by
      rw [heq]
      exact @MeasurableSet.sUnion BinarySequence
        (MeasurableSpace.generateFrom initialBinaryCylinders) S
        (initialBinaryCylinders_countable.mono hS)
        (fun s hs => MeasurableSpace.GenerateMeasurable.basic s (hS hs))
    simpa only [Function.eval_apply] using hgen
  · apply MeasurableSpace.generateFrom_le
    rintro C ⟨x, n, rfl⟩
    rw [PiNat.cylinder_eq_pi]
    exact MeasurableSet.pi (Finset.range n).countable_toSet
      (fun i hi => MeasurableSet.singleton (x i))

private theorem initialBinaryCylinders_piSystem :
    IsPiSystem initialBinaryCylinders := by
  rintro A ⟨x, n, rfl⟩ B ⟨y, m, rfl⟩ hne
  rcases hne with ⟨z, hzA, hzB⟩
  refine ⟨z, max n m, ?_⟩
  ext w
  simp only [Set.mem_inter_iff, PiNat.cylinder] at hzA hzB ⊢
  constructor
  · rintro ⟨hwx, hwy⟩ i hi
    by_cases hin : i < n
    · calc w i = x i := hwx i hin
           _ = z i := (hzA i hin).symm
    · have him : i < m := by omega
      calc w i = y i := hwy i him
           _ = z i := (hzB i him).symm
  · intro hw
    constructor
    · intro i hi
      calc w i = z i := hw i (lt_of_lt_of_le hi (Nat.le_max_left n m))
           _ = x i := hzA i hi
    · intro i hi
      calc w i = z i := hw i (lt_of_lt_of_le hi (Nat.le_max_right n m))
           _ = y i := hzB i hi

private theorem fairBernoulli_cylinder (x : BinarySequence) (n : ℕ) :
    oneSidedBernoulliMeasure 2 (fun _ => (1 / 2 : ℝ))
        (PiNat.cylinder x n) = (2 : ENNReal)⁻¹ ^ n := by
  let p : Fin 2 → ℝ := fun _ => 1 / 2
  have hp : ∀ i, 0 ≤ p i := by intro i; norm_num [p]
  have hsum : ∑ i, p i = 1 := by
    simp [p, Fin.sum_univ_two]
  letI : MeasureTheory.IsProbabilityMeasure (alphabetProbabilityMeasure 2 p) :=
    alphabetProbabilityMeasure_isProbabilityMeasure 2 p hp hsum
  rw [oneSidedBernoulliMeasure, PiNat.cylinder_eq_pi,
    MeasureTheory.Measure.infinitePi_pi]
  · simp_rw [alphabetProbabilityMeasure_singleton]
    simp [p, Finset.prod_const, ENNReal.ofReal_div_of_pos]
  · intro i hi
    exact MeasurableSet.singleton (x i)

private theorem circleBinaryDigits_map_fairBernoulli :
    MeasureTheory.Measure.map circleBinaryDigits AddCircle.haarAddCircle =
      oneSidedBernoulliMeasure 2 (fun _ => (1 / 2 : ℝ)) := by
  apply MeasureTheory.Measure.ext_of_generateFrom_of_cover_subset
      binary_measurableSpace_generate initialBinaryCylinders_piSystem
      (T := {Set.univ})
  · intro A hA
    simp only [Set.mem_singleton_iff] at hA
    subst A
    refine ⟨fun _ => 0, 0, ?_⟩
    ext x
    simp [PiNat.cylinder]
  · exact Set.countable_singleton Set.univ
  · simp
  · intro A hA
    simp only [Set.mem_singleton_iff] at hA
    subst A
    rw [MeasureTheory.Measure.map_apply circleBinaryDigits_measurable MeasurableSet.univ]
    simp
  · rintro C ⟨x, n, rfl⟩
    rw [MeasureTheory.Measure.map_apply circleBinaryDigits_measurable
      ((initialBinaryCylinders_basis.isOpen ⟨x, n, rfl⟩).measurableSet)]
    rw [circleBinaryCylinder_measure, fairBernoulli_cylinder]

private theorem binaryCoding_map_fairBernoulli :
    MeasureTheory.Measure.map binaryCoding
        (oneSidedBernoulliMeasure 2 (fun _ => (1 / 2 : ℝ))) =
      AddCircle.haarAddCircle := by
  rw [← circleBinaryDigits_map_fairBernoulli,
    MeasureTheory.Measure.map_map binaryCoding_continuous.measurable
      circleBinaryDigits_measurable]
  rw [show binaryCoding ∘ circleBinaryDigits = id by
    funext y
    exact binaryCoding_circleBinaryDigits y]
  exact MeasureTheory.Measure.map_id

private theorem measurePreservingOnFullUniv
    (S₁ S₂ : MeasurePreservingSystemData)
    (hS₁ : IsMeasurePreservingSystem S₁)
    (hS₂ : IsMeasurePreservingSystem S₂)
    (φ : S₁.X → S₂.X)
    (hφ : MeasureTheory.MeasurePreserving φ S₁.μ S₂.μ) :
    IsMeasurePreservingOnFullSets S₁ S₂ Set.univ Set.univ φ := by
  refine ⟨MeasurableSet.univ, MeasurableSet.univ,
    hS₁.1.measure_univ, hS₂.1.measure_univ, by simp, ?_⟩
  intro B hB
  constructor
  · simpa using hφ.measurable (hB.inter MeasurableSet.univ)
  · simpa using hφ.measure_preimage hB.nullMeasurableSet

private def binaryCanonicalSet : Set BinarySequence :=
  {x | circleBinaryDigits (binaryCoding x) = x}

private theorem binaryCanonicalSet_measurable : MeasurableSet binaryCanonicalSet := by
  exact measurableSet_eq_fun
    (circleBinaryDigits_measurable.comp binaryCoding_continuous.measurable)
    measurable_id

private theorem fairBinaryFactor :
    IsFactorMap
      (oneSidedBernoulliSystem 2 (fun _ => (1 / 2 : ℝ)))
      (circleTimesSystem 2) binaryCoding := by
  let S := oneSidedBernoulliSystem 2 (fun _ => (1 / 2 : ℝ))
  let C := circleTimesSystem 2
  have hp : ∀ i : Fin 2, 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hsum : ∑ _i : Fin 2, (1 / 2 : ℝ) = 1 := by simp
  have hS : IsMeasurePreservingSystem S :=
    oneSidedBernoulliExampleSystem_mps 2 _ hp hsum
  have hC : IsMeasurePreservingSystem C :=
    (doublingMapAndNTimesMapExamples.{0} 2 (by omega)).2.1
  have hφ : MeasureTheory.MeasurePreserving binaryCoding S.μ C.μ := by
    exact ⟨binaryCoding_continuous.measurable, binaryCoding_map_fairBernoulli⟩
  refine ⟨hS, hC, Set.univ, Set.univ, hS.1.measure_univ,
    hC.1.measure_univ, by simp, by simp,
    measurePreservingOnFullUniv S C hS hC binaryCoding hφ, ?_⟩
  intro x hx
  exact binaryCoding_shift x

private theorem fairBinaryIsomorphism :
    IsIsomorphicSystems
      (oneSidedBernoulliSystem 2 (fun _ => (1 / 2 : ℝ)))
      (circleTimesSystem 2) := by
  let S := oneSidedBernoulliSystem 2 (fun _ => (1 / 2 : ℝ))
  let C := circleTimesSystem 2
  have hp : ∀ i : Fin 2, 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hsum : ∑ _i : Fin 2, (1 / 2 : ℝ) = 1 := by simp
  have hS : IsMeasurePreservingSystem S :=
    oneSidedBernoulliExampleSystem_mps 2 _ hp hsum
  have hC : IsMeasurePreservingSystem C :=
    (doublingMapAndNTimesMapExamples.{0} 2 (by omega)).2.1
  have hφ : MeasureTheory.MeasurePreserving binaryCoding S.μ C.μ := by
    exact ⟨binaryCoding_continuous.measurable, binaryCoding_map_fairBernoulli⟩
  have hψ : MeasureTheory.MeasurePreserving circleBinaryDigits C.μ S.μ := by
    exact ⟨circleBinaryDigits_measurable, circleBinaryDigits_map_fairBernoulli⟩
  have hM : S.μ binaryCanonicalSet = 1 := by
    change oneSidedBernoulliMeasure 2 (fun _ => (1 / 2 : ℝ))
      binaryCanonicalSet = 1
    rw [← circleBinaryDigits_map_fairBernoulli,
      MeasureTheory.Measure.map_apply circleBinaryDigits_measurable
        binaryCanonicalSet_measurable]
    have hpre : circleBinaryDigits ⁻¹' binaryCanonicalSet = Set.univ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      change circleBinaryDigits (binaryCoding (circleBinaryDigits y)) =
        circleBinaryDigits y
      rw [binaryCoding_circleBinaryDigits]
    rw [hpre]
    exact hC.1.measure_univ
  have hMinv : ∀ x ∈ binaryCanonicalSet, oneSidedShift x ∈ binaryCanonicalSet := by
    intro x hx
    change circleBinaryDigits (binaryCoding (oneSidedShift x)) = oneSidedShift x
    rw [binaryCoding_shift]
    funext n
    rw [circleBinaryDigits_dynamics]
    exact congrFun hx (n + 1)
  have hforward : IsMeasurePreservingOnFullSets S C
      binaryCanonicalSet Set.univ binaryCoding := by
    refine ⟨binaryCanonicalSet_measurable, (by
        change MeasurableSet (Set.univ : Set (AddCircle (1 : ℝ)))
        exact MeasurableSet.univ), hM,
      hC.1.measure_univ, by simp, ?_⟩
    have hMfin : S.μ binaryCanonicalSet ≠ ⊤ := by rw [hM]; norm_num
    have hSuniv : S.μ Set.univ = 1 := by
      change oneSidedBernoulliMeasure 2 (fun _ => (1 / 2 : ℝ)) Set.univ = 1
      exact hS.1.measure_univ
    have hcomp : S.μ binaryCanonicalSetᶜ = 0 := by
      calc
        S.μ binaryCanonicalSetᶜ = S.μ Set.univ - S.μ binaryCanonicalSet :=
          MeasureTheory.measure_compl binaryCanonicalSet_measurable hMfin
        _ = 0 := by rw [hSuniv, hM]; simp
    have hae : ∀ᵐ x ∂S.μ, x ∈ binaryCanonicalSet := by
      apply MeasureTheory.ae_iff.mpr
      change S.μ binaryCanonicalSetᶜ = 0
      exact hcomp
    intro B hB
    change MeasurableSet B at hB
    constructor
    · exact binaryCanonicalSet_measurable.inter
        (hφ.measurable (hB.inter MeasurableSet.univ))
    · calc
        S.μ (binaryCanonicalSet ∩ binaryCoding ⁻¹' (B ∩ Set.univ)) =
            S.μ (binaryCoding ⁻¹' B) := by
          apply MeasureTheory.measure_congr
          filter_upwards [hae] with x hx
          apply propext
          constructor
          · intro h
            exact h.2.1
          · intro h
            exact ⟨hx, h, Set.mem_univ _⟩
        _ = C.μ B := hφ.measure_preimage hB.nullMeasurableSet
        _ = C.μ (B ∩ Set.univ) := by simp
  have hbackward : IsMeasurePreservingOnFullSets C S
      Set.univ binaryCanonicalSet circleBinaryDigits := by
    refine ⟨(by
        change MeasurableSet (Set.univ : Set (AddCircle (1 : ℝ)))
        exact MeasurableSet.univ), binaryCanonicalSet_measurable,
      hC.1.measure_univ, hM, ?_, ?_⟩
    · intro y hy
      change circleBinaryDigits (binaryCoding (circleBinaryDigits y)) =
        circleBinaryDigits y
      rw [binaryCoding_circleBinaryDigits]
    · intro B hB
      change MeasurableSet B at hB
      constructor
      · simpa using hψ.measurable (hB.inter binaryCanonicalSet_measurable)
      · simpa using hψ.measure_preimage
          (hB.inter binaryCanonicalSet_measurable).nullMeasurableSet
  refine ⟨hS, hC, binaryCanonicalSet, Set.univ, binaryCoding,
    circleBinaryDigits, hM, hC.1.measure_univ, hMinv, by simp,
    hforward, hbackward, ?_, ?_⟩
  · intro x hx
    exact ⟨Set.mem_univ _, hx, binaryCoding_shift x⟩
  · intro y hy
    constructor
    · change circleBinaryDigits (binaryCoding (circleBinaryDigits y)) =
        circleBinaryDigits y
      rw [binaryCoding_circleBinaryDigits]
    constructor
    · exact binaryCoding_circleBinaryDigits y
    · funext n
      simpa [oneSidedShift] using circleBinaryDigits_dynamics y n

private theorem addingOne_measurePreserving :
    MeasureTheory.MeasurePreserving addingOne binaryProductMeasure binaryProductMeasure := by
  have hmeas : Measurable addingOne := addingOne_continuous.measurable
  refine MeasureTheory.MeasurePreserving.mk hmeas ?_
  apply MeasureTheory.Measure.ext_of_generateFrom_of_cover_subset
      binary_measurableSpace_generate initialBinaryCylinders_piSystem
      (T := {Set.univ})
  · intro A hA
    simp only [Set.mem_singleton_iff] at hA
    subst A
    refine ⟨fun _ => 0, 0, ?_⟩
    ext x
    simp [PiNat.cylinder]
  · exact Set.countable_singleton Set.univ
  · simp
  · intro A hA
    simp only [Set.mem_singleton_iff] at hA
    subst A
    rw [MeasureTheory.Measure.map_apply hmeas MeasurableSet.univ]
    haveI : MeasureTheory.IsProbabilityMeasure binaryProductMeasure := by
      unfold binaryProductMeasure
      infer_instance
    simp
  · rintro C ⟨x, n, rfl⟩
    rw [MeasureTheory.Measure.map_apply hmeas
      ((initialBinaryCylinders_basis.isOpen ⟨x, n, rfl⟩).measurableSet)]
    rw [addingOne_preimage_cylinder]
    rw [binaryProductMeasure_cylinder, binaryProductMeasure_cylinder]

/-- Source: Example 1.2.8, Chapter 1, Section 2. -/
theorem addingMachineExample :
    IsMeasurePreservingSystem addingMachineSystem ∧
      Continuous addingOne ∧ Function.Bijective addingOne := by
  exact ⟨⟨by
    change MeasureTheory.IsProbabilityMeasure binaryProductMeasure
    unfold binaryProductMeasure
    infer_instance, addingOne_measurePreserving⟩,
    addingOne_continuous, addingOne_bijective⟩

/-- Source: Example 1.2.9, Chapter 1, Section 2. -/
theorem compactGroupRotationExample
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
    (hG_metrizable : TopologicalSpace.MetrizableSpace G)
    (m : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure m]
    [MeasureTheory.Measure.IsHaarMeasure m] (a : G) :
    IsMeasurePreservingSystem (groupRotationSystem m a) ∧
      Continuous (groupRotation a) ∧ Function.Bijective (groupRotation a) := by
  constructor
  · constructor
    · change MeasureTheory.IsProbabilityMeasure m
      infer_instance
    · change MeasureTheory.MeasurePreserving (fun x : G => a * x) m m
      exact MeasureTheory.MeasurePreserving.mul_left m a
        (MeasureTheory.MeasurePreserving.id m)
  · exact ⟨(Homeomorph.mulLeft a).continuous, (Homeomorph.mulLeft a).bijective⟩

/--
Source: Example 1.2.10, Chapter 1, Section 2.
A surjective continuous endomorphism of a compact metrizable group preserves
Haar measure.
-/
theorem compactGroupEndomorphismExample
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
    (hG_metrizable : TopologicalSpace.MetrizableSpace G)
    (m : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure m]
    [MeasureTheory.Measure.IsHaarMeasure m] (A : G →* G)
    (hA_continuous : Continuous A) (hA_surjective : Function.Surjective A) :
    IsMeasurePreservingSystem (groupEndomorphismSystem m A) := by
  constructor
  · change MeasureTheory.IsProbabilityMeasure m
    infer_instance
  · change MeasureTheory.MeasurePreserving (A : G -> G) m m
    exact A.measurePreserving hA_continuous hA_surjective rfl

/-- Source: Example 1.2.11, Chapter 1, Section 2. -/
theorem affineSystemExample
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
    (hG_metrizable : TopologicalSpace.MetrizableSpace G)
    (m : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure m]
    [MeasureTheory.Measure.IsHaarMeasure m] (a : G) (A : G →* G)
    (hA_continuous : Continuous A) (hA_surjective : Function.Surjective A) :
    IsMeasurePreservingSystem (affineGroupSystem m a A) := by
  constructor
  · change MeasureTheory.IsProbabilityMeasure m
    infer_instance
  · change MeasureTheory.MeasurePreserving (fun x : G => a * A x) m m
    exact MeasureTheory.MeasurePreserving.mul_left m a
      (A.measurePreserving hA_continuous hA_surjective rfl)

/--
Source: Definition 1.2.12, Chapter 1, Section 2.
Skew-product systems and compact group extensions.
-/
def skewProductAndGroupExtensionDefinition (X : Type u) (Y : Type v) (Z : Type w)
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
    (S : Y -> Y) (φ : Y -> Z -> Z) (T : X -> X) : Prop :=
  IsSkewProductSystem X Y Z S φ T

/--
Source: Definition 1.2.12, Chapter 1, Section 2.
The group-extension specialization of a skew-product system.
-/
def groupExtensionDefinition (X : Type u) (Y : Type v) (G : Type w)
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TopologicalSpace.MetrizableSpace G]
    (S : Y -> Y) (φ : Y -> G) (T : X -> X) : Prop :=
  IsGroupExtensionSystem X Y G S φ T

/-- Source: Example 1.2.13, Chapter 1, Section 2. -/
theorem torusSkewProductExample (k : ℕ) (hk : 2 ≤ k) (α : ℝ) :
    IsMeasurePreservingSystem (triangularTorusSystem k α) := by
  constructor
  · change MeasureTheory.IsProbabilityMeasure (torusHaarMeasure k)
    unfold torusHaarMeasure
    infer_instance
  · change MeasureTheory.MeasurePreserving (triangularTorusMap k α)
      (torusHaarMeasure k) (torusHaarMeasure k)
    letI : MeasureTheory.Measure.IsAddHaarMeasure (torusHaarMeasure k) := by
      unfold torusHaarMeasure
      infer_instance
    have hhom : MeasureTheory.MeasurePreserving (triangularTorusHom k)
        (torusHaarMeasure k) (torusHaarMeasure k) := by
      apply AddMonoidHom.measurePreserving
      · cases k with
        | zero =>
            apply continuous_pi
            intro i
            exact Fin.elim0 i
        | succ n =>
            apply continuous_pi
            intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · simpa [triangularTorusHom, triangularTorusMap] using
                (continuous_apply (0 : Fin (n + 1)))
            · simpa [triangularTorusHom, triangularTorusMap] using
                (continuous_apply j.succ).add (continuous_apply j.castSucc)
      · exact triangularTorusHom_surjective k
      · rfl
    let a : Torus k := fun i =>
      if i.val = 0 then (α : AddCircle (1 : ℝ)) else 0
    have hadd := MeasureTheory.MeasurePreserving.add_right
      (torusHaarMeasure k) a hhom
    convert hadd using 1
    funext x i
    cases k with
    | zero => exact Fin.elim0 i
    | succ n =>
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [a, triangularTorusHom, triangularTorusMap, add_comm]
        · simp [a, triangularTorusHom, triangularTorusMap]

/--
Source: Example 1.2.14, Chapter 1, Section 2.
One-sided full shifts, subshifts, words, cylinders, Bernoulli measures, and the
factor map from the binary one-sided shift to the doubling map.
-/
theorem oneSidedShiftSystemExample (k : ℕ) (hk : 2 ≤ k)
    (p : Fin k -> ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    OneSidedShiftExampleSemantics k p := by
  unfold OneSidedShiftExampleSemantics
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨oneSidedBernoulliExampleSystem_mps k p hp hsum,
      Equiv.refl _, measurable_id, measurable_id, hp, hsum, ?_, ?_⟩
    · intro x n
      rfl
    · intro n a
      exact oneSidedBernoulli_cylinder k n a p hp hsum
  · exact ⟨inferInstance⟩
  · exact ⟨inferInstance⟩
  · unfold oneSidedShift
    apply continuous_pi
    intro n
    exact continuous_apply (n + 1)
  · intro y
    let z : Fin k := ⟨0, by omega⟩
    refine ⟨fun n => if n = 0 then z else y (n - 1), ?_⟩
    funext n
    simp [oneSidedShift]
  · intro X
    rfl
  · intro u v
    simp [oneSidedWordConcat]
  · intro word
    exact oneSidedCylinder_isClopen k hk word
  · exact oneSidedCylinder_isTopologicalBasis k hk
  · exact binaryCoding_shift
  · exact fairBinaryFactor
  · exact fairBinaryIsomorphism

/-- Source: Example 1.2.15, Chapter 1, Section 2. -/
theorem cauchyMeasureSystemIsomorphicToDoublingMap :
    IsMeasurePreservingSystem cauchyDoublingSystem ∧
      IsIsomorphicSystems cauchyDoublingSystem (circleTimesSystem 2) := by
  constructor
  · exact cauchyDoublingSystem_isomorphism.1
  · exact cauchyDoublingSystem_isomorphism

private theorem liftedDoublingIntervalSystem :
    IsDoublingIntervalSystem (liftedCircleTimesSystem 2) := by
  refine ⟨liftedCircleTimesSystem_mps 2 (by omega), ?_⟩
  let u := MeasurableEquiv.ulift (α := AddCircle (1 : ℝ))
  let q : AddCircle (1 : ℝ) ≃ᵐ Set.Ioc (0 : ℝ) (0 + 1) :=
    AddCircle.measurableEquivIoc 1 0
  let e : ULift (AddCircle (1 : ℝ)) ≃ᵐ Set.Ioc (0 : ℝ) (0 + 1) :=
    u.trans q
  refine ⟨e.toEquiv, e.measurable, e.symm.measurable, ?_, ?_⟩
  · have hu : MeasureTheory.MeasurePreserving u
        (liftedCircleTimesSystem 2).μ AddCircle.haarAddCircle := by
      refine MeasureTheory.MeasurePreserving.mk u.measurable ?_
      change MeasureTheory.Measure.map u
        (MeasureTheory.Measure.map u.symm AddCircle.haarAddCircle) = _
      rw [MeasureTheory.Measure.map_map u.measurable u.symm.measurable]
      simpa [u] using (MeasureTheory.Measure.map_id :
        MeasureTheory.Measure.map id AddCircle.haarAddCircle = AddCircle.haarAddCircle)
    have hvol :
        (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
          AddCircle.haarAddCircle := by
      simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
    have hq : MeasureTheory.MeasurePreserving q AddCircle.haarAddCircle
        (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) := by
      rw [← hvol]
      simpa [q] using
        (AddCircle.measurePreserving_equivIoc (1 : ℝ) (a := 0))
    exact (hq.comp hu).map_eq
  · intro x
    have hq : (((q (u x) : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) :
        AddCircle (1 : ℝ)) = u x := by
      change q.symm (q (u x)) = u x
      exact q.symm_apply_apply _
    apply Subtype.ext
    simp [doublingIocMap, liftedCircleTimesSystem, e, u, q, circleTimes, hq]

private theorem liftedCircleTimesSystem_isomorphic_circle :
    IsIsomorphicSystems (liftedCircleTimesSystem 2) (circleTimesSystem 2) := by
  let L := liftedCircleTimesSystem 2
  let C := circleTimesSystem 2
  let e := MeasurableEquiv.ulift (α := AddCircle (1 : ℝ))
  have hL : IsMeasurePreservingSystem L :=
    liftedCircleTimesSystem_mps 2 (by omega)
  have hC : IsMeasurePreservingSystem C :=
    (doublingMapAndNTimesMapExamples.{0} 2 (by omega)).2.1
  have he : MeasureTheory.MeasurePreserving e L.μ C.μ := by
    refine ⟨e.measurable, ?_⟩
    change MeasureTheory.Measure.map e
      (MeasureTheory.Measure.map e.symm AddCircle.haarAddCircle) =
        (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle (1 : ℝ)))
    rw [MeasureTheory.Measure.map_map e.measurable e.symm.measurable]
    have hid : MeasureTheory.Measure.map
        (id : AddCircle (1 : ℝ) → AddCircle (1 : ℝ))
        (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
          AddCircle.haarAddCircle := MeasureTheory.Measure.map_id
    simpa [e] using hid
  have hes : MeasureTheory.MeasurePreserving e.symm C.μ L.μ :=
    ⟨e.symm.measurable, rfl⟩
  refine ⟨hL, hC, Set.univ, Set.univ, e, e.symm,
    hL.1.measure_univ, hC.1.measure_univ, by simp, by simp,
    measurePreservingOnFullUniv L C hL hC e he,
    measurePreservingOnFullUniv C L hC hL e.symm hes, ?_, ?_⟩
  · intro x hx
    exact ⟨Set.mem_univ _, e.symm_apply_apply x, rfl⟩
  · intro y hy
    exact ⟨Set.mem_univ _, e.apply_symm_apply y, rfl⟩

private theorem liftedCircleTimesSystem_circlePower :
    IsCirclePowerSystem (liftedCircleTimesSystem.{u} 2) 2 := by
  let L := liftedCircleTimesSystem.{u} 2
  let e := MeasurableEquiv.ulift (α := AddCircle (1 : ℝ))
  have hL : IsMeasurePreservingSystem L :=
    liftedCircleTimesSystem_mps 2 (by omega)
  refine ⟨hL, e.toEquiv, e.measurable, e.symm.measurable, ?_, ?_⟩
  · change MeasureTheory.Measure.map e
      (MeasureTheory.Measure.map e.symm AddCircle.haarAddCircle) = _
    rw [MeasureTheory.Measure.map_map e.measurable e.symm.measurable]
    have hid : MeasureTheory.Measure.map
        (id : AddCircle (1 : ℝ) → AddCircle (1 : ℝ))
        (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
          AddCircle.haarAddCircle := MeasureTheory.Measure.map_id
    simpa [e] using hid
  · intro x
    rfl

private theorem liftedFairBinaryIsomorphism :
    IsIsomorphicSystems
      (liftedOneSidedBernoulliSystem.{u} 2 (fun _ => (1 / 2 : ℝ)))
      (circleTimesSystem 2) := by
  let L := liftedOneSidedBernoulliSystem.{u} 2 (fun _ => (1 / 2 : ℝ))
  let B := oneSidedBernoulliSystem 2 (fun _ => (1 / 2 : ℝ))
  let C := circleTimesSystem 2
  let e := MeasurableEquiv.ulift (α := OneSidedSymbolicSpace 2)
  let φ : L.X → C.X := fun x => binaryCoding (e x)
  let ψ : C.X → L.X := fun y => e.symm (circleBinaryDigits y)
  let M : Set L.X := e ⁻¹' binaryCanonicalSet
  have hp : ∀ i : Fin 2, 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hsum : ∑ _i : Fin 2, (1 / 2 : ℝ) = 1 := by simp
  have hL : IsMeasurePreservingSystem L :=
    liftedOneSidedBernoulliSystem_mps 2 _ hp hsum
  have hB : IsMeasurePreservingSystem B :=
    oneSidedBernoulliExampleSystem_mps 2 _ hp hsum
  have hC : IsMeasurePreservingSystem C :=
    (doublingMapAndNTimesMapExamples.{0} 2 (by omega)).2.1
  have hdn : MeasureTheory.MeasurePreserving e L.μ B.μ := by
    refine ⟨e.measurable, ?_⟩
    change MeasureTheory.Measure.map e
      (MeasureTheory.Measure.map e.symm B.μ) = B.μ
    rw [MeasureTheory.Measure.map_map e.measurable e.symm.measurable]
    simpa [e] using (MeasureTheory.Measure.map_id :
      MeasureTheory.Measure.map (id : OneSidedSymbolicSpace 2 →
        OneSidedSymbolicSpace 2) B.μ = B.μ)
  have hup : MeasureTheory.MeasurePreserving e.symm B.μ L.μ :=
    ⟨e.symm.measurable, rfl⟩
  have hbaseφ : MeasureTheory.MeasurePreserving binaryCoding B.μ C.μ :=
    ⟨binaryCoding_continuous.measurable, binaryCoding_map_fairBernoulli⟩
  have hbaseψ : MeasureTheory.MeasurePreserving circleBinaryDigits C.μ B.μ :=
    ⟨circleBinaryDigits_measurable, circleBinaryDigits_map_fairBernoulli⟩
  have hφ : MeasureTheory.MeasurePreserving φ L.μ C.μ := hbaseφ.comp hdn
  have hψ : MeasureTheory.MeasurePreserving ψ C.μ L.μ := hup.comp hbaseψ
  have hMbase : B.μ binaryCanonicalSet = 1 := by
    change oneSidedBernoulliMeasure 2 (fun _ => (1 / 2 : ℝ))
      binaryCanonicalSet = 1
    rw [← circleBinaryDigits_map_fairBernoulli,
      MeasureTheory.Measure.map_apply circleBinaryDigits_measurable
        binaryCanonicalSet_measurable]
    have hpre : circleBinaryDigits ⁻¹' binaryCanonicalSet = Set.univ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      change circleBinaryDigits (binaryCoding (circleBinaryDigits y)) =
        circleBinaryDigits y
      rw [binaryCoding_circleBinaryDigits]
    rw [hpre]
    exact hC.1.measure_univ
  have hMmeas : MeasurableSet M :=
    binaryCanonicalSet_measurable.preimage e.measurable
  have hM : L.μ M = 1 :=
    (hdn.measure_preimage binaryCanonicalSet_measurable.nullMeasurableSet).trans hMbase
  have hMcomp : L.μ Mᶜ = 0 := by
    have hLuniv : L.μ Set.univ = 1 := hL.1.measure_univ
    rw [MeasureTheory.measure_compl hMmeas]
    · rw [hM, hLuniv]
      simp
    · rw [hM]
      norm_num
  have haeM : ∀ᵐ x ∂L.μ, x ∈ M := by
    apply MeasureTheory.ae_iff.mpr
    exact hMcomp
  have hMinv : ∀ x ∈ M, L.T x ∈ M := by
    intro x hx
    change circleBinaryDigits (binaryCoding (oneSidedShift (e x))) =
      oneSidedShift (e x)
    rw [binaryCoding_shift]
    funext n
    rw [circleBinaryDigits_dynamics]
    exact congrFun hx (n + 1)
  have hforward : IsMeasurePreservingOnFullSets L C M Set.univ φ := by
    refine ⟨hMmeas, (by
      change MeasurableSet (Set.univ : Set C.X)
      exact MeasurableSet.univ), hM, hC.1.measure_univ, by simp, ?_⟩
    intro D hD
    change MeasurableSet D at hD
    constructor
    · exact hMmeas.inter (hφ.measurable (hD.inter MeasurableSet.univ))
    · calc
        L.μ (M ∩ φ ⁻¹' (D ∩ Set.univ)) = L.μ (φ ⁻¹' D) := by
          apply MeasureTheory.measure_congr
          filter_upwards [haeM] with x hx
          apply propext
          constructor
          · exact fun h => h.2.1
          · exact fun h => ⟨hx, h, Set.mem_univ _⟩
        _ = C.μ D := hφ.measure_preimage hD.nullMeasurableSet
        _ = C.μ (D ∩ Set.univ) := by simp
  have hbackward : IsMeasurePreservingOnFullSets C L Set.univ M ψ := by
    refine ⟨(by
      change MeasurableSet (Set.univ : Set C.X)
      exact MeasurableSet.univ), hMmeas, hC.1.measure_univ, hM, ?_, ?_⟩
    · intro y hy
      change circleBinaryDigits (binaryCoding (circleBinaryDigits y)) =
        circleBinaryDigits y
      rw [binaryCoding_circleBinaryDigits]
    · intro D hD
      change MeasurableSet D at hD
      constructor
      · simpa using hψ.measurable (hD.inter hMmeas)
      · simpa using hψ.measure_preimage (hD.inter hMmeas).nullMeasurableSet
  refine ⟨hL, hC, M, Set.univ, φ, ψ, hM, hC.1.measure_univ,
    hMinv, by simp, hforward, hbackward, ?_, ?_⟩
  · intro x hx
    refine ⟨Set.mem_univ _, ?_, binaryCoding_shift (e x)⟩
    apply e.injective
    rw [e.apply_symm_apply]
    exact hx
  · intro y hy
    constructor
    · change circleBinaryDigits (binaryCoding (circleBinaryDigits y)) =
        circleBinaryDigits y
      rw [binaryCoding_circleBinaryDigits]
    constructor
    · exact binaryCoding_circleBinaryDigits y
    · apply e.injective
      change circleBinaryDigits (circleTimes 2 y) = oneSidedShift (circleBinaryDigits y)
      funext n
      exact circleBinaryDigits_dynamics y n

private theorem circleTimesSystem_isomorphic_refl :
    IsIsomorphicSystems (circleTimesSystem 2) (circleTimesSystem 2) := by
  let C := circleTimesSystem 2
  have hC : IsMeasurePreservingSystem C :=
    (doublingMapAndNTimesMapExamples.{0} 2 (by omega)).2.1
  have hid : MeasureTheory.MeasurePreserving id C.μ C.μ :=
    MeasureTheory.MeasurePreserving.id _
  refine ⟨hC, hC, Set.univ, Set.univ, id, id,
    hC.1.measure_univ, hC.1.measure_univ, by simp, by simp,
    measurePreservingOnFullUniv C C hC hC id hid,
    measurePreservingOnFullUniv C C hC hC id hid, ?_, ?_⟩
  · simp
  · simp

/-- Source: Remark 1.2.16, Chapter 1, Section 2. -/
theorem standardDoublingModelsAreIsomorphic :
    ∃ interval unitCircle shift : MeasurePreservingSystemData.{u},
      IsDoublingIntervalSystem interval ∧ IsCirclePowerSystem unitCircle 2 ∧
      IsOneSidedBernoulliShiftWith shift 2 (fun _ => (1 / 2 : ℝ)) ∧
      IsIsomorphicSystems interval (circleTimesSystem 2) ∧
      IsIsomorphicSystems unitCircle (circleTimesSystem 2) ∧
      IsIsomorphicSystems shift (circleTimesSystem 2) ∧
      IsIsomorphicSystems cauchyDoublingSystem (circleTimesSystem 2) := by
  refine ⟨liftedCircleTimesSystem.{u} 2,
    liftedCircleTimesSystem.{u} 2,
    liftedOneSidedBernoulliSystem.{u} 2 (fun _ => (1 / 2 : ℝ)),
    liftedDoublingIntervalSystem, liftedCircleTimesSystem_circlePower,
    ?_, liftedCircleTimesSystem_isomorphic_circle,
    liftedCircleTimesSystem_isomorphic_circle, liftedFairBinaryIsomorphism,
    cauchyDoublingSystem_isomorphism⟩
  exact liftedOneSidedBernoulliSystem_semantics 2
    (fun _ => (1 / 2 : ℝ)) (by norm_num) (by simp)

/-- Source: Example 1.2.17, Chapter 1, Section 2. -/
theorem twoSidedShiftSystemExample (k : ℕ) (hk : 2 ≤ k)
    (p : Fin k -> ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∃ S : MeasurePreservingSystemData.{0}, IsTwoSidedBernoulliShiftWith S k p := by
  refine ⟨twoSidedBernoulliExampleSystem k p, ?_, ?_⟩
  · exact twoSidedBernoulliExampleSystem_mps k p hp hsum
  · refine ⟨Equiv.refl _, measurable_id, measurable_id, ?_, hp, hsum, ?_, ?_⟩
    · change MeasureTheory.Measure.map (id : (ℤ → Fin k) → (ℤ → Fin k))
          (MeasureTheory.Measure.infinitePi
            (fun _ : ℤ ↦ alphabetProbabilityMeasure k p)) =
        MeasureTheory.Measure.infinitePi
          (fun _ : ℤ ↦ alphabetProbabilityMeasure k p)
      exact MeasureTheory.Measure.map_id
    · intro x n
      rfl
    · intro n a
      exact twoSidedBernoulli_cylinder k n a p hp hsum

/-- Source: Example 1.2.18, Chapter 1, Section 2. -/
theorem markovShiftSystemExample (k : ℕ) (hk : 2 ≤ k)
    (p : Fin k -> ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    (∃ S : MeasurePreservingSystemData, IsOneSidedMarkovShiftWith S k p P) ∧
      ∃ S : MeasurePreservingSystemData, IsTwoSidedMarkovShiftWith S k p P := by
  constructor
  · refine ⟨liftedSystem (oneSidedMarkovSystem k p P hP hPsum), ?_⟩
    exact liftedOneSidedMarkovSystem_semantics k p P hp hpsum hP hPsum hstationary
  · refine ⟨liftedSystem
      (twoSidedMarkovSystem k p P hp hpsum hP hPsum hstationary), ?_⟩
    exact liftedTwoSidedMarkovSystem_semantics k p P hp hpsum hP hPsum hstationary

private def realPathRectangles : Set (Set (ℤ → ℝ)) :=
  {A | ∃ s : Finset ℤ, ∃ B : ℤ → Set ℝ,
    (∀ i, MeasurableSet (B i)) ∧ A = Set.pi s B}

private theorem realPathRectangles_generate :
    (inferInstance : MeasurableSpace (ℤ → ℝ)) =
      MeasurableSpace.generateFrom realPathRectangles := by
  apply le_antisymm
  · rw [MeasurableSpace.pi_eq_generateFrom_projections]
    apply MeasurableSpace.generateFrom_mono
    rintro A ⟨i, B, hB, rfl⟩
    refine ⟨{i}, (fun j => if j = i then B else Set.univ), ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · simp [hji, hB]
      · simp [hji]
    · ext x
      simp
  · apply MeasurableSpace.generateFrom_le
    rintro A ⟨s, B, hB, rfl⟩
    exact MeasurableSet.pi s.countable_toSet (fun i hi => hB i)

private theorem realPathRectangles_piSystem : IsPiSystem realPathRectangles := by
  rintro A ⟨s, B, hB, rfl⟩ C ⟨t, D, hD, rfl⟩ hne
  let E : ℤ → Set ℝ := fun i =>
    (if i ∈ s then B i else Set.univ) ∩
      (if i ∈ t then D i else Set.univ)
  refine ⟨s ∪ t, E, ?_, ?_⟩
  · intro i
    simp only [E]
    apply MeasurableSet.inter <;> split_ifs <;> simp_all
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_pi, Finset.mem_coe, Finset.mem_union, E]
    aesop

private def stationaryPathMap {P : ProbabilitySpaceData} (f : ℤ → P.X → ℝ) :
    P.X → (ℤ → ℝ) := fun ω n => f n ω

private def realPathShift (x : ℤ → ℝ) : ℤ → ℝ := fun n => x (n + 1)

private theorem stationaryPathMap_measurable {P : ProbabilitySpaceData}
    {f : ℤ → P.X → ℝ} (hf : ∀ n, Measurable (f n)) :
    Measurable (stationaryPathMap f) := by
  rw [measurable_pi_iff]
  exact hf

private theorem realPathShift_measurable : Measurable realPathShift := by
  rw [measurable_pi_iff]
  intro n
  exact measurable_pi_apply (n + 1)

private theorem stationaryPathMeasure_shiftInvariant
    (P : ProbabilitySpaceData) (f : ℤ → P.X → ℝ)
    (hf : IsStationaryProcess P f) :
    MeasureTheory.Measure.map realPathShift
        (MeasureTheory.Measure.map (stationaryPathMap f) P.μ) =
      MeasureTheory.Measure.map (stationaryPathMap f) P.μ := by
  letI : MeasureTheory.IsProbabilityMeasure P.μ := hf.1
  have hfm : Measurable (stationaryPathMap f) := stationaryPathMap_measurable hf.2.1
  have hsm : Measurable realPathShift := realPathShift_measurable
  have hprob : MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.map (stationaryPathMap f) P.μ) := by
    constructor
    rw [MeasureTheory.Measure.map_apply hfm MeasurableSet.univ]
    simpa using (MeasureTheory.measure_univ : P.μ Set.univ = 1)
  letI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.Measure.map realPathShift
        (MeasureTheory.Measure.map (stationaryPathMap f) P.μ)) := by
    haveI : MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.map (stationaryPathMap f) P.μ) := hprob
    have hp2 : MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.map realPathShift
          (MeasureTheory.Measure.map (stationaryPathMap f) P.μ)) := by
      constructor
      rw [MeasureTheory.Measure.map_apply hsm MeasurableSet.univ]
      exact MeasureTheory.measure_univ
    exact ⟨by rw [hp2.measure_univ]; exact ENNReal.one_lt_top⟩
  apply MeasureTheory.ext_of_generate_finite realPathRectangles
      realPathRectangles_generate realPathRectangles_piSystem
  · rintro A ⟨s, B, hB, rfl⟩
    rw [MeasureTheory.Measure.map_apply hsm
      (MeasurableSet.pi s.countable_toSet (fun i hi => hB i))]
    rw [MeasureTheory.Measure.map_apply hfm
      ((MeasurableSet.pi s.countable_toSet (fun i hi => hB i)).preimage hsm)]
    rw [MeasureTheory.Measure.map_apply hfm
      (MeasurableSet.pi s.countable_toSet (fun i hi => hB i))]
    let r := Fintype.card {i // i ∈ s}
    let e : Fin r ≃ {i // i ∈ s} := (Fintype.equivFin {i // i ∈ s}).symm
    have hs := hf.2.2 r (fun q => (e q : ℤ)) (fun q => B (e q))
      (fun q => hB (e q)) 1
    have hset0 : (stationaryPathMap f) ⁻¹' Set.pi s B =
        {ω | ∀ q : Fin r, f (e q) ω ∈ B (e q)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi,
        stationaryPathMap]
      constructor
      · intro h q
        exact h (e q) (e q).property
      · intro h i hi
        obtain ⟨q, hq⟩ := e.surjective ⟨i, hi⟩
        have hval : (e q : ℤ) = i := congrArg Subtype.val hq
        simpa [hval] using h q
    have hset1 : (stationaryPathMap f) ⁻¹' (realPathShift ⁻¹' Set.pi s B) =
        {ω | ∀ q : Fin r, f ((e q : ℤ) + 1) ω ∈ B (e q)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi,
        stationaryPathMap, realPathShift]
      constructor
      · intro h q
        simpa using h (e q) (e q).property
      · intro h i hi
        obtain ⟨q, hq⟩ := e.surjective ⟨i, hi⟩
        have hval : (e q : ℤ) = i := congrArg Subtype.val hq
        simpa [hval] using h q
    rw [hset0, hset1]
    exact hs.symm
  · rw [MeasureTheory.Measure.map_apply hsm MeasurableSet.univ]
    rfl

private theorem stationaryProcessShiftModelExists
    (P : ProbabilitySpaceData.{u}) (f : ℤ → P.X → ℝ)
    (hf : IsStationaryProcess P f) :
    ∃ S : MeasurePreservingSystemData.{v},
      IsStationaryProcessShiftModel P f S := by
  let e := MeasurableEquiv.ulift (α := (ℤ → ℝ))
  let μ0 := MeasureTheory.Measure.map (stationaryPathMap f) P.μ
  let S : MeasurePreservingSystemData.{v} :=
    { X := ULift.{v} (ℤ → ℝ)
      measurableSpace := inferInstance
      μ := MeasureTheory.Measure.map e.symm μ0
      T := fun x => e.symm (realPathShift (e x)) }
  have hfm : Measurable (stationaryPathMap f) := stationaryPathMap_measurable hf.2.1
  have hprob0 : MeasureTheory.IsProbabilityMeasure μ0 := by
    constructor
    change MeasureTheory.Measure.map (stationaryPathMap f) P.μ Set.univ = 1
    rw [MeasureTheory.Measure.map_apply hfm MeasurableSet.univ]
    letI : MeasureTheory.IsProbabilityMeasure P.μ := hf.1
    exact MeasureTheory.measure_univ
  have hup : MeasureTheory.MeasurePreserving e.symm μ0 S.μ := by
    exact MeasureTheory.MeasurePreserving.mk e.symm.measurable rfl
  have hdn : MeasureTheory.MeasurePreserving e S.μ μ0 := by
    refine MeasureTheory.MeasurePreserving.mk e.measurable ?_
    change MeasureTheory.Measure.map e (MeasureTheory.Measure.map e.symm μ0) = μ0
    rw [MeasureTheory.Measure.map_map e.measurable e.symm.measurable]
    simpa [e] using (MeasureTheory.Measure.map_id :
      MeasureTheory.Measure.map id μ0 = μ0)
  have hshift : MeasureTheory.MeasurePreserving realPathShift μ0 μ0 := by
    exact ⟨realPathShift_measurable,
      stationaryPathMeasure_shiftInvariant P f hf⟩
  refine ⟨S, hf, ?_, e.toEquiv, e.measurable, e.symm.measurable, hdn.map_eq, ?_⟩
  · constructor
    · constructor
      change S.μ Set.univ = 1
      rw [MeasureTheory.Measure.map_apply e.symm.measurable MeasurableSet.univ]
      exact hprob0.measure_univ
    · change MeasureTheory.MeasurePreserving
        (fun x => e.symm (realPathShift (e x))) S.μ S.μ
      simpa only [Function.comp_apply] using hup.comp (hshift.comp hdn)
  · intro x n
    change e (e.symm (realPathShift (e x))) n = e x (n + 1)
    rw [e.apply_symm_apply]
    rfl

/-- Source: Example 1.2.19, Chapter 1, Section 2. -/
theorem stationaryProcessShiftModelExample :
    ∀ P : ProbabilitySpaceData.{u}, ∀ f : ℤ -> P.X -> ℝ,
      IsStationaryProcess P f ->
      ∃ S : MeasurePreservingSystemData,
        IsStationaryProcessShiftModel P f S := by
  intro P f hf
  exact stationaryProcessShiftModelExists P f hf

end Section02
end Chapter01
