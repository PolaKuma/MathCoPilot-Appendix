import Chapter01.Section02

noncomputable section

open Classical

namespace Chapter01
namespace Section03

universe u

private noncomputable def recurrenceFailureSystem.{v} :
    MeasurePreservingSystemData.{v} where
  X := ULift.{v} Bool
  measurableSpace := ⊤
  μ := MeasureTheory.Measure.count
  T := fun _ => ULift.up false

/--
Source: Theorem 1.3.1, Chapter 1, Section 3.
Poincare recurrence, form 1.
-/
theorem poincareRecurrenceFormOne (M : MeasurePreservingSystemData.{u})
    (A : Set M.X) (hM : IsMeasurePreservingSystem M) (hA : A ∈ M.𝓧)
    (hpos : 0 < M.μ A) :
    ∃ n : ℕ, 0 < n ∧ 0 < M.μ (A ∩ (iterateMap M.T n) ⁻¹' A) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  have hcons : MeasureTheory.Conservative M.T M.μ := hM.2.conservative
  obtain ⟨n, hn, hne⟩ :=
    hcons.exists_gt_measure_inter_ne_zero hA.nullMeasurableSet
      (ne_of_gt hpos) 0
  exact ⟨n, hn, bot_lt_iff_ne_bot.mpr hne⟩

/--
Source: Definition 1.3.2, Chapter 1, Section 3.
Poincare sequence.
-/
def poincareSequenceDefinition (S : Set ℕ) : Prop :=
  IsPoincareSequence.{u} S

/--
Source: Definition 1.3.3, Chapter 1, Section 3.
Difference sets and `Δ*` sets.
-/
def deltaSetAndDeltaStarDefinition (F H : Set ℕ) : Prop :=
  differenceSet F = {n : ℕ | ∃ a ∈ F, ∃ b ∈ F, b < a ∧ n = a - b} ∧
    (IsDeltaStarSet H ↔
      ∀ E : Set ℕ, Set.Infinite E -> (H ∩ differenceSet E).Nonempty)

/--
Source: Definition 1.3.4, Chapter 1, Section 3.
Return-time set `N^μ(A,B)`.
-/
def measureReturnTimesDefinition (M : MeasurePreservingSystemData.{u})
    (A B : Set M.X) : Set ℕ :=
  returnTimes M A B

private theorem returnTimes_deltaStar_core (M : MeasurePreservingSystemData.{u})
    (A : Set M.X) (hM : IsMeasurePreservingSystem M) (hA : A ∈ M.𝓧)
    (hpos : 0 < M.μ A) :
    IsDeltaStarSet (returnTimes M A A) := by
  intro F hF
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  letI : Infinite F := hF.to_subtype
  have hs : ∀ i : F, MeasurableSet ((M.T^[i.1]) ⁻¹' A) := by
    intro i
    exact (hM.2.iterate i.1).measurable hA
  have hmeasure : ∀ i : F, M.μ A ≤ M.μ ((M.T^[i.1]) ⁻¹' A) := by
    intro i
    exact le_of_eq ((hM.2.iterate i.1).measure_preimage hA.nullMeasurableSet).symm
  obtain ⟨t, htinf, htpos⟩ :=
    bergelson (μ := M.μ) (r := M.μ A)
      (s := fun i : F => (M.T^[i.1]) ⁻¹' A)
      hs (ne_of_gt hpos) hmeasure
  obtain ⟨i, hi⟩ := htinf.nonempty
  have htdiff : (t \ {i}).Infinite := htinf.diff (Set.finite_singleton i)
  obtain ⟨j, hjt, hji⟩ := htdiff.nonempty
  have hj : j ∈ t := hjt
  have hij : i ≠ j := by
    intro hij
    exact hji (by simpa [hij])
  have hpair :
      0 < M.μ (((M.T^[i.1]) ⁻¹' A) ∩ ((M.T^[j.1]) ⁻¹' A)) := by
    have hsub : ({i, j} : Set F) ⊆ t := by
      intro k hk
      rcases Set.mem_insert_iff.mp hk with hki | hkj
      · subst k
        exact hi
      · have hkj' : k = j := Set.mem_singleton_iff.mp hkj
        subst k
        exact hj
    have h := htpos (u := ({i, j} : Set F)) hsub (by simp)
    have hset :
        (⋂ k ∈ ({i, j} : Set F), (M.T^[k.1]) ⁻¹' A) =
          ((M.T^[i.1]) ⁻¹' A) ∩ ((M.T^[j.1]) ⁻¹' A) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_inter_iff,
        forall_eq_or_imp, forall_eq]
    rw [hset] at h
    exact h
  rcases lt_or_gt_of_ne (Subtype.coe_injective.ne hij) with hijlt | hjilt
  · let d := j.1 - i.1
    have hdpos : 0 < d := Nat.sub_pos_of_lt hijlt
    have hset :
        ((M.T^[i.1]) ⁻¹' A) ∩ ((M.T^[j.1]) ⁻¹' A) =
          (M.T^[i.1]) ⁻¹' (A ∩ (M.T^[d]) ⁻¹' A) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      have hsum : d + i.1 = j.1 := Nat.sub_add_cancel (Nat.le_of_lt hijlt)
      rw [← hsum, Function.iterate_add_apply]
    have hC : MeasurableSet (A ∩ (M.T^[d]) ⁻¹' A) :=
      hA.inter ((hM.2.iterate d).measurable hA)
    have hμeq := (hM.2.iterate i.1).measure_preimage hC.nullMeasurableSet
    refine ⟨d, ?_, ?_⟩
    · refine ⟨hdpos, ?_⟩
      change 0 < M.μ (A ∩ (M.T^[d]) ⁻¹' A)
      rw [← hμeq, ← hset]
      exact hpair
    · exact ⟨j.1, j.2, i.1, i.2, hijlt, rfl⟩
  · let d := i.1 - j.1
    have hdpos : 0 < d := Nat.sub_pos_of_lt hjilt
    have hset :
        ((M.T^[i.1]) ⁻¹' A) ∩ ((M.T^[j.1]) ⁻¹' A) =
          (M.T^[j.1]) ⁻¹' (A ∩ (M.T^[d]) ⁻¹' A) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      have hsum : d + j.1 = i.1 := Nat.sub_add_cancel (Nat.le_of_lt hjilt)
      rw [← hsum, Function.iterate_add_apply, and_comm]
    have hC : MeasurableSet (A ∩ (M.T^[d]) ⁻¹' A) :=
      hA.inter ((hM.2.iterate d).measurable hA)
    have hμeq := (hM.2.iterate j.1).measure_preimage hC.nullMeasurableSet
    refine ⟨d, ?_, ?_⟩
    · refine ⟨hdpos, ?_⟩
      change 0 < M.μ (A ∩ (M.T^[d]) ⁻¹' A)
      rw [← hμeq, ← hset]
      exact hpair
    · exact ⟨i.1, i.2, j.1, j.2, hjilt, rfl⟩

/--
Source: Proposition 1.3.5, Chapter 1, Section 3.
For every positive-measure set `A`, `N^μ(A,A)` is a `Δ*` set; equivalently,
`Δ` sets are Poincare sequences.
-/
theorem returnTimesOfPositiveSetDeltaStar (M : MeasurePreservingSystemData.{u})
    (A : Set M.X) (hM : IsMeasurePreservingSystem M) (hA : A ∈ M.𝓧)
    (hpos : 0 < M.μ A) :
    IsDeltaStarSet (returnTimes M A A) ∧
      ∀ F : Set ℕ, Set.Infinite F -> IsPoincareSequence.{u} (differenceSet F) := by
  constructor
  · exact returnTimes_deltaStar_core M A hM hA hpos
  · intro F hF N B hN hB hBpos
    obtain ⟨n, hnret, hndiff⟩ :=
      (returnTimes_deltaStar_core N B hN hB hBpos F hF)
    exact ⟨n, hndiff, hnret.1, hnret.2⟩

/--
Source: Theorem 1.3.6, Chapter 1, Section 3.
Poincare recurrence, form 2: almost every point of `A` returns to `A`
infinitely many times.
-/
theorem poincareRecurrenceFormTwo (M : MeasurePreservingSystemData.{u})
    (A : Set M.X) (hM : IsMeasurePreservingSystem M) (hA : A ∈ M.𝓧) :
    AlmostEveryPointReturnsInfinitelyOften M A := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  have hcons : MeasureTheory.Conservative M.T M.μ := hM.2.conservative
  let B : Set M.X :=
    A ∩ {x | ∃ᶠ n in Filter.atTop, (M.T^[n]) x ∈ A}
  refine ⟨B, Set.inter_subset_left, ?_, ?_⟩
  · exact hcons.measure_inter_frequently_image_mem_eq hA.nullMeasurableSet
  · intro x hx
    have hfreq : ∃ᶠ n in Filter.atTop, (M.T^[n]) x ∈ A := hx.2
    have harb : ∀ N : ℕ, ∃ n > N, (M.T^[n]) x ∈ A := by
      intro N
      obtain ⟨n, hn, hnA⟩ :=
        (Filter.frequently_atTop.mp hfreq) (N + 1)
      exact ⟨n, by omega, hnA⟩
    obtain ⟨n, hnmono, hnA⟩ := Nat.exists_strictMono_subsequence harb
    refine ⟨n, hnmono, ?_⟩
    intro i
    change (M.T^[n i]) x ∈ A ∩
      {y | ∃ᶠ m in Filter.atTop, (M.T^[m]) y ∈ A}
    refine ⟨hnA i, ?_⟩
    apply Filter.frequently_atTop.mpr
    intro N
    obtain ⟨b, hb, hbA⟩ :=
      (Filter.frequently_atTop.mp hfreq) (N + n i)
    refine ⟨b - n i, by omega, ?_⟩
    rw [← Function.iterate_add_apply]
    have hni : n i ≤ b := by omega
    simpa only [Nat.sub_add_cancel hni] using hbA

/--
Source: Remark 1.3.7, Chapter 1, Section 3.
Without finite total measure, recurrence may fail; translation on the real line
is the textbook counterexample.
-/
theorem infiniteMeasureRecurrenceCanFail :
    ∃ M : MeasurePreservingSystemData, ¬ IsProbabilitySpace M.toProbabilitySpace ∧
      ∃ A : Set M.X, A ∈ M.𝓧 ∧ 0 < M.μ A ∧ returnTimes M A A = ∅ := by
  refine ⟨recurrenceFailureSystem, ?_, {ULift.up true}, ?_, ?_, ?_⟩
  · intro h
    change MeasureTheory.IsProbabilityMeasure recurrenceFailureSystem.μ at h
    letI := h
    have htotal : recurrenceFailureSystem.μ Set.univ = 1 :=
      MeasureTheory.measure_univ
    simpa [recurrenceFailureSystem] using htotal
  · simp [recurrenceFailureSystem, MeasurePreservingSystemData.𝓧]
  · simp [recurrenceFailureSystem]
  · ext n
    simp only [returnTimes, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      recurrenceFailureSystem, iterateMap]
    rintro ⟨hn, hpos⟩
    have hiter :
        ((fun _ : ULift Bool => ULift.up false)^[n]) (ULift.up true) =
          ULift.up false := by
      cases n with
      | zero => omega
      | succ n =>
          rw [Function.iterate_succ_apply']
    have hset :
        ({ULift.up true} ∩
            (fun _ : ULift Bool => ULift.up false)^[n] ⁻¹' {ULift.up true}) = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_preimage,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl, heq⟩
      have hfalse : false = true :=
        congrArg ULift.down (hiter.symm.trans heq)
      exact Bool.noConfusion hfalse
    rw [hset, MeasureTheory.measure_empty] at hpos
    exact (lt_irrefl 0 hpos)

end Section03
end Chapter01
