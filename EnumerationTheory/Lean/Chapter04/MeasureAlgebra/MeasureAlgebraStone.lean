import Chapter04.MeasureAlgebra.MeasureAlgebraRepresentation
import Mathlib.Order.PrimeSeparator
import Mathlib.Order.Disjointed
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Measure.SeparableMeasure

noncomputable section

open Classical
open scoped ENNReal symmDiff

namespace Chapter04.MeasureAlgebraStone

universe u

open Chapter04.MeasureAlgebraRepresentation

variable {A : MeasureAlgebraData.{u}} (hA : IsMeasureAlgebra A)

abbrev Q := AlgebraQuotient A hA

/-- The Stone points of the quotient Boolean algebra are its prime ideals. -/
abbrev StonePoint :=
  {I : Order.Ideal (Q hA) // Order.Ideal.IsPrime I}

/-- The basic Stone set represented by a Boolean-algebra element. -/
def stoneSet (q : Q hA) : Set (StonePoint hA) :=
  {I | q ∉ I.1}

theorem exists_prime_ideal_separating {q r : Q hA} (hqr : ¬ q ≤ r) :
    ∃ I : StonePoint hA, q ∉ I.1 ∧ r ∈ I.1 := by
  let F : Order.PFilter (Q hA) := Order.PFilter.principal q
  let J₀ : Order.Ideal (Q hA) := Order.Ideal.principal r
  have hdisjoint : Disjoint (F : Set (Q hA)) (J₀ : Set (Q hA)) := by
    rw [Set.disjoint_left]
    intro x hxF hxJ
    apply hqr
    exact (Order.PFilter.mem_principal.mp hxF).trans
      (Order.Ideal.mem_principal.mp hxJ)
  obtain ⟨J, hJprime, hJ₀J, hFJ⟩ :=
    DistribLattice.prime_ideal_of_disjoint_filter_ideal hdisjoint
  refine ⟨⟨J, hJprime⟩, ?_, hJ₀J (Order.Ideal.mem_principal.mpr le_rfl)⟩
  intro hqJ
  exact Set.disjoint_left.mp hFJ
    (Order.PFilter.mem_principal.mpr le_rfl) hqJ

theorem stoneSet_subset_iff {q r : Q hA} :
    stoneSet hA q ⊆ stoneSet hA r ↔ q ≤ r := by
  constructor
  · intro hsub
    by_contra hqr
    obtain ⟨I, hqI, hrI⟩ := exists_prime_ideal_separating hA hqr
    exact (hsub hqI) hrI
  · intro hqr I hqI hrI
    exact hqI (I.1.lower hqr hrI)

theorem stoneSet_injective : Function.Injective (stoneSet hA) := by
  intro q r hqr
  apply le_antisymm
  · exact stoneSet_subset_iff hA |>.mp (Set.Subset.rfl.trans_eq hqr)
  · exact stoneSet_subset_iff hA |>.mp (Set.Subset.rfl.trans_eq hqr.symm)

@[simp] theorem stoneSet_bot :
    stoneSet hA (⊥ : Q hA) = ∅ := by
  ext I
  simp [stoneSet]

theorem stonePoint_top_not_mem (I : StonePoint hA) :
    (⊤ : Q hA) ∉ I.1 := by
  intro htop
  have hIeq : I.1 = ⊤ := by
    ext q
    constructor
    · exact fun _ => trivial
    · exact fun _ => I.1.lower le_top htop
  exact (Order.Ideal.IsProper.ne_top I.2.toIsProper) hIeq

@[simp] theorem stoneSet_top :
    stoneSet hA (⊤ : Q hA) = Set.univ := by
  ext I
  simp only [stoneSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact stonePoint_top_not_mem hA I

@[simp] theorem stoneSet_sup (q r : Q hA) :
    stoneSet hA (q ⊔ r) = stoneSet hA q ∪ stoneSet hA r := by
  ext I
  simp only [stoneSet, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · contrapose!
    rintro ⟨hq, hr⟩
    exact I.1.sup_mem hq hr
  · intro h hsup
    exact h.elim (fun hq => hq (I.1.lower le_sup_left hsup))
      (fun hr => hr (I.1.lower le_sup_right hsup))

@[simp] theorem stoneSet_inf (q r : Q hA) :
    stoneSet hA (q ⊓ r) = stoneSet hA q ∩ stoneSet hA r := by
  ext I
  simp only [stoneSet, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun hq => h (I.1.lower inf_le_left hq),
      fun hr => h (I.1.lower inf_le_right hr)⟩
  · intro h hinf
    exact (I.2.mem_or_mem hinf).elim h.1 h.2

@[simp] theorem stoneSet_compl (q : Q hA) :
    stoneSet hA qᶜ = (stoneSet hA q)ᶜ := by
  ext I
  simp only [stoneSet, Set.mem_setOf_eq, Set.mem_compl_iff]
  constructor
  · intro hqc
    by_contra hq
    exact hqc (I.2.compl_mem_of_notMem hq)
  · intro hq hqc
    have hq' : q ∈ I.1 := Classical.not_not.mp hq
    apply stonePoint_top_not_mem hA I
    rw [← sup_compl_eq_top]
    exact I.1.sup_mem hq' hqc

theorem disjoint_stoneSet_iff (q r : Q hA) :
    Disjoint (stoneSet hA q) (stoneSet hA r) ↔ Disjoint q r := by
  rw [disjoint_iff_inf_le, disjoint_iff_inf_le]
  change stoneSet hA q ∩ stoneSet hA r ⊆ ∅ ↔ q ⊓ r ≤ ⊥
  rw [← stoneSet_inf, ← stoneSet_bot, stoneSet_subset_iff]

theorem stoneSet_iUnion_subset (f : ℕ → Q hA) :
    (⋃ n, stoneSet hA (f n)) ⊆ stoneSet hA (quotientIUnion hA f) := by
  intro I hI
  simp only [Set.mem_iUnion] at hI
  obtain ⟨n, hn⟩ := hI
  exact (stoneSet_subset_iff hA).2 (le_quotientIUnion hA f n) hn

theorem quotientIUnion_eq_of_stoneSet_iUnion
    (f : ℕ → Q hA) (q : Q hA)
    (h : stoneSet hA q = ⋃ n, stoneSet hA (f n)) :
    quotientIUnion hA f = q := by
  apply le_antisymm
  · apply quotientIUnion_le
    intro n
    apply (stoneSet_subset_iff hA).1
    rw [h]
    exact Set.subset_iUnion (fun k => stoneSet hA (f k)) n
  · apply (stoneSet_subset_iff hA).1
    rw [h]
    exact stoneSet_iUnion_subset hA f

theorem quotientIUnion_disjointed (f : ℕ → Q hA) :
    quotientIUnion hA (disjointed f) = quotientIUnion hA f := by
  apply le_antisymm
  · apply quotientIUnion_le
    intro n
    exact (disjointed_le f n).trans (le_quotientIUnion hA f n)
  · apply quotientIUnion_le
    intro n
    have hpartial : ∀ k, partialSups (disjointed f) k ≤
        quotientIUnion hA (disjointed f) := by
      intro k
      rw [partialSups_apply]
      apply Finset.sup'_le Finset.nonempty_Iic
      intro i hi
      exact le_quotientIUnion hA (disjointed f) i
    calc
      f n ≤ partialSups f n := le_partialSups f n
      _ = partialSups (disjointed f) n := by
        rw [partialSups_disjointed]
      _ ≤ quotientIUnion hA (disjointed f) := hpartial n

theorem stoneSet_finset_sup (s : Finset ℕ) (f : ℕ → Q hA) :
    stoneSet hA (s.sup f) = ⋃ n ∈ s, stoneSet hA (f n) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert n s hn ih => simp [Finset.sup_insert, ih, stoneSet_sup]

theorem stoneSet_finset_inf (s : Finset ℕ) (f : ℕ → Q hA) :
    stoneSet hA (s.inf f) = ⋂ n ∈ s, stoneSet hA (f n) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert n s hn ih => simp [Finset.inf_insert, ih, stoneSet_inf]

theorem stoneSet_disjointed (f : ℕ → Q hA) (n : ℕ) :
    stoneSet hA (disjointed f n) =
      disjointed (fun k => stoneSet hA (f k)) n := by
  simp [disjointed, sdiff_eq, stoneSet_inf, stoneSet_compl,
    stoneSet_finset_inf]

/-- The Boolean set algebra generated by the Stone representation. -/
def stoneAlgebra : Set (Set (StonePoint hA)) :=
  Set.range (stoneSet hA)

theorem isSetAlgebra_stoneAlgebra :
    MeasureTheory.IsSetAlgebra (stoneAlgebra hA) where
  empty_mem := ⟨⊥, stoneSet_bot hA⟩
  compl_mem := by
    rintro s ⟨q, rfl⟩
    exact ⟨qᶜ, stoneSet_compl hA q⟩
  union_mem := by
    rintro s t ⟨q, rfl⟩ ⟨r, rfl⟩
    exact ⟨q ⊔ r, stoneSet_sup hA q r⟩

/-- The unique quotient-algebra element represented by a Stone-algebra set. -/
def stoneIndex (s : Set (StonePoint hA)) : Q hA :=
  if hs : s ∈ stoneAlgebra hA then Classical.choose hs else ⊥

theorem stoneSet_stoneIndex {s : Set (StonePoint hA)}
    (hs : s ∈ stoneAlgebra hA) :
    stoneSet hA (stoneIndex hA s) = s := by
  rw [stoneIndex, dif_pos hs]
  exact Classical.choose_spec hs

@[simp] theorem stoneIndex_stoneSet (q : Q hA) :
    stoneIndex hA (stoneSet hA q) = q := by
  apply stoneSet_injective hA
  exact stoneSet_stoneIndex hA ⟨q, rfl⟩

theorem stoneIndex_union {s t : Set (StonePoint hA)}
    (hs : s ∈ stoneAlgebra hA) (ht : t ∈ stoneAlgebra hA) :
    stoneIndex hA (s ∪ t) = stoneIndex hA s ⊔ stoneIndex hA t := by
  apply stoneSet_injective hA
  rw [stoneSet_stoneIndex hA
      ((isSetAlgebra_stoneAlgebra hA).union_mem hs ht),
    stoneSet_sup, stoneSet_stoneIndex hA hs, stoneSet_stoneIndex hA ht]

/-- The quotient measure transported to the Stone algebra. -/
def stoneContent : MeasureTheory.AddContent ℝ≥0∞ (stoneAlgebra hA) :=
  (isSetAlgebra_stoneAlgebra hA).isSetRing.addContent_of_union
    (fun s => ENNReal.ofReal (quotientMeasure hA (stoneIndex hA s)))
    (by
      have hempty : stoneIndex hA ∅ = ⊥ := by
        apply stoneSet_injective hA
        rw [stoneSet_stoneIndex hA (isSetAlgebra_stoneAlgebra hA).empty_mem,
          stoneSet_bot]
      change ENNReal.ofReal (quotientMeasure hA (stoneIndex hA ∅)) = 0
      rw [hempty, quotientMeasure_bot]
      simp)
    (by
      intro s t hs ht hst
      change ENNReal.ofReal (quotientMeasure hA (stoneIndex hA (s ∪ t))) =
        ENNReal.ofReal (quotientMeasure hA (stoneIndex hA s)) +
          ENNReal.ofReal (quotientMeasure hA (stoneIndex hA t))
      rw [stoneIndex_union hA hs ht,
        quotientMeasure_sup_of_disjoint hA]
      · exact ENNReal.ofReal_add
          (quotientMeasure_nonneg hA _) (quotientMeasure_nonneg hA _)
      · exact (disjoint_stoneSet_iff hA _ _).1 <| by
          simpa [stoneSet_stoneIndex hA hs, stoneSet_stoneIndex hA ht] using hst)

theorem stoneContent_iUnion_eq_tsum
    (f : ℕ → Set (StonePoint hA))
    (hf : ∀ n, f n ∈ stoneAlgebra hA)
    (hUnion : (⋃ n, f n) ∈ stoneAlgebra hA)
    (hdis : ∀ i j, i ≠ j → Disjoint (f i) (f j)) :
    stoneContent hA (⋃ n, f n) = ∑' n, stoneContent hA (f n) := by
  let q : ℕ → Q hA := fun n => stoneIndex hA (f n)
  have hqdis : ∀ i j, i ≠ j → Disjoint (q i) (q j) := by
    intro i j hij
    apply (disjoint_stoneSet_iff hA _ _).1
    rw [stoneSet_stoneIndex hA (hf i), stoneSet_stoneIndex hA (hf j)]
    exact hdis i j hij
  have hstone : stoneSet hA (stoneIndex hA (⋃ n, f n)) =
      ⋃ n, stoneSet hA (q n) := by
    ext I
    rw [stoneSet_stoneIndex hA hUnion]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, (stoneSet_stoneIndex hA (hf n)).symm ▸ hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, stoneSet_stoneIndex hA (hf n) ▸ hn⟩
  have hindex : stoneIndex hA (⋃ n, f n) = quotientIUnion hA q :=
    (quotientIUnion_eq_of_stoneSet_iUnion hA q _ hstone).symm
  change ENNReal.ofReal (quotientMeasure hA (stoneIndex hA (⋃ n, f n))) =
    ∑' n, ENNReal.ofReal (quotientMeasure hA (stoneIndex hA (f n)))
  rw [hindex, quotientMeasure_iUnion hA q hqdis]
  exact ENNReal.ofReal_tsum_of_nonneg
    (fun n => quotientMeasure_nonneg hA (q n))
    (summable_quotientMeasure_iUnion hA q hqdis)

theorem stoneContent_sigmaSubadditive :
    (stoneContent hA).IsSigmaSubadditive :=
  MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    (isSetAlgebra_stoneAlgebra hA).isSetRing
    (stoneContent_iUnion_eq_tsum hA)

/-- The measurable structure generated by the Stone algebra. -/
def stoneMeasurableSpace : MeasurableSpace (StonePoint hA) :=
  MeasurableSpace.generateFrom (stoneAlgebra hA)

local instance : MeasurableSpace (StonePoint hA) :=
  stoneMeasurableSpace hA

/-- The Carathéodory extension of the transported quotient measure. -/
def stoneMeasure : MeasureTheory.Measure (StonePoint hA) :=
  (stoneContent hA).measure
    (isSetAlgebra_stoneAlgebra hA).isSetRing.isSetSemiring le_rfl
    (stoneContent_sigmaSubadditive hA)

theorem stoneMeasure_stoneSet (q : Q hA) :
    stoneMeasure hA (stoneSet hA q) =
      ENNReal.ofReal (quotientMeasure hA q) := by
  rw [stoneMeasure, MeasureTheory.AddContent.measure_eq
    (stoneContent hA) (isSetAlgebra_stoneAlgebra hA).isSetRing.isSetSemiring rfl
    (stoneContent_sigmaSubadditive hA) ⟨q, rfl⟩]
  change ENNReal.ofReal (quotientMeasure hA (stoneIndex hA (stoneSet hA q))) = _
  rw [stoneIndex_stoneSet]

theorem measurableSet_stoneSet (q : Q hA) :
    MeasurableSet (stoneSet hA q) :=
  MeasurableSpace.measurableSet_generateFrom ⟨q, rfl⟩

theorem stoneMeasure_iUnion_stoneSet (f : ℕ → Q hA) :
    stoneMeasure hA (⋃ n, stoneSet hA (f n)) =
      stoneMeasure hA (stoneSet hA (quotientIUnion hA f)) := by
  let d : ℕ → Q hA := disjointed f
  have hdis : ∀ i j, i ≠ j → Disjoint (d i) (d j) := by
    intro i j hij
    exact disjoint_disjointed f hij
  have hunion : (⋃ n, stoneSet hA (f n)) =
      ⋃ n, stoneSet hA (d n) := by
    calc
      (⋃ n, stoneSet hA (f n)) =
          ⋃ n, disjointed (fun k => stoneSet hA (f k)) n :=
        iUnion_disjointed.symm
      _ = ⋃ n, stoneSet hA (d n) := by
        exact congrArg (fun g : ℕ → Set (StonePoint hA) => ⋃ n, g n) <|
          funext fun n => by
            change disjointed (fun k => stoneSet hA (f k)) n =
              stoneSet hA (disjointed f n)
            exact (stoneSet_disjointed hA f n).symm
  have hmeasureUnion : stoneMeasure hA (⋃ n, stoneSet hA (d n)) =
      ∑' n, stoneMeasure hA (stoneSet hA (d n)) := by
    apply MeasureTheory.measure_iUnion
    · intro i j hij
      exact (disjoint_stoneSet_iff hA _ _).2 (hdis i j hij)
    · exact fun n => measurableSet_stoneSet hA (d n)
  rw [hunion, hmeasureUnion]
  simp_rw [stoneMeasure_stoneSet hA]
  rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => quotientMeasure_nonneg hA (d n))
      (summable_quotientMeasure_iUnion hA d hdis),
    ← quotientMeasure_iUnion hA d hdis,
    quotientIUnion_disjointed hA f]

theorem stoneMeasure_iUnion_gap_zero (f : ℕ → Q hA) :
    stoneMeasure hA
      (stoneSet hA (quotientIUnion hA f) \ (⋃ n, stoneSet hA (f n))) = 0 := by
  let U : Set (StonePoint hA) := ⋃ n, stoneSet hA (f n)
  let T : Set (StonePoint hA) := stoneSet hA (quotientIUnion hA f)
  have hsub : U ⊆ T := stoneSet_iUnion_subset hA f
  have hUmeas : MeasurableSet U :=
    MeasurableSet.iUnion fun n => measurableSet_stoneSet hA (f n)
  have hGmeas : MeasurableSet (T \ U) :=
    (measurableSet_stoneSet hA (quotientIUnion hA f)).diff hUmeas
  have hadd : stoneMeasure hA T =
      stoneMeasure hA U + stoneMeasure hA (T \ U) := by
    calc
      stoneMeasure hA T = stoneMeasure hA (U ∪ (T \ U)) :=
        congrArg (stoneMeasure hA) (Set.union_diff_cancel hsub).symm
      _ = stoneMeasure hA U + stoneMeasure hA (T \ U) :=
        MeasureTheory.measure_union Set.disjoint_sdiff_right hGmeas
  have hUtop : stoneMeasure hA U ≠ ∞ := by
    rw [show U = ⋃ n, stoneSet hA (f n) by rfl,
      stoneMeasure_iUnion_stoneSet hA f, stoneMeasure_stoneSet]
    exact ENNReal.ofReal_ne_top
  change stoneMeasure hA (T \ U) = 0
  apply (ENNReal.add_left_inj hUtop).mp
  rw [add_comm (stoneMeasure hA (T \ U)), add_comm 0, ← hadd]
  simpa only [add_zero, U, T] using
    (stoneMeasure_iUnion_stoneSet hA f).symm

theorem exists_stoneSet_mod_null {s : Set (StonePoint hA)}
    (hs : MeasurableSet s) :
    ∃ q : Q hA, stoneMeasure hA (s ∆ stoneSet hA q) = 0 := by
  change @MeasurableSet (StonePoint hA)
    (MeasurableSpace.generateFrom (stoneAlgebra hA)) s at hs
  induction s, hs using MeasurableSpace.generateFrom_induction with
  | hC t ht _ =>
      obtain ⟨q, rfl⟩ := ht
      exact ⟨q, by simp⟩
  | empty =>
      exact ⟨⊥, by simp⟩
  | compl t _ ht =>
      obtain ⟨q, hq⟩ := ht
      refine ⟨qᶜ, ?_⟩
      rw [stoneSet_compl, compl_symmDiff_compl]
      exact hq
  | iUnion f _ hf =>
      choose q hq using fun n => hf n
      refine ⟨quotientIUnion hA q, ?_⟩
      apply MeasureTheory.measure_symmDiff_eq_zero_iff.mpr
      have hunion : (⋃ n, f n) =ᵐ[stoneMeasure hA]
          ⋃ n, stoneSet hA (q n) := by
        apply MeasureTheory.measure_symmDiff_eq_zero_iff.mp
        apply MeasureTheory.measure_mono_null
          (t := ⋃ n, f n ∆ stoneSet hA (q n))
        · intro x hx
          simp only [Set.mem_symmDiff, Set.mem_iUnion] at hx ⊢
          rcases hx with ⟨⟨n, hfn⟩, hstone⟩ | ⟨⟨n, hstone⟩, hf⟩
          · exact ⟨n, Or.inl ⟨hfn, fun hqn => hstone ⟨n, hqn⟩⟩⟩
          · exact ⟨n, Or.inr ⟨hstone, fun hfn => hf ⟨n, hfn⟩⟩⟩
        · apply MeasureTheory.measure_iUnion_null
          exact hq
      apply hunion.trans
      apply MeasureTheory.ae_eq_set.mpr
      constructor
      · rw [Set.diff_eq_empty.mpr (stoneSet_iUnion_subset hA q)]
        exact MeasureTheory.measure_empty
      · exact stoneMeasure_iUnion_gap_zero hA q

/-- The probability space carried by the Stone representation. -/
def stoneProbabilitySpace : ProbabilitySpace.{u} where
  X := StonePoint hA
  measurableSpace := stoneMeasurableSpace hA
  μ := stoneMeasure hA

theorem isProbabilitySpace_stoneProbabilitySpace
    (hTop : A.measure A.top = 1) :
    Chapter01.IsProbabilitySpace (stoneProbabilitySpace hA) := by
  constructor
  change stoneMeasure hA Set.univ = 1
  rw [← stoneSet_top hA, stoneMeasure_stoneSet hA,
    quotientMeasure_top hA hTop]
  norm_num

/-- The canonical map from the abstract algebra to measurable Stone sets. -/
def representationHom :
    MeasureAlgebraHomData A (inducedMeasureAlgebra (stoneProbabilitySpace hA)) where
  map a := ⟨stoneSet hA (Quotient.mk _ a),
    measurableSet_stoneSet hA (Quotient.mk _ a)⟩

theorem isMeasureAlgebraHom_representationHom :
    IsMeasureAlgebraHom (representationHom hA) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b c hbc
    have hq : (Quotient.mk _ b : Q hA) = Quotient.mk _ c := Quotient.sound hbc
    change stoneMeasure hA (stoneSet hA (Quotient.mk _ b) ∆
      stoneSet hA (Quotient.mk _ c)) = 0
    rw [hq]
    simp
  · intro b c
    change stoneMeasure hA (stoneSet hA (Quotient.mk _ (A.union b c)) ∆
      (stoneSet hA (Quotient.mk _ b) ∪ stoneSet hA (Quotient.mk _ c))) = 0
    rw [show (Quotient.mk _ (A.union b c) : Q hA) =
      Quotient.mk _ b ⊔ Quotient.mk _ c by rfl, stoneSet_sup]
    simp
  · intro b
    change stoneMeasure hA (stoneSet hA (Quotient.mk _ (A.compl b)) ∆
      (stoneSet hA (Quotient.mk _ b))ᶜ) = 0
    rw [quotientCompl_mk hA, stoneSet_compl]
    simp
  · intro f
    let q : ℕ → Q hA := fun n => Quotient.mk _ (f n)
    change stoneMeasure hA (stoneSet hA (Quotient.mk _ (A.iUnion f)) ∆
      ⋃ n, stoneSet hA (q n)) = 0
    rw [← quotientIUnion_mk hA f]
    apply MeasureTheory.measure_symmDiff_eq_zero_iff.mpr
    apply MeasureTheory.ae_eq_set.mpr
    constructor
    · exact stoneMeasure_iUnion_gap_zero hA q
    · rw [Set.diff_eq_empty.mpr (stoneSet_iUnion_subset hA q)]
      exact MeasureTheory.measure_empty
  · intro b
    have hb : 0 ≤ A.measure b := by
      rcases hA with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnonneg, _, _⟩
      exact hnonneg b
    change (stoneMeasure hA (stoneSet hA (Quotient.mk _ b))).toReal = A.measure b
    rw [stoneMeasure_stoneSet hA, quotientMeasure_mk,
      ENNReal.toReal_ofReal hb]

theorem isMeasureAlgebraIsomorphism_representationHom :
    IsMeasureAlgebraIsomorphism (representationHom hA) := by
  refine ⟨isMeasureAlgebraHom_representationHom hA, ?_, ?_⟩
  · intro b c hbc
    let q : Q hA := Quotient.mk _ b
    let r : Q hA := Quotient.mk _ c
    let d : Q hA := (q ⊓ rᶜ) ⊔ (r ⊓ qᶜ)
    have hset : stoneSet hA d = stoneSet hA q ∆ stoneSet hA r := by
      rw [show d = (q ⊓ rᶜ) ⊔ (r ⊓ qᶜ) by rfl,
        stoneSet_sup, stoneSet_inf, stoneSet_inf,
        stoneSet_compl, stoneSet_compl]
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
        Set.mem_symmDiff]
    have hdMeasure : stoneMeasure hA (stoneSet hA d) = 0 := by
      rw [hset]
      exact hbc
    have hdq : quotientMeasure hA d = 0 := by
      rw [stoneMeasure_stoneSet hA] at hdMeasure
      apply le_antisymm
      · exact ENNReal.ofReal_eq_zero.mp hdMeasure
      · exact quotientMeasure_nonneg hA d
    have hdBot : d = ⊥ := (quotientMeasure_eq_zero hA d).mp hdq
    have hqrBot : q ⊓ rᶜ = ⊥ := by
      apply le_antisymm
      · exact le_sup_left.trans_eq hdBot
      · exact bot_le
    have hrqBot : r ⊓ qᶜ = ⊥ := by
      apply le_antisymm
      · exact le_sup_right.trans_eq hdBot
      · exact bot_le
    have hqr : q ≤ r := by
      calc
        q = q ⊓ (r ⊔ rᶜ) := by simp
        _ = (q ⊓ r) ⊔ (q ⊓ rᶜ) := by exact inf_sup_left q r rᶜ
        _ = q ⊓ r := by simp [hqrBot]
        _ ≤ r := inf_le_right
    have hrq : r ≤ q := by
      calc
        r = r ⊓ (q ⊔ qᶜ) := by simp
        _ = (r ⊓ q) ⊔ (r ⊓ qᶜ) := by exact inf_sup_left r q qᶜ
        _ = r ⊓ q := by simp [hrqBot]
        _ ≤ q := inf_le_right
    exact Quotient.exact (le_antisymm hqr hrq)
  · intro s
    obtain ⟨q, hq⟩ := exists_stoneSet_mod_null hA s.2
    refine ⟨Quotient.out q, ?_⟩
    change stoneMeasure hA (stoneSet hA (Quotient.mk _ (Quotient.out q)) ∆ s.1) = 0
    rw [Quotient.out_eq]
    simpa [symmDiff_comm] using hq

end Chapter04.MeasureAlgebraStone
