import Chapter02.Spectral.HilbertSchmidtConsequences
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.SeparableMeasure

open Classical Filter Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Chapter02.SeparatedKernelDensity

universe u

def measurableRectangles (M : System.{u}) : Set (Set (M.X × M.X)) :=
  Set.image2 (· ×ˢ ·) {s : Set M.X | MeasurableSet s}
    {t : Set M.X | MeasurableSet t}

theorem measurableRectangles_isSetSemiring (M : System.{u}) :
    IsSetSemiring (measurableRectangles M) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨∅, MeasurableSet.empty, Set.univ, MeasurableSet.univ, empty_prod⟩
  · rintro _ ⟨s, hs, t, ht, rfl⟩ _ ⟨u, hu, v, hv, rfl⟩
    change MeasurableSet s at hs
    change MeasurableSet t at ht
    change MeasurableSet u at hu
    change MeasurableSet v at hv
    refine ⟨s ∩ u, hs.inter hu, t ∩ v, ht.inter hv, ?_⟩
    ext p
    simp only [mem_inter_iff, mem_prod]
    tauto
  · rintro _ ⟨s, hs, t, ht, rfl⟩ _ ⟨u, hu, v, hv, rfl⟩
    change MeasurableSet s at hs
    change MeasurableSet t at ht
    change MeasurableSet u at hu
    change MeasurableSet v at hv
    let r₁ : Set (M.X × M.X) := (s \ u) ×ˢ t
    let r₂ : Set (M.X × M.X) := (s ∩ u) ×ˢ (t \ v)
    refine ⟨{r₁, r₂}, ?_, ?_, ?_⟩
    · intro r hr
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl
      · exact ⟨s \ u, hs.diff hu, t, ht, rfl⟩
      · exact ⟨s ∩ u, hs.inter hu, t \ v, ht.diff hv, rfl⟩
    · intro X hX Y hY hXY
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hX hY
      rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
      · exact (hXY rfl).elim
      · exact Set.disjoint_left.2 (by
          intro p hp hq
          exact hp.1.2 hq.1.2)
      · exact Set.disjoint_left.2 (by
          intro p hp hq
          exact hq.1.2 hp.1.2)
      · exact (hXY rfl).elim
    · ext p
      simp only [Set.mem_diff, Set.mem_inter_iff, mem_prod,
        Finset.coe_insert, Finset.coe_singleton,
        sUnion_insert, sUnion_singleton, mem_union, r₁, r₂]
      tauto

def finiteRectangleAlgebra (M : System.{u}) : Set (Set (M.X × M.X)) :=
  supClosure (measurableRectangles M)

theorem finiteRectangleAlgebra_isSetAlgebra (M : System.{u}) :
    IsSetAlgebra (finiteRectangleAlgebra M) := by
  let hR := measurableRectangles_isSetSemiring M
  let hRing := hR.isSetRing_supClosure
  have hunivR : (Set.univ : Set (M.X × M.X)) ∈ measurableRectangles M :=
    ⟨Set.univ, MeasurableSet.univ, Set.univ, MeasurableSet.univ, univ_prod_univ⟩
  refine ⟨hRing.empty_mem, ?_, ?_⟩
  · intro s hs
    change s ∈ supClosure (measurableRectangles M) at hs
    change sᶜ ∈ supClosure (measurableRectangles M)
    rw [show sᶜ = (Set.univ : Set (M.X × M.X)) \ s by ext x; simp]
    exact hRing.diff_mem (subset_supClosure hunivR) hs
  · intro s t hs ht
    exact hRing.union_mem hs ht

theorem generateFrom_finiteRectangleAlgebra (M : System.{u}) :
    (inferInstance : MeasurableSpace (M.X × M.X)) =
      MeasurableSpace.generateFrom (finiteRectangleAlgebra M) := by
  apply le_antisymm
  · rw [← generateFrom_prod]
    exact MeasurableSpace.generateFrom_mono subset_supClosure
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    rw [← generateFrom_prod]
    exact measurableSet_generateFrom_of_mem_supClosure hs

theorem finiteRectangleAlgebra_measureDense
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    (M.μ.prod M.μ).MeasureDense (finiteRectangleAlgebra M) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  exact Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
    (M.μ.prod M.μ) (finiteRectangleAlgebra_isSetAlgebra M)
      (generateFrom_finiteRectangleAlgebra M)

def finiteRectangleIndicatorGenerators
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    Set (Lp ℂ 2 (M.μ.prod M.μ)) :=
  let hA := finiteRectangleAlgebra_measureDense M hM
  {Y | ∃ s : Set (M.X × M.X), ∃ hs : s ∈ finiteRectangleAlgebra M,
    ∃ hfin : (M.μ.prod M.μ) s ≠ ∞, ∃ c : ℂ,
      Y = indicatorConstLp 2 (hA.measurable s hs) hfin c}

def finiteRectangleIndicatorSpan
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    Submodule ℂ (Lp ℂ 2 (M.μ.prod M.μ)) :=
  Submodule.span ℂ (finiteRectangleIndicatorGenerators M hM)

theorem finiteRectangleIndicatorSpan_dense
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    (finiteRectangleIndicatorSpan M hM).topologicalClosure = ⊤ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let μ₂ := M.μ.prod M.μ
  let hA := finiteRectangleAlgebra_measureDense M hM
  let D := finiteRectangleIndicatorSpan M hM
  letI : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩
  apply top_unique
  intro F hF
  change F ∈ D.topologicalClosure
  apply Lp.induction (p := (2 : ENNReal)) (by norm_num)
    (motive := fun Y : Lp ℂ 2 μ₂ ↦ Y ∈ D.topologicalClosure)
  · intro c s hs hμs
    have hclose :=
      hA.indicatorConstLp_subset_closure (2 : ENNReal) c
        ⟨s, hs, hμs.ne, rfl⟩
    apply Submodule.closure_subset_topologicalClosure_span
      (R := ℂ) (finiteRectangleIndicatorGenerators M hM)
    apply (closure_mono ?_) hclose
    rintro Y ⟨t, ht, hμt, rfl⟩
    exact ⟨t, ht, hμt, c, rfl⟩
  · intro f g hf hg hdisj hfD hgD
    exact D.topologicalClosure.add_mem hfD hgD
  · exact D.isClosed_topologicalClosure

theorem exists_finiteRectangleSpan_approx
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y : Lp ℂ 2 (M.μ.prod M.μ),
      Y ∈ finiteRectangleIndicatorSpan M hM ∧
      ‖hH.toLp H - Y‖ < δ := by
  let D := finiteRectangleIndicatorSpan M hM
  have htop := finiteRectangleIndicatorSpan_dense M hM
  have hmem : hH.toLp H ∈ closure (D : Set (Lp ℂ 2 (M.μ.prod M.μ))) := by
    change hH.toLp H ∈ D.topologicalClosure
    rw [htop]
    trivial
  obtain ⟨Y, hYD, hdist⟩ :=
    SeminormedAddCommGroup.mem_closure_iff.1 hmem δ hδ
  exact ⟨Y, hYD, by simpa [dist_eq_norm] using hdist⟩

theorem finiteRectangle_indicator_isFiniteSeparated
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (s : Set (M.X × M.X)) (hs : s ∈ finiteRectangleAlgebra M) (c : ℂ) :
    HilbertSchmidtConsequences.IsFiniteSeparatedKernel M
      (s.indicator fun _ ↦ c) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let hR := measurableRectangles_isSetSemiring M
  obtain ⟨P, hPsub⟩ := hR.mem_supClosure_iff.mp hs
  let I := {R // R ∈ P.parts}
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let R : Fin (Fintype.card I) → Set (M.X × M.X) :=
    fun i ↦ (e.symm i).1
  have hRmem (i : Fin (Fintype.card I)) : R i ∈ measurableRectangles M :=
    hPsub (e.symm i).2
  let A : Fin (Fintype.card I) → Set M.X :=
    fun i ↦ Classical.choose (hRmem i)
  have hA (i : Fin (Fintype.card I)) : MeasurableSet (A i) := by
    exact (Classical.choose_spec (hRmem i)).1
  let B : Fin (Fintype.card I) → Set M.X :=
    fun i ↦ Classical.choose (Classical.choose_spec (hRmem i)).2
  have hB (i : Fin (Fintype.card I)) : MeasurableSet (B i) := by
    exact (Classical.choose_spec (Classical.choose_spec (hRmem i)).2).1
  have hrect (i : Fin (Fintype.card I)) : R i = A i ×ˢ B i := by
    exact (Classical.choose_spec (Classical.choose_spec (hRmem i)).2).2.symm
  let a : Fin (Fintype.card I) → M.X → ℂ :=
    fun i x ↦ if x ∈ A i then c else 0
  let b : Fin (Fintype.card I) → M.X → ℂ :=
    fun i y ↦ if y ∈ B i then 1 else 0
  refine ⟨Fintype.card I, a, b, ?_, ?_, ?_⟩
  · intro i
    simpa [a, Set.indicator] using
      (memLp_indicator_const (2 : ENNReal) (hA i) c (Or.inr (by simp)))
  · intro i
    simpa [b, Set.indicator] using
      (memLp_indicator_const (2 : ENNReal) (hB i) (1 : ℂ) (Or.inr (by simp)))
  · funext p
    by_cases hp : p ∈ s
    · have hpSup : p ∈ P.parts.sup id := by
        rw [P.sup_parts]
        exact hp
      rw [Finset.sup_id_set_eq_sUnion] at hpSup
      obtain ⟨T, hTP, hpT⟩ := Set.mem_sUnion.mp hpSup
      let k : I := ⟨T, hTP⟩
      let i : Fin (Fintype.card I) := e k
      have hRi : R i = T := by
        change (e.symm i).1 = T
        simp [i, k]
      rw [Set.indicator_of_mem hp]
      rw [Finset.sum_eq_single i]
      · have hpRi : p ∈ R i := hRi.symm ▸ hpT
        have hpAB : p.1 ∈ A i ∧ p.2 ∈ B i := by
          simpa only [Set.mem_prod] using
            (show p ∈ A i ×ˢ B i from hrect i ▸ hpRi)
        simp [a, b, hpAB.1, hpAB.2]
      · intro j hj hji
        have hpRj : p ∉ R j := by
          intro hpj
          have hEq : R j = T := by
            by_contra hne
            exact Set.disjoint_left.1
              (P.disjoint (e.symm j).2 hTP hne) hpj hpT
          have hsub : e.symm j = k := Subtype.ext hEq
          have : j = i := by
            calc
              j = e (e.symm j) := (e.apply_symm_apply j).symm
              _ = e k := congrArg e hsub
              _ = i := rfl
          exact hji this
        have hpAB : ¬(p.1 ∈ A j ∧ p.2 ∈ B j) := by
          rw [← Set.mem_prod, ← hrect j]
          exact hpRj
        simp only [a, b]
        by_cases hx : p.1 ∈ A j
        · by_cases hy : p.2 ∈ B j
          · exact (hpAB ⟨hx, hy⟩).elim
          · simp [hx, hy]
        · simp [hx]
      · simp
    · rw [Set.indicator_of_notMem hp]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      have hpRi : p ∉ R i := by
        intro hpR
        exact hp (P.le (e.symm i).2 hpR)
      have hpAB : ¬(p.1 ∈ A i ∧ p.2 ∈ B i) := by
        rw [← Set.mem_prod, ← hrect i]
        exact hpRi
      simp only [a, b]
      by_cases hx : p.1 ∈ A i
      · by_cases hy : p.2 ∈ B i
        · exact (hpAB ⟨hx, hy⟩).elim
        · simp [hx, hy]
      · simp [hx]

theorem isFiniteSeparatedKernel_zero (M : System.{u}) :
    HilbertSchmidtConsequences.IsFiniteSeparatedKernel M
      (0 : M.X × M.X → ℂ) := by
  refine ⟨0, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i, ?_, ?_, ?_⟩
  · exact fun i ↦ Fin.elim0 i
  · exact fun i ↦ Fin.elim0 i
  · funext p
    simp

theorem isFiniteSeparatedKernel_add
    (M : System.{u}) (G K : M.X × M.X → ℂ)
    (hG : HilbertSchmidtConsequences.IsFiniteSeparatedKernel M G)
    (hK : HilbertSchmidtConsequences.IsFiniteSeparatedKernel M K) :
    HilbertSchmidtConsequences.IsFiniteSeparatedKernel M (G + K) := by
  obtain ⟨n, a, b, ha, hb, hGform⟩ := hG
  obtain ⟨m, c, d, hc, hd, hKform⟩ := hK
  let left : Fin (n + m) → M.X → ℂ := fun i ↦
    if hi : i < n then a (Fin.castLT i hi)
    else c (Fin.subNat n (Fin.cast (Nat.add_comm n m) i) (le_of_not_gt hi))
  let right : Fin (n + m) → M.X → ℂ := fun i ↦
    if hi : i < n then b (Fin.castLT i hi)
    else d (Fin.subNat n (Fin.cast (Nat.add_comm n m) i) (le_of_not_gt hi))
  refine ⟨n + m, left, right, ?_, ?_, ?_⟩
  · intro i
    simp only [left]
    split_ifs with hi
    · exact ha _
    · exact hc _
  · intro i
    simp only [right]
    split_ifs with hi
    · exact hb _
    · exact hd _
  · rw [hGform, hKform]
    funext p
    simp [left, right, Fin.sum_univ_add]

theorem isFiniteSeparatedKernel_smul
    (M : System.{u}) (z : ℂ) (G : M.X × M.X → ℂ)
    (hG : HilbertSchmidtConsequences.IsFiniteSeparatedKernel M G) :
    HilbertSchmidtConsequences.IsFiniteSeparatedKernel M (z • G) := by
  obtain ⟨n, a, b, ha, hb, hGform⟩ := hG
  refine ⟨n, fun i x ↦ z * a i x, b, ?_, hb, ?_⟩
  · intro i
    simpa only [Pi.smul_apply, smul_eq_mul] using (ha i).const_smul z
  · rw [hGform]
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem exists_finiteSeparated_representation_of_mem_span
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (Y : Lp ℂ 2 (M.μ.prod M.μ))
    (hY : Y ∈ finiteRectangleIndicatorSpan M hM) :
    ∃ G : M.X × M.X → ℂ, ∃ hG : MemLp G 2 (M.μ.prod M.μ),
      HilbertSchmidtConsequences.IsFiniteSeparatedKernel M G ∧
      hG.toLp G = Y := by
  change Y ∈ Submodule.span ℂ (finiteRectangleIndicatorGenerators M hM) at hY
  induction hY using Submodule.span_induction with
  | mem Y hY =>
      obtain ⟨s, hs, hfin, c, rfl⟩ := hY
      let hA := finiteRectangleAlgebra_measureDense M hM
      let hmeas := hA.measurable s hs
      let hraw : MemLp (s.indicator fun _ ↦ c) 2 (M.μ.prod M.μ) :=
        memLp_indicator_const 2 hmeas c (Or.inr hfin)
      refine ⟨s.indicator fun _ ↦ c, hraw,
        finiteRectangle_indicator_isFiniteSeparated M hM s hs c, ?_⟩
      simp only [indicatorConstLp]
  | zero =>
      refine ⟨0, MemLp.zero, isFiniteSeparatedKernel_zero M, ?_⟩
      exact MemLp.toLp_zero
        (MemLp.zero : MemLp (0 : M.X × M.X → ℂ) 2 (M.μ.prod M.μ))
  | add X Y hX hY ihX ihY =>
      obtain ⟨G, hG, hGsep, hGX⟩ := ihX
      obtain ⟨K, hK, hKsep, hKY⟩ := ihY
      refine ⟨G + K, hG.add hK,
        isFiniteSeparatedKernel_add M G K hGsep hKsep, ?_⟩
      rw [MemLp.toLp_add hG hK, hGX, hKY]
  | smul z X hX ihX =>
      obtain ⟨G, hG, hGsep, hGX⟩ := ihX
      refine ⟨z • G, hG.const_smul z,
        isFiniteSeparatedKernel_smul M z G hGsep, ?_⟩
      rw [MemLp.toLp_const_smul z hG, hGX]

theorem exists_finiteSeparatedKernel_approx
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ G : M.X × M.X → ℂ, ∃ hG : MemLp G 2 (M.μ.prod M.μ),
      HilbertSchmidtConsequences.IsFiniteSeparatedKernel M G ∧
      (eLpNorm (fun p ↦ H p - G p) 2 (M.μ.prod M.μ)).toReal < δ := by
  obtain ⟨Y, hYspan, hHY⟩ :=
    exists_finiteRectangleSpan_approx M hM H hH δ hδ
  obtain ⟨G, hG, hGsep, hGY⟩ :=
    exists_finiteSeparated_representation_of_mem_span M hM Y hYspan
  refine ⟨G, hG, hGsep, ?_⟩
  rw [← Lp.norm_toLp (fun p ↦ H p - G p) (hH.sub hG)]
  have hto :
      (hH.sub hG).toLp (fun p ↦ H p - G p) =
        hH.toLp H - hG.toLp G := by
    simpa only [Pi.sub_apply] using hH.toLp_sub hG
  rw [hto, hGY]
  exact hHY

theorem kernelOperator_hasCompactClosedBallImage
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ)) :
    HilbertSchmidtConsequences.HasCompactClosedBallImage
      (HilbertSchmidtConsequences.kernelOperator M hM H hH) := by
  apply HilbertSchmidtConsequences.hasCompactClosedBallImage_of_finite_span_approx
  intro δ hδ
  obtain ⟨G, hG, hGsep, hHG⟩ :=
    exists_finiteSeparatedKernel_approx M hM H hH δ hδ
  obtain ⟨s, hs⟩ :=
    HilbertSchmidtConsequences.finiteSeparatedKernel_operator_finite_range
      M hM G hG hGsep
  refine ⟨HilbertSchmidtConsequences.kernelOperator M hM G hG, s, hs, ?_⟩
  exact lt_of_le_of_lt
    (HilbertSchmidtConsequences.kernelOperator_sub_norm_le
      M hM H G hH hG) hHG

end Chapter02.SeparatedKernelDensity
