import Chapter02.HostKra.HostKraCartesianCube

noncomputable section

open Classical MeasureTheory
open scoped ENNReal symmDiff

namespace Chapter02.HostKraRelativeJoining

universe u

/-- The invariant sigma-algebra used at every Host--Kra successor step. -/
def invariantMeasurableSpace (M : System.{u}) : MeasurableSpace M.X :=
  MeasurableSpace.generateFrom (invariantSigmaAlgebra M)

lemma invariantMeasurableSpace_le (M : System.{u}) :
    invariantMeasurableSpace M ≤ M.measurableSpace := by
  apply MeasurableSpace.generateFrom_le
  intro s hs
  exact hs.1

/-- Real-valued form of conditional-expectation invariance under the
Koopman map.  The chapter-level statement is complex-valued; the relative
joining uses real conditional probabilities, so this specialization avoids
any scalar-coercion bridge. -/
theorem condExp_invariant_comp_real
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℝ) (hf : Integrable f M.μ) :
    condExp (invariantMeasurableSpace M) M.μ (fun x => f (M.T x)) =ᵐ[M.μ]
      condExp (invariantMeasurableSpace M) M.μ f := by
  have hcomp : Integrable (fun x => f (M.T x)) M.μ :=
    (hM.2.integrable_comp hf.aestronglyMeasurable).2 hf
  let mInv := invariantMeasurableSpace M
  let hm : mInv ≤ M.measurableSpace := invariantMeasurableSpace_le M
  letI : IsProbabilityMeasure M.μ := hM.1
  have hinv : ∀ s : Set M.X, @MeasurableSet M.X mInv s →
      M.T ⁻¹' s =ᵐ[M.μ] s := by
    intro s hs
    exact MeasurableSpace.generateFrom_induction
      (invariantSigmaAlgebra M)
      (fun t _ => M.T ⁻¹' t =ᵐ[M.μ] t)
      (by
        intro t ht htm
        rw [← measure_symmDiff_eq_zero_iff]
        simpa [Chapter00.symmDiff, Set.symmDiff_def] using ht.2)
      (by simp)
      (by
        intro t ht hti
        simpa only [Set.preimage_compl] using hti.compl)
      (by
        intro t ht hti
        have hti' : ∀ᵐ x ∂M.μ, ∀ i, (M.T ⁻¹' t i) x = (t i) x :=
          ae_all_iff.mpr hti
        filter_upwards [hti'] with x hx
        change (x ∈ M.T ⁻¹' ⋃ i, t i) = (x ∈ ⋃ i, t i)
        simp only [Set.mem_preimage, Set.mem_iUnion]
        apply propext
        constructor
        · rintro ⟨i, hi⟩
          exact ⟨i, (hx i).mp hi⟩
        · rintro ⟨i, hi⟩
          exact ⟨i, (hx i).mpr hi⟩)
      s hs
  change condExp mInv M.μ (fun x => f (M.T x)) =ᵐ[M.μ]
    condExp mInv M.μ f
  have hsetIntegral : ∀ s : Set M.X, @MeasurableSet M.X mInv s →
      (∫ x in s, condExp mInv M.μ (fun y => f (M.T y)) x ∂M.μ) =
        ∫ x in s, f x ∂M.μ := by
    intro s hs
    letI : MeasurableSpace M.X := M.measurableSpace
    have hs0 : @MeasurableSet M.X M.measurableSpace s := hm s hs
    have hsetinv := hinv s hs
    have hmap_eq : Measure.map M.T M.μ = M.μ := hM.2.map_eq
    have hgsm : AEStronglyMeasurable (s.indicator f) (Measure.map M.T M.μ) := by
      rw [hmap_eq]
      exact (hf.indicator hs0).aestronglyMeasurable
    have hmap := integral_map (μ := M.μ) (φ := M.T)
      (f := s.indicator f) hM.2.measurable.aemeasurable hgsm
    rw [hmap_eq] at hmap
    calc
      (∫ x in s, condExp mInv M.μ (fun y => f (M.T y)) x ∂M.μ) =
          ∫ x in s, f (M.T x) ∂M.μ :=
        setIntegral_condExp hm hcomp hs
      _ = ∫ x, (s.indicator f) (M.T x) ∂M.μ := by
        rw [← integral_indicator hs0]
        apply integral_congr_ae
        filter_upwards [hsetinv] with x hx
        by_cases hTx : M.T x ∈ s
        · have hxS : x ∈ s := Eq.mp hx hTx
          simp [Set.indicator, hTx, hxS]
        · have hxS : x ∉ s := fun h => hTx (Eq.mpr hx h)
          simp [Set.indicator, hTx, hxS]
      _ = ∫ x, s.indicator f x ∂M.μ := hmap.symm
      _ = ∫ x in s, f x ∂M.μ := integral_indicator hs0
  refine ae_eq_condExp_of_forall_setIntegral_eq
    (f := f) (g := condExp mInv M.μ (fun x => f (M.T x)))
      hm hf ?_ ?_ ?_
  · intro s hs hfin
    exact integrable_condExp.integrableOn
  · intro s hs hfin
    exact hsetIntegral s hs
  · exact stronglyMeasurable_condExp.aestronglyMeasurable

/-- Real indicator, used so positivity of the relative rectangle functional
is visible to Lean's ordered integral API. -/
def indicatorReal {X : Type u} (A : Set X) : X → ℝ :=
  A.indicator (fun _ ↦ 1)

lemma indicatorReal_memLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    MemLp (indicatorReal A) 2 M.μ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  exact memLp_indicator_const 2 hA 1 (Or.inr (by simp))

/-- The canonical real `L²` indicator. -/
def indicatorRealLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) : Lp ℝ 2 M.μ :=
  (indicatorReal_memLp M hM A hA).toLp (indicatorReal A)

/-- Conditional probability of `A` with respect to the invariant
sigma-algebra, represented canonically in real `L²`. -/
def invariantIndicatorLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) : Lp ℝ 2 M.μ :=
  let hm := invariantMeasurableSpace_le M
  ↑((condExpL2 (m := invariantMeasurableSpace M)
      (m0 := M.measurableSpace) (μ := M.μ) ℝ ℝ hm)
    (indicatorRealLp M hM A hA))

lemma invariantIndicatorLp_coe
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    (fun x ↦ invariantIndicatorLp M hM A hA x) =ᵐ[M.μ]
      condExp (invariantMeasurableSpace M) M.μ (indicatorReal A) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let hA2 := indicatorReal_memLp M hM A hA
  have hAint : Integrable (indicatorReal A) M.μ :=
    hA2.integrable (by norm_num)
  simpa only [invariantIndicatorLp, indicatorRealLp, hA2] using
    hA2.condExpL2_ae_eq_condExp'
      (invariantMeasurableSpace_le M) hAint

/-- Rectangle functional of the relative independent square:
`∫ E(1_A | I) E(1_B | I) dμ`.  Constructing the measure extending this
positive bimeasure is the next extension step. -/
def relativeRectangleMass
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) : ℝ :=
  @inner ℝ (Lp ℝ 2 M.μ) _
    (invariantIndicatorLp M hM A hA)
    (invariantIndicatorLp M hM B hB)

theorem relativeRectangleMass_eq_integral_condExp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    relativeRectangleMass M hM A B hA hB =
      ∫ x,
        condExp (invariantMeasurableSpace M) M.μ (indicatorReal A) x *
        condExp (invariantMeasurableSpace M) M.μ (indicatorReal B) x
        ∂M.μ := by
  rw [relativeRectangleMass, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [invariantIndicatorLp_coe M hM A hA,
    invariantIndicatorLp_coe M hM B hB] with x hAx hBx
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hAx, hBx]
  exact mul_comm _ _

theorem relativeRectangleMass_preimage
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    relativeRectangleMass M hM (M.T ⁻¹' A) (M.T ⁻¹' B)
        (hA.preimage hM.2.measurable) (hB.preimage hM.2.measurable) =
      relativeRectangleMass M hM A B hA hB := by
  letI : IsProbabilityMeasure M.μ := hM.1
  have hindA :
      indicatorReal (M.T ⁻¹' A) = fun x => indicatorReal A (M.T x) := by
    funext x
    simp only [indicatorReal, Set.indicator, Set.mem_preimage]
  have hindB :
      indicatorReal (M.T ⁻¹' B) = fun x => indicatorReal B (M.T x) := by
    funext x
    simp only [indicatorReal, Set.indicator, Set.mem_preimage]
  have hAint : Integrable (indicatorReal A) M.μ :=
    (indicatorReal_memLp M hM A hA).integrable (by norm_num)
  have hBint : Integrable (indicatorReal B) M.μ :=
    (indicatorReal_memLp M hM B hB).integrable (by norm_num)
  have hceA := condExp_invariant_comp_real M hM (indicatorReal A) hAint
  have hceB := condExp_invariant_comp_real M hM (indicatorReal B) hBint
  rw [relativeRectangleMass_eq_integral_condExp,
    relativeRectangleMass_eq_integral_condExp, hindA, hindB]
  apply integral_congr_ae
  filter_upwards [hceA, hceB] with x hxA hxB
  rw [hxA, hxB]

theorem relativeRectangleMass_symm
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    relativeRectangleMass M hM A B hA hB =
      relativeRectangleMass M hM B A hB hA := by
  exact real_inner_comm _ _

theorem relativeRectangleMass_self
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    relativeRectangleMass M hM A A hA hA =
      ‖invariantIndicatorLp M hM A hA‖ ^ 2 := by
  exact inner_self_eq_norm_sq (𝕜 := ℝ)
    (invariantIndicatorLp M hM A hA)

theorem relativeRectangleMass_nonneg
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    0 ≤ relativeRectangleMass M hM A B hA hB := by
  rw [relativeRectangleMass_eq_integral_condExp]
  apply integral_nonneg_of_ae
  have hAnonneg : ∀ᵐ x ∂M.μ, 0 ≤ indicatorReal A x := by
    filter_upwards with x
    by_cases hx : x ∈ A <;> simp [indicatorReal, Set.indicator, hx]
  have hBnonneg : ∀ᵐ x ∂M.μ, 0 ≤ indicatorReal B x := by
    filter_upwards with x
    by_cases hx : x ∈ B <;> simp [indicatorReal, Set.indicator, hx]
  have hAce := condExp_nonneg
    (m := invariantMeasurableSpace M) hAnonneg
  have hBce := condExp_nonneg
    (m := invariantMeasurableSpace M) hBnonneg
  filter_upwards [hAce, hBce] with x hAx hBx
  exact mul_nonneg hAx hBx

theorem relativeRectangleMass_univ_right
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    relativeRectangleMass M hM A Set.univ hA MeasurableSet.univ =
      M.μ.real A := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let mInv := invariantMeasurableSpace M
  let hm := invariantMeasurableSpace_le M
  have hAint : Integrable (indicatorReal A) M.μ :=
    (indicatorReal_memLp M hM A hA).integrable (by norm_num)
  have huniv : indicatorReal (Set.univ : Set M.X) = fun _ ↦ (1 : ℝ) := by
    funext x
    simp [indicatorReal]
  have hone :
      condExp mInv M.μ (indicatorReal (Set.univ : Set M.X)) =ᵐ[M.μ]
        fun _ ↦ (1 : ℝ) := by
    rw [huniv]
    exact Filter.Eventually.of_forall fun x ↦ congrFun
      (condExp_of_stronglyMeasurable hm stronglyMeasurable_const
        (integrable_const (1 : ℝ))) x
  rw [relativeRectangleMass_eq_integral_condExp]
  calc
    (∫ x,
        condExp mInv M.μ (indicatorReal A) x *
          condExp mInv M.μ (indicatorReal (Set.univ : Set M.X)) x
        ∂M.μ) =
        ∫ x, condExp mInv M.μ (indicatorReal A) x ∂M.μ := by
          apply integral_congr_ae
          filter_upwards [hone] with x hx
          rw [hx, mul_one]
    _ = ∫ x, indicatorReal A x ∂M.μ :=
      integral_condExp hm
    _ = M.μ.real A := by
      rw [show indicatorReal A = A.indicator (fun _ ↦ (1 : ℝ)) by rfl,
        integral_indicator hA]
      simp [Measure.real]

theorem relativeRectangleMass_univ_left
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    relativeRectangleMass M hM Set.univ A MeasurableSet.univ hA =
      M.μ.real A := by
  rw [relativeRectangleMass_symm]
  exact relativeRectangleMass_univ_right M hM A hA

theorem relativeRectangleMass_univ
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    relativeRectangleMass M hM Set.univ Set.univ
        MeasurableSet.univ MeasurableSet.univ = 1 := by
  rw [relativeRectangleMass_univ_right]
  letI : IsProbabilityMeasure M.μ := hM.1
  simp [Measure.real]

theorem invariantIndicatorLp_union_of_disjoint
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) :
    invariantIndicatorLp M hM (A ∪ B) (hA.union hB) =
      invariantIndicatorLp M hM A hA +
        invariantIndicatorLp M hM B hB := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let mInv := invariantMeasurableSpace M
  have hAint : Integrable (indicatorReal A) M.μ :=
    (indicatorReal_memLp M hM A hA).integrable (by norm_num)
  have hBint : Integrable (indicatorReal B) M.μ :=
    (indicatorReal_memLp M hM B hB).integrable (by norm_num)
  have hindicator :
      indicatorReal (A ∪ B) =ᵐ[M.μ]
        fun x ↦ indicatorReal A x + indicatorReal B x := by
    filter_upwards with x
    by_cases hAx : x ∈ A
    · by_cases hBx : x ∈ B
      · exact (Set.disjoint_left.1 hAB hAx hBx).elim
      · simp [indicatorReal, Set.indicator, hAx, hBx]
    · by_cases hBx : x ∈ B <;>
        simp [indicatorReal, Set.indicator, hAx, hBx]
  have hcongr :=
    condExp_congr_ae (m := mInv) hindicator
  have hadd :
      condExp mInv M.μ (fun x ↦ indicatorReal A x + indicatorReal B x)
          =ᵐ[M.μ]
        fun x ↦ condExp mInv M.μ (indicatorReal A) x +
          condExp mInv M.μ (indicatorReal B) x := by
    simpa only [Pi.add_apply] using
      (condExp_add hAint hBint mInv)
  apply Lp.ext
  filter_upwards [
    invariantIndicatorLp_coe M hM (A ∪ B) (hA.union hB),
    invariantIndicatorLp_coe M hM A hA,
    invariantIndicatorLp_coe M hM B hB,
    Lp.coeFn_add (invariantIndicatorLp M hM A hA)
      (invariantIndicatorLp M hM B hB),
    hcongr, hadd] with x hU hAcoe hBcoe hsum hcongrx haddx
  rw [hU]
  rw [hsum]
  simp only [Pi.add_apply]
  rw [hAcoe, hBcoe, hcongrx, haddx]

theorem relativeRectangleMass_union_left_of_disjoint
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B C : Set M.X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) :
    relativeRectangleMass M hM (A ∪ B) C (hA.union hB) hC =
      relativeRectangleMass M hM A C hA hC +
        relativeRectangleMass M hM B C hB hC := by
  change @inner ℝ (Lp ℝ 2 M.μ) _
      (invariantIndicatorLp M hM (A ∪ B) (hA.union hB))
      (invariantIndicatorLp M hM C hC) = _
  rw [invariantIndicatorLp_union_of_disjoint M hM A B hA hB hAB,
    inner_add_left]
  rfl

theorem relativeRectangleMass_union_right_of_disjoint
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B C : Set M.X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : Disjoint B C) :
    relativeRectangleMass M hM A (B ∪ C) hA (hB.union hC) =
      relativeRectangleMass M hM A B hA hB +
        relativeRectangleMass M hM A C hA hC := by
  rw [relativeRectangleMass_symm,
    relativeRectangleMass_union_left_of_disjoint M hM B C A hB hC hA hBC,
    relativeRectangleMass_symm M hM B A hB hA,
    relativeRectangleMass_symm M hM C A hC hA]

private lemma tendsto_toLp_real_of_tendsto_eLpNorm_sub
    {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ) (g : X → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (h : Filter.Tendsto (fun n ↦ eLpNorm (f n - g) 2 μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ (hf n).toLp (f n))
      Filter.atTop (nhds (hg.toLp g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hreal :=
    (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp h
  convert hreal using 1
  funext n
  change ‖(hf n).toLp (f n) - hg.toLp g‖ =
    (eLpNorm (f n - g) 2 μ).toReal
  rw [← Lp.norm_toLp _ ((hf n).sub hg), MemLp.toLp_sub]

/-- Increasing finite unions of measurable sets converge in real `L²` to
the indicator of their countable union. -/
theorem indicatorRealLp_accumulate_tendsto_iUnion
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : ℕ → Set M.X) (hA : ∀ n, MeasurableSet (A n)) :
    Filter.Tendsto
      (fun n ↦ indicatorRealLp M hM (Set.accumulate A n)
        (by
          induction n with
          | zero => simpa using hA 0
          | succ n ih =>
              rw [Set.accumulate_succ]
              exact ih.union (hA (n + 1))))
      Filter.atTop
      (nhds (indicatorRealLp M hM (⋃ n, A n)
        (MeasurableSet.iUnion hA))) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let U : Set M.X := ⋃ n, A n
  let S : ℕ → Set M.X := Set.accumulate A
  have hS : ∀ n, MeasurableSet (S n) := by
    intro n
    induction n with
    | zero => simpa [S] using hA 0
    | succ n ih =>
        rw [show S (n + 1) = S n ∪ A (n + 1) by
          simp [S, Set.accumulate_succ]]
        exact ih.union (hA (n + 1))
  have hU : MeasurableSet U := MeasurableSet.iUnion hA
  apply tendsto_toLp_real_of_tendsto_eLpNorm_sub M.μ
    (fun n ↦ indicatorReal (S n)) (indicatorReal U)
    (fun n ↦ indicatorReal_memLp M hM (S n) (hS n))
    (indicatorReal_memLp M hM U hU)
  have hmono : Monotone S := by
    simpa [S] using (Set.monotone_accumulate (s := A))
  have hsymm : ∀ n, S n ∆ U = U \ S n := by
    intro n
    have hsub : S n ⊆ U := Set.accumulate_subset_iUnion n
    ext x
    simp only [Set.mem_symmDiff, Set.mem_diff]
    tauto
  have hdiffmeas : ∀ n, MeasurableSet (U \ S n) :=
    fun n ↦ hU.diff (hS n)
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
      Filter.Tendsto (fun n ↦ M.μ (S n ∆ U))
        Filter.atTop (nhds 0) := by
    simp_rw [hsymm]
    have ht := tendsto_measure_iInter_atTop
      (μ := M.μ) (fun n ↦ (hdiffmeas n).nullMeasurableSet)
      hantitone ⟨0, by finiteness⟩
    rw [hinter, measure_empty] at ht
    exact ht
  have hrpow :
      Filter.Tendsto
        (fun n ↦ M.μ (S n ∆ U) ^ (1 / (2 : ENNReal).toReal))
        Filter.atTop (nhds 0) := by
    convert (ENNReal.continuous_rpow_const.tendsto 0).comp hmeasure using 1
    simp
  convert hrpow using 1
  funext n
  change eLpNorm
    ((S n).indicator (fun _ ↦ (1 : ℝ)) -
      U.indicator (fun _ ↦ (1 : ℝ))) 2 M.μ =
    M.μ (S n ∆ U) ^ (1 / (2 : ENNReal).toReal)
  rw [eLpNorm_indicator_sub_indicator]
  rw [eLpNorm_indicator_const (p := (2 : ENNReal)) (c := (1 : ℝ))
    ((hS n).symmDiff hU) (by norm_num) (by norm_num)]
  simp

/-- Conditional expectation preserves the preceding increasing-union
convergence because `condExpL2` is a continuous linear projection. -/
theorem invariantIndicatorLp_accumulate_tendsto_iUnion
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : ℕ → Set M.X) (hA : ∀ n, MeasurableSet (A n)) :
    Filter.Tendsto
      (fun n ↦ invariantIndicatorLp M hM (Set.accumulate A n)
        (by
          induction n with
          | zero => simpa using hA 0
          | succ n ih =>
              rw [Set.accumulate_succ]
              exact ih.union (hA (n + 1))))
      Filter.atTop
      (nhds (invariantIndicatorLp M hM (⋃ n, A n)
        (MeasurableSet.iUnion hA))) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let hm := invariantMeasurableSpace_le M
  let CE := condExpL2 (m := invariantMeasurableSpace M)
    (m0 := M.measurableSpace) (μ := M.μ) ℝ ℝ hm
  have hraw :=
    indicatorRealLp_accumulate_tendsto_iUnion M hM A hA
  have hCE :
      Filter.Tendsto
        (fun n ↦ CE (indicatorRealLp M hM (Set.accumulate A n)
          (by
            induction n with
            | zero => simpa using hA 0
            | succ n ih =>
                rw [Set.accumulate_succ]
                exact ih.union (hA (n + 1)))))
        Filter.atTop
        (nhds (CE (indicatorRealLp M hM (⋃ n, A n)
          (MeasurableSet.iUnion hA)))) :=
    CE.continuous.continuousAt.tendsto.comp hraw
  have hcoe :=
    continuous_subtype_val.continuousAt.tendsto.comp hCE
  simpa only [invariantIndicatorLp, hm, CE] using hcoe

/-- Continuity from below of the relative rectangle functional in its first
coordinate.  This supplies the countable-additivity limit missing from the
finite rectangle algebra. -/
theorem relativeRectangleMass_accumulate_tendsto_iUnion_left
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : ℕ → Set M.X) (hA : ∀ n, MeasurableSet (A n))
    (B : Set M.X) (hB : MeasurableSet B) :
    Filter.Tendsto
      (fun n ↦ relativeRectangleMass M hM (Set.accumulate A n) B
        (by
          induction n with
          | zero => simpa using hA 0
          | succ n ih =>
              rw [Set.accumulate_succ]
              exact ih.union (hA (n + 1))) hB)
      Filter.atTop
      (nhds (relativeRectangleMass M hM (⋃ n, A n) B
        (MeasurableSet.iUnion hA) hB)) := by
  have hconv :=
    invariantIndicatorLp_accumulate_tendsto_iUnion M hM A hA
  have hinner :=
    (innerSL ℝ (invariantIndicatorLp M hM B hB)).continuous.continuousAt.tendsto.comp
      hconv
  simpa only [relativeRectangleMass, Function.comp_apply, real_inner_comm] using hinner

/-- Symmetric continuity from below in the second rectangle coordinate. -/
theorem relativeRectangleMass_accumulate_tendsto_iUnion_right
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (B : ℕ → Set M.X) (hB : ∀ n, MeasurableSet (B n)) :
    Filter.Tendsto
      (fun n ↦ relativeRectangleMass M hM A (Set.accumulate B n) hA
        (by
          induction n with
          | zero => simpa using hB 0
          | succ n ih =>
              rw [Set.accumulate_succ]
              exact ih.union (hB (n + 1))))
      Filter.atTop
      (nhds (relativeRectangleMass M hM A (⋃ n, B n) hA
        (MeasurableSet.iUnion hB))) := by
  have hleft :=
    relativeRectangleMass_accumulate_tendsto_iUnion_left
      M hM B hB A hA
  simpa only [relativeRectangleMass_symm M hM] using hleft

lemma measurableSet_accumulate
    {M : System.{u}} (A : ℕ → Set M.X)
    (hA : ∀ n, MeasurableSet (A n)) (n : ℕ) :
    MeasurableSet (Set.accumulate A n) := by
  induction n with
  | zero => simpa using hA 0
  | succ n ih =>
      rw [Set.accumulate_succ]
      exact ih.union (hA (n + 1))

lemma accumulate_disjoint_later
    {M : System.{u}} (A : ℕ → Set M.X)
    (hdisj : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    {n m : ℕ} (hnm : n < m) :
    Disjoint (Set.accumulate A n) (A m) := by
  induction n with
  | zero =>
      simpa using hdisj (Nat.ne_of_lt hnm)
  | succ n ih =>
      rw [Set.accumulate_succ, Set.disjoint_left]
      intro x hx hxm
      rcases hx with hx | hx
      · exact Set.disjoint_left.1
          (ih (Nat.lt_trans (Nat.lt_succ_self n) hnm)) hx hxm
      · exact Set.disjoint_left.1 (hdisj (Nat.ne_of_lt hnm)) hx hxm

private lemma tendsto_nat_sub_atTop (k : ℕ) :
    Filter.Tendsto (fun n : ℕ ↦ n - k) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards [Filter.eventually_ge_atTop (b + k)] with n hn
  omega

/-- Finite additivity identifies the mass of an accumulated disjoint union
with the corresponding finite partial sum. -/
theorem relativeRectangleMass_accumulate_eq_sum
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : ℕ → Set M.X) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (B : Set M.X) (hB : MeasurableSet B) (n : ℕ) :
    relativeRectangleMass M hM (Set.accumulate A n) B
        (measurableSet_accumulate A hA n) hB =
      ∑ k ∈ Finset.range (n + 1),
        relativeRectangleMass M hM (A k) B (hA k) hB := by
  induction n with
  | zero =>
      simp [Set.accumulate]
  | succ n ih =>
      have hstep :=
        relativeRectangleMass_union_left_of_disjoint M hM
        (Set.accumulate A n) (A (n + 1)) B
        (measurableSet_accumulate A hA n) (hA (n + 1)) hB
        (accumulate_disjoint_later A hdisj (Nat.lt_succ_self n))
      calc
        relativeRectangleMass M hM (Set.accumulate A (n + 1)) B
            (measurableSet_accumulate A hA (n + 1)) hB =
            relativeRectangleMass M hM (Set.accumulate A n) B
                (measurableSet_accumulate A hA n) hB +
              relativeRectangleMass M hM (A (n + 1)) B
                (hA (n + 1)) hB := by
                  simpa only [Set.accumulate_succ] using hstep
        _ = (∑ k ∈ Finset.range (n + 1),
              relativeRectangleMass M hM (A k) B (hA k) hB) +
              relativeRectangleMass M hM (A (n + 1)) B
                (hA (n + 1)) hB := by rw [ih]
        _ = ∑ k ∈ Finset.range ((n + 1) + 1),
              relativeRectangleMass M hM (A k) B (hA k) hB := by
                exact (Finset.sum_range_succ
                  (fun k ↦ relativeRectangleMass M hM (A k) B (hA k) hB)
                  (n + 1)).symm

/-- Countable additivity of the relative rectangle functional in its first
coordinate, stated as a convergent nonnegative series. -/
theorem relativeRectangleMass_hasSum_iUnion_left
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : ℕ → Set M.X) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (B : Set M.X) (hB : MeasurableSet B) :
    HasSum
      (fun n ↦ relativeRectangleMass M hM (A n) B (hA n) hB)
      (relativeRectangleMass M hM (⋃ n, A n) B
        (MeasurableSet.iUnion hA) hB) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun n ↦ relativeRectangleMass_nonneg M hM (A n) B (hA n) hB) _).2
  have hacc :=
    relativeRectangleMass_accumulate_tendsto_iUnion_left
      M hM A hA B hB
  have hshift := hacc.comp (tendsto_nat_sub_atTop 1)
  apply hshift.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  simp only [Function.comp_apply]
  have hs := relativeRectangleMass_accumulate_eq_sum
    M hM A hA hdisj B hB (n - 1)
  rw [Nat.sub_add_cancel hn] at hs
  exact hs

/-- Symmetric countable additivity in the second rectangle coordinate. -/
theorem relativeRectangleMass_hasSum_iUnion_right
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (B : ℕ → Set M.X) (hB : ∀ n, MeasurableSet (B n))
    (hdisj : Pairwise (fun i j ↦ Disjoint (B i) (B j))) :
    HasSum
      (fun n ↦ relativeRectangleMass M hM A (B n) hA (hB n))
      (relativeRectangleMass M hM A (⋃ n, B n) hA
        (MeasurableSet.iUnion hB)) := by
  simpa only [relativeRectangleMass_symm M hM] using
    (relativeRectangleMass_hasSum_iUnion_left
      M hM B hB hdisj A hA)

theorem relativeRectangleMass_empty_left
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (B : Set M.X) (hB : MeasurableSet B) :
    relativeRectangleMass M hM ∅ B MeasurableSet.empty hB = 0 := by
  have h :=
    relativeRectangleMass_union_left_of_disjoint M hM
      ∅ ∅ B MeasurableSet.empty MeasurableSet.empty hB
      (Set.disjoint_empty ∅)
  have h' :
      relativeRectangleMass M hM ∅ B MeasurableSet.empty hB =
        relativeRectangleMass M hM ∅ B MeasurableSet.empty hB +
          relativeRectangleMass M hM ∅ B MeasurableSet.empty hB := by
    simpa only [Set.empty_union] using h
  linarith

theorem relativeRectangleMass_empty_right
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    relativeRectangleMass M hM A ∅ hA MeasurableSet.empty = 0 := by
  rw [relativeRectangleMass_symm]
  exact relativeRectangleMass_empty_left M hM A hA

/-- For every fixed measurable second coordinate, the relative rectangle
functional is now a genuine measure on the first coordinate. -/
def relativeSectionMeasure
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (B : Set M.X) (hB : MeasurableSet B) : Measure M.X :=
  Measure.ofMeasurable
    (fun A hA ↦ ENNReal.ofReal
      (relativeRectangleMass M hM A B hA hB))
    (by
      dsimp
      rw [relativeRectangleMass_empty_left]
      simp)
    (by
      intro A hA hdisj
      have hs :=
        relativeRectangleMass_hasSum_iUnion_left M hM A hA hdisj B hB
      dsimp
      rw [← hs.tsum_eq]
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun n ↦ relativeRectangleMass_nonneg
          M hM (A n) B (hA n) hB)
        hs.summable)

theorem relativeSectionMeasure_apply
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (B : Set M.X) (hB : MeasurableSet B)
    (A : Set M.X) (hA : MeasurableSet A) :
    relativeSectionMeasure M hM B hB A =
      ENNReal.ofReal (relativeRectangleMass M hM A B hA hB) := by
  exact Measure.ofMeasurable_apply A hA

theorem relativeSectionMeasure_univ
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (B : Set M.X) (hB : MeasurableSet B) :
    relativeSectionMeasure M hM B hB Set.univ = M.μ B := by
  letI : IsProbabilityMeasure M.μ := hM.1
  rw [relativeSectionMeasure_apply M hM B hB Set.univ MeasurableSet.univ,
    relativeRectangleMass_univ_left]
  exact ofReal_measureReal (measure_ne_top M.μ B)

/-- The semiring of measurable rectangles generating the product
sigma-algebra. -/
def measurableRectangles (M : System.{u}) : Set (Set (M.X × M.X)) :=
  {s | ∃ A B : Set M.X,
    MeasurableSet A ∧ MeasurableSet B ∧ s = A ×ˢ B}

theorem measurableRectangles_isSetSemiring (M : System.{u}) :
    IsSetSemiring (measurableRectangles M) := by
  refine
    { empty_mem := ?_
      inter_mem := ?_
      diff_eq_sUnion' := ?_ }
  · exact ⟨∅, ∅, MeasurableSet.empty, MeasurableSet.empty, by simp⟩
  · intro s hs t ht
    rcases hs with ⟨A, B, hA, hB, rfl⟩
    rcases ht with ⟨C, D, hC, hD, rfl⟩
    refine ⟨A ∩ C, B ∩ D, hA.inter hC, hB.inter hD, ?_⟩
    ext p
    simp only [Set.mem_inter_iff, Set.mem_prod]
    tauto
  · intro s hs t ht
    rcases hs with ⟨A, B, hA, hB, rfl⟩
    rcases ht with ⟨C, D, hC, hD, rfl⟩
    let R₁ : Set (M.X × M.X) := (A \ C) ×ˢ B
    let R₂ : Set (M.X × M.X) := (A ∩ C) ×ˢ (B \ D)
    let I : Finset (Set (M.X × M.X)) := {R₁, R₂}
    refine ⟨I, ?_, ?_, ?_⟩
    · intro R hR
      have hR' : R = R₁ ∨ R = R₂ := by
        simpa [I] using hR
      rcases hR' with rfl | rfl
      · exact ⟨A \ C, B, hA.diff hC, hB, rfl⟩
      · exact ⟨A ∩ C, B \ D, hA.inter hC, hB.diff hD, rfl⟩
    · have hd : Disjoint R₁ R₂ := by
        rw [Set.disjoint_left]
        intro p hp₁ hp₂
        exact hp₁.1.2 hp₂.1.2
      intro X hX Y hY hXY
      have hX' : X = R₁ ∨ X = R₂ := by simpa [I] using hX
      have hY' : Y = R₁ ∨ Y = R₂ := by simpa [I] using hY
      rcases hX' with rfl | rfl <;> rcases hY' with rfl | rfl
      · exact (hXY rfl).elim
      · exact hd
      · exact hd.symm
      · exact (hXY rfl).elim
    · ext p
      simp only [Set.mem_diff, Set.mem_prod]
      simp [I, R₁, R₂]
      tauto

end Chapter02.HostKraRelativeJoining
