import Chapter02.HostKra.HostKraStructuredApproximation
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.MeasuredSets

open Classical Filter MeasureTheory Set Topology
open scoped ENNReal symmDiff

noncomputable section

namespace Chapter02.HostKraFiniteCoordinate

universe u v

/-- The part of a supremum of measurable spaces supported on a specified
set of coordinates. -/
def coordinateSup {α : Type u} {ι : Type v}
    (m : ι → MeasurableSpace α) (t : Set ι) : MeasurableSpace α :=
  ⨆ i, ⨆ (_hi : i ∈ t), m i

theorem coordinateSup_mono {α : Type u} {ι : Type v}
    (m : ι → MeasurableSpace α) {s t : Set ι} (hst : s ⊆ t) :
    coordinateSup m s ≤ coordinateSup m t := by
  refine iSup_le fun i ↦ ?_
  refine iSup_le fun hi ↦ ?_
  exact le_iSup_of_le i (le_iSup_of_le (hst hi) le_rfl)

/-- A set measurable in an arbitrary supremum of measurable spaces already
depends on only countably many members of that family.  This is the precise
countable-support fact needed before exhausting the fifteen-dual factor by
finite coordinate factors. -/
theorem measurableSet_iSup_exists_countable_support
    {α : Type u} {ι : Type v} (m : ι → MeasurableSpace α) {s : Set α}
    (hs : MeasurableSet[⨆ i, m i] s) :
    ∃ t : Set ι, t.Countable ∧ MeasurableSet[coordinateSup m t] s := by
  rw [MeasurableSpace.measurableSpace_iSup_eq] at hs
  induction s, hs using MeasurableSpace.generateFrom_induction with
  | hC s hs _ =>
      obtain ⟨i, hi⟩ := hs
      refine ⟨{i}, countable_singleton i, ?_⟩
      have hle : m i ≤ coordinateSup m {i} := by
        calc
          m i ≤ ⨆ (_hi : i ∈ ({i} : Set ι)), m i :=
            le_iSup (fun _hi : i ∈ ({i} : Set ι) ↦ m i) (by simp)
          _ ≤ coordinateSup m {i} :=
            le_iSup (fun j ↦ ⨆ (_hj : j ∈ ({i} : Set ι)), m j) i
      exact hle s hi
  | empty =>
      exact
        ⟨∅, countable_empty,
          @MeasurableSpace.measurableSet_empty α (coordinateSup m ∅)⟩
  | compl s _ ih =>
      obtain ⟨t, ht, hs⟩ := ih
      exact ⟨t, ht, hs.compl⟩
  | iUnion f _ ih =>
      choose t ht hmeas using ih
      refine ⟨⋃ n, t n, countable_iUnion ht, MeasurableSet.iUnion fun n ↦ ?_⟩
      exact
        (coordinateSup_mono m
          (subset_iUnion (fun n ↦ t n) n)) (f n) (hmeas n)

/-- A measurable map from a supremum into a countably generated measurable
space depends on only countably many source coordinates. -/
theorem measurable_iSup_exists_countable_support
    {α : Type u} {ι : Type v} {β : Type*}
    (m : ι → MeasurableSpace α) [mβ : MeasurableSpace β]
    [MeasurableSpace.CountablyGenerated β] (f : α → β)
    (hf : @Measurable α β (⨆ i, m i) mβ f) :
    ∃ t : Set ι, t.Countable ∧
      @Measurable α β (coordinateSup m t) mβ f := by
  have hpre (n : ℕ) :
      MeasurableSet[⨆ i, m i]
        (f ⁻¹' MeasurableSpace.natGeneratingSequence β n) :=
    hf (MeasurableSpace.measurableSet_natGeneratingSequence n)
  choose t ht hmeas using fun n ↦
    measurableSet_iSup_exists_countable_support m (hpre n)
  let support : Set ι := ⋃ n, t n
  refine ⟨support, countable_iUnion ht, ?_⟩
  letI : MeasurableSpace α := coordinateSup m support
  rw [← MeasurableSpace.generateFrom_natGeneratingSequence β]
  apply measurable_generateFrom
  rintro _ ⟨n, rfl⟩
  exact
    (coordinateSup_mono m
      (show t n ⊆ support from subset_iUnion (fun k ↦ t k) n))
      _ (hmeas n)

/-- An almost-everywhere strongly measurable complex-valued function on a
supremum is already almost-everywhere strongly measurable on a countably
supported sub-supremum. -/
theorem aestronglyMeasurable_iSup_exists_countable_support
    {α : Type u} {ι : Type v} [m₀ : MeasurableSpace α]
    (m : ι → MeasurableSpace α) (μ : Measure α) (f : α → ℂ)
    (hf : @AEStronglyMeasurable α ℂ _ (⨆ i, m i) m₀ f μ) :
    ∃ t : Set ι, t.Countable ∧
      @AEStronglyMeasurable α ℂ _ (coordinateSup m t) m₀ f μ := by
  obtain ⟨t, ht, hmeas⟩ :=
    measurable_iSup_exists_countable_support m (hf.mk f)
      hf.stronglyMeasurable_mk.measurable
  exact ⟨t, ht, ⟨hf.mk f, hmeas.stronglyMeasurable, hf.ae_eq_mk⟩⟩

/-- Every `L²` vector measurable with respect to a supremum belongs exactly
to the `lpMeas` subspace of some countably supported sub-supremum. -/
theorem mem_lpMeas_iSup_exists_countable_support
    {α : Type u} {ι : Type v} [m₀ : MeasurableSpace α]
    (m : ι → MeasurableSpace α) (μ : Measure α) (F : Lp ℂ 2 μ)
    (hF : F ∈ MeasureTheory.lpMeas ℂ ℂ (⨆ i, m i) 2 μ) :
    ∃ t : Set ι, t.Countable ∧
      F ∈ MeasureTheory.lpMeas ℂ ℂ (coordinateSup m t) 2 μ := by
  rw [MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable] at hF
  obtain ⟨t, ht, hFt⟩ :=
    aestronglyMeasurable_iSup_exists_countable_support m μ
      (fun x ↦ F x) hF
  exact
    ⟨t, ht,
      MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable.mpr hFt⟩

/-- Sets which are measurable at some stage of a sequence of measurable
spaces. -/
def stageMeasurableSets {α : Type u}
    (m : ℕ → MeasurableSpace α) : Set (Set α) :=
  {s | ∃ n, MeasurableSet[m n] s}

/-- For an increasing sequence of measurable spaces, the sets measurable at
some finite stage form a set ring. -/
theorem stageMeasurableSets_isSetRing
    {α : Type u} (m : ℕ → MeasurableSpace α) (hm : Monotone m) :
    IsSetRing (stageMeasurableSets m) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨0, @MeasurableSpace.measurableSet_empty α (m 0)⟩
  · rintro s t ⟨i, hs⟩ ⟨j, ht⟩
    refine ⟨max i j, ?_⟩
    exact
      (hm (Nat.le_max_left i j) s hs).union
        (hm (Nat.le_max_right i j) t ht)
  · rintro s t ⟨i, hs⟩ ⟨j, ht⟩
    refine ⟨max i j, ?_⟩
    exact
      (hm (Nat.le_max_left i j) s hs).diff
        (hm (Nat.le_max_right i j) t ht)

theorem iSup_eq_generateFrom_stageMeasurableSets
    {α : Type u} (m : ℕ → MeasurableSpace α) :
    (⨆ n, m n) =
      MeasurableSpace.generateFrom (stageMeasurableSets m) := by
  simpa only [stageMeasurableSets] using
    MeasurableSpace.measurableSpace_iSup_eq m

/-- In a finite measure space, every set measurable for the supremum of an
increasing sequence admits finite-stage approximants whose symmetric
differences have measure tending to zero. -/
theorem exists_stage_measurable_tendsto_symmDiff
    {α : Type u} [m₀ : MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (m : ℕ → MeasurableSpace α)
    (hm : Monotone m) (hm₀ : ∀ n, m n ≤ m₀) {s : Set α}
    (hs : MeasurableSet[⨆ n, m n] s) :
    ∃ t : ℕ → Set α,
      (∀ n, ∃ k, MeasurableSet[m k] (t n)) ∧
      Tendsto (fun n ↦ μ (t n ∆ s)) atTop (𝓝 0) := by
  let C : Set (Set α) := stageMeasurableSets m
  have hC : IsSetRing C := stageMeasurableSets_isSetRing m hm
  have hmInf : (⨆ n, m n) ≤ m₀ := iSup_le hm₀
  let ν : @Measure α (⨆ n, m n) := μ.trim hmInf
  have hcover :
      ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ ν (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, countable_singleton Set.univ, ?_, by simp⟩
    rintro _ rfl
    exact ⟨0, @MeasurableSet.univ α (m 0)⟩
  have hgen :
      (⨆ n, m n) = MeasurableSpace.generateFrom C := by
    exact iSup_eq_generateFrom_stageMeasurableSets m
  have happrox (n : ℕ) :
      ∃ t ∈ C,
        ν (t ∆ s) <
          ENNReal.ofReal ((1 : ℝ) / (n + 1)) := by
    exact
      @exists_measure_symmDiff_lt_of_generateFrom_isSetRing
        α (⨆ n, m n) ν inferInstance C hC hcover hgen s hs
        (ENNReal.ofReal ((1 : ℝ) / (n + 1))) (by positivity)
  choose t htC ht using happrox
  refine ⟨t, htC, ?_⟩
  have hνμ :
      (fun n ↦ ν (t n ∆ s)) = fun n ↦ μ (t n ∆ s) := by
    funext n
    obtain ⟨k, htk⟩ := htC n
    have htInf : MeasurableSet[⨆ n, m n] (t n) :=
      (le_iSup m k) _ htk
    exact MeasureTheory.trim_measurableSet_eq hmInf (htInf.symmDiff hs)
  rw [← hνμ]
  have hbound :
      Tendsto
        (fun n : ℕ ↦ ENNReal.ofReal ((1 : ℝ) / (n + 1)))
        atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1))
          atTop (𝓝 0))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n ↦ ν (t n ∆ s))
    (g := fun _ ↦ (0 : ENNReal))
    (h := fun n ↦ ENNReal.ofReal ((1 : ℝ) / (n + 1)))
    tendsto_const_nhds hbound
  · exact Filter.Eventually.of_forall fun _ ↦ bot_le
  · exact Filter.Eventually.of_forall fun n ↦ (ht n).le

/-- If an increasing sequence of sub-σ-algebras has supremum `m∞`, then the
union of the corresponding measurable `L²` subspaces is dense in the
`m∞`-measurable subspace.  This formulation only asserts density for the
specified vector, so no completion hypothesis on the ambient measurable
space is needed. -/
theorem mem_topologicalClosure_iSup_lpMeas
    {α : Type u} [m₀ : MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (m : ℕ → MeasurableSpace α)
    (hm : Monotone m) (hm₀ : ∀ n, m n ≤ m₀)
    (F : Lp ℂ 2 μ)
    (hF : F ∈ MeasureTheory.lpMeas ℂ ℂ (⨆ n, m n) 2 μ) :
    F ∈
      (⨆ n, MeasureTheory.lpMeas ℂ ℂ (m n) 2 μ).topologicalClosure := by
  let U : ℕ → Submodule ℂ (Lp ℂ 2 μ) :=
    fun n ↦ MeasureTheory.lpMeas ℂ ℂ (m n) 2 μ
  let K : Submodule ℂ (Lp ℂ 2 μ) := (⨆ n, U n).topologicalClosure
  have hKclosed : IsClosed (K : Set (Lp ℂ 2 μ)) := by
    dsimp only [K]
    exact Submodule.isClosed_topologicalClosure _
  have hmInf : (⨆ n, m n) ≤ m₀ := iSup_le hm₀
  have hFmeas :
      @AEStronglyMeasurable α ℂ _ (⨆ n, m n) m₀
        (fun x ↦ F x) μ :=
    MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable.mp hF
  change F ∈ K
  refine MeasureTheory.Lp.induction_stronglyMeasurable
    (F := ℂ) (p := (2 : ENNReal)) hmInf (by norm_num)
    (fun G ↦ G ∈ K) ?_ ?_ ?_ F hFmeas
  · intro c s hs hμs
    rw [MeasureTheory.Lp.simpleFunc.coe_indicatorConst]
    obtain ⟨t, htstage, htendsto⟩ :=
      exists_stage_measurable_tendsto_symmDiff μ m hm hm₀ hs
    choose k htk using htstage
    have ht₀ (n : ℕ) : MeasurableSet[m₀] (t n) :=
      hm₀ (k n) _ (htk n)
    have hμt (n : ℕ) : μ (t n) ≠ ∞ :=
      (measure_lt_top μ (t n)).ne
    have hqK (n : ℕ) :
        MeasureTheory.indicatorConstLp
            (2 : ENNReal) (ht₀ n) (hμt n) c ∈ K := by
      apply Submodule.le_topologicalClosure
      exact
        (le_iSup U (k n))
          (MeasureTheory.mem_lpMeas_indicatorConstLp
            (hm₀ (k n)) (htk n) (hμt n))
    have hq :
        Tendsto
          (fun n ↦
            MeasureTheory.indicatorConstLp
              (2 : ENNReal) (ht₀ n) (hμt n) c)
          atTop
          (𝓝
            (MeasureTheory.indicatorConstLp
              (2 : ENNReal) (hmInf s hs) hμs.ne c)) := by
      exact
        MeasureTheory.tendsto_indicatorConstLp_set
          (p := (2 : ENNReal)) (s := s) (c := c)
          (ht := ht₀) (hμt := hμt) (by norm_num) htendsto
    exact
      hKclosed.mem_of_tendsto hq
        (Filter.Eventually.of_forall hqK)
  · intro f g hf hg hfm hgm hdisj hfK hgK
    exact K.add_mem hfK hgK
  · change
      IsClosed
        ((fun G :
            MeasureTheory.lpMeas ℂ ℝ (⨆ n, m n) 2 μ ↦
              (G : Lp ℂ 2 μ)) ⁻¹' (K : Set (Lp ℂ 2 μ)))
    exact hKclosed.preimage continuous_subtype_val

/-- Enlarging the source measurable space enlarges the corresponding
measurable `L²` subspace. -/
theorem lpMeas_mono
    {α : Type u} [m₀ : MeasurableSpace α] (μ : Measure α)
    {m m' : MeasurableSpace α} (hmm' : m ≤ m') :
    @MeasureTheory.lpMeas α ℂ ℂ _ _ _ m m₀ 2 μ ≤
      @MeasureTheory.lpMeas α ℂ ℂ _ _ _ m' m₀ 2 μ := by
  intro F hF
  rw [MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable] at hF ⊢
  exact
    ⟨hF.mk (fun x ↦ F x),
      hF.stronglyMeasurable_mk.mono hmm',
      hF.ae_eq_mk⟩

/-- Quantitative finite-stage consequence of
`mem_topologicalClosure_iSup_lpMeas`. -/
theorem exists_lpMeas_stage_norm_sub_lt
    {α : Type u} [m₀ : MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (m : ℕ → MeasurableSpace α)
    (hm : Monotone m) (hm₀ : ∀ n, m n ≤ m₀)
    (F : Lp ℂ 2 μ)
    (hF : F ∈ MeasureTheory.lpMeas ℂ ℂ (⨆ n, m n) 2 μ)
    {η : ℝ} (hη : 0 < η) :
    ∃ n : ℕ, ∃ Q : Lp ℂ 2 μ,
      Q ∈ MeasureTheory.lpMeas ℂ ℂ (m n) 2 μ ∧
      ‖F - Q‖ < η := by
  let U : ℕ → Submodule ℂ (Lp ℂ 2 μ) :=
    fun n ↦ MeasureTheory.lpMeas ℂ ℂ (m n) 2 μ
  have hU : Monotone U := by
    intro i j hij
    exact lpMeas_mono μ (hm hij)
  have hclosure :=
    mem_topologicalClosure_iSup_lpMeas μ m hm hm₀ F hF
  change F ∈ (⨆ n, U n).topologicalClosure at hclosure
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Metric.mem_closure_iff] at hclosure
  obtain ⟨Q, hQ, hdist⟩ := hclosure η hη
  rw [dist_eq_norm] at hdist
  obtain ⟨n, hQn⟩ :
      ∃ n, Q ∈ U n := by
    exact
      (Submodule.mem_iSup_of_directed U hU.directed_le).mp
        (show Q ∈ ⨆ n, U n from hQ)
  exact ⟨n, Q, hQn, hdist⟩

/-- A coordinate space supported on a finite exhaustion increases to the
space supported on the exhausted countable set. -/
theorem iSup_coordinateSup_finiteExhaustion_eq
    {α : Type u} {ι : Type v} (m : ι → MeasurableSpace α)
    {s : Set ι} (K : Set.FiniteExhaustion s) :
    (⨆ n, coordinateSup m (K n)) = coordinateSup m s := by
  apply le_antisymm
  · refine iSup_le fun n ↦ coordinateSup_mono m ?_
    intro i hi
    rw [← K.iUnion_eq]
    exact Set.mem_iUnion.mpr ⟨n, hi⟩
  · unfold coordinateSup
    refine iSup_le fun i ↦ ?_
    refine iSup_le fun hi ↦ ?_
    have hiUnion : i ∈ ⋃ n, K n := by
      rwa [K.iUnion_eq]
    obtain ⟨n, hin⟩ := Set.mem_iUnion.mp hiUnion
    exact
      le_iSup_of_le n
        (le_iSup_of_le i (le_iSup_of_le hin le_rfl))

/-- Every vector measurable with respect to a coordinate supremum can be
approximated in `L²` by a vector depending on only finitely many
coordinates. -/
theorem exists_finite_coordinate_norm_sub_lt
    {α : Type u} {ι : Type v} [m₀ : MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (m : ι → MeasurableSpace α) (hm₀ : ∀ i, m i ≤ m₀)
    (F : Lp ℂ 2 μ)
    (hF : F ∈ MeasureTheory.lpMeas ℂ ℂ (⨆ i, m i) 2 μ)
    {η : ℝ} (hη : 0 < η) :
    ∃ t : Set ι, t.Finite ∧
      ∃ Q : Lp ℂ 2 μ,
        Q ∈ MeasureTheory.lpMeas ℂ ℂ (coordinateSup m t) 2 μ ∧
        ‖F - Q‖ < η := by
  obtain ⟨s, hsCount, hFs⟩ :=
    mem_lpMeas_iSup_exists_countable_support m μ F hF
  let K : Set.FiniteExhaustion s := hsCount.finiteExhaustion
  let stages : ℕ → MeasurableSpace α :=
    fun n ↦ coordinateSup m (K n)
  have hstages : Monotone stages := by
    intro i j hij
    exact coordinateSup_mono m (K.mono hij)
  have hstages₀ (n : ℕ) : stages n ≤ m₀ := by
    unfold stages coordinateSup
    exact iSup_le fun i ↦ iSup_le fun _ ↦ hm₀ i
  have hstageSup :
      (⨆ n, stages n) = coordinateSup m s := by
    exact iSup_coordinateSup_finiteExhaustion_eq m K
  have hFstage :
      F ∈ MeasureTheory.lpMeas ℂ ℂ (⨆ n, stages n) 2 μ := by
    rw [hstageSup]
    exact hFs
  obtain ⟨n, Q, hQ, hnorm⟩ :=
    exists_lpMeas_stage_norm_sub_lt
      μ stages hstages hstages₀ F hFstage hη
  exact ⟨K n, K.finite n, Q, hQ, hnorm⟩

/-- The sub-σ-algebra generated by a specified finite (or arbitrary)
collection of canonical fifteen-dual coordinates. -/
def finiteFifteenDualMeasurableSpace
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)) :
    MeasurableSpace M.X :=
  coordinateSup
    (fun d :
      HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM ↦
        MeasurableSpace.comap d.1 (borel ℂ))
    t

/-- The conditional projection to the full fifteen-dual factor can be
approximated in `L²` by a vector measurable with respect to finitely many
canonical fifteen-dual coordinates. -/
theorem exists_finite_fifteenDual_projection_approximation
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) {η : ℝ} (hη : 0 < η) :
    ∃ t : Set
        (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM),
      t.Finite ∧
      ∃ Q : Lp ℂ 2 M.μ,
        Q ∈ MeasureTheory.lpMeas ℂ ℂ
          (finiteFifteenDualMeasurableSpace M hM t) 2 M.μ ∧
        ‖HostKraDualSigma.condExpL2Value M.μ
            (HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM)
            F - Q‖ < η := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let 𝒟 :=
    HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM
  let generators : 𝒟 → MeasurableSpace M.X :=
    fun d ↦ MeasurableSpace.comap d.1 (borel ℂ)
  let hm :=
    HostKraFifteenDualFactor.fifteenDualMeasurableSpace_le M hM
  let P := HostKraDualSigma.condExpL2Value M.μ hm F
  have hgenerators (d : 𝒟) : generators d ≤ M.measurableSpace := by
    apply le_trans (le_iSup generators d)
    simpa only [generators, 𝒟,
      HostKraFifteenDualFactor.fifteenDualMeasurableSpace,
      HostKraDualSigma.generatedByFunctions] using hm
  have hP :
      P ∈ MeasureTheory.lpMeas ℂ ℂ (⨆ d, generators d) 2 M.μ := by
    rw [MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable]
    simpa only [P, hm, generators, 𝒟,
      HostKraDualSigma.condExpL2Value,
      HostKraFifteenDualFactor.fifteenDualMeasurableSpace,
      HostKraDualSigma.generatedByFunctions] using
      ((MeasureTheory.condExpL2 ℂ ℂ hm) F).2
  obtain ⟨t, ht, Q, hQ, hnorm⟩ :=
    exists_finite_coordinate_norm_sub_lt
      M.μ generators hgenerators P hP hη
  exact ⟨t, ht, Q, hQ, hnorm⟩

end Chapter02.HostKraFiniteCoordinate
