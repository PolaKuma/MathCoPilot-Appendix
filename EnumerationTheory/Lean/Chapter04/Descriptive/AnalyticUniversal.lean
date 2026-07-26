import Chapter04.Descriptive.AnalyticUniformization

noncomputable section

open Classical Function MeasureTheory Set Filter Topology

namespace Chapter04.AnalyticUniversal

universe u

abbrev Baire := AnalyticUniformization.Baire
abbrev Prefix := AnalyticUniformization.Prefix

def Cylinder {n : ℕ} (s : Prefix n) : Set Baire :=
  AnalyticUniformization.Cylinder s

def imageCylinder {X : Type*} (f : Baire → X)
    {n : ℕ} (s : Prefix n) : Set X :=
  f '' Cylinder s

def cylinderHull {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : Baire → X)
    {n : ℕ} (s : Prefix n) : Set X :=
  toMeasurable μ (imageCylinder f s)

def cylinderClosure {X : Type*} [TopologicalSpace X]
    (f : Baire → X) {n : ℕ} (s : Prefix n) : Set X :=
  closure (imageCylinder f s)

private theorem imageCylinder_children {X : Type*}
    (f : Baire → X) {n : ℕ} (s : Prefix n) :
    imageCylinder f s =
      ⋃ k : ℕ, imageCylinder f (Fin.lastCases k s) := by
  ext x
  constructor
  · rintro ⟨w, hws, rfl⟩
    apply mem_iUnion.2
    refine ⟨w n, w, ?_, rfl⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using hws j
  · intro hx
    obtain ⟨k, w, hw, rfl⟩ := mem_iUnion.1 hx
    refine ⟨w, ?_, rfl⟩
    intro i
    simpa using hw i.castSucc

private theorem hull_diff_measurable_superset_null
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (hfinite : μ univ < ⊤)
    {S T : Set X} (hST : S ⊆ T) (hT : MeasurableSet T) :
    μ (toMeasurable μ S \ T) = 0 := by
  let H := toMeasurable μ S
  let U := H ∩ T
  have hH : MeasurableSet H :=
    measurableSet_toMeasurable μ S
  have hU : MeasurableSet U := hH.inter hT
  have hUH : U ⊆ H := inter_subset_left
  have hSU : S ⊆ U := fun x hx =>
    ⟨subset_toMeasurable μ S hx, hST hx⟩
  have hmeasure : μ U = μ H := by
    apply le_antisymm
    · exact measure_mono hUH
    · calc
        μ H = μ S := measure_toMeasurable S
        _ ≤ μ U := measure_mono hSU
  have hUfinite : μ U ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (measure_mono (subset_univ U)) hfinite)
  have hdiff :
      μ (H \ U) = 0 := by
    rw [measure_diff hUH hU.nullMeasurableSet hUfinite, hmeasure,
      tsub_self]
  have heq : H \ U = H \ T := by
    ext x
    simp [U]
  simpa [H, heq] using hdiff

def badCover {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : Baire → X)
    {n : ℕ} (s : Prefix n) : Set X :=
  cylinderHull μ f s \
    ⋃ k : ℕ, cylinderHull μ f (Fin.lastCases k s)

def badClosure {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] (μ : Measure X) (f : Baire → X)
    {n : ℕ} (s : Prefix n) : Set X :=
  cylinderHull μ f s \ cylinderClosure f s

private theorem measure_badCover {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (hfinite : μ univ < ⊤)
    (f : Baire → X) {n : ℕ} (s : Prefix n) :
    μ (badCover μ f s) = 0 := by
  apply hull_diff_measurable_superset_null μ hfinite
  · intro x hx
    rw [imageCylinder_children] at hx
    obtain ⟨k, hxk⟩ := mem_iUnion.1 hx
    exact mem_iUnion.2
      ⟨k, subset_toMeasurable μ
        (imageCylinder f (Fin.lastCases k s)) hxk⟩
  · exact MeasurableSet.iUnion fun k =>
      by
        simpa only [cylinderHull] using
          measurableSet_toMeasurable μ
            (imageCylinder f (Fin.lastCases k s))

private theorem measure_badClosure {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (hfinite : μ univ < ⊤)
    (f : Baire → X) {n : ℕ} (s : Prefix n) :
    μ (badClosure μ f s) = 0 := by
  exact hull_diff_measurable_superset_null μ hfinite
    subset_closure isClosed_closure.measurableSet

def badSet {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (μ : Measure X) (f : Baire → X) : Set X :=
  ⋃ n : ℕ, ⋃ s : Prefix n, badCover μ f s ∪ badClosure μ f s

private theorem measure_badSet {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (hfinite : μ univ < ⊤)
    (f : Baire → X) :
    μ (badSet μ f) = 0 := by
  apply measure_iUnion_null
  intro n
  apply measure_iUnion_null
  intro s
  exact measure_union_null
    (measure_badCover μ hfinite f s)
    (measure_badClosure μ hfinite f s)

noncomputable def hullPrefix {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] (μ : Measure X) (f : Baire → X)
    (x : X)
    (hxroot :
      x ∈ cylinderHull μ f (fun i : Fin 0 => Fin.elim0 i))
    (hxgood : x ∉ badSet μ f) :
    (n : ℕ) → {s : Prefix n // x ∈ cylinderHull μ f s}
  | 0 => ⟨fun i => Fin.elim0 i, hxroot⟩
  | n + 1 =>
      let previous := hullPrefix μ f x hxroot hxgood n
      have hnobad : x ∉ badCover μ f previous.1 := by
        intro hbad
        apply hxgood
        apply mem_iUnion.2
        refine ⟨n, mem_iUnion.2 ⟨previous.1, ?_⟩⟩
        exact Or.inl hbad
      have hchildren :
          x ∈ ⋃ k : ℕ,
            cylinderHull μ f (Fin.lastCases k previous.1) := by
        by_contra hnot
        exact hnobad ⟨previous.2, hnot⟩
      let k := Classical.choose (mem_iUnion.1 hchildren)
      ⟨Fin.lastCases k previous.1,
        Classical.choose_spec (mem_iUnion.1 hchildren)⟩

def hullCode {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] (μ : Measure X) (f : Baire → X)
    (x : X)
    (hxroot :
      x ∈ cylinderHull μ f (fun i : Fin 0 => Fin.elim0 i))
    (hxgood : x ∉ badSet μ f) : Baire :=
  fun n => (hullPrefix μ f x hxroot hxgood (n + 1)).1 (Fin.last n)

@[simp]
private theorem hullPrefix_succ_last {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X]
    (μ : Measure X) (f : Baire → X) (x : X)
    (hxroot :
      x ∈ cylinderHull μ f (fun i : Fin 0 => Fin.elim0 i))
    (hxgood : x ∉ badSet μ f) (n : ℕ) :
    (hullPrefix μ f x hxroot hxgood (n + 1)).1 (Fin.last n) =
      hullCode μ f x hxroot hxgood n :=
  rfl

@[simp]
private theorem hullPrefix_succ_castSucc {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X]
    (μ : Measure X) (f : Baire → X) (x : X)
    (hxroot :
      x ∈ cylinderHull μ f (fun i : Fin 0 => Fin.elim0 i))
    (hxgood : x ∉ badSet μ f) (n : ℕ) (i : Fin n) :
    (hullPrefix μ f x hxroot hxgood (n + 1)).1 i.castSucc =
      (hullPrefix μ f x hxroot hxgood n).1 i := by
  simp only [hullPrefix, Fin.lastCases_castSucc]

private theorem hullCode_agrees_prefix {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X]
    (μ : Measure X) (f : Baire → X) (x : X)
    (hxroot :
      x ∈ cylinderHull μ f (fun i : Fin 0 => Fin.elim0 i))
    (hxgood : x ∉ badSet μ f) (n : ℕ) (i : Fin n) :
    hullCode μ f x hxroot hxgood i =
      (hullPrefix μ f x hxroot hxgood n).1 i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hullPrefix_succ_last μ f x hxroot hxgood n
      · rw [hullPrefix_succ_castSucc]
        exact ih j

private theorem hullPrefix_mem_closure {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X]
    (μ : Measure X) (f : Baire → X) (x : X)
    (hxroot :
      x ∈ cylinderHull μ f (fun i : Fin 0 => Fin.elim0 i))
    (hxgood : x ∉ badSet μ f) (n : ℕ) :
    x ∈ cylinderClosure f
      (hullPrefix μ f x hxroot hxgood n).1 := by
  let s := (hullPrefix μ f x hxroot hxgood n).1
  have hnobad : x ∉ badClosure μ f s := by
    intro hbad
    apply hxgood
    apply mem_iUnion.2
    refine ⟨n, mem_iUnion.2 ⟨s, ?_⟩⟩
    exact Or.inr hbad
  by_contra hnot
  exact hnobad ⟨(hullPrefix μ f x hxroot hxgood n).2, hnot⟩

private theorem exists_approxCode {X : Type*}
    [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) (f : Baire → X) (x : X)
    (hxroot :
      x ∈ cylinderHull μ f (fun i : Fin 0 => Fin.elim0 i))
    (hxgood : x ∉ badSet μ f) (n : ℕ) :
    ∃ w : Baire,
      w ∈ Cylinder (hullPrefix μ f x hxroot hxgood n).1 ∧
        dist x (f w) < 1 / ((n : ℝ) + 1) := by
  have hclosure :=
    hullPrefix_mem_closure μ f x hxroot hxgood n
  rw [cylinderClosure, Metric.mem_closure_iff] at hclosure
  obtain ⟨y, hy, hxy⟩ :=
    hclosure (1 / ((n : ℝ) + 1))
      (by positivity)
  obtain ⟨w, hw, rfl⟩ := hy
  exact ⟨w, hw, hxy⟩

noncomputable def approxCode {X : Type*}
    [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) (f : Baire → X) (x : X)
    (hxroot :
      x ∈ cylinderHull μ f (fun i : Fin 0 => Fin.elim0 i))
    (hxgood : x ∉ badSet μ f) (n : ℕ) : Baire :=
  Classical.choose (exists_approxCode μ f x hxroot hxgood n)

private theorem approxCode_spec {X : Type*}
    [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) (f : Baire → X) (x : X)
    (hxroot :
      x ∈ cylinderHull μ f (fun i : Fin 0 => Fin.elim0 i))
    (hxgood : x ∉ badSet μ f) (n : ℕ) :
    approxCode μ f x hxroot hxgood n ∈
        Cylinder (hullPrefix μ f x hxroot hxgood n).1 ∧
      dist x (f (approxCode μ f x hxroot hxgood n)) <
        1 / ((n : ℝ) + 1) :=
  Classical.choose_spec
    (exists_approxCode μ f x hxroot hxgood n)

private theorem approxCode_tendsto {X : Type*}
    [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) (f : Baire → X) (x : X)
    (hxroot :
      x ∈ cylinderHull μ f (fun i : Fin 0 => Fin.elim0 i))
    (hxgood : x ∉ badSet μ f) :
    Tendsto (approxCode μ f x hxroot hxgood) atTop
      (nhds (hullCode μ f x hxroot hxgood)) := by
  rw [tendsto_pi_nhds]
  intro i
  rw [nhds_discrete, Filter.tendsto_pure]
  refine Filter.eventually_atTop.2 ⟨i + 1, ?_⟩
  intro n hn
  have hi : i < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hn
  let j : Fin n := ⟨i, hi⟩
  calc
    approxCode μ f x hxroot hxgood n i =
        (hullPrefix μ f x hxroot hxgood n).1 j :=
      (approxCode_spec μ f x hxroot hxgood n).1 j
    _ = hullCode μ f x hxroot hxgood i :=
      (hullCode_agrees_prefix μ f x hxroot hxgood n j).symm

private theorem approxImage_tendsto {X : Type*}
    [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) (f : Baire → X) (x : X)
    (hxroot :
      x ∈ cylinderHull μ f (fun i : Fin 0 => Fin.elim0 i))
    (hxgood : x ∉ badSet μ f) :
    Tendsto (fun n => f (approxCode μ f x hxroot hxgood n))
      atTop (nhds x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hradius :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
        atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have heventually :
      ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
    (tendsto_order.1 hradius).2 ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 heventually
  refine ⟨N, fun n hn => ?_⟩
  have happrox :=
    (approxCode_spec μ f x hxroot hxgood n).2
  calc
    dist (f (approxCode μ f x hxroot hxgood n)) x =
        dist x (f (approxCode μ f x hxroot hxgood n)) :=
      dist_comm _ _
    _ < 1 / ((n : ℝ) + 1) := happrox
    _ < ε := hN n hn

private theorem point_mem_range_of_good {X : Type*}
    [MeasurableSpace X] [PseudoMetricSpace X] [T2Space X]
    (μ : Measure X) (f : Baire → X) (hf : Continuous f)
    (x : X)
    (hxroot :
      x ∈ cylinderHull μ f (fun i : Fin 0 => Fin.elim0 i))
    (hxgood : x ∉ badSet μ f) :
    x ∈ Set.range f := by
  let w := hullCode μ f x hxroot hxgood
  have hw :
      Tendsto (approxCode μ f x hxroot hxgood) atTop (nhds w) :=
    approxCode_tendsto μ f x hxroot hxgood
  have hfx :
      Tendsto (fun n => f (approxCode μ f x hxroot hxgood n))
        atTop (nhds x) :=
    approxImage_tendsto μ f x hxroot hxgood
  have hfw :
      Tendsto (fun n => f (approxCode μ f x hxroot hxgood n))
        atTop (nhds (f w)) :=
    hf.continuousAt.tendsto.comp hw
  exact ⟨w, (tendsto_nhds_unique hfw hfx)⟩

private theorem imageCylinder_empty_eq_range {X : Type*}
    (f : Baire → X) :
    imageCylinder f (fun i : Fin 0 => Fin.elim0 i) =
      Set.range f := by
  ext x
  constructor
  · rintro ⟨w, _, rfl⟩
    exact ⟨w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, (fun i => Fin.elim0 i), rfl⟩

theorem analyticSet_nullMeasurable {X : Type*}
    [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (hfinite : μ univ < ⊤)
    (A : Set X) (hA : MeasureTheory.AnalyticSet A) :
    NullMeasurableSet A μ := by
  letI : MetricSpace X :=
    TopologicalSpace.metrizableSpaceMetric X
  rw [MeasureTheory.AnalyticSet] at hA
  rcases hA with rfl | ⟨f, hf, hfrange⟩
  · exact MeasurableSet.empty.nullMeasurableSet
  · rw [← hfrange]
    let e : Prefix 0 := fun i => Fin.elim0 i
    let B : Set X := cylinderHull μ f e
    have hB : MeasurableSet B := by
      simpa only [B, cylinderHull] using
        measurableSet_toMeasurable μ (imageCylinder f e)
    refine ⟨B, hB, ?_⟩
    rw [ae_eq_set]
    constructor
    · have hsubset : Set.range f ⊆ B := by
        rw [← imageCylinder_empty_eq_range f]
        exact subset_toMeasurable μ (imageCylinder f e)
      have heq : Set.range f \ B = ∅ :=
        Set.diff_eq_empty.mpr hsubset
      rw [heq]
      exact measure_empty
    · apply measure_mono_null
        (t := badSet μ f)
        ?_ (measure_badSet μ hfinite f)
      intro x hx
      by_contra hxgood
      apply hx.2
      apply point_mem_range_of_good μ f hf x
      · exact hx.1
      · exact hxgood

theorem universallyMeasurable_of_data
    (M : MeasurableSpaceData.{u})
    (hM : IsStandardBorelSpaceData M)
    (A : Set M.X) (hA : IsAnalyticSet M A) :
    IsUniversallyMeasurable M A := by
  rw [StandardBorel.universallyMeasurable_iff_nullMeasurable]
  intro μ hfinite
  letI : StandardBorelSpace M.X :=
    StandardBorel.instanceOfData M hM
  letI : UpgradedStandardBorel M.X :=
    upgradeStandardBorel M.X
  exact analyticSet_nullMeasurable μ hfinite A
    (StandardBorel.analyticSet_of_data M hM A hA)

end Chapter04.AnalyticUniversal
