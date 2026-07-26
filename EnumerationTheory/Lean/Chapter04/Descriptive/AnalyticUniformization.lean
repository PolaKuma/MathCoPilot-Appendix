import Chapter04.Descriptive.AnalyticData

noncomputable section

open Classical Function MeasureTheory Set

namespace Chapter04.AnalyticUniformization

universe u

abbrev Baire := ℕ → ℕ
abbrev Prefix (n : ℕ) := Fin n → ℕ

def Cylinder {n : ℕ} (s : Prefix n) : Set Baire :=
  {w | ∀ i : Fin n, w i = s i}

def Possible {Y X : Type*} (F : Baire → Y × X)
    (y : Y) {n : ℕ} (s : Prefix n) : Prop :=
  ∃ w, (F w).1 = y ∧ w ∈ Cylinder s

private theorem possible_empty {Y X : Type*} (F : Baire → Y × X)
    (hsurj : ∀ y, ∃ w, (F w).1 = y) (y : Y) :
    Possible F y (fun i : Fin 0 => Fin.elim0 i) := by
  obtain ⟨w, hw⟩ := hsurj y
  exact ⟨w, hw, fun i => Fin.elim0 i⟩

private theorem possible_extend {Y X : Type*} (F : Baire → Y × X)
    (y : Y) {n : ℕ} {s : Prefix n} (hs : Possible F y s) :
    ∃ k, Possible F y (Fin.lastCases k s) := by
  obtain ⟨w, hwy, hws⟩ := hs
  refine ⟨w n, w, hwy, ?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simpa using hws j

noncomputable def leastExtension {Y X : Type*} (F : Baire → Y × X)
    (y : Y) {n : ℕ} (s : Prefix n) : ℕ :=
  if h : ∃ k, Possible F y (Fin.lastCases k s) then Nat.find h else 0

private theorem leastExtension_spec {Y X : Type*}
    (F : Baire → Y × X) (y : Y) {n : ℕ} (s : Prefix n)
    (h : ∃ k, Possible F y (Fin.lastCases k s)) :
    Possible F y (Fin.lastCases (leastExtension F y s) s) := by
  simp only [leastExtension, dif_pos h]
  exact Nat.find_spec h

noncomputable def selectedPrefix {Y X : Type*} (F : Baire → Y × X)
    (hsurj : ∀ y, ∃ w, (F w).1 = y) (y : Y) :
    (n : ℕ) → {s : Prefix n // Possible F y s}
  | 0 => ⟨fun i => Fin.elim0 i, possible_empty F hsurj y⟩
  | n + 1 =>
      let previous := selectedPrefix F hsurj y n
      let hex := possible_extend F y previous.2
      let k := leastExtension F y previous.1
      ⟨Fin.lastCases k previous.1,
        leastExtension_spec F y previous.1 hex⟩

def selectedCode {Y X : Type*} (F : Baire → Y × X)
    (hsurj : ∀ y, ∃ w, (F w).1 = y) (y : Y) (n : ℕ) : ℕ :=
  (selectedPrefix F hsurj y (n + 1)).1 (Fin.last n)

@[simp]
private theorem selectedPrefix_succ_last {Y X : Type*}
    (F : Baire → Y × X) (hsurj : ∀ y, ∃ w, (F w).1 = y)
    (y : Y) (n : ℕ) :
    (selectedPrefix F hsurj y (n + 1)).1 (Fin.last n) =
      selectedCode F hsurj y n :=
  rfl

@[simp]
private theorem selectedPrefix_succ_castSucc {Y X : Type*}
    (F : Baire → Y × X) (hsurj : ∀ y, ∃ w, (F w).1 = y)
    (y : Y) (n : ℕ) (i : Fin n) :
    (selectedPrefix F hsurj y (n + 1)).1 i.castSucc =
      (selectedPrefix F hsurj y n).1 i := by
  simp only [selectedPrefix, Fin.lastCases_castSucc]

@[simp]
private theorem selectedPrefix_succ_val {Y X : Type*}
    (F : Baire → Y × X) (hsurj : ∀ y, ∃ w, (F w).1 = y)
    (y : Y) (n : ℕ) :
    (selectedPrefix F hsurj y (n + 1)).1 =
      Fin.lastCases
        (leastExtension F y (selectedPrefix F hsurj y n).1)
        (selectedPrefix F hsurj y n).1 := by
  rfl

private theorem selectedCode_agrees_prefix {Y X : Type*}
    (F : Baire → Y × X) (hsurj : ∀ y, ∃ w, (F w).1 = y)
    (y : Y) (n : ℕ) (i : Fin n) :
    selectedCode F hsurj y i =
      (selectedPrefix F hsurj y n).1 i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact selectedPrefix_succ_last F hsurj y n
      · rw [selectedPrefix_succ_castSucc]
        exact ih j

noncomputable def selectedWitness {Y X : Type*} (F : Baire → Y × X)
    (hsurj : ∀ y, ∃ w, (F w).1 = y) (y : Y) (n : ℕ) : Baire :=
  Classical.choose (selectedPrefix F hsurj y n).2

private theorem selectedWitness_spec {Y X : Type*}
    (F : Baire → Y × X) (hsurj : ∀ y, ∃ w, (F w).1 = y)
    (y : Y) (n : ℕ) :
    (F (selectedWitness F hsurj y n)).1 = y ∧
      selectedWitness F hsurj y n ∈
        Cylinder (selectedPrefix F hsurj y n).1 :=
  Classical.choose_spec (selectedPrefix F hsurj y n).2

private theorem selectedWitness_tendsto {Y X : Type*}
    (F : Baire → Y × X) (hsurj : ∀ y, ∃ w, (F w).1 = y)
    (y : Y) :
    Filter.Tendsto (selectedWitness F hsurj y) Filter.atTop
      (nhds (selectedCode F hsurj y)) := by
  rw [tendsto_pi_nhds]
  intro i
  rw [nhds_discrete, Filter.tendsto_pure]
  refine Filter.eventually_atTop.2 ⟨i + 1, ?_⟩
  intro n hn
  have hi : i < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hn
  let j : Fin n := ⟨i, hi⟩
  calc
    selectedWitness F hsurj y n i =
        (selectedPrefix F hsurj y n).1 j :=
      (selectedWitness_spec F hsurj y n).2 j
    _ = selectedCode F hsurj y i :=
      (selectedCode_agrees_prefix F hsurj y n j).symm

theorem selectedCode_mem_fiber {Y X : Type*}
    [TopologicalSpace Y] [T1Space Y] [TopologicalSpace X]
    (F : Baire → Y × X) (hF : Continuous F)
    (hsurj : ∀ y, ∃ w, (F w).1 = y) (y : Y) :
    (F (selectedCode F hsurj y)).1 = y := by
  let C : Set Baire := (fun w => (F w).1) ⁻¹' {y}
  have hC : IsClosed C := IsClosed.preimage hF.fst isClosed_singleton
  have hmem : selectedCode F hsurj y ∈ C := hC.mem_of_tendsto
    (selectedWitness_tendsto F hsurj y)
    (Filter.Eventually.of_forall fun n =>
      (selectedWitness_spec F hsurj y n).1)
  exact hmem

private def liftedBaireData (_α : Type u) : MeasurableSpaceData.{u} where
  X := Baire × ULift.{u} Unit
  measurableSpace := inferInstance

private theorem liftedBaireData_standard (α : Type u) :
    IsStandardBorelSpaceData (liftedBaireData α) := by
  let L := liftedBaireData α
  have sL : @StandardBorelSpace L.X L.measurableSpace := by
    change @StandardBorelSpace
      (Baire × ULift.{u} Unit) inferInstance
    infer_instance
  exact ⟨L.X, L.measurableSpace, sL, id, id,
    fun _ => rfl, fun _ => rfl, fun _ h => h, fun _ h => h⟩

private theorem measurableSet_cylinder {n : ℕ} (s : Prefix n) :
    MeasurableSet (Cylinder s) := by
  have heq :
      Cylinder s = ⋂ i : Fin n, (fun w : Baire => w i) ⁻¹' {s i} := by
    ext w
    simp only [Cylinder, mem_setOf_eq, mem_iInter, mem_preimage,
      mem_singleton_iff]
  rw [heq]
  have hc :
      IsClosed
        (⋂ i : Fin n, (fun w : Baire => w i) ⁻¹' {s i}) := by
    apply isClosed_iInter
    intro i
    have hi : Continuous (fun w : Baire => w (i : ℕ)) :=
      continuous_apply (i : ℕ)
    exact IsClosed.preimage hi isClosed_singleton
  exact hc.measurableSet

theorem possible_analytic {X : Type u}
    (M : MeasurableSpaceData.{u}) (F : Baire → M.X × X)
    (hF :
      @Measurable Baire M.X inferInstance M.measurableSpace
        (fun w => (F w).1))
    {n : ℕ} (s : Prefix n) :
    IsAnalyticSet M {y | Possible F y s} := by
  let L := liftedBaireData M.X
  let B : Set L.X := {z | z.1 ∈ Cylinder s}
  let q : L.X → M.X := fun z => (F z.1).1
  have hB : B ∈ L.sets := by
    change MeasurableSet {z : Baire × ULift.{u} Unit |
      z.1 ∈ Cylinder s}
    exact (measurableSet_cylinder s).preimage measurable_fst
  have hq : IsMeasurableMap L M q := by
    exact hF.comp measurable_fst
  refine ⟨L, liftedBaireData_standard M.X, B, hB, q, hq, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨w, hwy, hws⟩ := hy
    refine ⟨(w, ULift.up ()), hws, ?_⟩
    exact hwy
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.1, rfl, hz⟩

private theorem measurable_of_singleton_preimages
    {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    [Countable Z] (f : Y → Z)
    (hf : ∀ z, MeasurableSet (f ⁻¹' {z})) :
    Measurable f := by
  intro A hA
  have heq : f ⁻¹' A = ⋃ z : A, f ⁻¹' ({z.1} : Set Z) := by
    ext y
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun z => hf z.1

private theorem leastExtension_zero_fiber {Y X : Type*}
    (F : Baire → Y × X) {n : ℕ} (s : Prefix n) :
    {y | leastExtension F y s = 0} =
      {y | Possible F y (Fin.lastCases 0 s)} ∪
        (⋃ k, {y | Possible F y (Fin.lastCases k s)})ᶜ := by
  ext y
  simp only [mem_setOf_eq, mem_union, mem_compl_iff, mem_iUnion]
  by_cases hex : ∃ k, Possible F y (Fin.lastCases k s)
  · have hnot :
        ¬(¬∃ k, Possible F y (Fin.lastCases k s)) :=
      not_not_intro hex
    rw [or_iff_left hnot]
    constructor
    · intro hfind
      have hfind' : Nat.find hex = 0 := by
        simpa only [leastExtension, dif_pos hex] using hfind
      simpa only [hfind'] using Nat.find_spec hex
    · intro hzero
      simp only [leastExtension, dif_pos hex]
      exact Nat.eq_zero_of_le_zero (Nat.find_min' hex hzero)
  · constructor
    · intro _
      exact Or.inr (by simpa only [not_exists] using hex)
    · intro _
      simp only [leastExtension, dif_neg hex]

private theorem leastExtension_succ_fiber {Y X : Type*}
    (F : Baire → Y × X) {n : ℕ} (s : Prefix n) (k : ℕ) :
    {y | leastExtension F y s = k + 1} =
      {y | Possible F y (Fin.lastCases (k + 1) s)} \
        ⋃ j : Fin (k + 1), {y | Possible F y (Fin.lastCases j s)} := by
  ext y
  simp only [mem_setOf_eq, mem_diff, mem_iUnion, not_exists]
  constructor
  · intro hleast
    have hex : ∃ j, Possible F y (Fin.lastCases j s) := by
      by_contra hno
      simp [leastExtension, hno] at hleast
    have hfind : Nat.find hex = k + 1 := by
      simpa [leastExtension, hex] using hleast
    constructor
    · simpa [hfind] using Nat.find_spec hex
    · intro j
      exact Nat.find_min hex (by simpa [hfind] using j.2)
  · rintro ⟨hpossible, hminimal⟩
    have hex : ∃ j, Possible F y (Fin.lastCases j s) :=
      ⟨k + 1, hpossible⟩
    simp only [leastExtension, dif_pos hex]
    apply le_antisymm
    · exact Nat.find_min' hex hpossible
    · apply Nat.le_of_not_gt
      intro hlt
      exact hminimal ⟨Nat.find hex, hlt⟩ (Nat.find_spec hex)

private theorem measurable_leastExtension {Y X : Type*}
    [MeasurableSpace Y] (F : Baire → Y × X) {n : ℕ} (s : Prefix n)
    (hpossible :
      ∀ k, MeasurableSet {y | Possible F y (Fin.lastCases k s)}) :
    Measurable (fun y => leastExtension F y s) := by
  apply measurable_of_singleton_preimages
  intro k
  cases k with
  | zero =>
      change MeasurableSet {y | leastExtension F y s = 0}
      rw [leastExtension_zero_fiber]
      exact (hpossible 0).union (MeasurableSet.iUnion hpossible).compl
  | succ k =>
      change MeasurableSet {y | leastExtension F y s = k + 1}
      rw [leastExtension_succ_fiber]
      exact (hpossible (k + 1)).diff
        (MeasurableSet.iUnion fun j : Fin (k + 1) => hpossible j)

private theorem measurableSet_possible_analytic {X : Type u}
    (M : MeasurableSpaceData.{u}) (F : Baire → M.X × X)
    (hF :
      @Measurable Baire M.X inferInstance M.measurableSpace
        (fun w => (F w).1))
    {n : ℕ} (s : Prefix n) :
    @MeasurableSet M.X
      (MeasurableSpace.generateFrom
        {A : Set M.X | IsAnalyticSet M A})
      {y | Possible F y s} :=
  MeasurableSpace.measurableSet_generateFrom
    (possible_analytic M F hF s)

private theorem measurable_selectedPrefix {X : Type u}
    (M : MeasurableSpaceData.{u}) (F : Baire → M.X × X)
    (hF :
      @Measurable Baire M.X inferInstance M.measurableSpace
        (fun w => (F w).1))
    (hsurj : ∀ y, ∃ w, (F w).1 = y) (n : ℕ) :
    @Measurable M.X (Prefix n)
      (MeasurableSpace.generateFrom
        {A : Set M.X | IsAnalyticSet M A})
      inferInstance
      (fun y => (selectedPrefix F hsurj y n).1) := by
  letI : MeasurableSpace M.X :=
    MeasurableSpace.generateFrom {A : Set M.X | IsAnalyticSet M A}
  induction n with
  | zero =>
      exact measurable_const
  | succ n ih =>
      let p : M.X → Prefix n :=
        fun y => (selectedPrefix F hsurj y n).1
      apply measurable_of_singleton_preimages
      intro s
      have heq :
          (fun y => (selectedPrefix F hsurj y (n + 1)).1) ⁻¹' {s} =
            ⋃ q : Prefix n,
              {y | p y = q} ∩
                ⋃ k : ℕ,
                  {y |
                    leastExtension F y q = k ∧
                      Fin.lastCases k q = s} := by
        ext y
        simp only [mem_preimage, mem_singleton_iff, mem_iUnion,
          mem_inter_iff, mem_setOf_eq]
        constructor
        · intro hy
          refine ⟨p y, rfl,
            leastExtension F y (p y), rfl, ?_⟩
          simpa only [p, selectedPrefix_succ_val] using hy
        · rintro ⟨q, hpq, k, hk, hks⟩
          subst q
          simpa only [p, selectedPrefix_succ_val, hk] using hks
      rw [heq]
      apply MeasurableSet.iUnion
      intro q
      have hpmeas : MeasurableSet {y | p y = q} := by
        change MeasurableSet
          ((fun y => (selectedPrefix F hsurj y n).1) ⁻¹' {q})
        exact ih (measurableSet_singleton q)
      apply hpmeas.inter
      apply MeasurableSet.iUnion
      intro k
      by_cases hks : Fin.lastCases k q = s
      · have hleast :
            Measurable (fun y => leastExtension F y q) :=
          measurable_leastExtension F q fun j =>
            measurableSet_possible_analytic M F hF
              (Fin.lastCases j q)
        have hkmeas :
            MeasurableSet
              ((fun y => leastExtension F y q) ⁻¹' {k}) :=
          hleast (measurableSet_singleton k)
        have heqset :
            {y |
              leastExtension F y q = k ∧
                Fin.lastCases k q = s} =
              (fun y => leastExtension F y q) ⁻¹' {k} := by
          ext y
          simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff,
            hks, and_true]
        rw [heqset]
        exact hkmeas
      · have heqset :
            {y |
              leastExtension F y q = k ∧
                Fin.lastCases k q = s} = ∅ := by
          ext y
          change
            (leastExtension F y q = k ∧
              Fin.lastCases k q = s) ↔ False
          constructor
          · rintro ⟨_, hs⟩
            exact (hks hs).elim
          · exact False.elim
        rw [heqset]
        exact MeasurableSet.empty

theorem measurable_selectedCode {X : Type u}
    (M : MeasurableSpaceData.{u}) (F : Baire → M.X × X)
    (hF :
      @Measurable Baire M.X inferInstance M.measurableSpace
        (fun w => (F w).1))
    (hsurj : ∀ y, ∃ w, (F w).1 = y) :
    @Measurable M.X Baire
      (MeasurableSpace.generateFrom
        {A : Set M.X | IsAnalyticSet M A})
      inferInstance
      (selectedCode F hsurj) := by
  letI : MeasurableSpace M.X :=
    MeasurableSpace.generateFrom {A : Set M.X | IsAnalyticSet M A}
  rw [measurable_pi_iff]
  intro n
  have hp := measurable_selectedPrefix M F hF hsurj (n + 1)
  exact (measurable_pi_apply (Fin.last n)).comp hp

theorem selector_of_continuous_baire_parametrization
    (M N : MeasurableSpaceData.{u})
    [TopologicalSpace M.X] [T1Space M.X] [TopologicalSpace N.X]
    (F : Baire → M.X × N.X) (hFcont : Continuous F)
    (hFfst :
      @Measurable Baire M.X inferInstance M.measurableSpace
        (fun w => (F w).1))
    (hFsnd :
      @Measurable Baire N.X inferInstance N.measurableSpace
        (fun w => (F w).2))
    (hsurj : ∀ y, ∃ w, (F w).1 = y) :
    ∃ g : M.X → N.X,
      (∀ A : Set N.X, A ∈ N.sets →
        g ⁻¹' A ∈ analyticSigmaAlgebra M) ∧
      ∀ y,
        (F (selectedCode F hsurj y)).1 = y ∧
          g y = (F (selectedCode F hsurj y)).2 := by
  let g : M.X → N.X :=
    fun y => (F (selectedCode F hsurj y)).2
  refine ⟨g, ?_, ?_⟩
  · intro A hA
    have hcode := measurable_selectedCode M F hFfst hsurj
    have hg :
        @Measurable M.X N.X
          (MeasurableSpace.generateFrom
            {B : Set M.X | IsAnalyticSet M B})
          N.measurableSpace g :=
      hFsnd.comp hcode
    exact hg hA
  · intro y
    exact ⟨selectedCode_mem_fiber F hFcont hsurj y, rfl⟩

theorem jankovVonNeumannSelection_of_data
    (M N : MeasurableSpaceData.{u}) (f : M.X → N.X)
    (hM : IsStandardBorelSpaceData M)
    (hN : IsStandardBorelSpaceData N)
    (hf : IsMeasurableMap M N f) :
    ∃ g : Set.range f → M.X,
      (∀ A : Set M.X, A ∈ M.sets →
        g ⁻¹' A ∈ analyticSigmaAlgebra
          (subspaceMeasurableSpace N (Set.range f))) ∧
      ∀ y : Set.range f, f (g y) = y.1 := by
  cases isEmpty_or_nonempty M.X with
  | inl hEmpty =>
      exact StandardBorel.injectiveSelection_of_data
        M N f hM hN hf (fun x => isEmptyElim x)
  | inr hnonempty =>
      letI : Nonempty M.X := hnonempty
      letI : StandardBorelSpace M.X :=
        StandardBorel.instanceOfData M hM
      letI : StandardBorelSpace N.X :=
        StandardBorel.instanceOfData N hN
      letI : UpgradedStandardBorel M.X :=
        upgradeStandardBorel M.X
      letI : UpgradedStandardBorel N.X :=
        upgradeStandardBorel N.X
      let oldTopology : TopologicalSpace M.X := inferInstance
      have oldBorel :
          @BorelSpace M.X oldTopology M.measurableSpace := by
        infer_instance
      have hf' : Measurable f := hf
      obtain ⟨refinedTopology, hrefined, hfcont, refinedPolish⟩ :=
        hf'.exists_continuous
      have hid :
          @Continuous M.X M.X refinedTopology oldTopology id := by
        rw [continuous_iff_le_induced]
        have hind :
            TopologicalSpace.induced (@id M.X) oldTopology =
              oldTopology := by
          ext s
          constructor
          · rintro ⟨t, ht, rfl⟩
            exact ht
          · intro hs
            exact ⟨s, hs, rfl⟩
        rw [hind]
        exact hrefined
      letI : TopologicalSpace M.X := refinedTopology
      letI : PolishSpace M.X := refinedPolish
      obtain ⟨q, hqcont, hqsurj⟩ :=
        PolishSpace.exists_nat_nat_continuous_surjective M.X
      have hqold :
          @Continuous Baire M.X inferInstance oldTopology q :=
        by
          simpa only [id_comp] using
            (@Continuous.comp Baire M.X M.X
              inferInstance refinedTopology oldTopology
              q id hid hqcont)
      have hqmeas :
          @Measurable Baire M.X inferInstance M.measurableSpace q := by
        letI : TopologicalSpace M.X := oldTopology
        letI : BorelSpace M.X := oldBorel
        exact hqold.measurable
      let R :=
        subspaceMeasurableSpace N (Set.range f)
      let rangeTopology : TopologicalSpace R.X := by
        change TopologicalSpace (Set.range f)
        infer_instance
      letI : TopologicalSpace R.X := rangeTopology
      let rangeT1 : @T1Space R.X rangeTopology := by
        change @T1Space (Set.range f) (inferInstance)
        infer_instance
      letI : T1Space R.X := rangeT1
      let F : Baire → R.X × M.X :=
        fun w => (Set.rangeFactorization f (q w), q w)
      have hrcont :
          Continuous (Set.rangeFactorization f) :=
        hfcont.subtype_mk fun x => Set.mem_range_self x
      have hFcont : Continuous F :=
        (hrcont.comp hqcont).prodMk hqcont
      have hFfst :
          @Measurable Baire R.X inferInstance R.measurableSpace
            (fun w => (F w).1) := by
        exact (hf'.comp hqmeas).subtype_mk
      have hFsnd :
          @Measurable Baire M.X inferInstance M.measurableSpace
            (fun w => (F w).2) := by
        exact hqmeas
      have hFsurj : ∀ y : R.X, ∃ w, (F w).1 = y := by
        intro y
        obtain ⟨x, hx⟩ := y.2
        obtain ⟨w, rfl⟩ := hqsurj x
        refine ⟨w, Subtype.ext ?_⟩
        exact hx
      obtain ⟨g, hg, hrel⟩ :=
        selector_of_continuous_baire_parametrization
          R M F hFcont hFfst hFsnd hFsurj
      refine ⟨g, hg, ?_⟩
      intro y
      have hy := hrel y
      rw [hy.2]
      exact congrArg Subtype.val hy.1

end Chapter04.AnalyticUniformization
