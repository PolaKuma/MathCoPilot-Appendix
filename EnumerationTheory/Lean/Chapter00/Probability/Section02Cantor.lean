import Chapter00.Common
import Mathlib.Topology.MetricSpace.PiNat

noncomputable section

open Classical
open Set Function

namespace Chapter00.Section02

universe u

private def ClopenSplits {X : Type u} [TopologicalSpace X]
    (D V : Set X) : Prop :=
  (D ∩ V).Nonempty ∧ (D \ V).Nonempty

private theorem exists_clopen_split_index
    {X : Type u} [TopologicalSpace X]
    (hzero : IsZeroDimensionalSpace X)
    (hno : ∀ x : X, ¬ IsOpen ({x} : Set X))
    (B : ℕ → Set X)
    (hBsurj : ∀ V : Set X, IsClopen V → ∃ n, B n = V)
    (D : Set X) (hD : IsClopen D) (hDne : D.Nonempty) :
    ∃ n, ClopenSplits D (B n) := by
  letI : T2Space X := hzero.1
  obtain ⟨x, hxD⟩ := hDne
  have hDns : ¬ D.Subsingleton := by
    intro hs
    have hDeq : D = {x} := Set.Subsingleton.eq_singleton_of_mem hs hxD
    exact hno x (hDeq ▸ hD.2)
  obtain ⟨y, hyD, hyx⟩ : ∃ y ∈ D, y ≠ x := by
    by_contra! hall
    apply hDns
    intro a ha b hb
    rw [hall a ha, hall b hb]
  have hxcomp : x ∈ ({y} : Set X)ᶜ := by simpa using hyx.symm
  obtain ⟨V, hV, hxV, hVsub⟩ :=
    hzero.2 x {y}ᶜ isClosed_singleton.isOpen_compl hxcomp
  obtain ⟨n, hn⟩ := hBsurj V hV
  refine ⟨n, ?_⟩
  rw [hn]
  exact ⟨⟨x, hxD, hxV⟩, ⟨y, hyD, fun hyV => (hVsub hyV) (by simp)⟩⟩

private abbrev ClopenBlock (X : Type u) [TopologicalSpace X] :=
  {D : TopologicalSpace.Clopens X // ((D : Set X)).Nonempty}

private noncomputable def splitIndex {X : Type u} [TopologicalSpace X]
    (B : ℕ → Set X) (hex : ∀ D : ClopenBlock X, ∃ n, ClopenSplits (D.1 : Set X) (B n))
    (D : ClopenBlock X) : ℕ :=
  Nat.find (hex D)

private theorem splitIndex_spec {X : Type u} [TopologicalSpace X]
    (B : ℕ → Set X) (hex : ∀ D : ClopenBlock X, ∃ n, ClopenSplits (D.1 : Set X) (B n))
    (D : ClopenBlock X) :
    ClopenSplits (D.1 : Set X) (B (splitIndex B hex D)) :=
  Nat.find_spec (hex D)

private noncomputable def splitChild {X : Type u} [TopologicalSpace X]
    (B : ℕ → Set X) (hB : ∀ n, IsClopen (B n))
    (hex : ∀ D : ClopenBlock X, ∃ n, ClopenSplits (D.1 : Set X) (B n))
    (a : Bool) (D : ClopenBlock X) : ClopenBlock X := by
  let n := splitIndex B hex D
  cases a
  · exact ⟨⟨(D.1 : Set X) ∩ B n, D.1.isClopen.inter (hB n)⟩,
      (splitIndex_spec B hex D).1⟩
  · exact ⟨⟨(D.1 : Set X) \ B n, by
        simpa [diff_eq] using D.1.isClopen.inter (hB n).compl⟩,
      (splitIndex_spec B hex D).2⟩

@[simp] private theorem splitChild_false {X : Type u} [TopologicalSpace X]
    (B : ℕ → Set X) (hB : ∀ n, IsClopen (B n))
    (hex : ∀ D : ClopenBlock X, ∃ n, ClopenSplits (D.1 : Set X) (B n))
    (D : ClopenBlock X) :
    ((splitChild B hB hex false D).1 : Set X) =
      (D.1 : Set X) ∩ B (splitIndex B hex D) := rfl

@[simp] private theorem splitChild_true {X : Type u} [TopologicalSpace X]
    (B : ℕ → Set X) (hB : ∀ n, IsClopen (B n))
    (hex : ∀ D : ClopenBlock X, ∃ n, ClopenSplits (D.1 : Set X) (B n))
    (D : ClopenBlock X) :
    ((splitChild B hB hex true D).1 : Set X) =
      (D.1 : Set X) \ B (splitIndex B hex D) := rfl

private noncomputable def clopenTree {X : Type u} [TopologicalSpace X] [Nonempty X]
    (B : ℕ → Set X) (hB : ∀ n, IsClopen (B n))
    (hex : ∀ D : ClopenBlock X, ∃ n, ClopenSplits (D.1 : Set X) (B n)) :
    List Bool → ClopenBlock X
  | [] => ⟨⊤, by simp⟩
  | a :: l => splitChild B hB hex a (clopenTree B hB hex l)

@[simp] private theorem clopenTree_nil {X : Type u} [TopologicalSpace X] [Nonempty X]
    (B : ℕ → Set X) (hB : ∀ n, IsClopen (B n))
    (hex : ∀ D : ClopenBlock X, ∃ n, ClopenSplits (D.1 : Set X) (B n)) :
    (((clopenTree B hB hex []).1 : Set X)) = Set.univ := rfl

@[simp] private theorem clopenTree_cons {X : Type u} [TopologicalSpace X] [Nonempty X]
    (B : ℕ → Set X) (hB : ∀ n, IsClopen (B n))
    (hex : ∀ D : ClopenBlock X, ∃ n, ClopenSplits (D.1 : Set X) (B n))
    (a : Bool) (l : List Bool) :
    clopenTree B hB hex (a :: l) =
      splitChild B hB hex a (clopenTree B hB hex l) := rfl

/-- A compact metrizable zero-dimensional space without isolated points is Cantor space. -/
theorem homeomorphicToNatBool_of_compact_metrizable_zeroDimensional_noIsolated
    (X : Type u) [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] [Nonempty X]
    (hzero : IsZeroDimensionalSpace X)
    (hno : ∀ x : X, ¬ IsOpen ({x} : Set X)) :
    Nonempty (X ≃ₜ (ℕ → Bool)) := by
  letI : T2Space X := hzero.1
  have hsep : IsTotallySeparated (Set.univ : Set X) := by
    intro x _hx y _hy hxy
    have hxcompl : x ∈ ({y} : Set X)ᶜ := by simpa
    obtain ⟨V, hV, hxV, hVU⟩ :=
      hzero.2 x {y}ᶜ isClosed_singleton.isOpen_compl hxcompl
    refine ⟨V, Vᶜ, hV.2, hV.1.isOpen_compl, hxV, ?_, by simp, disjoint_compl_right⟩
    intro hyV
    exact (hVU hyV) (by simp)
  have htd : IsTotallyDisconnected (Set.univ : Set X) :=
    isTotallyDisconnected_of_isTotallySeparated hsep
  letI : TotallyDisconnectedSpace X := ⟨by
    intro C _hC hpre x hx y hy
    exact htd C (Set.subset_univ C) hpre hx hy⟩
  letI : SecondCountableTopology X := inferInstance
  letI : Countable (TopologicalSpace.Clopens X) :=
    TopologicalSpace.Clopens.countable_iff_secondCountable.mpr inferInstance
  letI : Encodable (TopologicalSpace.Clopens X) :=
    Encodable.ofCountable _
  let fallback : TopologicalSpace.Clopens X := ⊤
  let E : ℕ → TopologicalSpace.Clopens X := fun n =>
    (Encodable.decode n).getD fallback
  let B : ℕ → Set X := fun n => (E n : Set X)
  have hBclopen : ∀ n, IsClopen (B n) := fun n => (E n).isClopen
  have hBsurj : ∀ V : Set X, IsClopen V → ∃ n, B n = V := by
    intro V hV
    let c : TopologicalSpace.Clopens X := ⟨V, hV⟩
    refine ⟨Encodable.encode c, ?_⟩
    simp [B, E, c, Encodable.encodek]
  have hex : ∀ Q : ClopenBlock X, ∃ n, ClopenSplits (Q.1 : Set X) (B n) := by
    intro Q
    exact exists_clopen_split_index hzero hno B hBsurj
      (Q.1 : Set X) Q.1.isClopen Q.2
  let T : List Bool → ClopenBlock X := clopenTree B hBclopen hex
  let D : List Bool → Set X := fun l => (T l).1
  let k : List Bool → ℕ := fun l => splitIndex B hex (T l)
  have hDclopen : ∀ l, IsClopen (D l) := fun l => (T l).1.isClopen
  have hDne : ∀ l, (D l).Nonempty := fun l => (T l).2
  have hDnil : D [] = Set.univ := by simp [D, T]
  have hDfalse (l : List Bool) : D (false :: l) = D l ∩ B (k l) := by
    rfl
  have hDtrue (l : List Bool) : D (true :: l) = D l \ B (k l) := by
    rfl
  have hDchild (a : Bool) (l : List Bool) : D (a :: l) ⊆ D l := by
    cases a
    · rw [hDfalse]
      exact Set.inter_subset_left
    · rw [hDtrue]
      exact Set.diff_subset
  have hksplit (l : List Bool) : ClopenSplits (D l) (B (k l)) := by
    exact splitIndex_spec B hex (T l)
  have hkmin (l : List Bool) {m : ℕ}
      (hm : ClopenSplits (D l) (B m)) : k l ≤ m := by
    exact Nat.find_min' (hex (T l)) hm
  have hnotSplit_of_subset (Q V : Set X)
      (hQV : Q ⊆ V) : ¬ ClopenSplits Q V := by
    rintro ⟨_hleft, ⟨x, hxQ, hxV⟩⟩
    exact hxV (hQV hxQ)
  have hnotSplit_of_subset_compl (Q V : Set X)
      (hQV : Q ⊆ Vᶜ) : ¬ ClopenSplits Q V := by
    rintro ⟨⟨x, hxQ, hxV⟩, _hright⟩
    exact (hQV hxQ) hxV
  have hdecide_of_not_split (Q V : Set X)
      (hns : ¬ ClopenSplits Q V) : Q ⊆ V ∨ Q ⊆ Vᶜ := by
    by_cases hi : (Q ∩ V).Nonempty
    · left
      intro x hxQ
      by_contra hxV
      exact hns ⟨hi, ⟨x, hxQ, hxV⟩⟩
    · right
      intro x hxQ hxV
      exact hi ⟨x, hxQ, hxV⟩
  -- All earlier clopens have already been decided on a child block.
  have hkchild (a : Bool) (l : List Bool) : k l < k (a :: l) := by
    by_contra hnot
    have hle : k (a :: l) ≤ k l := Nat.le_of_not_gt hnot
    have hs := hksplit (a :: l)
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hnsp : ¬ ClopenSplits (D l) (B (k (a :: l))) := by
        intro hsp
        have hminimal := hkmin l hsp
        omega
      rcases hdecide_of_not_split _ _ hnsp with hsub | hsub
      · exact (hnotSplit_of_subset _ _ ((hDchild a l).trans hsub)) hs
      · exact (hnotSplit_of_subset_compl _ _ ((hDchild a l).trans hsub)) hs
    · have heq' : k (a :: l) = k l := heq
      cases a
      · apply (hnotSplit_of_subset _ _ ?_) hs
        rw [hDfalse, heq']
        exact Set.inter_subset_right
      · apply (hnotSplit_of_subset_compl _ _ ?_) hs
        rw [hDtrue, heq']
        intro x hx
        exact hx.2
  have hk_length (l : List Bool) : l.length ≤ k l := by
    induction l with
    | nil => exact Nat.zero_le _
    | cons a l ih =>
      exact (Nat.succ_le_succ ih).trans (hkchild a l)
  have hnot_split_of_lt_length (l : List Bool) {m : ℕ} (hm : m < l.length) :
      ¬ ClopenSplits (D l) (B m) := by
    intro hs
    have := hkmin l hs
    have := hk_length l
    omega
  have hdecided (l : List Bool) {m : ℕ} (hm : m < l.length) :
      D l ⊆ B m ∨ D l ⊆ (B m)ᶜ := by
    exact hdecide_of_not_split _ _ (hnot_split_of_lt_length l hm)
  have hres_nested (x : ℕ → Bool) (n : ℕ) :
      D (PiNat.res x (n + 1)) ⊆ D (PiNat.res x n) := by
    rw [show n + 1 = n.succ by omega, PiNat.res_succ]
    exact hDchild _ _
  have hbranch_nonempty (x : ℕ → Bool) :
      (⋂ n, D (PiNat.res x n)).Nonempty := by
    apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    · exact hres_nested x
    · exact fun n => hDne _
    · rw [PiNat.res_zero, hDnil]
      exact isCompact_univ
    · exact fun n => (hDclopen _).1
  have hbranch_subsingleton (x : ℕ → Bool) :
      (⋂ n, D (PiNat.res x n)).Subsingleton := by
    intro y hy z hz
    by_contra hyz
    have hycomp : y ∈ ({z} : Set X)ᶜ := by simpa
    obtain ⟨V, hV, hyV, hVz⟩ :=
      hzero.2 y {z}ᶜ isClosed_singleton.isOpen_compl hycomp
    obtain ⟨j, hj⟩ := hBsurj V hV
    let l := PiNat.res x (j + 1)
    have hjlen : j < l.length := by
      simp [l, PiNat.res_length]
    have hyDl : y ∈ D l := Set.mem_iInter.mp hy (j + 1)
    have hzDl : z ∈ D l := Set.mem_iInter.mp hz (j + 1)
    rcases hdecided l hjlen with hsub | hsub
    · have hzV : z ∈ V := by
        rw [← hj]
        exact hsub hzDl
      exact (hVz hzV) (by simp)
    · have : y ∉ V := by
        rw [← hj]
        exact hsub hyDl
      exact this hyV
  let f : (ℕ → Bool) → X := fun x => (hbranch_nonempty x).some
  have hfmem (x : ℕ → Bool) (n : ℕ) : f x ∈ D (PiNat.res x n) := by
    exact Set.mem_iInter.mp (hbranch_nonempty x).some_mem n
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply PiNat.res_injective
    funext n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [PiNat.res_succ, PiNat.res_succ, ih]
      congr 1
      have hxmem := hfmem x (n + 1)
      have hymem := hfmem y (n + 1)
      rw [show n + 1 = n.succ by omega, PiNat.res_succ] at hxmem hymem
      have hymem' : f x ∈ D (y n :: PiNat.res x n) := by
        rw [hxy, ih]
        exact hymem
      have hdisj : Disjoint (D (false :: PiNat.res x n))
          (D (true :: PiNat.res x n)) := by
        rw [Set.disjoint_left]
        intro z hzfalse hztrue
        rw [hDfalse] at hzfalse
        rw [hDtrue] at hztrue
        exact hztrue.2 hzfalse.2
      cases hxv : x n <;> cases hyv : y n
      · rfl
      · exfalso
        exact Set.disjoint_left.mp hdisj
          (by simpa only [hxv] using hxmem)
          (by simpa only [hyv] using hymem')
      · exfalso
        exact Set.disjoint_left.mp hdisj
          (by simpa only [hyv] using hymem')
          (by simpa only [hxv] using hxmem)
      · rfl
  have hfcont : Continuous f := by
    rw [continuous_def]
    intro U hU
    rw [isOpen_iff_forall_mem_open]
    intro x hxU
    obtain ⟨V, hV, hfxV, hVU⟩ := hzero.2 (f x) U hU hxU
    obtain ⟨j, hj⟩ := hBsurj V hV
    let l := PiNat.res x (j + 1)
    have hjlen : j < l.length := by simp [l, PiNat.res_length]
    have hfl : f x ∈ D l := hfmem x (j + 1)
    have hDlV : D l ⊆ V := by
      rcases hdecided l hjlen with hsub | hsub
      · simpa only [hj] using hsub
      · exfalso
        have : f x ∉ V := by
          rw [← hj]
          exact hsub hfl
        exact this hfxV
    refine ⟨PiNat.cylinder x (j + 1), ?_, PiNat.isOpen_cylinder (fun _ => Bool) _ _,
      PiNat.self_mem_cylinder _ _⟩
    intro y hy
    apply hVU (hDlV ?_)
    have hres : PiNat.res y (j + 1) = PiNat.res x (j + 1) := by
      rw [PiNat.cylinder_eq_res] at hy
      exact hy
    simpa only [l, hres] using hfmem y (j + 1)
  have hres_extend (l : List Bool) :
      ∃ x : ℕ → Bool, PiNat.res x l.length = l := by
    induction l with
    | nil =>
      exact ⟨fun _ => false, rfl⟩
    | cons a l ih =>
      obtain ⟨x, hx⟩ := ih
      let y : ℕ → Bool := Function.update x l.length a
      refine ⟨y, ?_⟩
      rw [List.length_cons, PiNat.res_succ]
      have hyhead : y l.length = a := by simp [y]
      have hytail : PiNat.res y l.length = PiNat.res x l.length := by
        rw [PiNat.res_eq_res]
        intro m hm
        simp [y, Nat.ne_of_lt hm]
      rw [hyhead, hytail, hx]
  have hblock_cover (y : X) (n : ℕ) :
      ∃ l : List Bool, l.length = n ∧ y ∈ D l := by
    induction n with
    | zero =>
      refine ⟨[], rfl, ?_⟩
      rw [hDnil]
      trivial
    | succ n ih =>
      obtain ⟨l, hlen, hyl⟩ := ih
      by_cases hyB : y ∈ B (k l)
      · refine ⟨false :: l, by simp [hlen], ?_⟩
        rw [hDfalse]
        exact ⟨hyl, hyB⟩
      · refine ⟨true :: l, by simp [hlen], ?_⟩
        rw [hDtrue]
        exact ⟨hyl, hyB⟩
  have hfdense : DenseRange f := by
    change Dense (Set.range f)
    rw [dense_iff_inter_open]
    intro U hU hUne
    obtain ⟨y, hyU⟩ := hUne
    obtain ⟨V, hV, hyV, hVU⟩ := hzero.2 y U hU hyU
    obtain ⟨j, hj⟩ := hBsurj V hV
    obtain ⟨l, hlen, hyl⟩ := hblock_cover y (j + 1)
    have hjlen : j < l.length := by omega
    have hDlV : D l ⊆ V := by
      rcases hdecided l hjlen with hsub | hsub
      · simpa only [hj] using hsub
      · exfalso
        have : y ∉ V := by
          rw [← hj]
          exact hsub hyl
        exact this hyV
    obtain ⟨x, hxres⟩ := hres_extend l
    refine ⟨f x, hVU (hDlV ?_), ⟨x, rfl⟩⟩
    have hxmem := hfmem x l.length
    rwa [hxres] at hxmem
  have hfrange : Set.range f = Set.univ := by
    have hclosed : IsClosed (Set.range f) :=
      by simpa only [Set.image_univ] using (isCompact_univ.image hfcont).isClosed
    calc
      Set.range f = closure (Set.range f) := hclosed.closure_eq.symm
      _ = Set.univ := hfdense.closure_range
  have hfsurj : Function.Surjective f := by
    intro y
    have hy : y ∈ Set.range f := by rw [hfrange]; trivial
    exact hy
  let e : (ℕ → Bool) ≃ X := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  exact ⟨(hfcont.homeoOfEquivCompactToT2 (f := e)).symm⟩

end Chapter00.Section02
