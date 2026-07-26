import Chapter00.Section01
import Chapter00.Probability.Section02Cantor
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.UniformSpace.Ascoli

noncomputable section

open Classical

namespace Chapter00
namespace Section02

universe u v w

/--
Source: Proposition 0.2.5, Chapter 0, Section 2.
Every family of subsets of a nonempty set determines a unique topology for
which that family is a subbasis.
-/
theorem existsUniqueTopologyWithGivenSubbasis {X : Type u} [Nonempty X]
    (C : Set (Set X)) :
    ∃! T : TopologicalSpace X, IsTopologicalSubbasis C T := by
  refine ⟨TopologicalSpace.generateFrom C, rfl, ?_⟩
  intro T hT
  exact hT

/--
Source: Proposition 0.2.8, Chapter 0, Section 2.
Basic properties of derived set, interior, closure, closed sets, and frontier.
-/
theorem basicDerivedInteriorClosureFrontierProperties {X : Type u}
    [TopologicalSpace X] [T1Space X] (A : Set X) :
    IsClosed (derivedSet A) ∧
      (∀ U : Set X, IsOpen U -> U ⊆ A -> U ⊆ interior A) ∧
      interior A ⊆ A ∧ IsOpen (interior A) ∧
      (∀ C : Set X, IsClosed C -> A ⊆ C -> closure A ⊆ C) ∧
      A ⊆ closure A ∧ IsClosed (closure A) ∧
      (IsClosed A ↔ A = closure A) ∧
      closure A = interior A ∪ frontier A := by
  refine ⟨?_, ?_, interior_subset, isOpen_interior,
    ?_, subset_closure, isClosed_closure, ?_, closure_eq_interior_union_frontier A⟩
  · have heq : Chapter00.derivedSet A = _root_.derivedSet A := by
      ext x
      simp only [Chapter00.derivedSet, Set.mem_setOf_eq, mem_closure_iff_clusterPt,
        mem_derivedSet]
      exact accPt_principal_iff_clusterPt.symm
    rw [heq]
    exact isClosed_derivedSet A
  · intro U hU hUA
    exact interior_maximal hUA hU
  · intro C hC hAC
    exact closure_minimal hAC hC
  · constructor
    · intro hclosed
      exact hclosed.closure_eq.symm
    · intro heq
      rw [heq]
      exact isClosed_closure

/--
Source: Proposition 0.2.15, Chapter 0, Section 2.
A topological space is compact iff every family of closed sets with the finite
intersection property has nonempty total intersection.
-/
theorem compactIffClosedFamiliesWithFiniteIntersectionProperty {X : Type u}
    [TopologicalSpace X] :
    IsCompact (Set.univ : Set X) ↔
      ∀ F : Set (Set X),
        (∀ A ∈ F, IsClosed A) ->
        (∀ s : Finset (Set X), (∀ A ∈ s, A ∈ F) -> (⋂ A ∈ s, A).Nonempty) ->
        (⋂ A ∈ F, A).Nonempty := by
  constructor
  · intro h F hclosed hf
    let emb : F ↪ Set X := ⟨Subtype.val, Subtype.val_injective⟩
    have hfin : ∀ s : Finset F,
        (Set.univ ∩ ⋂ A ∈ s, (A : Set X)).Nonempty := by
      intro s
      obtain ⟨x, hx⟩ := hf (s.map emb) (by
        intro A hA
        obtain ⟨B, _hBs, rfl⟩ := Finset.mem_map.mp hA
        exact B.property)
      refine ⟨x, Set.mem_inter (Set.mem_univ _) ?_⟩
      simp only [Set.mem_iInter] at hx ⊢
      intro A hAs
      exact hx A (Finset.mem_map.mpr ⟨A, hAs, rfl⟩)
    obtain ⟨x, _hxuniv, hx⟩ := h.inter_iInter_nonempty
      (fun A : F => (A : Set X)) (fun A => hclosed A A.property) hfin
    have hx' : ∀ B : F, x ∈ (B : Set X) := by
      simpa only [Set.mem_iInter] using hx
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter]
    intro A hAF
    exact hx' ⟨A, hAF⟩
  · intro h
    rw [isCompact_iff_finite_subfamily_closed]
    intro ι t ht hinter
    by_contra hno
    have hne : ∀ u : Finset ι, (Set.univ ∩ ⋂ i ∈ u, t i).Nonempty := by
      intro u
      exact Set.nonempty_iff_ne_empty.mpr fun hempty => hno ⟨u, hempty⟩
    let F : Set (Set X) := Set.range t
    have hFclosed : ∀ A ∈ F, IsClosed A := by
      rintro A ⟨i, rfl⟩
      exact ht i
    have hFfin : ∀ s : Finset (Set X), (∀ A ∈ s, A ∈ F) →
        (⋂ A ∈ s, A).Nonempty := by
      intro s hs
      choose pick hpick using fun A : s => hs A A.property
      let u : Finset ι := s.attach.image pick
      have hu : (⋂ i ∈ u, t i) ⊆ ⋂ A ∈ s, A := by
        intro x hx
        simp only [Set.mem_iInter] at hx ⊢
        intro A hAs
        have hmem : pick ⟨A, hAs⟩ ∈ u := by
          exact Finset.mem_image.mpr ⟨⟨A, hAs⟩, Finset.mem_attach _ _, rfl⟩
        simpa [hpick ⟨A, hAs⟩] using hx (pick ⟨A, hAs⟩) hmem
      exact ((hne u).mono Set.inter_subset_right).mono hu
    have hall := h F hFclosed hFfin
    have : (⋂ i, t i).Nonempty := by
      simpa [F] using hall
    apply this.ne_empty
    simpa only [Set.univ_inter] using hinter

/--
Source: Proposition 0.2.18, Chapter 0, Section 2.
Equivalent characterizations of continuity between topological spaces.
-/
theorem continuousEquivalentCharacterizations {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X -> Y) :
    Continuous f ↔
      (∀ V : Set Y, IsOpen V -> IsOpen (f ⁻¹' V)) ∧
      (∀ C : Set Y, IsClosed C -> IsClosed (f ⁻¹' C)) ∧
      (∀ B : Set X, f '' closure B ⊆ closure (f '' B)) ∧
      (∀ C : Set Y, closure (f ⁻¹' C) ⊆ f ⁻¹' closure C) := by
  constructor
  · intro hf
    refine ⟨fun V hV => hV.preimage hf, fun C hC => hC.preimage hf, ?_, ?_⟩
    · intro B y hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact closure_subset_preimage_closure_image hf hx
    · intro C
      exact hf.closure_preimage_subset C
  · rintro ⟨hopen, _hclosed, _himage, _hpreimage⟩
    rw [continuous_def]
    exact hopen

/--
Source: Proposition 0.2.25, Chapter 0, Section 2.
The closure of a connected subset is connected, and the union of two connected
subsets with nonempty intersection is connected.
-/
theorem connectedClosureAndUnion {X : Type u} [TopologicalSpace X]
    (A B : Set X) :
    (IsConnectedSubset A -> IsConnectedSubset (closure A)) ∧
      (IsConnectedSubset A -> IsConnectedSubset B -> (A ∩ B).Nonempty ->
        IsConnectedSubset (A ∪ B)) := by
  exact ⟨fun hA => hA.closure,
    fun hA hB hAB => IsConnected.union hAB hA hB⟩

/--
Source: Proposition 0.2.26, Chapter 0, Section 2.
Continuous surjections preserve compactness and connectedness; a continuous
bijection from a compact Hausdorff space to a Hausdorff space is a homeomorphism.
-/
theorem continuousSurjectionCompactConnectedHomeomorphism {X : Type u}
    {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    [T2Space Y] (f : X -> Y) (hf_cont : Continuous f) (hf_surj : Function.Surjective f) :
    (IsCompact (Set.univ : Set X) -> IsCompact (Set.univ : Set Y)) ∧
      (IsConnectedSubset (Set.univ : Set X) -> IsConnectedSubset (Set.univ : Set Y)) ∧
      (IsCompact (Set.univ : Set X) -> Function.Injective f -> IsHomeomorphism f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hcompact
    simpa [Set.image_univ, Set.range_eq_univ.mpr hf_surj] using
      hcompact.image hf_cont
  · intro hconnected
    simpa [Set.image_univ, Set.range_eq_univ.mpr hf_surj] using
      hconnected.image f hf_cont.continuousOn
  · intro hcompact hinj
    letI : CompactSpace X := ⟨hcompact⟩
    let e₀ : X ≃ Y := Equiv.ofBijective f ⟨hinj, hf_surj⟩
    have he₀ : Continuous e₀ := by simpa [e₀] using hf_cont
    let e : X ≃ₜ Y := he₀.homeoOfEquivCompactToT2
    exact ⟨e, fun x => rfl⟩

/--
Source: Proposition 0.2.36, Chapter 0, Section 2.
For a finite discrete alphabet with at least two symbols, the product space
`A^ℤ` is homeomorphic to the standard middle-third Cantor set.
-/
theorem fullShiftOnFiniteDiscreteAlphabetHomeomorphicToCantor
    (k : ℕ) (hk : 2 ≤ k) :
    IsHomeomorphicToCantor (ℤ -> Fin k) := by
  letI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (by omega)
  have hzero : IsZeroDimensionalSpace (ℤ → Fin k) := by
    refine ⟨inferInstance, ?_⟩
    intro x U hU hxU
    obtain ⟨V, hVclopen, hxV, hVU⟩ :=
      loc_compact_Haus_tot_disc_of_zero_dim.exists_subset_of_mem_open hxU hU
    exact ⟨V, hVclopen, hxV, hVU⟩
  have hno : ∀ x : ℤ → Fin k, ¬ IsOpen ({x} : Set (ℤ → Fin k)) := by
    intro x hopen
    obtain ⟨I, u, hu, hsub⟩ :=
      isOpen_pi_iff.mp hopen x (Set.mem_singleton x)
    obtain ⟨n, hnI⟩ := Finset.exists_notMem I
    obtain ⟨a, hax⟩ := exists_ne (x n)
    let x' : ℤ → Fin k := Function.update x n a
    have hx'mem : x' ∈ (I : Set ℤ).pi u := by
      intro i hiI
      have hin : i ≠ n := fun hin => hnI (hin ▸ hiI)
      simpa [x', hin] using (hu i hiI).2
    have hx'eq : x' = x := Set.mem_singleton_iff.mp (hsub hx'mem)
    have heq := congrFun hx'eq n
    simp [x', hax] at heq
  obtain ⟨e⟩ :=
    homeomorphicToNatBool_of_compact_metrizable_zeroDimensional_noIsolated
      (ℤ → Fin k) hzero hno
  exact ⟨e.trans cantorSetHomeomorphNatToBool.symm⟩

private theorem isFirstCategorySubset_mono {X : Type u} [TopologicalSpace X]
    {A B : Set X} (hBA : B ⊆ A) (hA : IsFirstCategorySubset A) :
    IsFirstCategorySubset B := by
  obtain ⟨N, hN, rfl⟩ := hA
  refine ⟨fun n => B ∩ N n, ?_, ?_⟩
  · intro n
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hmono : interior (closure (B ∩ N n)) ⊆ interior (closure (N n)) :=
      interior_mono (closure_mono Set.inter_subset_right)
    have hx' := hmono hx
    rw [hN n] at hx'
    exact hx'
  · apply Set.Subset.antisymm
    · intro x hx
      simp only [Set.mem_iUnion]
      have hxA : x ∈ ⋃ n, N n := hBA hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxA
      exact ⟨n, hx, hn⟩
    · intro x hx
      simp only [Set.mem_iUnion, Set.mem_inter_iff] at hx
      exact hx.choose_spec.1

/--
Source: Theorem 0.2.12, Chapter 0, Section 2.
Equivalent Baire-space characterizations by dense open intersections and
residual dense sets.
-/
theorem baireSpaceEquivalentCharacterizations {X : Type u} [TopologicalSpace X] :
    IsBaireSpaceProperty X ↔
      (∀ D : Set X, IsFirstCategorySubset Dᶜ -> Dense D) ∧
      ∀ U : ℕ -> Set X, (∀ n, IsOpen (U n)) -> (∀ n, Dense (U n)) ->
        Dense (⋂ n, U n) := by
  constructor
  · intro hB
    constructor
    · intro D hDc
      rw [dense_iff_inter_open]
      intro U hU hUne
      by_contra hUD
      have hsub : U ⊆ Dᶜ := by
        intro x hxU hxD
        exact hUD ⟨x, hxU, hxD⟩
      exact hB U hU hUne (isFirstCategorySubset_mono hsub hDc)
    · intro U hUopen hUdense
      rw [dense_iff_inter_open]
      intro V hVopen hVne
      by_contra hVinter
      have hsub : V ⊆ (⋂ n, U n)ᶜ := by
        intro x hxV hxall
        exact hVinter ⟨x, hxV, hxall⟩
      have hnowhere : ∀ n, IsNowhereDenseSubset ((U n)ᶜ) := by
        intro n
        rw [IsNowhereDenseSubset, (hUopen n).isClosed_compl.closure_eq,
          interior_compl, dense_iff_closure_eq.mp (hUdense n)]
        simp
      have hfirst : IsFirstCategorySubset ((⋂ n, U n)ᶜ) := by
        refine ⟨fun n => (U n)ᶜ, hnowhere, ?_⟩
        simp
      exact hB V hVopen hVne (isFirstCategorySubset_mono hsub hfirst)
  · rintro ⟨hdense, _hinter⟩ U hU hUne hUfirst
    have hfirstcompl : IsFirstCategorySubset Uᶜᶜ := by
      simpa using hUfirst
    obtain ⟨x, hxU, hxcompl⟩ :=
      (hdense Uᶜ hfirstcompl).inter_open_nonempty U hU hUne
    exact hxcompl hxU

private theorem isMeagre_of_isFirstCategorySubset {X : Type u} [TopologicalSpace X]
    {A : Set X} (hA : IsFirstCategorySubset A) : IsMeagre A := by
  obtain ⟨N, hN, rfl⟩ := hA
  rw [isMeagre_iff_countable_union_isNowhereDense]
  refine ⟨Set.range N, ?_, Set.countable_range N, ?_⟩
  · rintro T ⟨n, rfl⟩
    exact hN n
  · simp

private theorem baireSpaceProperty_of_baireSpace {Z : Type w}
    [TopologicalSpace Z] [BaireSpace Z] : IsBaireSpaceProperty Z := by
  intro U hU hUne hfirst
  exact not_isMeagre_of_isOpen hU hUne
    (isMeagre_of_isFirstCategorySubset hfirst)

/--
Source: Theorem 0.2.13, Chapter 0, Section 2.
Complete metric spaces and locally compact Hausdorff spaces are Baire spaces.
-/
theorem completeMetricAndLocallyCompactHausdorffAreBaire
    {X : Type u} [PseudoMetricSpace X] [CompleteSpace X]
    {Y : Type v} [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y] :
    IsBaireSpaceProperty X ∧ IsBaireSpaceProperty Y := by
  exact ⟨baireSpaceProperty_of_baireSpace, baireSpaceProperty_of_baireSpace⟩

/--
Source: Theorem 0.2.16, Chapter 0, Section 2.
Lebesgue covering lemma for compact metric spaces.
-/
theorem lebesgueCoveringLemma {X : Type u} [PseudoMetricSpace X] [Nonempty X]
    (α : Set (Set X)) :
    IsCompact (Set.univ : Set X) -> (∀ U ∈ α, IsOpen U) -> ⋃₀ α = Set.univ ->
      ∃ δ : ℝ, HasLebesgueNumber α δ := by
  intro hcompact hopen hcover
  obtain ⟨r, hr, hballs⟩ := lebesgue_number_lemma_of_metric_sUnion hcompact hopen
    (by simpa [hcover])
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro A hdiam
  rcases A.eq_empty_or_nonempty with rfl | ⟨x, hxA⟩
  · let x₀ : X := Classical.choice inferInstance
    have hx₀ : x₀ ∈ ⋃₀ α := by rw [hcover]; trivial
    obtain ⟨U, hUα, _hxU⟩ := hx₀
    exact ⟨U, hUα, Set.empty_subset U⟩
  · obtain ⟨U, hUα, hballU⟩ := hballs x (Set.mem_univ x)
    refine ⟨U, hUα, fun y hyA => hballU ?_⟩
    simpa [Metric.mem_ball, dist_comm] using
      (hdiam x hxA y hyA).trans_lt (half_lt_self hr)

/--
Source: Theorem 0.2.21, Chapter 0, Section 2.
Tychonoff theorem for compact Hausdorff spaces.
-/
theorem tychonoffTheorem {ι : Type v} (X : ι -> Type u)
    [∀ i, TopologicalSpace (X i)] :
    (∀ i, CompactSpace (X i)) -> (∀ i, T2Space (X i)) ->
      CompactSpace (∀ i, X i) ∧ T2Space (∀ i, X i) := by
  intro hcompact hT2
  letI (i : ι) : CompactSpace (X i) := hcompact i
  letI (i : ι) : T2Space (X i) := hT2 i
  exact ⟨inferInstance, inferInstance⟩

/--
Source: Theorem 0.2.23, Chapter 0, Section 2.
A quotient by a closed equivalence relation on a compact Hausdorff space is
again compact Hausdorff.
-/
theorem quotientByClosedEquivalenceCompactHausdorff
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (R : X -> X -> Prop) (hR : Equivalence R)
    (hclosed : IsClosed {p : X × X | R p.1 p.2}) :
    let s : Setoid X := ⟨R, hR⟩
    @CompactSpace (Quotient s) (quotientTopologicalSpace s) ∧
      @T2Space (Quotient s) (quotientTopologicalSpace s) := by
  let s : Setoid X := ⟨R, hR⟩
  letI : TopologicalSpace (Quotient s) := quotientTopologicalSpace s
  let q : X → Quotient s := Quotient.mk'
  have hqcont : Continuous q := isQuotientMap_quotient_mk'.continuous
  have hqsurj : Function.Surjective q := Quotient.mk'_surjective
  have hqclosed : IsClosedMap q := by
    intro C hC
    have hKclosed : IsClosed ({p : X × X | R p.1 p.2} ∩ (Set.univ ×ˢ C)) :=
      hclosed.inter (isClosed_univ.prod hC)
    have hK : IsCompact ({p : X × X | R p.1 p.2} ∩ (Set.univ ×ˢ C)) :=
      by simpa only [Set.univ_inter] using isCompact_univ.inter_right hKclosed
    have hsat : IsCompact {x : X | ∃ y ∈ C, R x y} := by
      convert hK.image continuous_fst using 1
      ext x
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq,
        Set.mem_prod, Set.mem_univ, true_and]
      aesop
    rw [isClosed_coinduced]
    have hpre : q ⁻¹' (q '' C) = {x : X | ∃ y ∈ C, R x y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨y, hyC, hyx⟩
        exact ⟨y, hyC, (Quotient.eq'' (s₁ := s)).mp hyx.symm⟩
      · rintro ⟨y, hyC, hRxy⟩
        exact ⟨y, hyC, (Quotient.eq'' (s₁ := s)).mpr hRxy |>.symm⟩
    rw [hpre]
    exact hsat.isClosed
  have hT2 : T2Space (Quotient s) := by
    rw [t2Space_iff]
    rintro a b hab
    obtain ⟨x, rfl⟩ := hqsurj a
    obtain ⟨y, rfl⟩ := hqsurj b
    let Fx : Set X := q ⁻¹' {q x}
    let Fy : Set X := q ⁻¹' {q y}
    have hFxclosed : IsClosed Fx := by
      have : IsClosed ({q x} : Set (Quotient s)) := by
        simpa only [Set.image_singleton] using
          hqclosed ({x} : Set X) isClosed_singleton
      exact this.preimage hqcont
    have hFyclosed : IsClosed Fy := by
      have : IsClosed ({q y} : Set (Quotient s)) := by
        simpa only [Set.image_singleton] using
          hqclosed ({y} : Set X) isClosed_singleton
      exact this.preimage hqcont
    have hdisj : Disjoint Fx Fy := by
      rw [Set.disjoint_left]
      intro z hzx hzy
      exact hab ((Set.mem_singleton_iff.mp hzy) ▸ (Set.mem_singleton_iff.mp hzx).symm)
    have hsep : SeparatedNhds Fx Fy := normal_separation hFxclosed hFyclosed hdisj
    obtain ⟨U, V, hUopen, hVopen, hFxU, hFyV, hUV⟩ := hsep
    let Uq : Set (Quotient s) := (q '' Uᶜ)ᶜ
    let Vq : Set (Quotient s) := (q '' Vᶜ)ᶜ
    refine ⟨Uq, Vq, (hqclosed Uᶜ hUopen.isClosed_compl).isOpen_compl,
      (hqclosed Vᶜ hVopen.isClosed_compl).isOpen_compl, ?_, ?_, ?_⟩
    · intro hx
      obtain ⟨z, hzUc, hzx⟩ := hx
      exact hzUc (hFxU (by simpa [Fx, hzx]))
    · intro hy
      obtain ⟨z, hzVc, hzy⟩ := hy
      exact hzVc (hFyV (by simpa [Fy, hzy]))
    · rw [Set.disjoint_left]
      intro c hcU hcV
      obtain ⟨z, hz⟩ := hqsurj c
      have hzU : z ∈ U := by
        by_contra hznot
        exact hcU ⟨z, hznot, hz⟩
      have hzV : z ∈ V := by
        by_contra hznot
        exact hcV ⟨z, hznot, hz⟩
      exact Set.disjoint_left.1 hUV hzU hzV
  exact ⟨Quotient.compactSpace, hT2⟩

/--
Source: Theorem 0.2.29, Chapter 0, Section 2.
For compact Hausdorff spaces, total disconnectedness is equivalent to
zero-dimensionality.
-/
theorem compactHausdorffTotallyDisconnectedIffZeroDimensional
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    IsTotallyDisconnectedSpace X ↔ IsZeroDimensionalSpace X := by
  constructor
  · intro htd
    letI : TotallyDisconnectedSpace X := ⟨by
      intro C _hC hpre x hx y hy
      exact htd C hpre x hx y hy⟩
    refine ⟨inferInstance, ?_⟩
    intro x U hU hxU
    obtain ⟨V, hVclopen, hxV, hVU⟩ :=
      loc_compact_Haus_tot_disc_of_zero_dim.exists_subset_of_mem_open hxU hU
    exact ⟨V, hVclopen, hxV, hVU⟩
  · rintro ⟨_hT2, hzero⟩
    have hsep : IsTotallySeparated (Set.univ : Set X) := by
      intro x _hx y _hy hxy
      have hxcompl : x ∈ ({y} : Set X)ᶜ := by simpa
      obtain ⟨V, hV, hxV, hVsub⟩ :=
        hzero x {y}ᶜ isClosed_singleton.isOpen_compl hxcompl
      refine ⟨V, Vᶜ, hV.2, hV.1.isOpen_compl, hxV, ?_, by simp, disjoint_compl_right⟩
      intro hyV
      exact (hVsub hyV) (by simp)
    have htd : IsTotallyDisconnected (Set.univ : Set X) :=
      isTotallyDisconnected_of_isTotallySeparated hsep
    intro C hC x hx y hy
    exact htd C (Set.subset_univ C) hC hx hy

/--
Source: Theorem 0.2.30, Chapter 0, Section 2.
The quotient of a compact Hausdorff space by its connected relation is
zero-dimensional compact Hausdorff.
-/
theorem quotientByConnectedRelationZeroDimensional
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (s : Setoid X)
    (hs : ∀ x y : X, s.r x y ↔ ConnectedRelation x y) :
    @IsZeroDimensionalSpace (Quotient s) (quotientTopologicalSpace s) ∧
      @CompactSpace (Quotient s) (quotientTopologicalSpace s) := by
  let t : Setoid X := connectedComponentSetoid X
  have hst : ∀ x y : X, s.r x y ↔ t.r x y := by
    intro x y
    rw [hs]
    constructor
    · rintro ⟨C, hC, hx, hy⟩
      change connectedComponent x = connectedComponent y
      exact connectedComponent_eq (hC.subset_connectedComponent hx hy)
    · intro hxy
      change connectedComponent x = connectedComponent y at hxy
      refine ⟨connectedComponent x, isConnected_connectedComponent,
        mem_connectedComponent, ?_⟩
      rw [hxy]
      exact mem_connectedComponent
  letI : TopologicalSpace (Quotient s) := quotientTopologicalSpace s
  let f : Quotient s → ConnectedComponents X :=
    Quotient.lift (fun x : X => (x : ConnectedComponents X)) (fun x y hxy =>
      Quotient.sound ((hst x y).mp hxy))
  let g : ConnectedComponents X → Quotient s :=
    Quotient.lift (fun x : X => @Quotient.mk' X s x) (fun x y hxy =>
      Quotient.sound ((hst x y).mpr hxy))
  let e : Quotient s ≃ₜ ConnectedComponents X := {
    toFun := f
    invFun := g
    left_inv := by
      intro z
      induction z using Quotient.inductionOn
      rfl
    right_inv := by
      intro z
      induction z using Quotient.inductionOn
      rfl
    continuous_toFun := continuous_quot_lift _ ConnectedComponents.continuous_coe
    continuous_invFun := continuous_quot_lift _ isQuotientMap_quotient_mk'.continuous
  }
  letI : CompactSpace (Quotient s) := e.symm.compactSpace
  letI : T2Space (Quotient s) := e.symm.t2Space
  letI : TotallyDisconnectedSpace (Quotient s) := e.symm.totallyDisconnectedSpace
  have htd : IsTotallyDisconnectedSpace (Quotient s) := by
    intro C hC x hx y hy
    exact hC.subsingleton hx hy
  exact ⟨(compactHausdorffTotallyDisconnectedIffZeroDimensional
    (Quotient s)).mp htd, inferInstance⟩

/--
Source: Theorem 0.2.33, Chapter 0, Section 2.
Brouwer theorem: every Cantor set is homeomorphic to the standard Cantor set.
-/
theorem brouwerCantorSetUniqueness
    {X : Type u} [TopologicalSpace X] (A : Set X) :
    IsCantorSubset A -> Nonempty (A ≃ₜ StandardCantorSet) := by
  rintro ⟨hAne, hAcompact, hAmetrizable, hAzero, hAno⟩
  letI : Nonempty A := hAne.to_subtype
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hAcompact
  letI : TopologicalSpace.MetrizableSpace A := hAmetrizable
  obtain ⟨e⟩ :=
    homeomorphicToNatBool_of_compact_metrizable_zeroDimensional_noIsolated
      A hAzero hAno
  exact ⟨e.trans cantorSetHomeomorphNatToBool.symm⟩

/--
Source: Theorem 0.2.34, Chapter 0, Section 2.
Alexandroff theorem: every compact metrizable space is a continuous image of
the Cantor set.
-/
theorem alexandroffCompactMetrizableContinuousImageOfCantor
    (X : Type u) [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] [Nonempty X] :
    ∃ f : StandardCantorSet -> X, Continuous f ∧ Function.Surjective f := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨g, hgcont, hgsurj⟩ := exists_nat_bool_continuous_surjective_of_compact X
  refine ⟨fun x => g (cantorSetHomeomorphNatToBool x),
    hgcont.comp cantorSetHomeomorphNatToBool.continuous, ?_⟩
  exact hgsurj.comp cantorSetHomeomorphNatToBool.surjective

/--
Source: Theorem 0.2.35, Chapter 0, Section 2.
An uncountable Borel subset of a complete separable metric space contains a
Cantor set.
-/
theorem uncountableBorelSetContainsCantorSet
    {X : Type u} [MetricSpace X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) :
    MeasurableSet A -> ¬ A.Countable ->
      ∃ C : Set X, C ⊆ A ∧ IsCantorSubset C := by
  intro hA hAunc
  let t₀ : TopologicalSpace X := inferInstance
  obtain ⟨t', ht'le, ht'polish, hAclosed, _hAopen⟩ := hA.isClopenable
  have hex : ∃ f : (ℕ → Bool) → X, Set.range f ⊆ A ∧
      @Continuous (ℕ → Bool) X inferInstance t₀ f ∧ Function.Injective f := by
    letI : TopologicalSpace X := t'
    letI : PolishSpace X := ht'polish
    obtain ⟨f, hfrange, hfcont, hfinj⟩ :=
      hAclosed.exists_nat_bool_injection_of_not_countable hAunc
    refine ⟨f, hfrange, ?_, hfinj⟩
    have hid : @Continuous X X t' t₀ id := by
      rw [continuous_def]
      intro U hU
      exact ht'le U hU
    exact @Continuous.comp (ℕ → Bool) X X inferInstance t' t₀
      (f := f) (g := id) hid hfcont
  letI : TopologicalSpace X := t₀
  obtain ⟨f, hfrange, hfcont, hfinj⟩ := hex
  let C : Set X := Set.range f
  let e₀ : (ℕ → Bool) ≃ C := Equiv.ofInjective f hfinj
  have he₀cont : Continuous e₀ := by
    exact hfcont.subtype_mk _
  let e : (ℕ → Bool) ≃ₜ C := he₀cont.homeoOfEquivCompactToT2
  have hCcompact : IsCompact C := by
    simpa [C] using isCompact_range hfcont
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hCcompact
  have hCtd : IsTotallyDisconnectedSpace C := by
    letI : TotallyDisconnectedSpace C := e.totallyDisconnectedSpace
    intro D hD x hx y hy
    exact hD.subsingleton hx hy
  have hCzero : IsZeroDimensionalSpace C :=
    (compactHausdorffTotallyDisconnectedIffZeroDimensional C).mp hCtd
  refine ⟨C, hfrange, ?_⟩
  refine ⟨Set.range_nonempty f, hCcompact, inferInstance, hCzero, ?_⟩
  intro x hxopen
  have hopenpre : IsOpen (e ⁻¹' ({x} : Set C)) := hxopen.preimage e.continuous
  have heq : e ⁻¹' ({x} : Set C) = {e.symm x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      exact e.injective (by simpa using hz)
    · intro hz
      simpa [hz]
  rw [heq] at hopenpre
  have hnot : ¬ IsOpen ({e.symm x} : Set (ℕ → Bool)) := by
    intro hopen
    obtain ⟨I, u, hu, hsub⟩ :=
      isOpen_pi_iff.mp hopen (e.symm x) (Set.mem_singleton _)
    obtain ⟨n, hnI⟩ := Finset.exists_notMem I
    let b' : ℕ → Bool := Function.update (e.symm x) n (!(e.symm x n))
    have hb'mem : b' ∈ (I : Set ℕ).pi u := by
      intro i hiI
      have hin : i ≠ n := fun hin => hnI (hin ▸ hiI)
      simpa [b', hin] using (hu i hiI).2
    have hb'eq : b' = e.symm x := Set.mem_singleton_iff.mp (hsub hb'mem)
    have := congrFun hb'eq n
    simp [b'] at this
  exact hnot hopenpre

/--
Source: Theorem 0.2.41, Chapter 0, Section 2.
Real Stone-Weierstrass theorem.
-/
theorem stoneWeierstrassReal
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] (A : Set C(X, ℝ)) :
    IsRealContinuousSubalgebra A -> SeparatesPointsContinuous A -> Dense A := by
  intro hA hsep
  let B : Subalgebra ℝ C(X, ℝ) :=
    { carrier := A
      zero_mem' := by simpa using hA.2.1 0 (1 : C(X, ℝ)) hA.1
      one_mem' := hA.1
      add_mem' := fun hf hg => (hA.2.2 _ hf _ hg).1
      mul_mem' := fun hf hg => (hA.2.2 _ hf _ hg).2
      algebraMap_mem' := fun c => by
        convert hA.2.1 c (1 : C(X, ℝ)) hA.1 using 1
        ext x
        simp }
  have hBsep : B.SeparatesPoints := by
    intro x y hxy
    obtain ⟨f, hfA, hfxy⟩ := hsep x y hxy
    exact ⟨⇑f, ⟨f, hfA, rfl⟩, hfxy⟩
  intro f
  have hf := ContinuousMap.continuousMap_mem_subalgebra_closure_of_separatesPoints B hBsep f
  exact hf

/--
Source: Theorem 0.2.42, Chapter 0, Section 2.
Complex Stone-Weierstrass theorem.
-/
theorem stoneWeierstrassComplex
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] (A : Set C(X, ℂ)) :
    IsStarClosedComplexContinuousSubalgebra A ->
      SeparatesPointsContinuous A -> Dense A := by
  intro hA hsep
  let B : StarSubalgebra ℂ C(X, ℂ) :=
    { carrier := A
      zero_mem' := by simpa using (hA.2.1 0 (1 : C(X, ℂ)) hA.1).1
      one_mem' := hA.1
      add_mem' := fun hf hg => (hA.2.2 _ hf _ hg).1
      mul_mem' := fun hf hg => (hA.2.2 _ hf _ hg).2
      algebraMap_mem' := fun c => by
        convert (hA.2.1 c (1 : C(X, ℂ)) hA.1).1 using 1
        ext x
        simp
      star_mem' := fun hf => (hA.2.1 1 _ hf).2 }
  have hBsep : B.SeparatesPoints := by
    intro x y hxy
    obtain ⟨f, hfA, hfxy⟩ := hsep x y hxy
    exact ⟨⇑f, ⟨f, hfA, rfl⟩, hfxy⟩
  have htop :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints B hBsep
  intro f
  change f ∈ B.topologicalClosure
  rw [htop]
  trivial

private theorem compactContinuousMapFamilyEquicontinuous
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {Y : Type v} [PseudoMetricSpace Y] (A : Set C(X, Y))
    (hA : IsCompact A) : IsEquicontinuousContinuousMapFamily A := by
  intro x ε hε
  obtain ⟨t, htfin, htcover⟩ :=
    Metric.totallyBounded_iff.mp hA.totallyBounded (ε / 3) (by positivity)
  let U : Set X := ⋂ g ∈ t, {y | dist (g y) (g x) < ε / 3}
  have hUopen : IsOpen U := by
    apply Set.Finite.isOpen_biInter htfin
    intro g _hg
    exact isOpen_lt (g.continuous.dist continuous_const) continuous_const
  have hxU : x ∈ U := by simp [U, hε]
  refine ⟨U, hUopen, hxU, ?_⟩
  intro y hy f hf
  have hft : f ∈ ⋃ g ∈ t, Metric.ball g (ε / 3) := htcover hf
  simp only [Set.mem_iUnion] at hft
  obtain ⟨g, hgt, hfg⟩ := hft
  have hgy : dist (g y) (g x) < ε / 3 := Set.mem_iInter₂.mp hy g hgt
  have hfy : dist (f y) (g y) < ε / 3 :=
    (ContinuousMap.dist_apply_le_dist y).trans_lt
      (by simpa [Metric.mem_ball] using hfg)
  have hfx : dist (g x) (f x) < ε / 3 := by
    rw [dist_comm]
    exact (ContinuousMap.dist_apply_le_dist x).trans_lt
      (by simpa [Metric.mem_ball] using hfg)
  calc
    dist (f y) (f x) ≤
        dist (f y) (g y) + dist (g y) (g x) + dist (g x) (f x) :=
      dist_triangle4 _ _ _ _
    _ < ε := by linarith

private theorem customContinuousMapFamilyEquicontinuous
    {X : Type u} [TopologicalSpace X]
    {Y : Type v} [PseudoMetricSpace Y] (A : Set C(X, Y))
    (hA : IsEquicontinuousContinuousMapFamily A) :
    Equicontinuous ((↑) : A → X → Y) := by
  intro x
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  obtain ⟨U, hUopen, hxU, hU⟩ := hA x ε hε
  filter_upwards [hUopen.mem_nhds hxU] with y hy f
  simpa [dist_comm] using hU y hy f f.property

private theorem pointwiseRelativelyCompactOfCompactContinuousMapFamily
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {Y : Type v} [PseudoMetricSpace Y] (A : Set C(X, Y))
    (hA : IsCompact A) : IsPointwiseRelativelyCompactContinuousMapFamily A := by
  intro x
  exact (hA.image (continuous_eval_const x)).closure

private theorem continuousMapClosedEmbedding
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {Y : Type v} [PseudoMetricSpace Y] :
    Topology.IsClosedEmbedding
      (ContinuousMap.toUniformOnFunIsCompact :
        C(X, Y) → UniformOnFun X Y {K : Set X | IsCompact K}) := by
  refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
  rw [ContinuousMap.range_toUniformOnFunIsCompact]
  exact UniformOnFun.isClosed_setOf_continuous
    CompactlyCoherentSpace.isCoherentWith

private theorem compactClosureOfEquicontinuousPointwiseRelativelyCompact
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {Y : Type v} [PseudoMetricSpace Y] [T2Space Y] (A : Set C(X, Y))
    (hequi : IsEquicontinuousContinuousMapFamily A)
    (hpoint : IsPointwiseRelativelyCompactContinuousMapFamily A) :
    IsCompact (closure A) := by
  exact ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (𝔖 := {K : Set X | IsCompact K})
    (F := fun f : C(X, Y) => (f : X → Y))
    (fun K hK => hK)
    continuousMapClosedEmbedding
    (fun K _hK => (customContinuousMapFamilyEquicontinuous A hequi).equicontinuousOn K)
    (by
      intro K _hK x _hx
      refine ⟨closure ((fun f : C(X, Y) => f x) '' A), hpoint x, ?_⟩
      intro f hf
      exact subset_closure ⟨f, hf, rfl⟩)

private theorem compactClosedContinuousMapFamily
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {Y : Type v} [PseudoMetricSpace Y] (A : Set C(X, Y))
    (hclosed : IsClosed A) (heq : Equicontinuous ((↑) : A → X → Y))
    (hpoint : IsPointwiseRelativelyCompactContinuousMapFamily A) : IsCompact A := by
  have hclosedRange : IsClosed (Set.range
      (ContinuousMap.toFun ∘ ((↑) : A → C(X, Y)))) := by
    have hclosedUniform : IsClosed (Set.range
        (ContinuousMap.toUniformOnFunIsCompact ∘ ((↑) : A → C(X, Y)))) :=
      ((@continuousMapClosedEmbedding X _ _ Y _).comp
        hclosed.isClosedEmbedding_subtypeVal).isClosed_range
    exact EquicontinuousOn.isClosed_range_pi_of_uniformOnFun
      (𝔖 := {K : Set X | IsCompact K})
      (fun K hK => hK)
      (by
        ext x
        simp only [Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact Set.mem_sUnion_of_mem (Set.mem_singleton x)
          (show IsCompact ({x} : Set X) from isCompact_singleton))
      (fun K _hK => heq.equicontinuousOn K)
      hclosedUniform
  have hprod : IsCompact (Set.univ.pi
      (fun x => closure ((fun f : C(X, Y) => f x) '' A))) :=
    isCompact_univ_pi fun x => hpoint x
  have himage : IsCompact (ContinuousMap.toFun '' A) := by
    apply IsCompact.of_isClosed_subset hprod
    · simpa [Set.range_comp] using hclosedRange
    · intro f hf x _hx
      obtain ⟨g, hgA, rfl⟩ := hf
      exact subset_closure ⟨g, hgA, rfl⟩
  exact ArzelaAscoli.isCompact_of_equicontinuous A himage heq

/--
Source: Theorem 0.2.44, Chapter 0, Section 2.
Arzelà-Ascoli theorem for compact metric domain and scalar-valued functions.
-/
theorem arzelaAscoliCompactMetricScalar
    {X : Type u} [PseudoMetricSpace X] [CompactSpace X]
    (A : Set C(X, ℂ)) :
    IsCompact (closure A) ↔
      IsUniformlyBoundedContinuousMapFamily A ∧
        IsUniformlyEquicontinuousContinuousMapFamily A := by
  constructor
  · intro hcompact
    have hequi := compactContinuousMapFamilyEquicontinuous (closure A) hcompact
    have hequi' : Equicontinuous ((↑) : closure A → X → ℂ) :=
      customContinuousMapFamilyEquicontinuous (closure A) hequi
    have hunif := CompactSpace.uniformEquicontinuous_of_equicontinuous hequi'
    have hbound := hcompact.isBounded.subset_ball (0 : C(X, ℂ))
    obtain ⟨M, hM⟩ := hbound
    refine ⟨?_, ?_⟩
    · refine ⟨max M 1, by positivity, ?_⟩
      intro f hf x
      have hfM : dist f 0 < M := by
        simpa [Metric.mem_ball] using hM (subset_closure hf)
      have hfnorm : ‖f‖ < M := by simpa [dist_eq_norm] using hfM
      exact (ContinuousMap.norm_coe_le_norm f x).trans
        (hfnorm.le.trans (le_max_left _ _))
    · rw [Metric.uniformEquicontinuous_iff] at hunif
      intro ε hε
      obtain ⟨δ, hδ, hfamily⟩ := hunif ε hε
      refine ⟨δ, hδ, ?_⟩
      intro f hf x y hxy
      exact hfamily x y hxy ⟨f, subset_closure hf⟩
  · rintro ⟨⟨M, hM, hbound⟩, hunif⟩
    have hequi : IsEquicontinuousContinuousMapFamily A := by
      intro x ε hε
      obtain ⟨δ, hδ, hfamily⟩ := hunif ε hε
      refine ⟨Metric.ball x δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, ?_⟩
      intro y hy f hf
      exact hfamily f hf y x (by simpa [Metric.mem_ball, dist_comm] using hy)
    have hpoint : IsPointwiseRelativelyCompactContinuousMapFamily A := by
      intro x
      apply IsCompact.closure_of_subset (isCompact_closedBall (0 : ℂ) M)
      rintro y ⟨f, hf, rfl⟩
      simpa [Metric.mem_closedBall, dist_zero_right] using hbound f hf x
    exact compactClosureOfEquicontinuousPointwiseRelativelyCompact A hequi hpoint

/--
Source: Theorem 0.2.45, Chapter 0, Section 2.
General Arzelà-Ascoli theorem for maps into a metric space.
-/
theorem arzelaAscoliGeneral
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {Y : Type v} [PseudoMetricSpace Y]
    [T2Space X] (A : Set C(X, Y)) :
    IsClosed A -> (IsCompact A ↔ IsEquicontinuousContinuousMapFamily A ∧
      IsPointwiseRelativelyCompactContinuousMapFamily A) := by
  intro hclosed
  constructor
  · intro hcompact
    exact ⟨compactContinuousMapFamilyEquicontinuous A hcompact,
      pointwiseRelativelyCompactOfCompactContinuousMapFamily A hcompact⟩
  · rintro ⟨hequi, hpoint⟩
    have heq : Equicontinuous ((↑) : A → X → Y) :=
      customContinuousMapFamilyEquicontinuous A hequi
    exact compactClosedContinuousMapFamily A hclosed heq hpoint

/--
Source: Corollary 0.2.46, Chapter 0, Section 2.
For self-maps of a compact metric space, compactness of the closure is
equivalent to equicontinuity.
-/
theorem arzelaAscoliSelfMapCorollary
    {X : Type u} [PseudoMetricSpace X] [CompactSpace X]
    (A : Set C(X, X)) :
    IsCompact (closure A) ↔ IsUniformlyEquicontinuousContinuousMapFamily A := by
  constructor
  · intro hcompact
    have hequi := compactContinuousMapFamilyEquicontinuous (closure A) hcompact
    have hequi' : Equicontinuous ((↑) : closure A → X → X) :=
      customContinuousMapFamilyEquicontinuous (closure A) hequi
    have hunif := CompactSpace.uniformEquicontinuous_of_equicontinuous hequi'
    rw [Metric.uniformEquicontinuous_iff] at hunif
    intro ε hε
    obtain ⟨δ, hδ, hfamily⟩ := hunif ε hε
    refine ⟨δ, hδ, ?_⟩
    intro f hf x y hxy
    exact hfamily x y hxy ⟨f, subset_closure hf⟩
  · intro hunif
    have hequi : IsEquicontinuousContinuousMapFamily A := by
      intro x ε hε
      obtain ⟨δ, hδ, hfamily⟩ := hunif ε hε
      refine ⟨Metric.ball x δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, ?_⟩
      intro y hy f hf
      exact hfamily f hf y x (by simpa [Metric.mem_ball, dist_comm] using hy)
    have heqA : Equicontinuous ((↑) : A → X → X) :=
      customContinuousMapFamilyEquicontinuous A hequi
    have heqClosure : Equicontinuous ((↑) : closure A → X → X) := by
      simpa only [Function.comp_apply] using heqA.closure'
        (continuous_pi fun x => continuous_eval_const x)
    have hpoint : IsPointwiseRelativelyCompactContinuousMapFamily (closure A) := by
      intro x
      exact isCompact_univ.closure_of_subset (Set.subset_univ _)
    exact compactClosedContinuousMapFamily (closure A) isClosed_closure heqClosure hpoint

private theorem hasCountableBasisSpace_iff_secondCountable
    (X : Type u) [TopologicalSpace X] :
    HasCountableBasisSpace X ↔ SecondCountableTopology X := by
  constructor
  · rintro ⟨B, hBopen, hBbasis⟩
    have hb : TopologicalSpace.IsTopologicalBasis (Set.range B) :=
      TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
        (by rintro U ⟨n, rfl⟩; exact hBopen n)
        (by
          intro x U hx hU
          obtain ⟨n, hxn, hnU⟩ := hBbasis U hU x hx
          exact ⟨B n, ⟨n, rfl⟩, hxn, hnU⟩)
    exact hb.secondCountableTopology (Set.countable_range B)
  · intro hsecond
    letI : SecondCountableTopology X := hsecond
    rcases isEmpty_or_nonempty X with hX | hX
    · refine ⟨fun _ => ∅, fun _ => isOpen_empty, ?_⟩
      intro U _hU x
      exact isEmptyElim x
    · obtain ⟨B, hBcount, _hBempty, hBbasis⟩ :=
        TopologicalSpace.exists_countable_basis X
      have hBne : B.Nonempty := by
        obtain ⟨x⟩ := hX
        obtain ⟨V, hVB, _hxV, _hVsub⟩ :=
          hBbasis.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
        exact ⟨V, hVB⟩
      obtain ⟨b, hbsurj⟩ := hBcount.exists_surjective hBne
      refine ⟨fun n => (b n : Set X),
        fun n => hBbasis.isOpen (b n).property, ?_⟩
      intro U hU x hx
      obtain ⟨V, hVB, hxV, hVU⟩ := hBbasis.exists_subset_of_mem_open hx hU
      obtain ⟨n, hn⟩ := hbsurj ⟨V, hVB⟩
      exact ⟨n, by simpa [hn] using hxV, by simpa [hn] using hVU⟩

/--
Source: Theorem 0.2.47, Chapter 0, Section 2.
For compact Hausdorff spaces, metrizability, countable base, and separability of
`C(X)` are equivalent.
-/
theorem compactHausdorffMetrizationCharacterizations
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    ((TopologicalSpace.MetrizableSpace X) ↔ HasCountableBasisSpace X) ∧
      (HasCountableBasisSpace X ↔
        ∃ D : Set C(X, ℂ), D.Countable ∧ Dense D) := by
  have hmetric_basis :
      TopologicalSpace.MetrizableSpace X ↔ HasCountableBasisSpace X := by
    constructor
    · intro hmetric
      letI : TopologicalSpace.MetrizableSpace X := hmetric
      letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
      haveI : SecondCountableTopology X := inferInstance
      exact (hasCountableBasisSpace_iff_secondCountable X).mpr inferInstance
    · intro hbasis
      letI : SecondCountableTopology X :=
        (hasCountableBasisSpace_iff_secondCountable X).mp hbasis
      exact inferInstance
  refine ⟨hmetric_basis, ?_⟩
  constructor
  · intro hbasis
    letI : SecondCountableTopology X :=
      (hasCountableBasisSpace_iff_secondCountable X).mp hbasis
    letI : TopologicalSpace.SeparableSpace C(X, ℂ) := inferInstance
    exact TopologicalSpace.SeparableSpace.exists_countable_dense
  · rintro ⟨D, hDcount, hDdense⟩
    have hDne : D.Nonempty := by
      have hzero : (0 : C(X, ℂ)) ∈ closure D :=
        (dense_iff_closure_eq.mp hDdense).symm ▸ Set.mem_univ _
      exact Set.nonempty_iff_ne_empty.mpr fun hDempty => by
        rw [hDempty, closure_empty] at hzero
        exact hzero
    obtain ⟨d, hdRange⟩ := hDcount.exists_eq_range hDne
    have hDsep : ∀ x y : X, x ≠ y → ∃ g ∈ D, g x ≠ g y := by
      intro x y hxy
      obtain ⟨f, hfcont, hfxy⟩ := separatesPoints_continuous_of_t35Space hxy
      let fc : C(X, ℂ) := ⟨fun z => (f z : ℂ),
        Complex.continuous_ofReal.comp hfcont⟩
      have hdist : 0 < dist (fc x) (fc y) := dist_pos.mpr (by
        change (f x : ℂ) ≠ (f y : ℂ)
        exact_mod_cast hfxy)
      have hfc : fc ∈ closure D := by
        rw [dense_iff_closure_eq.mp hDdense]
        exact Set.mem_univ _
      rw [Metric.mem_closure_iff] at hfc
      obtain ⟨g, hgD, hgf⟩ := hfc (dist (fc x) (fc y) / 3) (by positivity)
      refine ⟨g, hgD, ?_⟩
      intro hgxy
      have hx : dist (fc x) (g x) < dist (fc x) (fc y) / 3 := by
        exact (ContinuousMap.dist_apply_le_dist x).trans_lt hgf
      have hy : dist (g y) (fc y) < dist (fc x) (fc y) / 3 := by
        exact (ContinuousMap.dist_apply_le_dist y).trans_lt (by simpa [dist_comm] using hgf)
      have htri : dist (fc x) (fc y) ≤ dist (fc x) (g x) + dist (g y) (fc y) := by
        simpa [hgxy] using dist_triangle (fc x) (g x) (fc y)
      linarith
    have hmetrizable : TopologicalSpace.MetrizableSpace X :=
      Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
        (Y := fun _ : ℕ => ℂ) (fun n => (d n : X → ℂ))
        (fun n => (d n).continuous)
        (by
          intro x y hxy
          obtain ⟨g, hgD, hgxy⟩ := hDsep x y hxy
          rw [hdRange] at hgD
          obtain ⟨n, rfl⟩ := hgD
          exact ⟨n, hgxy⟩)
    exact hmetric_basis.mp hmetrizable

/--
Source: Definition 0.2.1, Chapter 0, Section 2.
A topology is a family containing the whole space and the empty set, closed
under arbitrary unions and finite intersections.
-/
def topologyDefinition (X : Type u) (T : Set (Set X)) : Prop :=
  (Set.univ : Set X) ∈ T ∧ ∅ ∈ T ∧
    (∀ U : Set (Set X), U ⊆ T -> ⋃₀ U ∈ T) ∧
    (∀ U ∈ T, ∀ V ∈ T, U ∩ V ∈ T)

/--
Source: Definition 0.2.2, Chapter 0, Section 2.
The trivial and discrete topologies on a set.
-/
def trivialAndDiscreteTopologyDefinition (X : Type u)
    (Ttrivial Tdiscrete : Set (Set X)) : Prop × Prop :=
  (Ttrivial = {∅, Set.univ}, Tdiscrete = Set.univ)

/--
Source: Definition 0.2.3, Chapter 0, Section 2.
The subspace topology on a subset.
-/
def subspaceTopologyDefinition {X : Type u} [TopologicalSpace X]
    (Y : Set X) (T : TopologicalSpace Y) : Prop :=
  T = TopologicalSpace.induced (fun y : Y => (y : X)) inferInstance

/--
Source: Definition 0.2.4, Chapter 0, Section 2.
A base for a topology is a subfamily whose unions give all open sets.
-/
def topologicalBasisDefinition {X : Type u} [TopologicalSpace X]
    (A : Set (Set X)) : Prop :=
  (∀ V ∈ A, IsOpen V) ∧
    ∀ U : Set X, IsOpen U -> U = ⋃₀ {V ∈ A | V ⊆ U}

/-- Source: Definition 0.2.4. A countable topological basis. -/
def secondCountableDefinition (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ A : Set (Set X), A.Countable ∧ topologicalBasisDefinition A

/--
Source: Definition 0.2.6, Chapter 0, Section 2.
A neighborhood of a point contains an open set containing that point.
-/
def neighborhoodDefinition {X : Type u} [TopologicalSpace X]
    (x : X) (U : Set X) : Prop :=
  ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U

/--
Source: Definition 0.2.7, Chapter 0, Section 2.
Derived set, interior, closure, closed sets, and frontier of a subset.
-/
def derivedInteriorClosureClosedFrontierDefinition {X : Type u}
    [TopologicalSpace X] (A : Set X) : Prop × Prop × Prop × Prop × Prop :=
  (∀ x : X, x ∈ derivedSet A ↔
      ∀ U : Set X, neighborhoodDefinition x U -> (U ∩ (A \ {x})).Nonempty,
    ∀ x : X, x ∈ interior A ↔ neighborhoodDefinition x A,
    ∀ x : X, (x ∈ A ∧ ∃ U : Set X, neighborhoodDefinition x U ∧ U ∩ A = {x}) ↔
      x ∈ A ∧ IsOpen {y : A | (y : X) = x},
    ∀ x : X, x ∈ frontier A ↔
      ∀ U : Set X, neighborhoodDefinition x U ->
        (U ∩ A).Nonempty ∧ (U ∩ Aᶜ).Nonempty,
    closure A = A ∪ derivedSet A)

/--
Source: Definition 0.2.9, Chapter 0, Section 2.
Dense subsets and separable topological spaces.
-/
def denseAndSeparableDefinition {X : Type u} [TopologicalSpace X]
    (A : Set X) : Prop × Prop :=
  (closure A = Set.univ, ∃ D : Set X, D.Countable ∧ closure D = Set.univ)

/--
Source: Definition 0.2.10, Chapter 0, Section 2.
Hausdorff topological spaces.
-/
def hausdorffSpaceDefinition (X : Type u) [TopologicalSpace X] : Prop :=
  T2Space X

/--
Source: Definition 0.2.11, Chapter 0, Section 2.
Nowhere dense, first category, second category, residual, and Baire spaces.
-/
def categoryAndBaireSpaceDefinition (X : Type u) [TopologicalSpace X]
    (A B C D : Set X) : Prop × Prop × Prop × Prop × Prop :=
  (IsNowhereDenseSubset A,
    IsFirstCategorySubset B,
    ¬ IsFirstCategorySubset C,
    IsFirstCategorySubset Dᶜ,
    IsBaireSpaceProperty X)

/--
Source: Definition 0.2.14, Chapter 0, Section 2.
Compactness and the finite intersection property.
-/
def compactnessAndFiniteIntersectionPropertyDefinition
    (X : Type u) [TopologicalSpace X] : Prop × Prop :=
  (IsCompact (Set.univ : Set X),
    ∀ F : Set (Set X),
      (∀ A ∈ F, IsClosed A) ->
      (∀ s : Finset (Set X), (∀ A ∈ s, A ∈ F) -> (⋂ A ∈ s, A).Nonempty) ->
      (⋂ A ∈ F, A).Nonempty)

/--
Source: Definition 0.2.17, Chapter 0, Section 2.
Continuity of a map at a point and continuity of a map between topological
spaces.
-/
def continuousMapDefinition {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X -> Y) : Prop :=
  Continuous f

/--
Source: Definition 0.2.19, Chapter 0, Section 2.
Compact subsets and locally compact topological spaces.
-/
def compactSubsetAndLocallyCompactDefinition
    (X : Type u) [TopologicalSpace X] (A : Set X) : Prop × Prop :=
  (IsCompact A, ∀ x : X, ∃ K : Set X, neighborhoodDefinition x K ∧ IsCompact K)

/--
Source: Definition 0.2.20, Chapter 0, Section 2.
Embeddings, the product topology, and coordinate projections.
-/
def embeddingAndProductTopologyDefinition
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X -> Y) : Prop :=
  Function.Injective f ∧
    ∃ e : X ≃ₜ f '' Set.univ, ∀ x : X, ((e x : f '' Set.univ) : Y) = f x

/-- Source: Definition 0.2.20. The product topology is generated by coordinate cylinders. -/
def productTopologyDefinition {ι : Type v} (X : ι -> Type u)
    [∀ i, TopologicalSpace (X i)] (T : TopologicalSpace (∀ i, X i)) : Prop :=
  T = TopologicalSpace.generateFrom
    {U | ∃ i : ι, ∃ V : Set (X i), IsOpen V ∧ U = (fun x => x i) ⁻¹' V}

/--
Source: Definition 0.2.22, Chapter 0, Section 2.
The quotient topology associated to a surjective map.
-/
def quotientTopologyDefinition {X : Type u} {Y : Type v}
    [TopologicalSpace X] (f : X -> Y) (T : TopologicalSpace Y) : Prop :=
  Function.Surjective f ∧ T = TopologicalSpace.coinduced f inferInstance

/--
Source: Definition 0.2.24, Chapter 0, Section 2.
Connected and disconnected spaces and connected subsets.
-/
def connectedSpaceAndSubsetDefinition {X : Type u} [TopologicalSpace X]
    (A : Set X) : Prop × Prop × Prop :=
  (IsConnected (Set.univ : Set X),
    ∃ U : Set X, U.Nonempty ∧ U ≠ Set.univ ∧ IsOpen U ∧ IsClosed U,
    IsConnected A)

/--
Source: Definition 0.2.27, Chapter 0, Section 2.
Connected components of a topological space.
-/
def connectedComponentDefinition {X : Type u} [TopologicalSpace X]
    (x : X) (C : Set X) : Prop :=
  x ∈ C ∧ IsConnectedSubset C ∧
    ∀ D : Set X, x ∈ D -> IsConnectedSubset D -> D ⊆ C

/--
Source: Definition 0.2.28, Chapter 0, Section 2.
Totally disconnected and zero-dimensional Hausdorff spaces.
-/
def totallyDisconnectedAndZeroDimensionalDefinition
    (X : Type u) [TopologicalSpace X] : Prop × Prop :=
  (IsTotallyDisconnectedSpace X, IsZeroDimensionalSpace X)

/--
Source: Definition 0.2.31, Chapter 0, Section 2.
Construction of the standard middle-third Cantor set.
-/
def standardCantorSetDefinition : Type :=
  StandardCantorSet

/--
Source: Definition 0.2.32, Chapter 0, Section 2.
A Cantor set is a compact metrizable zero-dimensional set without isolated
points.
-/
def cantorSetDefinition {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  IsCantorSubset A

/--
Source: Definition 0.2.37, Chapter 0, Section 2.
Function spaces and the product topology on `X^I`.
-/
def productTopologyOnFunctionSpaceDefinition
    (ι : Type v) (X : Type u) [TopologicalSpace X]
    (T : TopologicalSpace (ι -> X)) : Prop :=
  T = TopologicalSpace.generateFrom
    {U | ∃ i : ι, ∃ V : Set X, IsOpen V ∧ U = (fun f : ι -> X => f i) ⁻¹' V}

/--
Source: Definition 0.2.38, Chapter 0, Section 2.
The compact-open topology on a function space.
-/
def compactOpenTopologyDefinition
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (T : TopologicalSpace (X -> Y)) : Prop :=
  T = TopologicalSpace.generateFrom
    {W | ∃ E : Set X, ∃ U : Set Y, IsCompact E ∧ IsOpen U ∧
      W = {f : X -> Y | f '' E ⊆ U}}

/--
Source: Definition 0.2.39, Chapter 0, Section 2.
The uniform metric on a function space with metric codomain.
-/
def uniformMetricOnFunctionSpaceDefinition
    (X : Type u) (Y : Type v) [PseudoMetricSpace Y]
    (du : (X -> Y) -> (X -> Y) -> ℝ) : Prop :=
  ∀ f g, du f g = sSup (Set.range fun x : X => min 1 (dist (f x) (g x)))

/--
Source: Definition 0.2.40, Chapter 0, Section 2.
Subalgebras of `C(X, R)`, separation of points, and density.
-/
def continuousFunctionAlgebraDefinition
    {X : Type u} [TopologicalSpace X] (A : Set C(X, ℝ)) : Prop × Prop × Prop :=
  (IsRealContinuousSubalgebra A, SeparatesPointsContinuous A, Dense A)

/--
Source: Definition 0.2.43, Chapter 0, Section 2.
Uniform boundedness, equicontinuity, and pointwise relative compactness of a
family of functions.
-/
def boundedEquicontinuousPointwiseCompactFamilyDefinition
    {X : Type u} [PseudoMetricSpace X] (A : Set C(X, ℂ)) : Prop × Prop × Prop :=
  (IsUniformlyBoundedContinuousMapFamily A,
    IsUniformlyEquicontinuousContinuousMapFamily A,
    IsPointwiseRelativelyCompactContinuousMapFamily A)

end Section02
end Chapter00
