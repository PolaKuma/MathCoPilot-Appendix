import Chapter02.Dynamics.CompactForwardMinimalSubset
import Chapter02.Dynamics.MinimalFactorOrbitClosure

open Classical Set
open scoped Pointwise

noncomputable section

namespace Chapter02.CompactGroupExtensionRecurrence

open Chapter02.CompactForwardMinimalSubset
open Chapter02.HallPetrescoMeasureOrbit
open Chapter02.HostKraStructuredRecurrence
open Chapter02.MinimalFactorOrbitClosure

universe u v w

/-- The closure of a forward orbit is forward invariant under a continuous
map. -/
theorem image_closure_forwardOrbit_subset
    {Y : Type u} [TopologicalSpace Y]
    (T : Y → Y) (hT : Continuous T) (y : Y) :
    T '' closure (forwardOrbit T y) ⊆
      closure (forwardOrbit T y) := by
  rintro _ ⟨z, hz, rfl⟩
  apply map_mem_closure hT hz
  rintro _ ⟨n, rfl⟩
  change T ((T^[n]) y) ∈ forwardOrbit T y
  exact ⟨n + 1, Function.iterate_succ_apply' T n y⟩

/-- A compact group extension of a minimal forward system is pointwise
recurrent, provided the compact group acts transitively on every factor
fiber and commutes with the dynamics.

The proof selects a minimal closed invariant subset inside the orbit
closure.  Its image is the whole minimal base.  Translating a point of that
minimal subset inside the required fiber and then pulling back the positive
tail closure forces the initial point to lie in its own positive tail. -/
theorem recurrent_of_compact_group_extension
    {K : Type u} {Y : Type v} {B : Type w}
    [Group K]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [TopologicalSpace B] [T2Space B]
    [MulAction K Y] [ContinuousConstSMul K Y]
    (T : Y → Y) (hT : Continuous T)
    (S : B → B)
    (π : Y → B) (hπ : Continuous π)
    (hequiv : ∀ y, π (T y) = S (π y))
    (hbase : EveryOrbitHitsOpen S)
    (hcomm : ∀ k : K, ∀ y : Y, T (k • y) = k • T y)
    (hfiber : ∀ y z : Y, π y = π z → ∃ k : K, k • y = z)
    (y : Y) :
    y ∈ closure (forwardOrbit T (T y)) := by
  let C : Set Y := closure (forwardOrbit T y)
  have hCne : C.Nonempty :=
    ⟨y, subset_closure ⟨0, by simp only [Function.iterate_zero_apply]⟩⟩
  have hCclosed : IsClosed C := isClosed_closure
  have hCinv : T '' C ⊆ C :=
    image_closure_forwardOrbit_subset T hT y
  obtain ⟨D, hDC, hDne, hDclosed, hDinv, hDmin⟩ :=
    exists_minimal_nonempty_closed_forwardInvariant_subset
      T C hCne hCclosed hCinv
  have hπDclosed : IsClosed (π '' D) :=
    (hDclosed.isCompact.image hπ).isClosed
  have hπDne : (π '' D).Nonempty := hDne.image π
  have hπDinv : S '' (π '' D) ⊆ π '' D := by
    rintro _ ⟨_, ⟨d, hdD, rfl⟩, rfl⟩
    rw [← hequiv]
    exact ⟨T d, hDinv ⟨d, hdD, rfl⟩, rfl⟩
  have hπD : π '' D = Set.univ := by
    obtain ⟨d₀, hd₀D⟩ := hDne
    have hdense :
        Dense (forwardOrbit S (π d₀)) :=
      dense_forwardOrbit_of_everyOrbitHitsOpen S hbase (π d₀)
    have horbit : forwardOrbit S (π d₀) ⊆ π '' D := by
      rintro _ ⟨n, rfl⟩
      induction n with
      | zero =>
          exact ⟨d₀, hd₀D, rfl⟩
      | succ n ih =>
          simpa only [Nat.succ_eq_add_one,
            Function.iterate_succ_apply'] using
              hπDinv ⟨_, ih, rfl⟩
    have hall :
        closure (forwardOrbit S (π d₀)) ⊆ π '' D :=
      closure_minimal horbit hπDclosed
    rw [hdense.closure_eq] at hall
    exact Set.eq_univ_of_univ_subset hall
  have hπy : π y ∈ π '' D := by
    rw [hπD]
    exact Set.mem_univ _
  obtain ⟨d, hdD, hπdy⟩ := hπy
  obtain ⟨k, hkdy⟩ := hfiber d y hπdy
  let kD : Set Y := (fun z : Y ↦ k • z) '' D
  have hkDclosed : IsClosed kD :=
    (Homeomorph.smul k).isClosedMap D hDclosed
  have hykD : y ∈ kD :=
    ⟨d, hdD, hkdy⟩
  have hkDinv : T '' kD ⊆ kD := by
    rintro _ ⟨_, ⟨z, hzD, rfl⟩, rfl⟩
    rw [hcomm]
    exact ⟨T z, hDinv ⟨z, hzD, rfl⟩, rfl⟩
  have horbit_kD : forwardOrbit T y ⊆ kD := by
    rintro _ ⟨n, rfl⟩
    induction n with
    | zero =>
        simpa only [Function.iterate_zero_apply] using hykD
    | succ n ih =>
        simpa only [Nat.succ_eq_add_one,
          Function.iterate_succ_apply'] using
            hkDinv ⟨_, ih, rfl⟩
  have hCkD : C ⊆ kD :=
    closure_minimal horbit_kD hkDclosed
  let R : Set Y := closure (forwardOrbit T (T y))
  have hRne : R.Nonempty :=
    ⟨T y, subset_closure
      ⟨0, by simp only [Function.iterate_zero_apply]⟩⟩
  have hRclosed : IsClosed R := isClosed_closure
  have hRinv : T '' R ⊆ R :=
    image_closure_forwardOrbit_subset T hT (T y)
  have hRsubC : R ⊆ C := by
    apply closure_minimal
    · rintro _ ⟨n, rfl⟩
      induction n with
      | zero =>
          exact hCinv ⟨y,
            subset_closure
              ⟨0, by simp only [Function.iterate_zero_apply]⟩,
            by simp only [Function.iterate_zero_apply]⟩
      | succ n ih =>
          simpa only [Nat.succ_eq_add_one,
            Function.iterate_succ_apply'] using
              hCinv ⟨_, ih, rfl⟩
    · exact hCclosed
  let E : Set Y := (fun z : Y ↦ k⁻¹ • z) '' R
  have hEne : E.Nonempty := hRne.image (fun z : Y ↦ k⁻¹ • z)
  have hEclosed : IsClosed E :=
    (Homeomorph.smul k⁻¹).isClosedMap R hRclosed
  have hED : E ⊆ D := by
    rintro e ⟨r, hrR, rfl⟩
    obtain ⟨d', hd'D, hkd'r⟩ := hCkD (hRsubC hrR)
    have : k⁻¹ • r = d' := by
      rw [← hkd'r, inv_smul_smul]
    change k⁻¹ • r ∈ D
    rw [this]
    exact hd'D
  have hEinv : T '' E ⊆ E := by
    rintro _ ⟨_, ⟨r, hrR, rfl⟩, rfl⟩
    rw [hcomm]
    exact ⟨T r, hRinv ⟨r, hrR, rfl⟩, rfl⟩
  have hDE : D ⊆ E :=
    hDmin E hED hEne hEclosed hEinv
  have hdE : d ∈ E := hDE hdD
  obtain ⟨r, hrR, hkrd⟩ := hdE
  have hry : r = y := by
    calc
      r = k • (k⁻¹ • r) := by simp
      _ = k • d := congrArg (fun z : Y ↦ k • z) hkrd
      _ = y := hkdy
  change y ∈ R
  rwa [← hry]

/-- In the same compact-group extension setting, every forward orbit
closure is itself a minimal nonempty closed forward-invariant set.

The minimal subset selected by Zorn meets the fiber of the initial point.
Translating it inside that fiber produces a minimal set containing the
initial point, hence containing its orbit closure; minimality then forces
equality. -/
theorem orbitClosure_minimal_of_compact_group_extension
    {K : Type u} {Y : Type v} {B : Type w}
    [Group K]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [TopologicalSpace B] [T2Space B]
    [MulAction K Y] [ContinuousConstSMul K Y]
    (T : Y → Y) (hT : Continuous T)
    (S : B → B)
    (π : Y → B) (hπ : Continuous π)
    (hequiv : ∀ y, π (T y) = S (π y))
    (hbase : EveryOrbitHitsOpen S)
    (hcomm : ∀ k : K, ∀ y : Y, T (k • y) = k • T y)
    (hfiber : ∀ y z : Y, π y = π z → ∃ k : K, k • y = z)
    (y : Y) :
    let C := closure (forwardOrbit T y)
    ∀ E : Set Y, E ⊆ C → E.Nonempty → IsClosed E →
      T '' E ⊆ E → C ⊆ E := by
  let C : Set Y := closure (forwardOrbit T y)
  have hCne : C.Nonempty :=
    ⟨y, subset_closure ⟨0, by simp only [Function.iterate_zero_apply]⟩⟩
  have hCclosed : IsClosed C := isClosed_closure
  have hCinv : T '' C ⊆ C :=
    image_closure_forwardOrbit_subset T hT y
  obtain ⟨D, hDC, hDne, hDclosed, hDinv, hDmin⟩ :=
    exists_minimal_nonempty_closed_forwardInvariant_subset
      T C hCne hCclosed hCinv
  have hπDclosed : IsClosed (π '' D) :=
    (hDclosed.isCompact.image hπ).isClosed
  have hπDne : (π '' D).Nonempty := hDne.image π
  have hπDinv : S '' (π '' D) ⊆ π '' D := by
    rintro _ ⟨_, ⟨d, hdD, rfl⟩, rfl⟩
    rw [← hequiv]
    exact ⟨T d, hDinv ⟨d, hdD, rfl⟩, rfl⟩
  have hπD : π '' D = Set.univ := by
    obtain ⟨d₀, hd₀D⟩ := hDne
    have hdense :
        Dense (forwardOrbit S (π d₀)) :=
      dense_forwardOrbit_of_everyOrbitHitsOpen S hbase (π d₀)
    have horbit : forwardOrbit S (π d₀) ⊆ π '' D := by
      rintro _ ⟨n, rfl⟩
      induction n with
      | zero =>
          exact ⟨d₀, hd₀D, rfl⟩
      | succ n ih =>
          simpa only [Nat.succ_eq_add_one,
            Function.iterate_succ_apply'] using
              hπDinv ⟨_, ih, rfl⟩
    have hall :
        closure (forwardOrbit S (π d₀)) ⊆ π '' D :=
      closure_minimal horbit hπDclosed
    rw [hdense.closure_eq] at hall
    exact Set.eq_univ_of_univ_subset hall
  have hπy : π y ∈ π '' D := by
    rw [hπD]
    exact Set.mem_univ _
  obtain ⟨d, hdD, hπdy⟩ := hπy
  obtain ⟨k, hkdy⟩ := hfiber d y hπdy
  let kD : Set Y := (fun z : Y ↦ k • z) '' D
  have hkDne : kD.Nonempty := hDne.image _
  have hkDclosed : IsClosed kD :=
    (Homeomorph.smul k).isClosedMap D hDclosed
  have hykD : y ∈ kD :=
    ⟨d, hdD, hkdy⟩
  have hkDinv : T '' kD ⊆ kD := by
    rintro _ ⟨_, ⟨z, hzD, rfl⟩, rfl⟩
    rw [hcomm]
    exact ⟨T z, hDinv ⟨z, hzD, rfl⟩, rfl⟩
  have hkDmin :
      ∀ E : Set Y, E ⊆ kD → E.Nonempty → IsClosed E →
        T '' E ⊆ E → kD ⊆ E := by
    intro E hEkD hEne hEclosed hEinv
    let F : Set Y := (fun z : Y ↦ k⁻¹ • z) '' E
    have hFne : F.Nonempty := hEne.image _
    have hFclosed : IsClosed F :=
      (Homeomorph.smul k⁻¹).isClosedMap E hEclosed
    have hFD : F ⊆ D := by
      rintro z ⟨e, heE, rfl⟩
      obtain ⟨d', hd'D, hkd'e⟩ := hEkD heE
      have heq : k⁻¹ • e = d' := by
        rw [← hkd'e, inv_smul_smul]
      change k⁻¹ • e ∈ D
      rw [heq]
      exact hd'D
    have hFinv : T '' F ⊆ F := by
      rintro _ ⟨_, ⟨e, heE, rfl⟩, rfl⟩
      rw [hcomm]
      exact ⟨T e, hEinv ⟨e, heE, rfl⟩, rfl⟩
    have hDF : D ⊆ F :=
      hDmin F hFD hFne hFclosed hFinv
    rintro z ⟨d', hd'D, rfl⟩
    obtain ⟨e, heE, hkied⟩ := hDF hd'D
    have hke : k • d' = e := by
      rw [← hkied, smul_inv_smul]
    change k • d' ∈ E
    rw [hke]
    exact heE
  have hCkD : C ⊆ kD :=
    closure_minimal
      (fun _ h ↦ by
        rcases h with ⟨n, rfl⟩
        induction n with
        | zero =>
            simpa only [Function.iterate_zero_apply] using hykD
        | succ n ih =>
            simpa only [Nat.succ_eq_add_one,
              Function.iterate_succ_apply'] using
                hkDinv ⟨_, ih, rfl⟩)
      hkDclosed
  have hkDC : kD ⊆ C :=
    hkDmin C hCkD hCne hCclosed hCinv
  have hCeq : C = kD :=
    Set.Subset.antisymm hCkD hkDC
  change
    ∀ E : Set Y, E ⊆ C → E.Nonempty → IsClosed E →
      T '' E ⊆ E → C ⊆ E
  intro E hEC hEne hEclosed hEinv
  rw [hCeq]
  apply hkDmin E
  · rwa [← hCeq]
  · exact hEne
  · exact hEclosed
  · exact hEinv

end Chapter02.CompactGroupExtensionRecurrence
