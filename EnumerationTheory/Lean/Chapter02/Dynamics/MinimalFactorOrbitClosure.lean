import Chapter02.HallPetresco.HallPetrescoMeasureOrbit

open Classical Set

noncomputable section

namespace Chapter02.MinimalFactorOrbitClosure

open Chapter02.HallPetrescoMeasureOrbit
open Chapter02.HostKraStructuredRecurrence

universe u v

/-- Every forward orbit is dense when it meets every nonempty open set. -/
theorem dense_forwardOrbit_of_everyOrbitHitsOpen
    {Y : Type u} [TopologicalSpace Y]
    (S : Y → Y) (hminimal : EveryOrbitHitsOpen S) (y : Y) :
    Dense (forwardOrbit S y) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨n, hn⟩ := hminimal y U hU hUne
  exact ⟨(S^[n]) y, hn, ⟨n, rfl⟩⟩

/-- Iterated equivariance of a factor map. -/
theorem equivariant_iterate
    {Y : Type u} {P : Type v}
    (S : Y → Y) (T : P → P) (φ : Y → P)
    (hequiv : ∀ y, φ (S y) = T (φ y))
    (n : ℕ) (y : Y) :
    φ ((S^[n]) y) = (T^[n]) (φ y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hequiv,
        ih]

/-- Every point of a compact minimal system maps into the orbit closure of
the image of any chosen base point. -/
theorem factor_mem_orbitClosure_of_minimal
    {Y : Type u} {P : Type v}
    [TopologicalSpace Y]
    [TopologicalSpace P]
    (S : Y → Y) (T : P → P)
    (φ : Y → P) (hφ : Continuous φ)
    (hequiv : ∀ y, φ (S y) = T (φ y))
    (hminimal : EveryOrbitHitsOpen S)
    (y₀ y : Y) :
    φ y ∈ closure (forwardOrbit T (φ y₀)) := by
  have hequiv_iter (n : ℕ) (z : Y) :
      φ ((S^[n]) z) = (T^[n]) (φ z) :=
    equivariant_iterate S T φ hequiv n z
  have horbit_dense :
      Dense (forwardOrbit S y₀) :=
    dense_forwardOrbit_of_everyOrbitHitsOpen S hminimal y₀
  have hsubset :
      forwardOrbit S y₀ ⊆
        φ ⁻¹' closure (forwardOrbit T (φ y₀)) := by
    rintro _ ⟨n, rfl⟩
    change φ ((S^[n]) y₀) ∈ closure (forwardOrbit T (φ y₀))
    rw [hequiv_iter]
    exact subset_closure ⟨n, rfl⟩
  have hall :
      closure (forwardOrbit S y₀) ⊆
        φ ⁻¹' closure (forwardOrbit T (φ y₀)) :=
    closure_minimal hsubset (isClosed_closure.preimage hφ)
  rw [horbit_dense.closure_eq] at hall
  exact hall (Set.mem_univ y)

/-- A continuous factor of a compact minimal forward system has a minimal
orbit closure.  The conclusion is stated directly for the explicit orbit
closure construction used by the Hall--Petresco measure dynamics. -/
theorem everyOrbitHitsOpen_orbitClosure_of_factor
    {Y : Type u} {P : Type v}
    [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace P] [T2Space P]
    (S : Y → Y) (T : P → P)
    (hT : Continuous T)
    (φ : Y → P) (hφ : Continuous φ)
    (hequiv : ∀ y, φ (S y) = T (φ y))
    (hminimal : EveryOrbitHitsOpen S)
    (y₀ : Y) :
    EveryOrbitHitsOpen
      (orbitClosureStep T (φ y₀) hT) := by
  let Q := orbitClosure T (φ y₀)
  have hequiv_iter (n : ℕ) (y : Y) :
      φ ((S^[n]) y) = (T^[n]) (φ y) :=
    equivariant_iterate S T φ hequiv n y
  have horbit_sub_range :
      forwardOrbit T (φ y₀) ⊆ Set.range φ := by
    rintro _ ⟨n, rfl⟩
    exact ⟨(S^[n]) y₀, hequiv_iter n y₀⟩
  have hrange_closed : IsClosed (Set.range φ) :=
    (isCompact_range hφ).isClosed
  have hQ_range (q : Q) : q.1 ∈ Set.range φ :=
    (closure_minimal horbit_sub_range hrange_closed) q.2
  have hφ_mem (y : Y) :
      φ y ∈ closure (forwardOrbit T (φ y₀)) :=
    factor_mem_orbitClosure_of_minimal
      S T φ hφ hequiv hminimal y₀ y
  let φQ : Y → Q := fun y ↦ ⟨φ y, hφ_mem y⟩
  have hφQ : Continuous φQ :=
    hφ.subtype_mk _
  have hφQ_surj : Function.Surjective φQ := by
    intro q
    obtain ⟨y, hy⟩ := hQ_range q
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact hy
  have hequivQ (n : ℕ) (y : Y) :
      ((orbitClosureStep T (φ y₀) hT)^[n]) (φQ y) =
        φQ ((S^[n]) y) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        apply Subtype.ext
        exact (hequiv ((S^[n]) y)).symm
  intro q U hU hUne
  obtain ⟨y, rfl⟩ := hφQ_surj q
  have hpreopen : IsOpen (φQ ⁻¹' U) := hU.preimage hφQ
  have hprene : (φQ ⁻¹' U).Nonempty := by
    obtain ⟨q', hq'⟩ := hUne
    obtain ⟨y', rfl⟩ := hφQ_surj q'
    exact ⟨y', hq'⟩
  obtain ⟨n, hn⟩ := hminimal y (φQ ⁻¹' U) hpreopen hprene
  refine ⟨n, ?_⟩
  rw [hequivQ]
  exact hn

end Chapter02.MinimalFactorOrbitClosure
