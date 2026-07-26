import Chapter02.HostKra.HostKraStructuredRecurrence

open Classical Set

noncomputable section

namespace Chapter02.MinimalOrbitUniverseLowering

open Chapter02.HostKraStructuredRecurrence

universe u

/-- Left shift on real one-sided sequences. -/
def realShift (y : ℕ → ℝ) : ℕ → ℝ :=
  fun n ↦ y (n + 1)

theorem continuous_realShift :
    Continuous realShift := by
  rw [continuous_pi_iff]
  intro n
  exact continuous_apply (n + 1)

/-- The complete forward observation name of a point. -/
def observationName
    {X : Type u} (T : X → X) (f : X → ℝ) (x : X) : ℕ → ℝ :=
  fun n ↦ f ((T^[n]) x)

theorem continuous_observationName
    {X : Type u} [TopologicalSpace X]
    (T : X → X) (hT : Continuous T)
    (f : X → ℝ) (hf : Continuous f) :
    Continuous (observationName T f) := by
  rw [continuous_pi_iff]
  intro n
  exact hf.comp (hT.iterate n)

theorem observationName_equivariant
    {X : Type u} (T : X → X) (f : X → ℝ) (x : X) :
    observationName T f (T x) =
      realShift (observationName T f x) := by
  funext n
  simp only [observationName, realShift]
  rw [Function.iterate_succ_apply]

/-- Restriction of the real shift to the compact range of an observation
name. -/
def rangeShift
    {X : Type u} (T : X → X) (f : X → ℝ) :
    Set.range (observationName T f) →
      Set.range (observationName T f) := by
  intro y
  refine ⟨realShift y.1, ?_⟩
  obtain ⟨x, hx⟩ := y.2
  refine ⟨T x, ?_⟩
  rw [← hx]
  exact (observationName_equivariant T f x).symm

theorem continuous_rangeShift
    {X : Type u} [TopologicalSpace X]
    (T : X → X) (f : X → ℝ) :
    Continuous (rangeShift T f) := by
  exact
    (continuous_realShift.comp continuous_subtype_val).subtype_mk _

theorem rangeShift_observationName
    {X : Type u} (T : X → X) (f : X → ℝ) (x : X) :
    rangeShift T f
        ⟨observationName T f x, Set.mem_range_self x⟩ =
      ⟨observationName T f (T x), Set.mem_range_self (T x)⟩ := by
  apply Subtype.ext
  change realShift (observationName T f x) =
    observationName T f (T x)
  exact (observationName_equivariant T f x).symm

theorem rangeShift_iterate_observationName
    {X : Type u} (T : X → X) (f : X → ℝ)
    (x : X) (n : ℕ) :
    ((rangeShift T f)^[n])
        ⟨observationName T f x, Set.mem_range_self x⟩ =
      ⟨observationName T f ((T^[n]) x),
        Set.mem_range_self ((T^[n]) x)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih,
        Function.iterate_succ_apply']
      exact rangeShift_observationName T f ((T^[n]) x)

/-- A compact-minimal orbit representation can always be universe-lowered
to the compact range of its real observation-name map, a subtype of
`ℕ → ℝ` in `Type 0`. -/
theorem isMinimalOrbitSequence_zero_of
    {a : ℕ → ℝ}
    (ha : IsMinimalOrbitSequence.{u} a) :
    IsMinimalOrbitSequence.{0} a := by
  obtain ⟨X, topX, compactX, T, x₀, f, hT, hminimal, hf, haeq⟩ := ha
  letI : TopologicalSpace X := topX
  letI : CompactSpace X := compactX
  let Y : Type := Set.range (observationName T f)
  let S : Y → Y := rangeShift T f
  let code : X → Y :=
    fun x ↦ ⟨observationName T f x, Set.mem_range_self x⟩
  have hcode : Continuous code :=
    (continuous_observationName T hT f hf).subtype_mk _
  have hcodeSurj : Function.Surjective code := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  letI : CompactSpace Y :=
    isCompact_iff_compactSpace.mp
      (by
        simpa only [Y] using
          isCompact_range
            (continuous_observationName T hT f hf))
  have hequiv (x : X) : S (code x) = code (T x) :=
    rangeShift_observationName T f x
  have hequiv_iterate (n : ℕ) (x : X) :
      (S^[n]) (code x) = code ((T^[n]) x) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih,
          Function.iterate_succ_apply', hequiv]
  have hSminimal : EveryOrbitHitsOpen S := by
    intro y U hU hUne
    obtain ⟨x, rfl⟩ := hcodeSurj y
    have hpreOpen : IsOpen (code ⁻¹' U) := hU.preimage hcode
    have hpreNe : (code ⁻¹' U).Nonempty := by
      obtain ⟨y', hy'⟩ := hUne
      obtain ⟨x', rfl⟩ := hcodeSurj y'
      exact ⟨x', hy'⟩
    obtain ⟨n, hn⟩ := hminimal x (code ⁻¹' U) hpreOpen hpreNe
    refine ⟨n, ?_⟩
    rw [hequiv_iterate]
    exact hn
  let y₀ : Y := code x₀
  let g : Y → ℝ := fun y ↦ y.1 0
  have hg : Continuous g :=
    (continuous_apply 0).comp continuous_subtype_val
  refine ⟨Y, inferInstance, inferInstance, S, y₀, g,
    continuous_rangeShift T f, hSminimal, hg, fun n ↦ ?_⟩
  rw [hequiv_iterate]
  change a n = f ((T^[n]) x₀)
  exact haeq n

end Chapter02.MinimalOrbitUniverseLowering
