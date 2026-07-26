import Chapter02.HallPetresco.HallPetrescoParryPropertyH

open Classical Set

noncomputable section

namespace Chapter02.HallPetrescoOrbitClosureRecurrence

open Chapter02.HallPetrescoMeasureOrbit
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoCentralExtensionMinimality

universe u v

/-- Translation by the reduced progression element, bundled as the actual
homeomorphism of the reduced homogeneous quotient. -/
def reducedStepHomeomorph
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) :
    ReducedQuotient N Γ ≃ₜ ReducedQuotient N Γ :=
  Homeomorph.smul (reducedProgressionGenerator N)

@[simp]
theorem reducedStepHomeomorph_apply
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ) :
    reducedStepHomeomorph N Γ q = reducedStep N Γ q :=
  rfl

/-- Applying a map to its forward orbit removes precisely the zeroth
iterate and gives the forward orbit based at the first iterate. -/
theorem image_forwardOrbit_eq_forwardOrbit_apply
    {Y : Type*} (T : Y → Y) (q : Y) :
    T '' forwardOrbit T q = forwardOrbit T (T q) := by
  ext y
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    refine ⟨n, ?_⟩
    exact ((Function.Commute.refl T).iterate_right n).eq q |>.symm
  · rintro ⟨n, rfl⟩
    refine ⟨(T^[n]) q, ⟨n, rfl⟩, ?_⟩
    exact ((Function.Commute.refl T).iterate_right n).eq q

/-- A homeomorphism maps the closure of a forward orbit onto the closure
of the corresponding tail orbit. -/
theorem image_closure_forwardOrbit_eq_closure_tail
    {Y : Type*} [TopologicalSpace Y]
    (e : Y ≃ₜ Y) (q : Y) :
    e '' closure (forwardOrbit e q) =
      closure (forwardOrbit e (e q)) := by
  rw [← e.isClosedMap.closure_image_eq_of_continuous e.continuous,
    image_forwardOrbit_eq_forwardOrbit_apply]

/-- If the initial point is a limit of its positive tail, then deleting
the zeroth iterate does not change the orbit closure. -/
theorem closure_forwardOrbit_eq_closure_tail_of_recurrent
    {Y : Type*} [TopologicalSpace Y]
    (T : Y → Y) (q : Y)
    (hrec : q ∈ closure (forwardOrbit T (T q))) :
    closure (forwardOrbit T q) =
      closure (forwardOrbit T (T q)) := by
  apply le_antisymm
  · apply closure_minimal
    · rintro y ⟨n, rfl⟩
      cases n with
      | zero =>
          simpa only [Function.iterate_zero_apply] using hrec
      | succ n =>
          apply subset_closure
          refine ⟨n, ?_⟩
          simpa only [Nat.succ_eq_add_one] using
            (Function.iterate_succ_apply T n q).symm
    · exact isClosed_closure
  · apply closure_mono
    rintro y ⟨n, rfl⟩
    refine ⟨n + 1, ?_⟩
    simpa only [Nat.succ_eq_add_one] using
      Function.iterate_succ_apply T n q

/-- A recurrent base point makes its forward orbit closure invariant under
the whole homeomorphism, not merely forward invariant. -/
theorem image_closure_forwardOrbit_eq_self_of_recurrent
    {Y : Type*} [TopologicalSpace Y]
    (e : Y ≃ₜ Y) (q : Y)
    (hrec : q ∈ closure (forwardOrbit e (e q))) :
    e '' closure (forwardOrbit e q) =
      closure (forwardOrbit e q) := by
  rw [image_closure_forwardOrbit_eq_closure_tail,
    ← closure_forwardOrbit_eq_closure_tail_of_recurrent e q hrec]

/-- For a homeomorphism, recurrence of the initial point is exactly
setwise invariance of its forward orbit closure. -/
theorem image_closure_forwardOrbit_eq_self_iff_recurrent
    {Y : Type*} [TopologicalSpace Y]
    (e : Y ≃ₜ Y) (q : Y) :
    e '' closure (forwardOrbit e q) =
        closure (forwardOrbit e q) ↔
      q ∈ closure (forwardOrbit e (e q)) := by
  constructor
  · intro hinv
    rw [← image_closure_forwardOrbit_eq_closure_tail e q, hinv]
    exact subset_closure ⟨0, by simp⟩
  · exact image_closure_forwardOrbit_eq_self_of_recurrent e q

/-- Consequently, a recurrent reduced progression point has the actual
progression generator in the setwise stabilizer of its orbit closure. -/
theorem reducedProgressionGenerator_mem_orbitClosureStabilizer_of_recurrent
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ)
    (hrec :
      q ∈ closure
        (forwardOrbit (reducedStep N Γ) (reducedStep N Γ q))) :
    reducedProgressionGenerator N ∈ orbitClosureStabilizer N Γ q := by
  change
    (fun x : ReducedQuotient N Γ ↦
        reducedProgressionGenerator N • x) ''
        closure (forwardOrbit (reducedStep N Γ) q) =
      closure (forwardOrbit (reducedStep N Γ) q)
  simpa only [reducedStepHomeomorph_apply] using
    image_closure_forwardOrbit_eq_self_of_recurrent
      (reducedStepHomeomorph N Γ) q hrec

/-- In the actual reduced homogeneous quotient, membership of the
progression generator in the orbit-closure stabilizer is equivalent to
recurrence of the base point. -/
theorem reducedProgressionGenerator_mem_orbitClosureStabilizer_iff
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ) :
    reducedProgressionGenerator N ∈ orbitClosureStabilizer N Γ q ↔
      q ∈ closure
        (forwardOrbit (reducedStep N Γ) (reducedStep N Γ q)) := by
  change
    ((fun x : ReducedQuotient N Γ ↦
        reducedProgressionGenerator N • x) ''
          closure (forwardOrbit (reducedStep N Γ) q) =
        closure (forwardOrbit (reducedStep N Γ) q)) ↔ _
  simpa only [reducedStepHomeomorph_apply] using
    image_closure_forwardOrbit_eq_self_iff_recurrent
      (reducedStepHomeomorph N Γ) q

end Chapter02.HallPetrescoOrbitClosureRecurrence
