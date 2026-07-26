import Chapter02.HallPetresco.HallPetrescoReducedRecurrence

open Classical Set

noncomputable section

namespace Chapter02.HallPetrescoReducedOrbitObservation

open Chapter02.HallPetrescoCompactReduced
open Chapter02.HallPetrescoMeasureOrbit
open Chapter02.HallPetrescoReducedHausdorff
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoReducedRecurrence
open Chapter02.HostKraStructuredRecurrence

universe u v

/-- The forward orbit closure of every actual reduced Hall--Petresco point
is a compact minimal forward system.

This is the dynamical statement needed for recurrence of one fixed
nilsystem correlation sequence.  It is strictly weaker than minimality of
the whole reduced quotient and follows from the already proved pointwise
orbit-closure minimality. -/
theorem everyOrbitHitsOpen_reducedStep_orbitClosure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : ReducedQuotient N P.lattice) :
    EveryOrbitHitsOpen
      (orbitClosureStep
        (reducedStep N P.lattice) q
        (continuous_reducedStep N P.lattice)) := by
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    reducedQuotientCompactSpaceOfPresentation N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  let T : ReducedQuotient N P.lattice →
      ReducedQuotient N P.lattice :=
    reducedStep N P.lattice
  let C : Set (ReducedQuotient N P.lattice) :=
    closure (forwardOrbit T q)
  let Q := {y : ReducedQuotient N P.lattice // y ∈ C}
  let S : Q → Q :=
    orbitClosureStep T q (continuous_reducedStep N P.lattice)
  have hiterate_all (m : ℕ) (s : Q) :
      ((S^[m]) s).1 = (T^[m]) s.1 := by
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [Function.iterate_succ_apply',
          Function.iterate_succ_apply']
        change T (((S^[m]) s).1) = T ((T^[m]) s.1)
        exact congrArg T ih
  intro r U hU hUne
  obtain ⟨V, hVopen, hVU⟩ := isOpen_induced_iff.mp hU
  obtain ⟨y, hyU⟩ := hUne
  have hyV : y.1 ∈ V := by
    have : y ∈ Subtype.val ⁻¹' V := by
      rw [hVU]
      exact hyU
    exact this
  have hyr :
      y.1 ∈ closure (forwardOrbit T r.1) := by
    rw [closure_forwardOrbit_eq_of_mem_reduced_orbitClosure
      N P q r.1 r.2]
    exact y.2
  obtain ⟨z, hzV, n, hzn⟩ :=
    mem_closure_iff.mp hyr V hVopen hyV
  refine ⟨n, ?_⟩
  have hiterate := hiterate_all n r
  change (T^[n]) r.1 = z at hzn
  have hnV : ((S^[n]) r).1 ∈ V := by
    rw [hiterate, hzn]
    exact hzV
  change (S^[n]) r ∈ U
  rw [← hVU]
  exact hnV

/-- Every continuous real observation along the orbit of an arbitrary
actual reduced Hall--Petresco point is a compact-minimal orbit sequence.

This supplies exactly the syndetic return-to-initial-value property used by
the already checked sharp time-zero bound. -/
theorem isMinimalOrbitSequence_reducedOrbitObservation
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : ReducedQuotient N P.lattice)
    (ψ : ReducedQuotient N P.lattice → ℝ)
    (hψ : Continuous ψ) :
    IsMinimalOrbitSequence.{u}
      (fun n ↦ ψ (((reducedStep N P.lattice)^[n]) q)) := by
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    reducedQuotientCompactSpaceOfPresentation N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  let T : ReducedQuotient N P.lattice →
      ReducedQuotient N P.lattice :=
    reducedStep N P.lattice
  let C : Set (ReducedQuotient N P.lattice) :=
    closure (forwardOrbit T q)
  let Q := {y : ReducedQuotient N P.lattice // y ∈ C}
  let S : Q → Q :=
    orbitClosureStep T q (continuous_reducedStep N P.lattice)
  let q₀ : Q := orbitClosureBase T q
  let φ : Q → ℝ := fun y ↦ ψ y.1
  refine ⟨Q, inferInstance,
    isCompact_iff_compactSpace.mp isClosed_closure.isCompact,
    S, q₀, φ, continuous_orbitClosureStep T q
      (continuous_reducedStep N P.lattice),
    everyOrbitHitsOpen_reducedStep_orbitClosure N P q,
    hψ.comp continuous_subtype_val, ?_⟩
  intro n
  change ψ ((T^[n]) q) = ψ (((S^[n]) q₀).1)
  rw [orbitClosureStep_iterate_base]

end Chapter02.HallPetrescoReducedOrbitObservation
