import Chapter02.HallPetresco.LawfulCompactCentralAction
import Chapter02.HostKra.HostKraStructuredRecurrence
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Topology.Algebra.Group.Quotient

open Classical MeasureTheory

noncomputable section

namespace Chapter02.ToralTwoStepNilsystem

universe u v

/-- Operational data of a minimal two-step nilsystem whose last central
group is a finite-dimensional torus.

The carrier `H` is the ambient nilpotent group and `X` its compact
homogeneous probability space.  The lattice quotient construction will
produce this package; subsequent Hall--Petresco arguments need only the
listed intrinsic properties. -/
structure Model
    (H : Type u) (X : Type v)
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] (μ : Measure X) where
  t2Ambient : T2Space H
  ambientAction : Chapter02.LawfulCompactCentralAction H X μ
  transitive_ambientAction :
    ∀ x y : X, ∃ h : H, ambientAction.toMulAction.smul h x = y
  nilpotent : Group.IsNilpotent H
  twoStep : @Group.nilpotencyClass H _ nilpotent ≤ 2
  torusDim : ℕ
  centralHom : (Fin torusDim → Circle) →* H
  continuous_centralHom : Continuous centralHom
  injective_centralHom : Function.Injective centralHom
  centralHom_mem_center :
    ∀ z, centralHom z ∈ Subgroup.center H
  centralHom_range :
    centralHom.range = _root_.commutator H
  translation : H
  minimal_translation :
    Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen
      (ambientAction.toMulAction.smul translation)

/-- In every model of nilpotency class at most two, the full commutator
subgroup is central.  This extracts the genuine lower-central-series content
of `twoStep`; it does not identify that subgroup with the separately chosen
compact central torus. -/
theorem Model.commutator_le_center
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Model H X μ) :
    _root_.commutator H ≤ Subgroup.center H := by
  letI : Group.IsNilpotent H := N.nilpotent
  have h₂ : upperCentralSeries H 2 = ⊤ :=
    upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr
      N.twoStep
  rw [_root_.commutator_def]
  apply Subgroup.commutator_le.mpr
  intro g _ h _
  have hg₂ : g ∈ upperCentralSeries H 2 := by
    rw [h₂]
    exact Subgroup.mem_top g
  have hcomm : ⁅g, h⁆ ∈ upperCentralSeries H 1 :=
    (mem_upperCentralSeries_succ_iff.mp
      (show g ∈ upperCentralSeries H (1 + 1) by
        simpa using hg₂)) h
  simpa using hcomm

/-- The second lower-central subgroup is compact: by construction it is the
continuous image of the finite-dimensional central torus. -/
theorem Model.isCompact_commutator
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Model H X μ) :
    IsCompact (_root_.commutator H : Set H) := by
  rw [← N.centralHom_range]
  simpa only [MonoidHom.coe_range, Set.image_univ] using
    isCompact_univ.image N.continuous_centralHom

/-- The second lower-central subgroup is closed in the Hausdorff ambient
group. -/
theorem Model.isClosed_commutator
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Model H X μ) :
    IsClosed (_root_.commutator H : Set H) := by
  letI : T2Space H := N.t2Ambient
  exact N.isCompact_commutator.isClosed

/-- The genuine compact central torus action induced by the ambient
nilsystem action and the central embedding. -/
def Model.centralAction
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Model H X μ) :
    Chapter02.LawfulCompactCentralAction
      (Fin N.torusDim → Circle) X μ :=
  N.ambientAction.restrict N.centralHom N.continuous_centralHom

@[simp]
theorem Model.centralAction_smul
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Model H X μ) (z : Fin N.torusDim → Circle) (x : X) :
    N.centralAction.toMulAction.smul z x =
      N.ambientAction.toMulAction.smul (N.centralHom z) x :=
  rfl

/-- Central torus translations commute with every ambient translation on
the nilmanifold. -/
theorem Model.centralAction_commutes
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Model H X μ) (z : Fin N.torusDim → Circle)
    (h : H) (x : X) :
    N.centralAction.toMulAction.smul z
        (N.ambientAction.toMulAction.smul h x) =
      N.ambientAction.toMulAction.smul h
        (N.centralAction.toMulAction.smul z x) := by
  rw [N.centralAction_smul, N.centralAction_smul]
  calc
    N.ambientAction.toMulAction.smul (N.centralHom z)
        (N.ambientAction.toMulAction.smul h x) =
      N.ambientAction.toMulAction.smul (N.centralHom z * h) x := by
        symm
        exact N.ambientAction.toMulAction.mul_smul _ _ _
    _ = N.ambientAction.toMulAction.smul (h * N.centralHom z) x := by
      rw [(Subgroup.mem_center_iff.mp
        (N.centralHom_mem_center z) h).symm]
    _ = N.ambientAction.toMulAction.smul h
        (N.ambientAction.toMulAction.smul (N.centralHom z) x) :=
      N.ambientAction.toMulAction.mul_smul _ _ _

/-- The nilrotation underlying a toral two-step model. -/
def Model.nilrotation
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Model H X μ) : X → X :=
  N.ambientAction.toMulAction.smul N.translation

theorem Model.continuous_nilrotation
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Model H X μ) :
    Continuous N.nilrotation := by
  exact N.ambientAction.continuous_smul.comp
    (continuous_const.prodMk continuous_id)

theorem Model.measurePreserving_nilrotation
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Model H X μ) :
    MeasurePreserving N.nilrotation μ μ :=
  N.ambientAction.measurePreserving_smul N.translation

theorem Model.everyOrbitHitsOpen_nilrotation
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Model H X μ) :
    Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen
      N.nilrotation :=
  N.minimal_translation

/-- Iterating the nilrotation is the same as acting by the corresponding
power of its translating group element. -/
theorem Model.nilrotation_iterate
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Model H X μ) (n : ℕ) (x : X) :
    (N.nilrotation^[n]) x =
      N.ambientAction.toMulAction.smul (N.translation ^ n) x := by
  induction n generalizing x with
  | zero =>
      rw [Function.iterate_zero_apply, pow_zero]
      exact (N.ambientAction.toMulAction.one_smul x).symm
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      unfold Model.nilrotation
      calc
        N.ambientAction.toMulAction.smul (N.translation ^ n)
            (N.ambientAction.toMulAction.smul N.translation x) =
          N.ambientAction.toMulAction.smul
            (N.translation ^ n * N.translation) x := by
              symm
              exact N.ambientAction.toMulAction.mul_smul _ _ _
        _ = N.ambientAction.toMulAction.smul
            (N.translation ^ (n + 1)) x := by
              rw [pow_succ]

/-- Build the operational nilsystem package from a compact left-coset
quotient `H / Γ` with its invariant measure.  The quotient action and its
continuity are supplied by Mathlib; only the genuinely dynamical and
nilpotent hypotheses remain explicit. -/
def ofQuotient
    (H : Type u) [Group H] [TopologicalSpace H] [T2Space H]
    [IsTopologicalGroup H]
    (Γ : Subgroup H)
    [CompactSpace (H ⧸ Γ)]
    [MeasurableSpace (H ⧸ Γ)] [BorelSpace (H ⧸ Γ)]
    (μ : Measure (H ⧸ Γ))
    (hinv : ∀ h : H, MeasurePreserving (h • ·) μ μ)
    (hnil : Group.IsNilpotent H)
    (htwo : @Group.nilpotencyClass H _ hnil ≤ 2)
    (d : ℕ)
    (ι : (Fin d → Circle) →* H)
    (hιc : Continuous ι)
    (hιinj : Function.Injective ι)
    (hιcenter : ∀ z, ι z ∈ Subgroup.center H)
    (hιrange : ι.range = _root_.commutator H)
    (a : H)
    (hminimal :
      Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen
        (fun x : H ⧸ Γ ↦ a • x)) :
    Model H (H ⧸ Γ) μ where
  t2Ambient := inferInstance
  ambientAction :=
    Chapter02.LawfulCompactCentralAction.ofContinuousMulAction μ hinv
  transitive_ambientAction := by
    intro x y
    exact MulAction.exists_smul_eq H x y
  nilpotent := hnil
  twoStep := htwo
  torusDim := d
  centralHom := ι
  continuous_centralHom := hιc
  injective_centralHom := hιinj
  centralHom_mem_center := hιcenter
  centralHom_range := hιrange
  translation := a
  minimal_translation := hminimal

/-- A concrete homogeneous-space presentation of a toral nilsystem.

Unlike the operational `Model`, this structure remembers the actual lattice
and an equivariant homeomorphism with its left-coset quotient.  The explicit
`CompactSpace` witness prevents later Hall--Petresco arguments from silently
treating an arbitrary subgroup as a cocompact lattice. -/
structure QuotientPresentation
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Model H X μ) where
  lattice : Subgroup H
  discreteLattice : DiscreteTopology lattice
  compactFundamentalDomain :
    ∃ K : Set H, IsCompact K ∧
      (QuotientGroup.mk '' K : Set (H ⧸ lattice)) = Set.univ
  compactQuotient : CompactSpace (H ⧸ lattice)
  t2Quotient : T2Space (H ⧸ lattice)
  toQuotient : X ≃ₜ H ⧸ lattice
  equivariant :
    ∀ h x, toQuotient
      (N.ambientAction.toMulAction.smul h x) = h • toQuotient x

/-- The model built by `ofQuotient` carries its tautological genuine
homogeneous-space presentation. -/
def quotientPresentationOfQuotient
    (H : Type u) [Group H] [TopologicalSpace H] [T2Space H]
    [IsTopologicalGroup H]
    (Γ : Subgroup H)
    [DiscreteTopology Γ]
    (hfund :
      ∃ K : Set H, IsCompact K ∧
        (QuotientGroup.mk '' K : Set (H ⧸ Γ)) = Set.univ)
    [CompactSpace (H ⧸ Γ)]
    [T2Space (H ⧸ Γ)]
    [MeasurableSpace (H ⧸ Γ)] [BorelSpace (H ⧸ Γ)]
    (μ : Measure (H ⧸ Γ))
    (hinv : ∀ h : H, MeasurePreserving (h • ·) μ μ)
    (hnil : Group.IsNilpotent H)
    (htwo : @Group.nilpotencyClass H _ hnil ≤ 2)
    (d : ℕ)
    (ι : (Fin d → Circle) →* H)
    (hιc : Continuous ι)
    (hιinj : Function.Injective ι)
    (hιcenter : ∀ z, ι z ∈ Subgroup.center H)
    (hιrange : ι.range = _root_.commutator H)
    (a : H)
    (hminimal :
      Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen
        (fun x : H ⧸ Γ ↦ a • x)) :
    QuotientPresentation
      (ofQuotient
        H Γ μ hinv hnil htwo d ι hιc hιinj hιcenter hιrange a hminimal) where
  lattice := Γ
  discreteLattice := inferInstance
  compactFundamentalDomain := hfund
  compactQuotient := inferInstance
  t2Quotient := inferInstance
  toQuotient := Homeomorph.refl _
  equivariant := by
    intro h x
    rfl

end Chapter02.ToralTwoStepNilsystem
