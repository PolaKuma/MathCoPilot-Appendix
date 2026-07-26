import Chapter02.Dynamics.CompactGroupExtensionRecurrence
import Chapter02.HallPetresco.HallPetrescoOrbitClosureRecurrence
import Chapter02.HallPetresco.HallPetrescoReducedHausdorff

open Classical Set

noncomputable section

namespace Chapter02.HallPetrescoReducedRecurrence

open Chapter02.CompactGroupExtensionRecurrence
open Chapter02.HallPetrescoCentralExtensionMinimality
open Chapter02.HallPetrescoOrbitClosureRecurrence
open Chapter02.HallPetrescoReducedAbelianFactor
open Chapter02.HallPetrescoReducedHausdorff
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HostKraStructuredRecurrence
open Chapter02.MinimalFactorOrbitClosure

universe u v

/-- Every point of the actual reduced Hall--Petresco quotient is recurrent
under the progression translation.

The reduced quotient is a compact central-torus extension of its common
minimal abelian factor.  The quadratic torus acts transitively on each
factor fiber and commutes with the reduced progression, so the general
compact-group-extension recurrence theorem applies. -/
theorem reducedStep_recurrent
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : ReducedQuotient N P.lattice) :
    q ∈ closure
      (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
        (reducedStep N P.lattice) (reducedStep N P.lattice q)) := by
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    Chapter02.HallPetrescoCompactReduced.reducedQuotientCompactSpaceOfPresentation
      N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  letI : CompactSpace (AbelianQuotient P.lattice) :=
    abelianQuotientCompactSpace N P
  letI : T2Space (AbelianQuotient P.lattice) :=
    abelianQuotientT2Space N P
  letI : MulAction (Fin N.torusDim → Circle)
      (ReducedQuotient N P.lattice) :=
    MulAction.compHom _ (quadraticReducedHom N)
  letI : ContinuousSMul (Fin N.torusDim → Circle)
      (ReducedQuotient N P.lattice) :=
    MulAction.continuousSMul_compHom
      (continuous_quadraticReducedHom N)
  apply recurrent_of_compact_group_extension
    (K := Fin N.torusDim → Circle)
    (T := reducedStep N P.lattice)
    (S := abelianStep P.lattice N.translation)
    (π := reducedToAbelianQuotient N P.lattice)
    (continuous_reducedStep N P.lattice)
    (continuous_reducedToAbelianQuotient N P.lattice)
    (reducedToAbelianQuotient_reducedStep N P.lattice)
    (everyOrbitHitsOpen_abelianStep N P)
  · intro z r
    change reducedStep N P.lattice
        (quadraticReducedElement N z • r) =
      quadraticReducedElement N z • reducedStep N P.lattice r
    exact reducedStep_quadratic_smul N P.lattice z r
  · intro r s hrs
    obtain ⟨z, hzs⟩ :=
      (reducedToAbelianQuotient_eq_iff_exists_quadratic_smul
        N P.lattice r s).mp hrs
    refine ⟨z, ?_⟩
    change quadraticReducedElement N z • r = s
    exact hzs.symm

/-- Every actual reduced Hall--Petresco forward orbit closure is a minimal
nonempty closed forward-invariant subsystem. -/
theorem reducedStep_orbitClosure_minimal
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : ReducedQuotient N P.lattice) :
    let C := closure
      (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
        (reducedStep N P.lattice) q)
    ∀ E : Set (ReducedQuotient N P.lattice),
      E ⊆ C → E.Nonempty → IsClosed E →
        reducedStep N P.lattice '' E ⊆ E → C ⊆ E := by
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    Chapter02.HallPetrescoCompactReduced.reducedQuotientCompactSpaceOfPresentation
      N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  letI : CompactSpace (AbelianQuotient P.lattice) :=
    abelianQuotientCompactSpace N P
  letI : T2Space (AbelianQuotient P.lattice) :=
    abelianQuotientT2Space N P
  letI : MulAction (Fin N.torusDim → Circle)
      (ReducedQuotient N P.lattice) :=
    MulAction.compHom _ (quadraticReducedHom N)
  letI : ContinuousSMul (Fin N.torusDim → Circle)
      (ReducedQuotient N P.lattice) :=
    MulAction.continuousSMul_compHom
      (continuous_quadraticReducedHom N)
  apply orbitClosure_minimal_of_compact_group_extension
    (K := Fin N.torusDim → Circle)
    (T := reducedStep N P.lattice)
    (S := abelianStep P.lattice N.translation)
    (π := reducedToAbelianQuotient N P.lattice)
    (continuous_reducedStep N P.lattice)
    (continuous_reducedToAbelianQuotient N P.lattice)
    (reducedToAbelianQuotient_reducedStep N P.lattice)
    (everyOrbitHitsOpen_abelianStep N P)
  · intro z r
    change reducedStep N P.lattice
        (quadraticReducedElement N z • r) =
      quadraticReducedElement N z • reducedStep N P.lattice r
    exact reducedStep_quadratic_smul N P.lattice z r
  · intro r s hrs
    obtain ⟨z, hzs⟩ :=
      (reducedToAbelianQuotient_eq_iff_exists_quadratic_smul
        N P.lattice r s).mp hrs
    refine ⟨z, ?_⟩
    change quadraticReducedElement N z • r = s
    exact hzs.symm

/-- Every reduced progression orbit closure still projects onto the whole
minimal common abelian factor. -/
theorem image_reduced_orbitClosure_eq_univ
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : ReducedQuotient N P.lattice) :
    reducedToAbelianQuotient N P.lattice ''
        closure
          (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
            (reducedStep N P.lattice) q) =
      Set.univ := by
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    Chapter02.HallPetrescoCompactReduced.reducedQuotientCompactSpaceOfPresentation
      N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  letI : T2Space (AbelianQuotient P.lattice) :=
    abelianQuotientT2Space N P
  let C := closure
    (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
      (reducedStep N P.lattice) q)
  have himageClosed :
      IsClosed (reducedToAbelianQuotient N P.lattice '' C) :=
    (isClosed_closure.isCompact.image
      (continuous_reducedToAbelianQuotient N P.lattice)).isClosed
  have horbit :
      Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
          (abelianStep P.lattice N.translation)
          (reducedToAbelianQuotient N P.lattice q) ⊆
        reducedToAbelianQuotient N P.lattice '' C := by
    rintro _ ⟨n, rfl⟩
    refine ⟨(reducedStep N P.lattice)^[n] q,
      subset_closure ⟨n, rfl⟩, ?_⟩
    exact equivariant_iterate
      (reducedStep N P.lattice)
      (abelianStep P.lattice N.translation)
      (reducedToAbelianQuotient N P.lattice)
      (reducedToAbelianQuotient_reducedStep N P.lattice)
      n q
  have hdense :
      Dense
        (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
          (abelianStep P.lattice N.translation)
          (reducedToAbelianQuotient N P.lattice q)) :=
    dense_forwardOrbit_of_everyOrbitHitsOpen
      (abelianStep P.lattice N.translation)
      (everyOrbitHitsOpen_abelianStep N P)
      (reducedToAbelianQuotient N P.lattice q)
  have hall :=
    closure_minimal horbit himageClosed
  rw [hdense.closure_eq] at hall
  exact Set.eq_univ_of_univ_subset hall

/-- Every point in a reduced progression orbit closure generates that
same orbit closure. -/
theorem closure_forwardOrbit_eq_of_mem_reduced_orbitClosure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q r : ReducedQuotient N P.lattice)
    (hr : r ∈ closure
      (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
        (reducedStep N P.lattice) q)) :
    closure
        (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
          (reducedStep N P.lattice) r) =
      closure
        (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
          (reducedStep N P.lattice) q) := by
  let C := closure
    (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
      (reducedStep N P.lattice) q)
  let D := closure
    (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
      (reducedStep N P.lattice) r)
  have hCclosed : IsClosed C := isClosed_closure
  have hCinv :
      reducedStep N P.lattice '' C ⊆ C :=
    image_closure_forwardOrbit_subset
      (reducedStep N P.lattice)
      (continuous_reducedStep N P.lattice) q
  have horbitDC :
      Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
          (reducedStep N P.lattice) r ⊆ C := by
    rintro _ ⟨n, rfl⟩
    induction n with
    | zero =>
        simpa only [Function.iterate_zero_apply] using hr
    | succ n ih =>
        simpa only [Nat.succ_eq_add_one,
          Function.iterate_succ_apply'] using
            hCinv ⟨_, ih, rfl⟩
  have hDC : D ⊆ C :=
    closure_minimal horbitDC hCclosed
  have hDne : D.Nonempty :=
    ⟨r, subset_closure
      ⟨0, by simp only [Function.iterate_zero_apply]⟩⟩
  have hDclosed : IsClosed D := isClosed_closure
  have hDinv :
      reducedStep N P.lattice '' D ⊆ D :=
    image_closure_forwardOrbit_subset
      (reducedStep N P.lattice)
      (continuous_reducedStep N P.lattice) r
  have hCD : C ⊆ D :=
    reducedStep_orbitClosure_minimal N P q D hDC hDne hDclosed hDinv
  exact Set.Subset.antisymm hDC hCD

/-- The vertical return subgroup is constant throughout a reduced
progression orbit closure. -/
theorem quadraticReturnSubgroup_eq_of_mem_reduced_orbitClosure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q r : ReducedQuotient N P.lattice)
    (hr : r ∈ closure
      (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
        (reducedStep N P.lattice) q)) :
    quadraticReturnSubgroup N P.lattice r =
      quadraticReturnSubgroup N P.lattice q := by
  have hclosure :=
    closure_forwardOrbit_eq_of_mem_reduced_orbitClosure
      N P q r hr
  apply Subgroup.ext
  intro z
  change
    quadraticReducedElement N z • r ∈
        closure
          (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
            (reducedStep N P.lattice) r) ↔
      quadraticReducedElement N z • q ∈
        closure
          (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
            (reducedStep N P.lattice) q)
  constructor
  · intro hz
    have hq :
        q ∈ closure
          (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
            (reducedStep N P.lattice) r) := by
      rw [hclosure]
      exact subset_closure ⟨0, rfl⟩
    have hzq :=
      quadratic_smul_orbitClosure_subset
        N P.lattice r z hz ⟨q, hq, rfl⟩
    rwa [hclosure] at hzq
  · intro hz
    have hzr :=
      quadratic_smul_orbitClosure_subset
        N P.lattice q z hz ⟨r, hr, rfl⟩
    rwa [hclosure]

/-- Inside one reduced progression orbit closure, every common-abelian
fiber is exactly one orbit of the common vertical return subgroup. -/
theorem exists_returnParameter_of_mem_orbitClosure_of_same_abelian
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q r s : ReducedQuotient N P.lattice)
    (hr : r ∈ closure
      (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
        (reducedStep N P.lattice) q))
    (hs : s ∈ closure
      (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
        (reducedStep N P.lattice) q))
    (hfactor :
      reducedToAbelianQuotient N P.lattice r =
        reducedToAbelianQuotient N P.lattice s) :
    ∃ z : Fin N.torusDim → Circle,
      z ∈ quadraticReturnSubgroup N P.lattice q ∧
        s = quadraticReducedElement N z • r := by
  obtain ⟨z, hzs⟩ :=
    (reducedToAbelianQuotient_eq_iff_exists_quadratic_smul
      N P.lattice r s).mp hfactor
  refine ⟨z, ?_, hzs⟩
  have hclosure :=
    closure_forwardOrbit_eq_of_mem_reduced_orbitClosure
      N P q r hr
  have hz_at_r :
      z ∈ quadraticReturnSubgroup N P.lattice r := by
    change quadraticReducedElement N z • r ∈
      closure
        (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
          (reducedStep N P.lattice) r)
    rw [hclosure, ← hzs]
    exact hs
  rw [quadraticReturnSubgroup_eq_of_mem_reduced_orbitClosure
    N P q r hr] at hz_at_r
  exact hz_at_r

/-- A vertical translate of a reduced progression orbit closure meets that
closure exactly when its parameter is a genuine vertical return. -/
theorem quadratic_translate_orbitClosure_inter_nonempty_iff
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : ReducedQuotient N P.lattice)
    (z : Fin N.torusDim → Circle) :
    (((quadraticReducedElement N z • ·) ''
          closure
            (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
              (reducedStep N P.lattice) q)) ∩
        closure
          (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
            (reducedStep N P.lattice) q)).Nonempty ↔
      z ∈ quadraticReturnSubgroup N P.lattice q := by
  constructor
  · rintro ⟨s, ⟨r, hr, rfl⟩, hzr⟩
    have hz_at_r :
        z ∈ quadraticReturnSubgroup N P.lattice r := by
      change quadraticReducedElement N z • r ∈
        closure
          (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
            (reducedStep N P.lattice) r)
      rw [closure_forwardOrbit_eq_of_mem_reduced_orbitClosure
        N P q r hr]
      exact hzr
    rw [quadraticReturnSubgroup_eq_of_mem_reduced_orbitClosure
      N P q r hr] at hz_at_r
    exact hz_at_r
  · intro hz
    refine ⟨quadraticReducedElement N z • q, ?_, hz⟩
    exact ⟨q, subset_closure ⟨0, rfl⟩, rfl⟩

/-- Thus the reduced progression generator belongs to every setwise
orbit-closure stabilizer. -/
theorem reducedProgressionGenerator_mem_orbitClosureStabilizer
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : ReducedQuotient N P.lattice) :
    reducedProgressionGenerator N ∈
      orbitClosureStabilizer N P.lattice q :=
  (reducedProgressionGenerator_mem_orbitClosureStabilizer_iff
    N P.lattice q).mpr (reducedStep_recurrent N P q)

/-- The orbit-closure stabilizer maps canonically to the common abelian
factor. -/
def stabilizerToAbelianQuotient
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ) :
    orbitClosureStabilizer N Γ q → AbelianQuotient Γ :=
  fun k ↦ QuotientGroup.mk (reducedLinearAbelianHom N k.1)

theorem continuous_stabilizerToAbelianQuotient
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ) :
    Continuous (stabilizerToAbelianQuotient N Γ q) :=
  QuotientGroup.continuous_mk.comp
    ((continuous_reducedLinearAbelianHom N).comp continuous_subtype_val)

/-- Because the progression generator is in the stabilizer and its image
is the minimal abelian rotation generator, the stabilizer has dense image
in the common abelian factor.  This is the horizontal half of the remaining
closed-orbit theorem. -/
theorem denseRange_stabilizerToAbelianQuotient
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : ReducedQuotient N P.lattice) :
    DenseRange (stabilizerToAbelianQuotient N P.lattice q) := by
  let a : ReducedGroup N := reducedProgressionGenerator N
  let K : Subgroup (ReducedGroup N) :=
    orbitClosureStabilizer N P.lattice q
  let b₀ : AbelianQuotient P.lattice :=
    (QuotientGroup.mk 1 : AbelianQuotient P.lattice)
  have haK : a ∈ K :=
    reducedProgressionGenerator_mem_orbitClosureStabilizer N P q
  have hiterate (n : ℕ) :
      ((abelianStep P.lattice N.translation)^[n]) b₀ =
        (QuotientGroup.mk
          (reducedLinearAbelianHom N (a ^ n)) :
            AbelianQuotient P.lattice) := by
    induction n with
    | zero =>
        simp only [Function.iterate_zero_apply, pow_zero, map_one]
        rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        change
          QuotientGroup.mk (Abelianization.of N.translation) *
              QuotientGroup.mk
                (reducedLinearAbelianHom N (a ^ n)) =
            QuotientGroup.mk
              (reducedLinearAbelianHom N (a ^ (n + 1)))
        rw [pow_succ, map_mul, reducedLinearAbelianHom_progression]
        rw [mul_comm]
        exact
          (QuotientGroup.mk_mul
            (abelianLattice P.lattice) _ _).symm
  have hdense :
      Dense (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
        (abelianStep P.lattice N.translation) b₀) :=
    dense_forwardOrbit_of_everyOrbitHitsOpen
      (abelianStep P.lattice N.translation)
      (everyOrbitHitsOpen_abelianStep N P) b₀
  apply hdense.mono
  rintro _ ⟨n, rfl⟩
  refine ⟨⟨a ^ n, K.pow_mem haK n⟩, ?_⟩
  exact (hiterate n).symm

end Chapter02.HallPetrescoReducedRecurrence
