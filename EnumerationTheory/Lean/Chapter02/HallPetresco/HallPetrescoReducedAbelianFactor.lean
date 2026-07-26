import Chapter02.HallPetresco.HallPetrescoAveragingSubgroup
import Chapter02.Dynamics.MinimalFactorOrbitClosure
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoReducedAbelianFactor

open Chapter02.HallPetrescoTwoStepGroup
open Chapter02.HallPetrescoLattice
open Chapter02.HallPetrescoNormalForm
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoAveragingSubgroup

universe u v

/-- The abelianization equipped with its quotient topology.  This
abbreviation keeps the quotient shape visible to typeclass inference. -/
abbrev AbelianFactor (H : Type u) [Group H] :=
  H ⧸ _root_.commutator H

instance {H : Type u} [Group H] : CommGroup (AbelianFactor H) :=
  Abelianization.commGroup H

/-- The linear Hall coefficient, after projection to the abelianization of
the original nilpotent group.  Although the raw extracted coefficient is not
multiplicative, its commutator defect disappears in the abelianization. -/
def linearAbelianHom
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    subgroup N →* AbelianFactor H where
  toFun s := Abelianization.of
    (extractedLinear ((s : subgroup N) : Vertex → H))
  map_one' := by
    simp [extractedLinear, extractedBase]
  map_mul' s t := by
    change Abelianization.of
        ((s.1 0 * t.1 0)⁻¹ * (s.1 1 * t.1 1)) =
      Abelianization.of ((s.1 0)⁻¹ * s.1 1) *
        Abelianization.of ((t.1 0)⁻¹ * t.1 1)
    simp only [map_mul, map_inv, mul_inv_rev]
    ac_rfl

@[simp]
theorem linearAbelianHom_apply
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (s : subgroup N) :
    linearAbelianHom N s = Abelianization.of
      (extractedLinear ((s : subgroup N) : Vertex → H)) :=
  rfl

theorem continuous_linearAbelianHom
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    Continuous (linearAbelianHom N) := by
  exact QuotientGroup.continuous_mk.comp
    (continuous_extractedLinear.comp continuous_subtype_val)

/-- The averaging subgroup is killed by the linear abelian coordinate. -/
theorem averagingNormalSubgroup_le_ker_linearAbelianHom
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    averagingNormalSubgroup N ≤ (linearAbelianHom N).ker := by
  intro s hs
  rw [← explicitAveragingSubgroup_eq_averagingNormalSubgroup N] at hs
  have hlin := (mem_explicitAveragingSubgroup_iff_extract N s).mp hs |>.1
  change Abelianization.of
      (extractedLinear ((s : subgroup N) : Vertex → H)) = 1
  exact (QuotientGroup.eq_one_iff _).mpr hlin

/-- The canonical homomorphism from the reduced HP group to the
abelianization of the original group. -/
def reducedLinearAbelianHom
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    ReducedGroup N →* AbelianFactor H :=
  QuotientGroup.lift (averagingNormalSubgroup N)
    (linearAbelianHom N)
    (averagingNormalSubgroup_le_ker_linearAbelianHom N)

@[simp]
theorem reducedLinearAbelianHom_mk
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (s : subgroup N) :
    reducedLinearAbelianHom N
        (QuotientGroup.mk' (averagingNormalSubgroup N) s) =
      Abelianization.of
        (extractedLinear ((s : subgroup N) : Vertex → H)) :=
  rfl

theorem continuous_reducedLinearAbelianHom
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    Continuous (reducedLinearAbelianHom N) := by
  apply QuotientGroup.isQuotientMap_mk
      (averagingNormalSubgroup N) |>.continuous_iff.mpr
  exact continuous_linearAbelianHom N

/-- Every abelianized linear coefficient is represented by a genuine
linear Hall--Petresco element. -/
theorem surjective_reducedLinearAbelianHom
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    Function.Surjective (reducedLinearAbelianHom N) := by
  intro a
  refine Quotient.inductionOn' a ?_
  intro h
  let s : subgroup N := ⟨linear h, linear_mem_subgroup N h⟩
  refine ⟨QuotientGroup.mk' (averagingNormalSubgroup N) s, ?_⟩
  change Abelianization.of
      (extractedLinear (linear h)) = Abelianization.of h
  rw [linear_eq_hallTuple N h, extractedLinear_hallTuple]

/-- The progression generator projects to the original translating element
in the abelianization. -/
@[simp]
theorem reducedLinearAbelianHom_progression
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    reducedLinearAbelianHom N (reducedProgressionGenerator N) =
      Abelianization.of N.translation := by
  change Abelianization.of
      (extractedLinear (linear N.translation)) =
    Abelianization.of N.translation
  rw [linear_eq_hallTuple N N.translation,
    extractedLinear_hallTuple]

/-- The image of the original lattice in the abelianization. -/
def abelianLattice
    {H : Type u} [Group H] (Γ : Subgroup H) :
    Subgroup (AbelianFactor H) :=
  Γ.map Abelianization.of

/-- The reduced HP lattice has exactly the same image in the abelianization
as the original lattice. -/
theorem map_reducedLattice_eq_abelianLattice
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) :
    (reducedLattice N Γ).map (reducedLinearAbelianHom N) =
      abelianLattice Γ := by
  apply le_antisymm
  · rintro y ⟨k, hk, rfl⟩
    rcases hk with ⟨s, hs, rfl⟩
    refine ⟨extractedLinear
      ((s : subgroup N) : Vertex → H), ?_, rfl⟩
    exact Γ.mul_mem (Γ.inv_mem (hs 0)) (hs 1)
  · rintro y ⟨γ, hγ, rfl⟩
    let s : subgroup N := ⟨linear γ, linear_mem_subgroup N γ⟩
    have hs : s ∈ subgroupLattice N Γ := by
      intro j
      change γ ^ j.val ∈ Γ
      exact Γ.pow_mem hγ j.val
    refine ⟨QuotientGroup.mk' (averagingNormalSubgroup N) s,
      ⟨s, hs, rfl⟩, ?_⟩
    change Abelianization.of
        (extractedLinear (linear γ)) = Abelianization.of γ
    rw [linear_eq_hallTuple N γ, extractedLinear_hallTuple]

/-- The common maximal abelian homogeneous factor appearing in BHK
Lemma 7.1. -/
abbrev AbelianQuotient
    {H : Type u} [Group H] (Γ : Subgroup H) :=
  AbelianFactor H ⧸ abelianLattice Γ

/-- The original homogeneous space maps canonically to its abelian
factor. -/
def originalQuotientToAbelianQuotient
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (Γ : Subgroup H) :
    (H ⧸ Γ) → AbelianQuotient Γ :=
  Quotient.map' Abelianization.of (by
    intro g h hgh
    apply QuotientGroup.leftRel_apply.mpr
    change (Abelianization.of g)⁻¹ * Abelianization.of h ∈
      abelianLattice Γ
    rw [← map_inv, ← map_mul]
    exact ⟨g⁻¹ * h, QuotientGroup.leftRel_apply.mp hgh, rfl⟩)

@[simp]
theorem originalQuotientToAbelianQuotient_mk
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (Γ : Subgroup H) (h : H) :
    originalQuotientToAbelianQuotient Γ
        (QuotientGroup.mk h : H ⧸ Γ) =
      (QuotientGroup.mk (Abelianization.of h) :
        AbelianQuotient Γ) :=
  Quotient.map'_mk'' _ _ _

theorem continuous_originalQuotientToAbelianQuotient
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (Γ : Subgroup H) :
    Continuous (originalQuotientToAbelianQuotient Γ) := by
  apply Continuous.quotient_lift
  exact QuotientGroup.continuous_mk.comp QuotientGroup.continuous_mk

theorem surjective_originalQuotientToAbelianQuotient
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (Γ : Subgroup H) :
    Function.Surjective (originalQuotientToAbelianQuotient Γ) := by
  intro y
  refine Quotient.inductionOn' y ?_
  intro a
  refine Quotient.inductionOn' a ?_
  intro h
  exact ⟨QuotientGroup.mk h,
    originalQuotientToAbelianQuotient_mk Γ h⟩

/-- The actual reduced HP homogeneous space maps to the same abelian
factor. -/
def reducedToAbelianQuotient
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) :
    ReducedQuotient N Γ → AbelianQuotient Γ :=
  Quotient.map' (reducedLinearAbelianHom N) (by
    intro g h hgh
    apply QuotientGroup.leftRel_apply.mpr
    change (reducedLinearAbelianHom N g)⁻¹ *
        reducedLinearAbelianHom N h ∈ abelianLattice Γ
    rw [← map_inv, ← map_mul,
      ← map_reducedLattice_eq_abelianLattice N Γ]
    exact ⟨g⁻¹ * h, QuotientGroup.leftRel_apply.mp hgh, rfl⟩)

@[simp]
theorem reducedToAbelianQuotient_mk
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (k : ReducedGroup N) :
    reducedToAbelianQuotient N Γ
        (QuotientGroup.mk k : ReducedQuotient N Γ) =
      (QuotientGroup.mk (reducedLinearAbelianHom N k) :
        AbelianQuotient Γ) :=
  Quotient.map'_mk'' _ _ _

theorem continuous_reducedToAbelianQuotient
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) :
    Continuous (reducedToAbelianQuotient N Γ) := by
  apply Continuous.quotient_lift
  exact QuotientGroup.continuous_mk.comp
    (continuous_reducedLinearAbelianHom N)

theorem surjective_reducedToAbelianQuotient
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) :
    Function.Surjective (reducedToAbelianQuotient N Γ) := by
  intro y
  refine Quotient.inductionOn' y ?_
  intro a
  obtain ⟨k, rfl⟩ := surjective_reducedLinearAbelianHom N a
  exact ⟨QuotientGroup.mk k,
    reducedToAbelianQuotient_mk N Γ k⟩

/-- Translation by the original nilrotation element on the common abelian
factor. -/
def abelianStep
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (Γ : Subgroup H) (t : H) :
    AbelianQuotient Γ → AbelianQuotient Γ :=
  fun q ↦ (QuotientGroup.mk (Abelianization.of t) :
    AbelianQuotient Γ) * q

theorem continuous_abelianStep
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (Γ : Subgroup H) (t : H) :
    Continuous (abelianStep Γ t) :=
  by
    unfold abelianStep
    fun_prop

theorem reducedToAbelianQuotient_reducedStep
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ) :
    reducedToAbelianQuotient N Γ (reducedStep N Γ q) =
      abelianStep Γ N.translation
        (reducedToAbelianQuotient N Γ q) := by
  refine Quotient.inductionOn' q ?_
  intro k
  change QuotientGroup.mk
      (reducedLinearAbelianHom N
        (reducedProgressionGenerator N * k)) =
    QuotientGroup.mk (Abelianization.of N.translation) *
      QuotientGroup.mk (reducedLinearAbelianHom N k)
  rw [map_mul, reducedLinearAbelianHom_progression]
  rfl

theorem originalQuotientToAbelianQuotient_translation
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (Γ : Subgroup H) (t : H) (q : H ⧸ Γ) :
    originalQuotientToAbelianQuotient Γ (t • q) =
      abelianStep Γ t (originalQuotientToAbelianQuotient Γ q) := by
  refine Quotient.inductionOn' q ?_
  intro h
  simp [abelianStep]

/-- The common abelian factor as a concrete factor of the original model. -/
def modelToAbelianQuotient
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    X → AbelianQuotient P.lattice :=
  originalQuotientToAbelianQuotient P.lattice ∘ P.toQuotient

theorem continuous_modelToAbelianQuotient
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Continuous (modelToAbelianQuotient N P) :=
  (continuous_originalQuotientToAbelianQuotient P.lattice).comp
    P.toQuotient.continuous

theorem surjective_modelToAbelianQuotient
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Function.Surjective (modelToAbelianQuotient N P) :=
  (surjective_originalQuotientToAbelianQuotient P.lattice).comp
    P.toQuotient.surjective

theorem modelToAbelianQuotient_nilrotation
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (x : X) :
    modelToAbelianQuotient N P (N.nilrotation x) =
      abelianStep P.lattice N.translation
        (modelToAbelianQuotient N P x) := by
  change originalQuotientToAbelianQuotient P.lattice
      (P.toQuotient (N.nilrotation x)) =
    abelianStep P.lattice N.translation
      (originalQuotientToAbelianQuotient P.lattice
        (P.toQuotient x))
  change originalQuotientToAbelianQuotient P.lattice
      (P.toQuotient
        (N.ambientAction.toMulAction.smul N.translation x)) = _
  rw [P.equivariant]
  exact originalQuotientToAbelianQuotient_translation
    P.lattice N.translation (P.toQuotient x)

/-- Minimality descends along a continuous surjective semiconjugacy. -/
theorem everyOrbitHitsOpen_of_surjective_factor
    {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B]
    (S : A → A) (T : B → B) (φ : A → B)
    (hφ : Continuous φ) (hφsurj : Function.Surjective φ)
    (hequiv : ∀ x, φ (S x) = T (φ x))
    (hminimal : Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen S) :
    Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen T := by
  intro y U hU hUne
  obtain ⟨x, rfl⟩ := hφsurj y
  have hpreopen : IsOpen (φ ⁻¹' U) := hU.preimage hφ
  have hprene : (φ ⁻¹' U).Nonempty := by
    obtain ⟨z, hz⟩ := hUne
    obtain ⟨w, rfl⟩ := hφsurj z
    exact ⟨w, hz⟩
  obtain ⟨n, hn⟩ := hminimal x (φ ⁻¹' U) hpreopen hprene
  refine ⟨n, ?_⟩
  rw [← Chapter02.MinimalFactorOrbitClosure.equivariant_iterate
    S T φ hequiv]
  exact hn

/-- The common abelian factor is minimal because it is a genuine factor of
the original minimal nilrotation. -/
theorem everyOrbitHitsOpen_abelianStep
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen
      (abelianStep P.lattice N.translation) :=
  everyOrbitHitsOpen_of_surjective_factor
    N.nilrotation (abelianStep P.lattice N.translation)
    (modelToAbelianQuotient N P)
    (continuous_modelToAbelianQuotient N P)
    (surjective_modelToAbelianQuotient N P)
    (modelToAbelianQuotient_nilrotation N P)
    N.minimal_translation

/-- Compactness of the common abelian factor follows directly from the
original compact homogeneous model. -/
noncomputable def abelianQuotientCompactSpace
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    CompactSpace (AbelianQuotient P.lattice) where
  isCompact_univ := by
    have h := isCompact_univ.image
      (continuous_modelToAbelianQuotient N P)
    rw [Set.image_univ,
      Set.range_eq_univ.mpr (surjective_modelToAbelianQuotient N P)] at h
    exact h

/-- The lattice in the common abelian factor is closed.  Its preimage is
the product of the original closed lattice with the compact commutator
kernel; equivalently, the quotient map by that compact kernel is closed. -/
theorem isClosed_abelianLattice
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    IsClosed (abelianLattice P.lattice : Set (AbelianFactor H)) := by
  letI : T2Space H := N.t2Ambient
  letI : T2Space (H ⧸ P.lattice) := P.t2Quotient
  have hΓ : IsClosed (P.lattice : Set H) :=
    QuotientGroup.t1Space_iff.mp inferInstance
  change IsClosed
    (P.lattice.map (QuotientGroup.mk' (_root_.commutator H)) :
      Set (AbelianFactor H))
  exact (QuotientGroup.isClosedMap_coe N.isCompact_commutator)
    (P.lattice : Set H) hΓ

/-- Hence the common maximal abelian homogeneous factor is Hausdorff. -/
noncomputable def abelianQuotientT2Space
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    T2Space (AbelianQuotient P.lattice) := by
  letI : IsClosed
      (abelianLattice P.lattice : Set (AbelianFactor H)) :=
    isClosed_abelianLattice N P
  infer_instance

/-- A quadratic central Hall element, viewed in the reduced group. -/
def quadraticReducedElement
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (z : Fin N.torusDim → Circle) : ReducedGroup N :=
  QuotientGroup.mk' (averagingNormalSubgroup N)
    ⟨quadratic (N.centralHom z),
      quadratic_central_mem_subgroup N z⟩

/-- The compact central torus maps homomorphically to the fiber of the
linear abelian coordinate. -/
def quadraticReducedHom
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    (Fin N.torusDim → Circle) →* ReducedGroup N where
  toFun := quadraticReducedElement N
  map_one' := by
    apply congrArg (QuotientGroup.mk' (averagingNormalSubgroup N))
    apply Subtype.ext
    funext j
    simp [quadratic]
  map_mul' z w := by
    apply congrArg (QuotientGroup.mk' (averagingNormalSubgroup N))
    apply Subtype.ext
    funext j
    change N.centralHom (z * w) ^ j.val.choose 2 =
      N.centralHom z ^ j.val.choose 2 *
        N.centralHom w ^ j.val.choose 2
    have hcomm : Commute (N.centralHom z) (N.centralHom w) :=
      (Subgroup.mem_center_iff.mp
        (N.centralHom_mem_center z) (N.centralHom w)).symm
    rw [map_mul]
    exact hcomm.mul_pow _

@[simp]
theorem quadraticReducedHom_apply
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (z : Fin N.torusDim → Circle) :
    quadraticReducedHom N z = quadraticReducedElement N z :=
  rfl

theorem continuous_quadraticReducedHom
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    Continuous (quadraticReducedHom N) := by
  apply QuotientGroup.continuous_mk.comp
  apply Continuous.subtype_mk
  rw [continuous_pi_iff]
  intro j
  exact N.continuous_centralHom.pow (j.val.choose 2)

/-- The quadratic torus parameter survives faithfully in the reduced
Hall--Petresco group. -/
theorem injective_quadraticReducedHom
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    Function.Injective (quadraticReducedHom N) := by
  intro z w hzw
  have hone :
      quadraticReducedHom N (z⁻¹ * w) = 1 := by
    rw [map_mul, map_inv, hzw, inv_mul_cancel]
  have hextract :=
    (reduced_mk_eq_one_iff_extract N
      (⟨quadratic (N.centralHom (z⁻¹ * w)),
        quadratic_central_mem_subgroup N (z⁻¹ * w)⟩ :
          subgroup N)).mp hone
  have hcentral : N.centralHom (z⁻¹ * w) = 1 := by
    simpa [extractedQuadratic, extractedLinear, extractedBase,
      quadratic] using hextract.2
  have hparam : z⁻¹ * w = 1 := by
    apply N.injective_centralHom
    rw [hcentral, map_one]
  exact inv_mul_eq_one.mp hparam

/-- The quadratic torus is a closed topological copy of its image in the
reduced Hall--Petresco group.  In particular, its inverse parameter on the
commutator layer is continuous. -/
theorem isClosedEmbedding_quadraticReducedHom
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    Topology.IsClosedEmbedding (quadraticReducedHom N) := by
  letI : T2Space H := N.t2Ambient
  exact (continuous_quadraticReducedHom N).isClosedEmbedding
    (injective_quadraticReducedHom N)

/-- The fiber of the reduced linear coordinate is exactly the image of the
quadratic central torus.  Thus the reduced HP group is a concrete central
torus extension of the original abelianization. -/
theorem ker_reducedLinearAbelianHom_eq_range_quadraticReducedHom
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    (reducedLinearAbelianHom N).ker =
      (quadraticReducedHom N).range := by
  apply le_antisymm
  · intro k hk
    refine Quotient.inductionOn' k ?_ hk
    intro s hs
    have hlin : extractedLinear
        ((s : subgroup N) : Vertex → H) ∈ _root_.commutator H := by
      exact (QuotientGroup.eq_one_iff _).mp hs
    have hsNormal :
        ((s : subgroup N) : Vertex → H) ∈ normalFormSubgroup N := by
      rw [← subgroup_eq_normalFormSubgroup N]
      exact s.property
    rcases hsNormal with ⟨⟨⟨g, a⟩, z⟩, hsa⟩
    have ha : a ∈ _root_.commutator H := by
      rw [← hsa, extractedLinear_hallTuple] at hlin
      exact hlin
    have harange : a ∈ N.centralHom.range := by
      rw [N.centralHom_range]
      exact ha
    rcases harange with ⟨w, hw⟩
    refine ⟨z, ?_⟩
    have hsdecomp :
        s = diagonalElement N g * linearCentralElement N w *
          ⟨quadratic (N.centralHom z),
            quadratic_central_mem_subgroup N z⟩ := by
      apply Subtype.ext
      funext j
      change ((s : subgroup N) : Vertex → H) j =
        g * N.centralHom w ^ j.val *
          N.centralHom z ^ j.val.choose 2
      rw [← hsa]
      simp only [hallTuple_apply, hw]
    change QuotientGroup.mk' (averagingNormalSubgroup N)
        ⟨quadratic (N.centralHom z),
          quadratic_central_mem_subgroup N z⟩ =
      QuotientGroup.mk' (averagingNormalSubgroup N) s
    rw [hsdecomp, map_mul, map_mul]
    have hd : QuotientGroup.mk' (averagingNormalSubgroup N)
        (diagonalElement N g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr
        (diagonalElement_mem_averagingNormalSubgroup N g)
    have hl : QuotientGroup.mk' (averagingNormalSubgroup N)
        (linearCentralElement N w) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr
        (linearCentralElement_mem_averagingNormalSubgroup N w)
    rw [hd, hl]
    simp
  · rintro k ⟨z, rfl⟩
    change reducedLinearAbelianHom N
        (quadraticReducedElement N z) = 1
    change Abelianization.of
        (extractedLinear (quadratic (N.centralHom z))) = 1
    rw [quadraticCentral_eq_hallTuple N z,
      extractedLinear_hallTuple]
    simp

/-- The quadratic torus is central in the reduced Hall--Petresco group. -/
theorem quadraticReducedElement_mem_center
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (z : Fin N.torusDim → Circle) :
    quadraticReducedElement N z ∈ Subgroup.center (ReducedGroup N) := by
  rw [Subgroup.mem_center_iff]
  intro k
  refine Quotient.inductionOn' k ?_
  intro s
  change
    QuotientGroup.mk' (averagingNormalSubgroup N) s *
        QuotientGroup.mk' (averagingNormalSubgroup N)
          ⟨quadratic (N.centralHom z),
            quadratic_central_mem_subgroup N z⟩ =
      QuotientGroup.mk' (averagingNormalSubgroup N)
          ⟨quadratic (N.centralHom z),
            quadratic_central_mem_subgroup N z⟩ *
        QuotientGroup.mk' (averagingNormalSubgroup N) s
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  funext j
  exact Subgroup.mem_center_iff.mp
    ((Subgroup.center H).pow_mem
      (N.centralHom_mem_center z) (j.val.choose 2))
    (((s : subgroup N) : Vertex → H) j)

/-- A pure linear Hall element in the reduced group. -/
def linearReducedElement
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) (a : H) :
    ReducedGroup N :=
  QuotientGroup.mk' (averagingNormalSubgroup N)
    ⟨linear a, linear_mem_subgroup N a⟩

/-- Multiplication of two reduced linear elements records precisely one
quadratic commutator coordinate. -/
theorem linearReducedElement_mul
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (a b : H) (z : Fin N.torusDim → Circle)
    (hz : N.centralHom z = ⁅a, b⁆) :
    linearReducedElement N a * linearReducedElement N b =
      linearReducedElement N (a * b) * quadraticReducedElement N z := by
  change
    QuotientGroup.mk' (averagingNormalSubgroup N)
        (⟨linear a, linear_mem_subgroup N a⟩ : subgroup N) *
      QuotientGroup.mk' (averagingNormalSubgroup N)
        (⟨linear b, linear_mem_subgroup N b⟩ : subgroup N) =
    QuotientGroup.mk' (averagingNormalSubgroup N)
        (⟨linear (a * b), linear_mem_subgroup N (a * b)⟩ : subgroup N) *
      QuotientGroup.mk' (averagingNormalSubgroup N)
        ⟨quadratic (N.centralHom z),
          quadratic_central_mem_subgroup N z⟩
  rw [← map_mul, ← map_mul]
  apply congrArg (QuotientGroup.mk' (averagingNormalSubgroup N))
  apply Subtype.ext
  change linear a * linear b =
    linear (a * b) * quadratic (N.centralHom z)
  have hswap : N.centralHom z = ⁅b, a⁆⁻¹ := by
    exact hz.trans (commutatorElement_inv b a).symm
  funext j
  have hm := congrFun (hallTuple_mul_eq N 1 a 1 b
      (1 : Fin N.torusDim → Circle)
      (1 : Fin N.torusDim → Circle) z (by simpa using hswap)) j
  simpa [hallTuple, mul_assoc] using hm

/-- Swapping two linear coefficients changes only by the linear central
commutator, which is killed in the reduced group. -/
theorem linearReducedElement_mul_commutator_swap
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (a b : H) (z : Fin N.torusDim → Circle)
    (hz : N.centralHom z = ⁅a, b⁆) :
    linearReducedElement N (a * b) =
      linearReducedElement N (b * a) := by
  have hc : N.centralHom z ∈ Subgroup.center H :=
    N.centralHom_mem_center z
  change QuotientGroup.mk' (averagingNormalSubgroup N)
      (⟨linear (a * b), linear_mem_subgroup N (a * b)⟩ : subgroup N) =
    QuotientGroup.mk' (averagingNormalSubgroup N)
      (⟨linear (b * a), linear_mem_subgroup N (b * a)⟩ : subgroup N)
  have hlinear :
      (⟨linear (a * b), linear_mem_subgroup N (a * b)⟩ : subgroup N) =
        linearCentralElement N z *
          ⟨linear (b * a), linear_mem_subgroup N (b * a)⟩ := by
    apply Subtype.ext
    funext j
    change (a * b) ^ j.val =
      N.centralHom z ^ j.val * (b * a) ^ j.val
    rw [Chapter02.HallPetrescoNormalForm.mul_eq_commutatorElement_mul_swap,
      ← hz]
    have hcomm : Commute (N.centralHom z) (b * a) :=
      (Subgroup.mem_center_iff.mp hc (b * a)).symm
    simpa [mul_assoc] using hcomm.mul_pow j.val
  rw [hlinear, map_mul, reduced_mk_linearCentralElement, one_mul]

/-- Every basic commutator of reduced linear elements is the square of its
quadratic central commutator coordinate. -/
theorem commutatorElement_linearReducedElement
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (a b : H) (z : Fin N.torusDim → Circle)
    (hz : N.centralHom z = ⁅a, b⁆) :
    ⁅linearReducedElement N a, linearReducedElement N b⁆ =
      quadraticReducedElement N (z ^ 2) := by
  have hab := linearReducedElement_mul N a b z hz
  have hzinv : N.centralHom z⁻¹ = ⁅b, a⁆ := by
    rw [map_inv, hz]
    exact commutatorElement_inv a b
  have hba := linearReducedElement_mul N b a z⁻¹ hzinv
  have hswap := linearReducedElement_mul_commutator_swap N a b z hz
  have hqcentral := quadraticReducedElement_mem_center N z
  have hqcomm (k : ReducedGroup N) :
      k * quadraticReducedElement N z =
        quadraticReducedElement N z * k :=
    Subgroup.mem_center_iff.mp hqcentral k
  have hmul :
      linearReducedElement N a * linearReducedElement N b =
        quadraticReducedElement N (z ^ 2) *
          (linearReducedElement N b * linearReducedElement N a) := by
    rw [hab, hba, hswap]
    change linearReducedElement N (b * a) * quadraticReducedHom N z =
      quadraticReducedHom N (z ^ 2) *
        (linearReducedElement N (b * a) *
          quadraticReducedHom N z⁻¹)
    rw [map_pow, map_inv]
    change linearReducedElement N (b * a) * quadraticReducedElement N z =
      quadraticReducedElement N z ^ 2 *
        (linearReducedElement N (b * a) *
          (quadraticReducedElement N z)⁻¹)
    rw [hqcomm]
    have hqinvcomm :
        linearReducedElement N (b * a) *
            (quadraticReducedElement N z)⁻¹ =
          (quadraticReducedElement N z)⁻¹ *
            linearReducedElement N (b * a) :=
      (show Commute (linearReducedElement N (b * a))
        (quadraticReducedElement N z) from
          hqcomm (linearReducedElement N (b * a))).inv_right.eq
    rw [hqinvcomm]
    group
  rw [commutatorElement_def, hmul]
  group

/-- Consequently the exact kernel of the reduced linear coordinate is a
central subgroup. -/
theorem ker_reducedLinearAbelianHom_le_center
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    (reducedLinearAbelianHom N).ker ≤
      Subgroup.center (ReducedGroup N) := by
  rw [ker_reducedLinearAbelianHom_eq_range_quadraticReducedHom N]
  rintro _ ⟨z, rfl⟩
  exact quadraticReducedElement_mem_center N z

/-- The algebraic commutator subgroup of the reduced group lies in the
explicit quadratic central kernel. -/
theorem commutator_le_ker_reducedLinearAbelianHom
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    _root_.commutator (ReducedGroup N) ≤
      (reducedLinearAbelianHom N).ker := by
  rw [_root_.commutator_def]
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  change reducedLinearAbelianHom N ⁅x, y⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

/-- Conversely, divisibility of the central torus makes every quadratic
kernel element an actual commutator in the reduced group. -/
theorem ker_reducedLinearAbelianHom_le_commutator
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    (reducedLinearAbelianHom N).ker ≤
      _root_.commutator (ReducedGroup N) := by
  rw [ker_reducedLinearAbelianHom_eq_range_quadraticReducedHom N]
  rintro _ ⟨z, rfl⟩
  have hsquare : Function.Surjective
      (fun w : Fin N.torusDim → Circle ↦ w ^ 2) := by
    intro q
    choose w hw using fun i ↦
      (Circle.isQuotientCoveringMap_npow 2).surjective (q i)
    refine ⟨w, funext fun i ↦ ?_⟩
    simpa only [Pi.pow_apply] using hw i
  obtain ⟨w, hw⟩ := hsquare z
  rw [← hw]
  have hc : N.centralHom w ∈ _root_.commutator H := by
    rw [← N.centralHom_range]
    exact ⟨w, rfl⟩
  rw [commutator_eq_closure] at hc
  have hgenerated_general (c : H)
      (hc : c ∈ Subgroup.closure (commutatorSet H)) :
      ∃ v : Fin N.torusDim → Circle,
        N.centralHom v = c ∧
          quadraticReducedElement N (v ^ 2) ∈
            _root_.commutator (ReducedGroup N) := by
    induction hc using Subgroup.closure_induction with
    | mem c hc =>
        rcases hc with ⟨a, b, rfl⟩
        have hc' : ⁅a, b⁆ ∈ N.centralHom.range := by
          rw [N.centralHom_range]
          exact Subgroup.commutator_mem_commutator
            (Subgroup.mem_top a) (Subgroup.mem_top b)
        rcases hc' with ⟨v, hv⟩
        refine ⟨v, hv, ?_⟩
        rw [← commutatorElement_linearReducedElement N a b v hv]
        exact Subgroup.commutator_mem_commutator
          (Subgroup.mem_top (linearReducedElement N a))
          (Subgroup.mem_top (linearReducedElement N b))
    | one =>
        refine ⟨1, map_one _, ?_⟩
        have hqone : quadraticReducedElement N 1 = 1 := by
          change quadraticReducedHom N 1 = 1
          exact map_one _
        simpa only [one_pow, hqone] using
          (_root_.commutator (ReducedGroup N)).one_mem
    | mul c d _ _ hc hd =>
        rcases hc with ⟨v, hv, hvc⟩
        rcases hd with ⟨u, hu, huc⟩
        refine ⟨v * u, by rw [map_mul, hv, hu], ?_⟩
        change quadraticReducedHom N ((v * u) ^ 2) ∈
          _root_.commutator (ReducedGroup N)
        rw [mul_pow, map_mul]
        exact (_root_.commutator (ReducedGroup N)).mul_mem hvc huc
    | inv c _ hc =>
        rcases hc with ⟨v, hv, hvc⟩
        refine ⟨v⁻¹, by rw [map_inv, hv], ?_⟩
        change quadraticReducedHom N ((v⁻¹) ^ 2) ∈
          _root_.commutator (ReducedGroup N)
        rw [inv_pow, map_inv]
        exact (_root_.commutator (ReducedGroup N)).inv_mem hvc
  have hgenerated := hgenerated_general (N.centralHom w) hc
  rcases hgenerated with ⟨v, hv, hvc⟩
  have hvw : v = w := N.injective_centralHom hv
  simpa [hvw] using hvc

/-- Thus the concrete quadratic torus is exactly the full commutator
subgroup of the reduced Hall--Petresco group. -/
theorem commutator_reducedGroup_eq_quadratic_range
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    _root_.commutator (ReducedGroup N) =
      (quadraticReducedHom N).range := by
  rw [← ker_reducedLinearAbelianHom_eq_range_quadraticReducedHom N]
  exact le_antisymm
    (commutator_le_ker_reducedLinearAbelianHom N)
    (ker_reducedLinearAbelianHom_le_commutator N)

/-- Equivalent exactness form: the linear abelian coordinate is the
algebraic abelianization map of the reduced group. -/
theorem ker_reducedLinearAbelianHom_eq_commutator
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    (reducedLinearAbelianHom N).ker =
      _root_.commutator (ReducedGroup N) :=
  le_antisymm
    (ker_reducedLinearAbelianHom_le_commutator N)
    (commutator_le_ker_reducedLinearAbelianHom N)

/-- The full commutator layer of the reduced group is compact. -/
theorem isCompact_commutator_reducedGroup
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    IsCompact
      (_root_.commutator (ReducedGroup N) : Set (ReducedGroup N)) := by
  rw [commutator_reducedGroup_eq_quadratic_range N]
  change IsCompact (Set.range (quadraticReducedHom N))
  simpa only [Set.image_univ] using
    isCompact_univ.image (continuous_quadraticReducedHom N)

/-- The full commutator layer is connected, since it is the continuous
image of a finite-dimensional circle torus. -/
theorem isConnected_commutator_reducedGroup
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    IsConnected
      (_root_.commutator (ReducedGroup N) : Set (ReducedGroup N)) := by
  letI : PathConnectedSpace (AddCircle (1 : ℝ)) :=
    AddCircle.pathConnectedSpace 1
  letI : ConnectedSpace Circle :=
    (AddCircle.homeomorphCircle one_ne_zero).surjective.connectedSpace
      (AddCircle.homeomorphCircle one_ne_zero).continuous
  letI : ∀ _ : Fin N.torusDim, ConnectedSpace Circle :=
    fun _ ↦ inferInstance
  rw [commutator_reducedGroup_eq_quadratic_range N]
  change IsConnected (Set.range (quadraticReducedHom N))
  simpa only [Set.image_univ] using
    isConnected_univ.image (quadraticReducedHom N)
      (continuous_quadraticReducedHom N).continuousOn

/-- In particular, the reduced Hall--Petresco group is genuinely
two-step: its full commutator subgroup is central. -/
theorem reducedGroup_commutator_le_center
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    _root_.commutator (ReducedGroup N) ≤
      Subgroup.center (ReducedGroup N) :=
  (commutator_le_ker_reducedLinearAbelianHom N).trans
    (ker_reducedLinearAbelianHom_le_center N)

/-- The central kernel is compact, as it is the continuous image of the
finite-dimensional quadratic torus. -/
theorem isCompact_ker_reducedLinearAbelianHom
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    IsCompact
      ((reducedLinearAbelianHom N).ker : Set (ReducedGroup N)) := by
  rw [ker_reducedLinearAbelianHom_eq_range_quadraticReducedHom N]
  change IsCompact (Set.range (quadraticReducedHom N))
  simpa only [Set.image_univ] using
    isCompact_univ.image (continuous_quadraticReducedHom N)

/-- Two points of the reduced homogeneous space have the same abelian
coordinate exactly when they differ by the central kernel action. -/
theorem reducedToAbelianQuotient_eq_iff_exists_kernel_smul
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q r : ReducedQuotient N Γ) :
    reducedToAbelianQuotient N Γ q =
        reducedToAbelianQuotient N Γ r ↔
      ∃ h : ReducedGroup N,
        h ∈ (reducedLinearAbelianHom N).ker ∧ r = h • q := by
  refine Quotient.inductionOn' q ?_
  intro k
  refine Quotient.inductionOn' r ?_
  intro l
  constructor
  · intro hfac
    rw [reducedToAbelianQuotient_mk,
      reducedToAbelianQuotient_mk] at hfac
    have hab :
        (reducedLinearAbelianHom N k)⁻¹ *
            reducedLinearAbelianHom N l ∈ abelianLattice Γ :=
      QuotientGroup.eq.mp hfac
    rw [← map_reducedLattice_eq_abelianLattice N Γ] at hab
    rcases hab with ⟨a, ha, hfa⟩
    let h : ReducedGroup N := l * a⁻¹ * k⁻¹
    have hh : h ∈ (reducedLinearAbelianHom N).ker := by
      change reducedLinearAbelianHom N h = 1
      dsimp [h]
      rw [map_mul, map_mul, map_inv, map_inv, hfa]
      group
    refine ⟨h, hh, ?_⟩
    change QuotientGroup.mk l =
      QuotientGroup.mk (h * k)
    apply QuotientGroup.eq.mpr
    change l⁻¹ * (h * k) ∈ reducedLattice N Γ
    simpa [h] using (reducedLattice N Γ).inv_mem ha
  · rintro ⟨h, hh, hr⟩
    rw [hr]
    change QuotientGroup.mk (reducedLinearAbelianHom N k) =
      QuotientGroup.mk
        (reducedLinearAbelianHom N (h * k))
    change reducedLinearAbelianHom N h = 1 at hh
    rw [map_mul, hh, one_mul]

/-- Using the exact kernel parameterization, equality in the common
abelian factor is equivalently orbit-equivalence under the concrete
quadratic torus. -/
theorem reducedToAbelianQuotient_eq_iff_exists_quadratic_smul
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q r : ReducedQuotient N Γ) :
    reducedToAbelianQuotient N Γ q =
        reducedToAbelianQuotient N Γ r ↔
      ∃ z : Fin N.torusDim → Circle,
        r = quadraticReducedElement N z • q := by
  rw [reducedToAbelianQuotient_eq_iff_exists_kernel_smul N Γ q r,
    ker_reducedLinearAbelianHom_eq_range_quadraticReducedHom N]
  constructor
  · rintro ⟨h, ⟨z, rfl⟩, hr⟩
    exact ⟨z, hr⟩
  · rintro ⟨z, hr⟩
    exact ⟨quadraticReducedHom N z, ⟨z, rfl⟩, hr⟩

/-- Intrinsic maximal-abelian-factor form of the fiber theorem: the fibers
are exactly the orbits of the full commutator subgroup. -/
theorem reducedToAbelianQuotient_eq_iff_exists_commutator_smul
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q r : ReducedQuotient N Γ) :
    reducedToAbelianQuotient N Γ q =
        reducedToAbelianQuotient N Γ r ↔
      ∃ h : ReducedGroup N,
        h ∈ _root_.commutator (ReducedGroup N) ∧ r = h • q := by
  simpa only [ker_reducedLinearAbelianHom_eq_commutator N] using
    reducedToAbelianQuotient_eq_iff_exists_kernel_smul N Γ q r

end Chapter02.HallPetrescoReducedAbelianFactor
