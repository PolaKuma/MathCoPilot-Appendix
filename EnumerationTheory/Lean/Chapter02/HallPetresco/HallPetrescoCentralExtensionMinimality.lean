import Chapter02.HallPetresco.HallPetrescoReducedAbelianFactor
import Chapter02.HallPetresco.HallPetrescoCompactReduced
import Chapter02.HallPetresco.HallPetrescoReducedHausdorff
import Mathlib.Topology.Algebra.Group.SubmonoidClosure

open Classical Set
open scoped Pointwise

noncomputable section

namespace Chapter02.HallPetrescoCentralExtensionMinimality

open Chapter02.HostKraStructuredRecurrence
open Chapter02.HallPetrescoMeasureOrbit
open Chapter02.HallPetrescoTwoStepGroup
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoCompactReduced
open Chapter02.HallPetrescoReducedHausdorff
open Chapter02.HallPetrescoReducedAbelianFactor
open Chapter02.MinimalFactorOrbitClosure

universe u v

/-- Saturation of a subset of the reduced quotient by the concrete
quadratic central torus. -/
def quadraticSaturation
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (U : Set (ReducedQuotient N Γ)) :
    Set (ReducedQuotient N Γ) :=
  ⋃ z : Fin N.torusDim → Circle,
    (Homeomorph.smul (quadraticReducedElement N z)) '' U

theorem isOpen_quadraticSaturation
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (U : Set (ReducedQuotient N Γ))
    (hU : IsOpen U) :
    IsOpen (quadraticSaturation N Γ U) := by
  apply isOpen_iUnion
  intro z
  exact (Homeomorph.smul (quadraticReducedElement N z)).isOpenMap U hU

/-- The saturation is exactly the pullback of the image in the common
maximal abelian factor. -/
theorem quadraticSaturation_eq_preimage_image
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (U : Set (ReducedQuotient N Γ)) :
    quadraticSaturation N Γ U =
      reducedToAbelianQuotient N Γ ⁻¹'
        (reducedToAbelianQuotient N Γ '' U) := by
  ext q
  constructor
  · intro hq
    simp only [quadraticSaturation, mem_iUnion] at hq
    rcases hq with ⟨z, u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    exact (reducedToAbelianQuotient_eq_iff_exists_quadratic_smul
      N Γ u (quadraticReducedElement N z • u)).mpr ⟨z, rfl⟩
  · rintro ⟨u, hu, hqu⟩
    have hfiber :=
      (reducedToAbelianQuotient_eq_iff_exists_quadratic_smul
        N Γ u q).mp hqu
    rcases hfiber with ⟨z, rfl⟩
    simp only [quadraticSaturation, mem_iUnion]
    exact ⟨z, u, hu, rfl⟩

/-- The common abelian factor map is open.  This follows from compact-to-
Hausdorff quotientness together with the explicit open central saturation
of every open subset. -/
theorem isOpenMap_reducedToAbelianQuotient
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    IsOpenMap (reducedToAbelianQuotient N P.lattice) := by
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    reducedQuotientCompactSpaceOfPresentation N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  letI : T2Space (AbelianQuotient P.lattice) :=
    abelianQuotientT2Space N P
  have hquot : Topology.IsQuotientMap
      (reducedToAbelianQuotient N P.lattice) :=
    (continuous_reducedToAbelianQuotient N P.lattice).isClosedMap.isQuotientMap
      (continuous_reducedToAbelianQuotient N P.lattice)
      (surjective_reducedToAbelianQuotient N P.lattice)
  intro U hU
  apply hquot.isOpen_preimage.mp
  rw [← quadraticSaturation_eq_preimage_image N P.lattice U]
  exact isOpen_quadraticSaturation N P.lattice U hU

/-- The saturated forward orbit is dense as soon as the common abelian
factor rotation is minimal. -/
theorem dense_quadraticSaturation_forwardOrbit
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : ReducedQuotient N P.lattice) :
    Dense (quadraticSaturation N P.lattice
      (forwardOrbit (reducedStep N P.lattice) q)) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  have hπUopen : IsOpen
      (reducedToAbelianQuotient N P.lattice '' U) :=
    isOpenMap_reducedToAbelianQuotient N P U hU
  have hπUne :
      (reducedToAbelianQuotient N P.lattice '' U).Nonempty :=
    hUne.image _
  obtain ⟨n, hn⟩ := everyOrbitHitsOpen_abelianStep N P
    (reducedToAbelianQuotient N P.lattice q)
    (reducedToAbelianQuotient N P.lattice '' U) hπUopen hπUne
  have hequiv := equivariant_iterate
    (reducedStep N P.lattice) (abelianStep P.lattice N.translation)
    (reducedToAbelianQuotient N P.lattice)
    (reducedToAbelianQuotient_reducedStep N P.lattice) n q
  rw [← hequiv] at hn
  rcases hn with ⟨u, hu, hπu⟩
  have hfiber :=
    (reducedToAbelianQuotient_eq_iff_exists_quadratic_smul
      N P.lattice ((reducedStep N P.lattice)^[n] q) u).mp hπu.symm
  rcases hfiber with ⟨z, rfl⟩
  refine ⟨quadraticReducedElement N z •
      ((reducedStep N P.lattice)^[n] q), hu, ?_⟩
  simp only [quadraticSaturation, mem_iUnion]
  exact ⟨z, (reducedStep N P.lattice)^[n] q, ⟨n, rfl⟩, rfl⟩

/-- The reduced progression commutes with every quadratic central
translation. -/
theorem reducedStep_quadratic_smul
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (z : Fin N.torusDim → Circle)
    (q : ReducedQuotient N Γ) :
    reducedStep N Γ (quadraticReducedElement N z • q) =
      quadraticReducedElement N z • reducedStep N Γ q := by
  change reducedProgressionGenerator N •
      (quadraticReducedElement N z • q) =
    quadraticReducedElement N z •
      (reducedProgressionGenerator N • q)
  rw [← mul_smul, ← mul_smul]
  congr 1
  exact Subgroup.mem_center_iff.mp
    (quadraticReducedElement_mem_center N z)
    (reducedProgressionGenerator N)

theorem reducedStep_iterate_quadratic_smul
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (z : Fin N.torusDim → Circle)
    (n : ℕ) (q : ReducedQuotient N Γ) :
    ((reducedStep N Γ)^[n]) (quadraticReducedElement N z • q) =
      quadraticReducedElement N z •
        ((reducedStep N Γ)^[n]) q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        reducedStep_quadratic_smul]

/-- The one remaining vertical recurrence property in the central
extension proof: every forward orbit closure contains its entire concrete
quadratic fiber. -/
def HasFullQuadraticFiberOrbitClosure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) : Prop :=
  ∀ q : ReducedQuotient N Γ,
    ∀ z : Fin N.torusDim → Circle,
      quadraticReducedElement N z • q ∈
        closure (forwardOrbit (reducedStep N Γ) q)

/-- Forward iteration preserves the closure of a forward orbit. -/
theorem iterate_mem_orbitClosure_of_mem_orbitClosure
    {Y : Type*} [TopologicalSpace Y]
    (T : Y → Y) (hT : Continuous T) (q r : Y)
    (hr : r ∈ closure (forwardOrbit T q)) (n : ℕ) :
    (T^[n]) r ∈ closure (forwardOrbit T q) := by
  apply map_mem_closure (hT.iterate n) hr
  rintro _ ⟨m, rfl⟩
  refine ⟨n + m, ?_⟩
  change (T^[n + m]) q = (T^[n]) ((T^[m]) q)
  rw [Function.iterate_add_apply]

/-- A central parameter which returns the base point into its orbit closure
preserves that entire orbit closure. -/
theorem quadratic_smul_orbitClosure_subset
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ)
    (z : Fin N.torusDim → Circle)
    (hz : quadraticReducedElement N z • q ∈
      closure (forwardOrbit (reducedStep N Γ) q)) :
    (quadraticReducedElement N z • ·) ''
        closure (forwardOrbit (reducedStep N Γ) q) ⊆
      closure (forwardOrbit (reducedStep N Γ) q) := by
  rintro _ ⟨r, hr, rfl⟩
  let f : ReducedQuotient N Γ → ReducedQuotient N Γ :=
    fun x ↦ quadraticReducedElement N z • x
  have hf : Continuous f := continuous_const_smul _
  have himage : f '' forwardOrbit (reducedStep N Γ) q ⊆
      closure (forwardOrbit (reducedStep N Γ) q) := by
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    change quadraticReducedElement N z •
        ((reducedStep N Γ)^[n]) q ∈
      closure (forwardOrbit (reducedStep N Γ) q)
    rw [← reducedStep_iterate_quadratic_smul]
    exact iterate_mem_orbitClosure_of_mem_orbitClosure
      (reducedStep N Γ) (continuous_reducedStep N Γ) q
      (quadraticReducedElement N z • q) hz n
  apply closure_minimal himage isClosed_closure
  exact image_closure_subset_closure_image hf ⟨r, hr, rfl⟩

/-- Parameters whose central translate of `q` lies in the forward orbit
closure. -/
def quadraticReturnSet
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ) :
    Set (Fin N.torusDim → Circle) :=
  {z | quadraticReducedElement N z • q ∈
    closure (forwardOrbit (reducedStep N Γ) q)}

theorem one_mem_quadraticReturnSet
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ) :
    1 ∈ quadraticReturnSet N Γ q := by
  change quadraticReducedHom N 1 • q ∈
    closure (forwardOrbit (reducedStep N Γ) q)
  rw [map_one, one_smul]
  exact subset_closure ⟨0, rfl⟩

theorem mul_mem_quadraticReturnSet
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ)
    {z w : Fin N.torusDim → Circle}
    (hz : z ∈ quadraticReturnSet N Γ q)
    (hw : w ∈ quadraticReturnSet N Γ q) :
    z * w ∈ quadraticReturnSet N Γ q := by
  change quadraticReducedHom N (z * w) • q ∈
    closure (forwardOrbit (reducedStep N Γ) q)
  rw [map_mul, mul_smul]
  exact quadratic_smul_orbitClosure_subset N Γ q z hz ⟨_, hw, rfl⟩

theorem isClosed_quadraticReturnSet
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ) :
    IsClosed (quadraticReturnSet N Γ q) := by
  apply isClosed_closure.preimage
  exact continuous_smul.comp
    ((continuous_quadraticReducedHom N).prodMk continuous_const)

theorem inv_mem_quadraticReturnSet
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ)
    {z : Fin N.torusDim → Circle}
    (hz : z ∈ quadraticReturnSet N Γ q) :
    z⁻¹ ∈ quadraticReturnSet N Γ q := by
  have hpowers : Set.range (z ^ · : ℕ → Fin N.torusDim → Circle) ⊆
      quadraticReturnSet N Γ q := by
    rintro _ ⟨n, rfl⟩
    induction n with
    | zero => simpa using one_mem_quadraticReturnSet N Γ q
    | succ n ih =>
        change z ^ (n + 1) ∈ quadraticReturnSet N Γ q
        rw [pow_succ]
        exact mul_mem_quadraticReturnSet N Γ q ih hz
  apply closure_minimal hpowers (isClosed_quadraticReturnSet N Γ q)
  rw [← closure_range_zpow_eq_pow]
  exact subset_closure ⟨(-1 : ℤ), by simp⟩

/-- The return parameters form a genuine closed subgroup of the quadratic
torus. -/
def quadraticReturnSubgroup
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ) :
    Subgroup (Fin N.torusDim → Circle) where
  carrier := quadraticReturnSet N Γ q
  one_mem' := one_mem_quadraticReturnSet N Γ q
  mul_mem' := mul_mem_quadraticReturnSet N Γ q
  inv_mem' := inv_mem_quadraticReturnSet N Γ q

theorem quadraticReturnSubgroup_isClosed
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ) :
    IsClosed (quadraticReturnSubgroup N Γ q :
      Set (Fin N.torusDim → Circle)) :=
  isClosed_quadraticReturnSet N Γ q

/-- Translating the base point inside its quadratic central fiber does not
change the vertical return subgroup. -/
theorem quadraticReturnSubgroup_quadratic_smul
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (w : Fin N.torusDim → Circle)
    (q : ReducedQuotient N Γ) :
    quadraticReturnSubgroup N Γ
        (quadraticReducedElement N w • q) =
      quadraticReturnSubgroup N Γ q := by
  apply Subgroup.ext
  intro z
  change
    quadraticReducedElement N z •
          (quadraticReducedElement N w • q) ∈
        closure (forwardOrbit (reducedStep N Γ)
          (quadraticReducedElement N w • q)) ↔
      quadraticReducedElement N z • q ∈
        closure (forwardOrbit (reducedStep N Γ) q)
  constructor
  · intro hz
    let f : ReducedQuotient N Γ → ReducedQuotient N Γ :=
      fun x ↦ quadraticReducedElement N w⁻¹ • x
    have hf : Continuous f := continuous_const_smul _
    have hmap : f (quadraticReducedElement N z •
          (quadraticReducedElement N w • q)) ∈
        closure (forwardOrbit (reducedStep N Γ) q) := by
      apply map_mem_closure hf hz
      rintro _ ⟨n, rfl⟩
      change quadraticReducedElement N w⁻¹ •
          ((reducedStep N Γ)^[n])
            (quadraticReducedElement N w • q) ∈ _
      rw [reducedStep_iterate_quadratic_smul]
      refine ⟨n, ?_⟩
      change ((reducedStep N Γ)^[n]) q =
          quadraticReducedHom N w⁻¹ •
            (quadraticReducedHom N w •
              ((reducedStep N Γ)^[n]) q)
      rw [← mul_smul, ← map_mul]
      have hone : quadraticReducedHom N 1 = 1 := map_one _
      rw [show w⁻¹ * w = 1 by simp, hone, one_smul]
    change quadraticReducedHom N w⁻¹ •
        (quadraticReducedHom N z •
          (quadraticReducedHom N w • q)) ∈ _ at hmap
    rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul] at hmap
    simpa [mul_comm] using hmap
  · intro hz
    let f : ReducedQuotient N Γ → ReducedQuotient N Γ :=
      fun x ↦ quadraticReducedElement N w • x
    have hf : Continuous f := continuous_const_smul _
    have hmap : f (quadraticReducedElement N z • q) ∈
        closure (forwardOrbit (reducedStep N Γ)
          (quadraticReducedElement N w • q)) := by
      apply map_mem_closure hf hz
      rintro _ ⟨n, rfl⟩
      change quadraticReducedElement N w •
          ((reducedStep N Γ)^[n]) q ∈ _
      rw [← reducedStep_iterate_quadratic_smul]
      exact ⟨n, rfl⟩
    change quadraticReducedHom N w •
        (quadraticReducedHom N z • q) ∈ _ at hmap
    change quadraticReducedHom N z •
        (quadraticReducedHom N w • q) ∈ _
    rw [← mul_smul, ← map_mul]
    rw [← mul_smul] at hmap
    rw [map_mul]
    have hcomm : quadraticReducedHom N w * quadraticReducedHom N z =
        quadraticReducedHom N z * quadraticReducedHom N w := by
      exact (Subgroup.mem_center_iff.mp
        (quadraticReducedElement_mem_center N w)
        (quadraticReducedElement N z)).symm
    rw [← hcomm]
    exact hmap

/-- Setwise stabilizer of the forward orbit closure inside the reduced
Hall--Petresco group. -/
def orbitClosureStabilizer
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ) :
    Subgroup (ReducedGroup N) :=
  MulAction.stabilizer (ReducedGroup N)
    (closure (forwardOrbit (reducedStep N Γ) q))

/-- The concrete quadratic return subgroup is exactly the pullback of the
setwise orbit-closure stabilizer along the quadratic torus homomorphism. -/
theorem mem_quadraticReturnSubgroup_iff_mem_orbitClosureStabilizer
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ)
    (z : Fin N.torusDim → Circle) :
    z ∈ quadraticReturnSubgroup N Γ q ↔
      quadraticReducedElement N z ∈ orbitClosureStabilizer N Γ q := by
  let Y : Set (ReducedQuotient N Γ) :=
    closure (forwardOrbit (reducedStep N Γ) q)
  change quadraticReducedElement N z • q ∈ Y ↔
    quadraticReducedElement N z • Y = Y
  constructor
  · intro hz
    apply Set.Subset.antisymm
    · change (quadraticReducedElement N z • ·) '' Y ⊆ Y
      exact quadratic_smul_orbitClosure_subset N Γ q z hz
    · intro r hr
      change r ∈ (quadraticReducedElement N z • ·) '' Y
      have hzinv : z⁻¹ ∈ quadraticReturnSubgroup N Γ q :=
        (quadraticReturnSubgroup N Γ q).inv_mem hz
      have hinv := quadratic_smul_orbitClosure_subset N Γ q z⁻¹ hzinv
      refine ⟨quadraticReducedElement N z⁻¹ • r, ?_, ?_⟩
      · exact hinv ⟨r, hr, rfl⟩
      · change quadraticReducedHom N z •
          (quadraticReducedHom N z⁻¹ • r) = r
        rw [← mul_smul, ← map_mul]
        have hone : quadraticReducedHom N 1 = 1 := map_one _
        rw [show z * z⁻¹ = 1 by simp, hone, one_smul]
  · intro hstab
    rw [← hstab]
    change quadraticReducedElement N z • q ∈
      (quadraticReducedElement N z • ·) '' Y
    exact ⟨q, subset_closure ⟨0, rfl⟩, rfl⟩

/-- It is enough to put the full reduced commutator subgroup into every
orbit-closure stabilizer.  The previously proved identification of that
commutator with the quadratic torus then gives all vertical returns. -/
theorem hasFullQuadraticFiberOrbitClosure_of_commutator_le_stabilizer
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H)
    (hcomm : ∀ q : ReducedQuotient N Γ,
      _root_.commutator (ReducedGroup N) ≤
        orbitClosureStabilizer N Γ q) :
    HasFullQuadraticFiberOrbitClosure N Γ := by
  intro q z
  apply (mem_quadraticReturnSubgroup_iff_mem_orbitClosureStabilizer
    N Γ q z).mpr
  apply hcomm q
  rw [commutator_reducedGroup_eq_quadratic_range N]
  exact ⟨z, rfl⟩

/-- Full vertical recurrence is exactly the assertion that every return
subgroup is the whole quadratic torus. -/
theorem hasFullQuadraticFiberOrbitClosure_iff_returnSubgroup_eq_top
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) :
    HasFullQuadraticFiberOrbitClosure N Γ ↔
      ∀ q : ReducedQuotient N Γ,
        quadraticReturnSubgroup N Γ q = ⊤ := by
  constructor
  · intro h q
    apply top_unique
    intro z _
    exact h q z
  · intro h q z
    have hz : z ∈ quadraticReturnSubgroup N Γ q := by
      rw [h q]
      exact Subgroup.mem_top z
    exact hz

/-- Under the vertical recurrence property, the whole central saturation
of an orbit is contained in the orbit closure. -/
theorem quadraticSaturation_forwardOrbit_subset_closure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H)
    (hvertical : HasFullQuadraticFiberOrbitClosure N Γ)
    (q : ReducedQuotient N Γ) :
    quadraticSaturation N Γ
        (forwardOrbit (reducedStep N Γ) q) ⊆
      closure (forwardOrbit (reducedStep N Γ) q) := by
  intro r hr
  simp only [quadraticSaturation, mem_iUnion] at hr
  rcases hr with ⟨z, p, ⟨n, rfl⟩, rfl⟩
  change quadraticReducedElement N z •
      ((reducedStep N Γ)^[n]) q ∈
    closure (forwardOrbit (reducedStep N Γ) q)
  rw [← reducedStep_iterate_quadratic_smul]
  apply map_mem_closure
    ((continuous_reducedStep N Γ).iterate n)
    (hvertical q z)
  rintro _ ⟨m, rfl⟩
  refine ⟨n + m, ?_⟩
  change ((reducedStep N Γ)^[n + m]) q =
    ((reducedStep N Γ)^[n]) (((reducedStep N Γ)^[m]) q)
  rw [Function.iterate_add_apply]

/-- BHK Lemma 7.1 is reduced to the vertical fiber recurrence property:
the already proved maximal-abelian-factor minimality and openness then force
every reduced progression orbit to be dense. -/
theorem everyOrbitHitsOpen_reducedStep_of_fullQuadraticFiber
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (hvertical : HasFullQuadraticFiberOrbitClosure N P.lattice) :
    EveryOrbitHitsOpen (reducedStep N P.lattice) := by
  intro q U hU hUne
  have hdenseSat := dense_quadraticSaturation_forwardOrbit N P q
  have hsatSub := quadraticSaturation_forwardOrbit_subset_closure
    N P.lattice hvertical q
  have horbitDense : Dense
      (forwardOrbit (reducedStep N P.lattice) q) := by
    rw [dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ closure
        (quadraticSaturation N P.lattice
          (forwardOrbit (reducedStep N P.lattice) q)) := by
      rw [hdenseSat.closure_eq]
      exact Set.mem_univ x
    exact closure_minimal hsatSub isClosed_closure hx
  obtain ⟨x, hxU, hxorb⟩ :=
    (dense_iff_inter_open.mp horbitDense) U hU hUne
  rcases hxorb with ⟨n, rfl⟩
  exact ⟨n, hxU⟩

end Chapter02.HallPetrescoCentralExtensionMinimality
