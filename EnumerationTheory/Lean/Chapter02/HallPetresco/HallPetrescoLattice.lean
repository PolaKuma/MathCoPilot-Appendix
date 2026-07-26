import Chapter02.HallPetresco.HallPetrescoTwoStepGroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Topology.Algebra.Group.Quotient

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoLattice

open Chapter02.HallPetrescoTwoStepGroup

universe u v

/-- The pointwise four-coordinate copy of a lattice `Γ ≤ H`. -/
def coordinateLattice
    {H : Type u} [Group H] (Γ : Subgroup H) :
    Subgroup (Vertex → H) where
  carrier := {g | ∀ j, g j ∈ Γ}
  one_mem' := fun _ ↦ Γ.one_mem
  mul_mem' := by
    intro g h hg hh j
    exact Γ.mul_mem (hg j) (hh j)
  inv_mem' := by
    intro g hg j
    exact Γ.inv_mem (hg j)

@[simp]
theorem mem_coordinateLattice_iff
    {H : Type u} [Group H] (Γ : Subgroup H) (g : Vertex → H) :
    g ∈ coordinateLattice Γ ↔ ∀ j, g j ∈ Γ :=
  Iff.rfl

theorem isClosed_coordinateLattice
    {H : Type u} [Group H] [TopologicalSpace H]
    (Γ : Subgroup H) (hΓ : IsClosed (Γ : Set H)) :
    IsClosed (coordinateLattice Γ : Set (Vertex → H)) := by
  change IsClosed {g : Vertex → H | ∀ j, g j ∈ Γ}
  rw [show {g : Vertex → H | ∀ j, g j ∈ Γ} =
      ⋂ j, (fun g : Vertex → H ↦ g j) ⁻¹' (Γ : Set H) by
    ext g
    simp]
  exact isClosed_iInter fun j ↦ hΓ.preimage (continuous_apply j)

/-- The lattice inside the Hall--Petresco group is the pullback of the
pointwise lattice along the subgroup inclusion. -/
def subgroupLattice
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) :
    Subgroup (subgroup N) :=
  (coordinateLattice Γ).comap (subgroup N).subtype

@[simp]
theorem mem_subgroupLattice_iff
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (g : subgroup N) :
    g ∈ subgroupLattice N Γ ↔ ∀ j, (g : Vertex → H) j ∈ Γ :=
  Iff.rfl

/-- The pulled-back four-coordinate lattice is closed for every genuine
Hausdorff quotient presentation. -/
theorem isClosed_subgroupLattice
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    IsClosed (subgroupLattice N P.lattice : Set (subgroup N)) := by
  letI : T2Space (H ⧸ P.lattice) := P.t2Quotient
  have hΓ : IsClosed (P.lattice : Set H) :=
    QuotientGroup.t1Space_iff.mp inferInstance
  exact (isClosed_coordinateLattice P.lattice hΓ).preimage
    continuous_subtype_val

/-- The concrete Hall--Petresco homogeneous space associated to a lattice
quotient nilsystem. -/
abbrev Quotient
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) :=
  (subgroup N) ⧸ subgroupLattice N Γ

/-- The Hall--Petresco subgroup acts coordinatewise on four
configurations in the nilsystem. -/
def configurationAction
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    MulAction (subgroup N) (Vertex → X) where
  smul g y := fun j ↦
    N.ambientAction.toMulAction.smul ((g : Vertex → H) j) (y j)
  one_smul y := by
    funext j
    exact N.ambientAction.toMulAction.one_smul (y j)
  mul_smul g h y := by
    funext j
    exact N.ambientAction.toMulAction.mul_smul
      ((g : Vertex → H) j) ((h : Vertex → H) j) (y j)

/-- The point of `X` represented by the identity coset in a genuine
quotient presentation. -/
def quotientBasePoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) : X :=
  P.toQuotient.symm
    (QuotientGroup.mk (1 : H) : H ⧸ P.lattice)

/-- The diagonal identity-coset configuration. -/
def quotientBaseConfiguration
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Vertex → X :=
  fun _ ↦ quotientBasePoint N P

/-- For a genuine quotient presentation, the stabilizer of the diagonal
identity-coset configuration is exactly the pulled-back four-coordinate
lattice. -/
theorem stabilizer_quotientBaseConfiguration
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    letI := configurationAction N
    MulAction.stabilizer (subgroup N) (quotientBaseConfiguration N P) =
      subgroupLattice N P.lattice := by
  letI := configurationAction N
  ext g
  constructor
  · intro hg j
    have hgj :
        N.ambientAction.toMulAction.smul
            ((g : Vertex → H) j) (quotientBasePoint N P) =
          quotientBasePoint N P := by
      exact congr_fun hg j
    have hq := congr_arg P.toQuotient hgj
    rw [P.equivariant] at hq
    have hq' :
        ((g : Vertex → H) j) •
            (QuotientGroup.mk (1 : H) : H ⧸ P.lattice) =
          (QuotientGroup.mk (1 : H) : H ⧸ P.lattice) := by
      simpa [quotientBasePoint] using hq
    change QuotientGroup.mk (((g : Vertex → H) j) * 1) =
      QuotientGroup.mk (1 : H) at hq'
    have hm := QuotientGroup.eq.mp hq'
    simpa using P.lattice.inv_mem hm
  · intro hg
    change (fun j ↦
      N.ambientAction.toMulAction.smul
        ((g : Vertex → H) j) (quotientBasePoint N P)) =
      quotientBaseConfiguration N P
    funext j
    apply P.toQuotient.injective
    rw [P.equivariant]
    simp only [quotientBasePoint, quotientBaseConfiguration,
      Homeomorph.apply_symm_apply]
    change QuotientGroup.mk (((g : Vertex → H) j) * 1) =
      QuotientGroup.mk (1 : H)
    apply QuotientGroup.eq.mpr
    simpa using P.lattice.inv_mem (hg j)

/-- The concrete Hall--Petresco quotient is exactly the orbit of the
diagonal base configuration under the coordinatewise subgroup action. -/
noncomputable def quotientEquivConfigurationOrbit
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Quotient N P.lattice ≃
      letI := configurationAction N
      MulAction.orbit (subgroup N) (quotientBaseConfiguration N P) := by
  letI := configurationAction N
  change ((subgroup N) ⧸ subgroupLattice N P.lattice) ≃
    MulAction.orbit (subgroup N) (quotientBaseConfiguration N P)
  rw [← stabilizer_quotientBaseConfiguration N P]
  exact
    (MulAction.orbitEquivQuotientStabilizer
      (subgroup N) (quotientBaseConfiguration N P)).symm

/-- The canonical configuration represented by a point of the actual
Hall--Petresco quotient. -/
def quotientConfiguration
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : Quotient N P.lattice) : Vertex → X := by
  letI := configurationAction N
  exact Quotient.liftOn' q
    (fun g : subgroup N ↦ g • quotientBaseConfiguration N P)
    (by
      intro g h hgh
      have hs :
          g⁻¹ * h ∈
            MulAction.stabilizer
              (subgroup N) (quotientBaseConfiguration N P) := by
        rw [stabilizer_quotientBaseConfiguration N P]
        exact QuotientGroup.leftRel_apply.mp hgh
      calc
        g • quotientBaseConfiguration N P =
            g • ((g⁻¹ * h) • quotientBaseConfiguration N P) := by
          rw [hs]
        _ = h • quotientBaseConfiguration N P := by
          rw [smul_smul, mul_inv_cancel_left])

@[simp]
theorem quotientConfiguration_mk
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (g : subgroup N) :
    quotientConfiguration N P
      (QuotientGroup.mk g : Quotient N P.lattice) =
      letI := configurationAction N
      g • quotientBaseConfiguration N P :=
  rfl

/-- The quotient configuration map intertwines the full Hall--Petresco
subgroup action with the coordinatewise action on configurations. -/
theorem quotientConfiguration_smul
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (g : subgroup N) (q : Quotient N P.lattice) :
    quotientConfiguration N P (g • q) =
      letI := configurationAction N
      g • quotientConfiguration N P q := by
  letI := configurationAction N
  refine Quotient.inductionOn' q ?_
  intro h
  simp only [quotientConfiguration_mk]
  exact (smul_smul g h (quotientBaseConfiguration N P)).symm

theorem continuous_quotientConfiguration
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Continuous (quotientConfiguration N P) := by
  apply Continuous.quotient_lift
  rw [continuous_pi_iff]
  intro j
  change Continuous (fun g : subgroup N ↦
    N.ambientAction.toMulAction.smul
      ((g : Vertex → H) j) (quotientBasePoint N P))
  exact N.ambientAction.continuous_smul.comp
    (((continuous_apply j).comp continuous_subtype_val).prodMk
      (continuous_const :
        Continuous (fun _ : subgroup N ↦ quotientBasePoint N P)))

/-- The actual Hall--Petresco quotient embeds faithfully into the four-point
configuration space.  Algebraically this is the orbit--stabilizer
identification above, expressed directly for the canonical map. -/
theorem injective_quotientConfiguration
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Function.Injective (quotientConfiguration N P) := by
  letI := configurationAction N
  intro q r
  refine Quotient.inductionOn' q ?_
  intro g
  refine Quotient.inductionOn' r ?_
  intro h heq
  apply QuotientGroup.eq.mpr
  rw [← stabilizer_quotientBaseConfiguration N P]
  change
    (g⁻¹ * h) • quotientBaseConfiguration N P =
      quotientBaseConfiguration N P
  change
    g • quotientBaseConfiguration N P =
      h • quotientBaseConfiguration N P at heq
  calc
    (g⁻¹ * h) • quotientBaseConfiguration N P =
        g⁻¹ • (h • quotientBaseConfiguration N P) := by
      rw [mul_smul]
    _ = g⁻¹ • (g • quotientBaseConfiguration N P) := by
      rw [heq]
    _ = quotientBaseConfiguration N P :=
      inv_smul_smul g (quotientBaseConfiguration N P)

/-- The faithful configuration map supplies the Hausdorff structure of the
actual Hall--Petresco quotient. -/
noncomputable def quotientT2Space
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    T2Space (Quotient N P.lattice) :=
  T2Space.of_injective_continuous
    (injective_quotientConfiguration N P)
    (continuous_quotientConfiguration N P)

/-- If the actual Hall--Petresco quotient is compact, its faithful embedding
into the finite metric configuration space also supplies a compatible
pseudometric topology. -/
noncomputable def quotientPseudoMetrizableSpace
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [CompactSpace (Quotient N P.lattice)] :
    TopologicalSpace.PseudoMetrizableSpace (Quotient N P.lattice) :=
  ((continuous_quotientConfiguration N P).isClosedEmbedding
      (injective_quotientConfiguration N P)).isInducing.pseudoMetrizableSpace

/-- The element of the Hall--Petresco subgroup generating one
arithmetic-progression time step. -/
def progressionGenerator
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    subgroup N :=
  ⟨linear N.translation, linear_mem_subgroup N N.translation⟩

theorem progressionGenerator_pow_coe
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) (n : ℕ) :
    (((progressionGenerator N) ^ n : subgroup N) : Vertex → H) =
      arithmeticProgression N.translation n := by
  rw [arithmeticProgression_eq_linear_pow]
  rfl

/-- Left translation by the progression generator on the actual
Hall--Petresco quotient. -/
def quotientStep
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) :
    Quotient N Γ → Quotient N Γ :=
  fun q ↦ progressionGenerator N • q

theorem continuous_quotientStep
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) :
    Continuous (quotientStep N Γ) :=
  (Homeomorph.smul (progressionGenerator N)).continuous

theorem quotientStep_iterate
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (n : ℕ) (q : Quotient N Γ) :
    ((quotientStep N Γ)^[n]) q =
      (progressionGenerator N) ^ n • q := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [quotientStep, smul_smul]
      rw [pow_succ']

/-- The identity coset in the actual Hall--Petresco quotient. -/
def quotientIdentityCoset
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) :
    Quotient N Γ :=
  QuotientGroup.mk (1 : subgroup N)

/-- The zeroth coordinate of a Hall--Petresco quotient configuration.

This is the base-point parameter carried by the diagonal generators. -/
def quotientZerothCoordinate
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Quotient N P.lattice → X :=
  fun q ↦ quotientConfiguration N P q 0

theorem continuous_quotientZerothCoordinate
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Continuous (quotientZerothCoordinate N P) :=
  (continuous_apply (0 : Vertex)).comp
    (continuous_quotientConfiguration N P)

/-- Every point of the original nilsystem occurs as the zeroth coordinate
of a point of the full Hall--Petresco quotient. -/
theorem surjective_quotientZerothCoordinate
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Function.Surjective (quotientZerothCoordinate N P) := by
  intro x
  obtain ⟨h, hh⟩ :=
    N.transitive_ambientAction (quotientBasePoint N P) x
  let g : subgroup N :=
    ⟨diagonal h, diagonal_mem_subgroup N h⟩
  refine ⟨(QuotientGroup.mk g : Quotient N P.lattice), ?_⟩
  change
    N.ambientAction.toMulAction.smul h (quotientBasePoint N P) = x
  exact hh

/-- The progression translation fixes the zeroth coordinate. -/
theorem quotientZerothCoordinate_quotientStep
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : Quotient N P.lattice) :
    quotientZerothCoordinate N P (quotientStep N P.lattice q) =
      quotientZerothCoordinate N P q := by
  letI := configurationAction N
  have h :=
    congr_fun
      (quotientConfiguration_smul N P (progressionGenerator N) q)
      (0 : Vertex)
  calc
    quotientZerothCoordinate N P (quotientStep N P.lattice q) =
        (progressionGenerator N • quotientConfiguration N P q) 0 := by
      simpa [quotientZerothCoordinate, quotientStep] using h
    _ = quotientZerothCoordinate N P q := by
      change
        N.ambientAction.toMulAction.smul
            ((((progressionGenerator N : subgroup N) : Vertex → H) 0))
            (quotientConfiguration N P q 0) =
          quotientConfiguration N P q 0
      change
        N.ambientAction.toMulAction.smul
            (N.translation ^ (0 : Vertex).val)
            (quotientConfiguration N P q 0) =
          quotientConfiguration N P q 0
      have hzero : (0 : Vertex).val = 0 := by
        decide
      rw [hzero, pow_zero]
      exact
        N.ambientAction.toMulAction.one_smul
          (quotientConfiguration N P q 0)

theorem quotientZerothCoordinate_quotientStep_iterate
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (n : ℕ) (q : Quotient N P.lattice) :
    quotientZerothCoordinate N P
        (((quotientStep N P.lattice)^[n]) q) =
      quotientZerothCoordinate N P q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',
        quotientZerothCoordinate_quotientStep, ih]

/-- The full Hall--Petresco quotient cannot be minimal under the progression
translation unless the original nilsystem is a singleton.  Thus the genuine
minimal Hall--Petresco carrier must be a fixed-zeroth-coordinate fibre (or
the corresponding orbit closure), not the quotient containing all diagonal
base-point parameters. -/
theorem subsingleton_of_everyOrbitHitsOpen_quotientStep
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [T1Space X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (hminimal :
      Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen
        (quotientStep N P.lattice)) :
    Subsingleton X := by
  constructor
  intro x y
  by_contra hxy
  obtain ⟨qx, hqx⟩ :=
    surjective_quotientZerothCoordinate N P x
  obtain ⟨qy, hqy⟩ :=
    surjective_quotientZerothCoordinate N P y
  let U : Set (Quotient N P.lattice) :=
    quotientZerothCoordinate N P ⁻¹' ({x}ᶜ : Set X)
  have hUopen : IsOpen U :=
    isClosed_singleton.isOpen_compl.preimage
      (continuous_quotientZerothCoordinate N P)
  have hUne : U.Nonempty := by
    refine ⟨qy, ?_⟩
    change quotientZerothCoordinate N P qy ≠ x
    rw [hqy]
    exact fun hyx ↦ hxy hyx.symm
  obtain ⟨n, hn⟩ := hminimal qx U hUopen hUne
  have hn' :
      quotientZerothCoordinate N P
          (((quotientStep N P.lattice)^[n]) qx) ≠ x :=
    hn
  apply hn'
  rw [quotientZerothCoordinate_quotientStep_iterate, hqx]

/-- Diagonal embedding of the original homogeneous quotient into the
actual Hall--Petresco quotient.  It is defined on cosets, so it does not
choose representatives of points of the nilmanifold. -/
def quotientDiagonalCoset
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    (H ⧸ P.lattice) → Quotient N P.lattice := by
  intro q
  exact Quotient.liftOn' q
    (fun h ↦ QuotientGroup.mk
      (⟨diagonal h, diagonal_mem_subgroup N h⟩ : subgroup N))
    (by
      intro h k hhk
      apply QuotientGroup.eq.mpr
      intro j
      exact QuotientGroup.leftRel_apply.mp hhk)

theorem continuous_quotientDiagonalCoset
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Continuous (quotientDiagonalCoset N P) := by
  unfold quotientDiagonalCoset
  apply Continuous.quotient_lift
  exact isQuotientMap_quotient_mk'.continuous.comp
    ((by
      rw [continuous_pi_iff]
      intro _
      exact continuous_id : Continuous (diagonal : H → Vertex → H)).subtype_mk _)

@[simp]
theorem quotientConfiguration_quotientDiagonalCoset
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : H ⧸ P.lattice) :
    quotientConfiguration N P (quotientDiagonalCoset N P q) =
      fun _ ↦ P.toQuotient.symm q := by
  refine Quotient.inductionOn' q ?_
  intro h
  funext j
  change
    N.ambientAction.toMulAction.smul h (quotientBasePoint N P) =
      P.toQuotient.symm (QuotientGroup.mk h)
  apply P.toQuotient.injective
  rw [P.equivariant]
  simp only [quotientBasePoint, Homeomorph.apply_symm_apply]
  change QuotientGroup.mk (h * 1) = QuotientGroup.mk h
  rw [mul_one]

/-- The diagonal embedding written directly on the original nilsystem. -/
def quotientDiagonalPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    X → Quotient N P.lattice :=
  quotientDiagonalCoset N P ∘ P.toQuotient

theorem continuous_quotientDiagonalPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Continuous (quotientDiagonalPoint N P) :=
  (continuous_quotientDiagonalCoset N P).comp P.toQuotient.continuous

@[simp]
theorem quotientConfiguration_quotientDiagonalPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (x : X) :
    quotientConfiguration N P (quotientDiagonalPoint N P x) =
      fun _ ↦ x := by
  simp [quotientDiagonalPoint]

end Chapter02.HallPetrescoLattice
