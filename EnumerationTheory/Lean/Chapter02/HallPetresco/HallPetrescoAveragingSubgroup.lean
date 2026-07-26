import Chapter02.HallPetresco.HallPetrescoNormalForm
import Chapter02.HallPetresco.HallPetrescoReducedQuotient

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoAveragingSubgroup

open Chapter02.HallPetrescoTwoStepGroup
open Chapter02.HallPetrescoNormalForm
open Chapter02.HallPetrescoReducedQuotient

universe u v

/-- The explicit element `diag(g) · lin(ι(z))` of BHK's averaging
subgroup `Ḡ`. -/
def averagingElement
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (p : H × (Fin N.torusDim → Circle)) :
    subgroup N :=
  ⟨diagonal p.1 * linear (N.centralHom p.2),
    (subgroup N).mul_mem
      (diagonal_mem_subgroup N p.1)
      (linear_mem_subgroup N (N.centralHom p.2))⟩

@[simp]
theorem averagingElement_apply
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (p : H × (Fin N.torusDim → Circle)) (j : Vertex) :
    ((averagingElement N p : subgroup N) : Vertex → H) j =
      p.1 * N.centralHom p.2 ^ j.val :=
  rfl

/-- The explicit averaging parameterization is a group homomorphism. -/
def averagingHom
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    (H × (Fin N.torusDim → Circle)) →* subgroup N where
  toFun := averagingElement N
  map_one' := by
    apply Subtype.ext
    funext j
    simp [averagingElement]
  map_mul' := by
    intro p q
    apply Subtype.ext
    funext j
    change
      (p.1 * q.1) * N.centralHom (p.2 * q.2) ^ j.val =
        p.1 * N.centralHom p.2 ^ j.val *
          (q.1 * N.centralHom q.2 ^ j.val)
    have hpcenter :
        N.centralHom p.2 ^ j.val ∈ Subgroup.center H :=
      (Subgroup.center H).pow_mem (N.centralHom_mem_center p.2) j.val
    have hcomm_h :
        N.centralHom p.2 ^ j.val * q.1 =
          q.1 * N.centralHom p.2 ^ j.val :=
      (Subgroup.mem_center_iff.mp hpcenter q.1).symm
    have hcomm_c :
        Commute (N.centralHom p.2) (N.centralHom q.2) :=
      (Subgroup.mem_center_iff.mp
        (N.centralHom_mem_center p.2) (N.centralHom q.2)).symm
    rw [map_mul, hcomm_c.mul_pow]
    calc
      (p.1 * q.1) *
          (N.centralHom p.2 ^ j.val * N.centralHom q.2 ^ j.val) =
        p.1 * (q.1 * N.centralHom p.2 ^ j.val) *
          N.centralHom q.2 ^ j.val := by group
      _ = p.1 * (N.centralHom p.2 ^ j.val * q.1) *
          N.centralHom q.2 ^ j.val := by rw [← hcomm_h]
      _ = p.1 * N.centralHom p.2 ^ j.val *
          (q.1 * N.centralHom q.2 ^ j.val) := by group

/-- The explicitly parameterized subgroup `diag(H) · lin(G₂)`. -/
def explicitAveragingSubgroup
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    Subgroup (subgroup N) :=
  (averagingHom N).range

theorem mem_explicitAveragingSubgroup_iff
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (s : subgroup N) :
    s ∈ explicitAveragingSubgroup N ↔
      ∃ g : H, ∃ z : Fin N.torusDim → Circle,
        s = averagingElement N (g, z) := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨g, z, rfl⟩
    exact ⟨(g, z), rfl⟩

theorem continuous_averagingElement
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    Continuous (averagingElement N) := by
  apply Continuous.subtype_mk
  rw [continuous_pi_iff]
  intro j
  exact (continuous_fst.mul
    ((N.continuous_centralHom.comp continuous_snd).pow j.val))

theorem averagingElement_eq_hallTuple
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (g : H) (z : Fin N.torusDim → Circle) :
    ((averagingElement N (g, z) : subgroup N) : Vertex → H) =
      hallTuple N ((g, N.centralHom z),
        (1 : Fin N.torusDim → Circle)) := by
  funext j
  simp [averagingElement, hallTuple]

@[simp]
theorem extractedLinear_averagingElement
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (g : H) (z : Fin N.torusDim → Circle) :
    extractedLinear
        (((averagingElement N (g, z) : subgroup N) : Vertex → H)) =
      N.centralHom z := by
  rw [averagingElement_eq_hallTuple,
    extractedLinear_hallTuple]

@[simp]
theorem extractedQuadratic_averagingElement
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (g : H) (z : Fin N.torusDim → Circle) :
    extractedQuadratic
        (((averagingElement N (g, z) : subgroup N) : Vertex → H)) =
      1 := by
  rw [averagingElement_eq_hallTuple,
    extractedQuadratic_hallTuple, map_one]

/-- Intrinsic closed coordinate characterization of `Ḡ`: its linear
coefficient lies in the full commutator torus and its quadratic coefficient
is trivial. -/
theorem mem_explicitAveragingSubgroup_iff_extract
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (s : subgroup N) :
    s ∈ explicitAveragingSubgroup N ↔
      extractedLinear ((s : subgroup N) : Vertex → H) ∈
          _root_.commutator H ∧
        extractedQuadratic ((s : subgroup N) : Vertex → H) = 1 := by
  constructor
  · intro hs
    rw [mem_explicitAveragingSubgroup_iff] at hs
    rcases hs with ⟨g, z, rfl⟩
    constructor
    · rw [extractedLinear_averagingElement, ← N.centralHom_range]
      exact ⟨z, rfl⟩
    · exact extractedQuadratic_averagingElement N g z
  · rintro ⟨hlin, hquad⟩
    have hsNormal :
        ((s : subgroup N) : Vertex → H) ∈ normalFormSubgroup N := by
      rw [← subgroup_eq_normalFormSubgroup N]
      exact s.property
    rcases hsNormal with ⟨p, hp⟩
    have hlinear :
        p.1.2 =
          extractedLinear ((s : subgroup N) : Vertex → H) := by
      rw [← hp, extractedLinear_hallTuple]
    have hpquad : N.centralHom p.2 = 1 := by
      rw [← extractedQuadratic_hallTuple N p, hp, hquad]
    have hpz :
        p.2 = (1 : Fin N.torusDim → Circle) := by
      apply N.injective_centralHom
      rw [hpquad, map_one]
    have hlinRange :
        p.1.2 ∈ N.centralHom.range := by
      rw [hlinear, N.centralHom_range]
      exact hlin
    rcases hlinRange with ⟨z, hz⟩
    rw [mem_explicitAveragingSubgroup_iff]
    refine ⟨p.1.1, z, ?_⟩
    apply Subtype.ext
    change ((s : subgroup N) : Vertex → H) =
      ((averagingElement N (p.1.1, z) : subgroup N) : Vertex → H)
    rw [← hp, averagingElement_eq_hallTuple]
    funext j
    simp only [hallTuple_apply]
    rw [hpz, hz, map_one, one_pow, mul_one]

theorem isClosed_explicitAveragingSubgroup
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    IsClosed (explicitAveragingSubgroup N : Set (subgroup N)) := by
  letI : T2Space H := N.t2Ambient
  have hlinear : Continuous (fun s : subgroup N ↦
      extractedLinear ((s : subgroup N) : Vertex → H)) :=
    continuous_extractedLinear.comp continuous_subtype_val
  have hquad : Continuous (fun s : subgroup N ↦
      extractedQuadratic ((s : subgroup N) : Vertex → H)) :=
    continuous_extractedQuadratic.comp continuous_subtype_val
  have heq :
      (explicitAveragingSubgroup N : Set (subgroup N)) =
        {s | extractedLinear ((s : subgroup N) : Vertex → H) ∈
              _root_.commutator H} ∩
          {s | extractedQuadratic ((s : subgroup N) : Vertex → H) = 1} := by
    ext s
    exact mem_explicitAveragingSubgroup_iff_extract N s
  rw [heq]
  exact (N.isClosed_commutator.preimage hlinear).inter
    (isClosed_singleton.preimage hquad)

private theorem conjugate_linear_coordinate
    {H : Type u} [Group H]
    (h a g q c u : H) (n : ℕ)
    (hq : q ∈ Subgroup.center H)
    (hc : c ∈ Subgroup.center H)
    (hu : u ∈ Subgroup.center H)
    (hag : a ^ n * g = u ^ n * g * a ^ n) :
    (h * a ^ n * q) * (g * c ^ n) * (h * a ^ n * q)⁻¹ =
      (h * g * h⁻¹) * (u * c) ^ n := by
  have hqg : q * g = g * q :=
    (Subgroup.mem_center_iff.mp hq g).symm
  have hqc : q * c ^ n = c ^ n * q :=
    (Subgroup.mem_center_iff.mp hq (c ^ n)).symm
  have hca : c ^ n * (a ^ n)⁻¹ = (a ^ n)⁻¹ * c ^ n :=
    (Subgroup.mem_center_iff.mp
      ((Subgroup.center H).pow_mem hc n) ((a ^ n)⁻¹)).symm
  have hug : u ^ n * g = g * u ^ n :=
    (Subgroup.mem_center_iff.mp
      ((Subgroup.center H).pow_mem hu n) g).symm
  have huh : u ^ n * h⁻¹ = h⁻¹ * u ^ n :=
    (Subgroup.mem_center_iff.mp
      ((Subgroup.center H).pow_mem hu n) h⁻¹).symm
  have hch : c ^ n * h⁻¹ = h⁻¹ * c ^ n :=
    (Subgroup.mem_center_iff.mp
      ((Subgroup.center H).pow_mem hc n) h⁻¹).symm
  have huc : Commute u c :=
    (Subgroup.mem_center_iff.mp hu c).symm
  calc
    (h * a ^ n * q) * (g * c ^ n) * (h * a ^ n * q)⁻¹ =
        h * a ^ n * q * g * c ^ n * q⁻¹ * (a ^ n)⁻¹ * h⁻¹ := by
          group
    _ = h * a ^ n * (q * g) * c ^ n * q⁻¹ * (a ^ n)⁻¹ * h⁻¹ := by
      group
    _ = h * a ^ n * (g * q) * c ^ n * q⁻¹ * (a ^ n)⁻¹ * h⁻¹ := by
      rw [hqg]
    _ = h * a ^ n * g * (q * c ^ n) * q⁻¹ * (a ^ n)⁻¹ * h⁻¹ := by
      group
    _ = h * a ^ n * g * (c ^ n * q) * q⁻¹ * (a ^ n)⁻¹ * h⁻¹ := by
      rw [hqc]
    _ = h * (a ^ n * g) * c ^ n * (a ^ n)⁻¹ * h⁻¹ := by
      group
    _ = h * (u ^ n * g * a ^ n) * c ^ n * (a ^ n)⁻¹ * h⁻¹ := by
      rw [hag]
    _ = h * u ^ n * g * a ^ n * (c ^ n * (a ^ n)⁻¹) * h⁻¹ := by
      group
    _ = h * u ^ n * g * a ^ n * ((a ^ n)⁻¹ * c ^ n) * h⁻¹ := by
      rw [hca]
    _ = h * u ^ n * g * c ^ n * h⁻¹ := by
      group
    _ = h * (u ^ n * g) * c ^ n * h⁻¹ := by
      group
    _ = h * (g * u ^ n) * c ^ n * h⁻¹ := by
      rw [hug]
    _ = h * g * u ^ n * (c ^ n * h⁻¹) := by
      group
    _ = h * g * u ^ n * (h⁻¹ * c ^ n) := by
      rw [hch]
    _ = h * g * (u ^ n * h⁻¹) * c ^ n := by
      group
    _ = h * g * (h⁻¹ * u ^ n) * c ^ n := by
      rw [huh]
    _ = (h * g * h⁻¹) * (u ^ n * c ^ n) := by
      group
    _ = (h * g * h⁻¹) * (u * c) ^ n := by
      rw [huc.mul_pow]

/-- Explicit normal-form coordinates for conjugating an averaging element
by an arbitrary Hall--Petresco element. -/
theorem exists_conjugate_averagingElement
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (s : subgroup N) (g : H) :
    ∃ h a : H, ∃ w t : Fin N.torusDim → Circle,
      ((s : subgroup N) : Vertex → H) =
          hallTuple N ((h, a), w) ∧
        N.centralHom t = ⁅a, g⁆ ∧
        ∀ z : Fin N.torusDim → Circle,
          s * averagingElement N (g, z) * s⁻¹ =
            averagingElement N (h * g * h⁻¹, t * z) := by
  have hsNormal :
      ((s : subgroup N) : Vertex → H) ∈ normalFormSubgroup N := by
    rw [← subgroup_eq_normalFormSubgroup N]
    exact s.property
  rcases hsNormal with ⟨⟨⟨h, a⟩, w⟩, hs⟩
  let u₀ : H := ⁅a, g⁆
  have hu₀_commutator : u₀ ∈ _root_.commutator H :=
    Subgroup.commutator_mem_commutator
      (Subgroup.mem_top a) (Subgroup.mem_top g)
  have hu₀_center : u₀ ∈ Subgroup.center H :=
    N.commutator_le_center hu₀_commutator
  have hu₀_range : u₀ ∈ N.centralHom.range := by
    rw [N.centralHom_range]
    exact hu₀_commutator
  rcases hu₀_range with ⟨t, ht⟩
  refine ⟨h, a, w, t, hs.symm, ht, ?_⟩
  intro z
  apply Subtype.ext
  funext j
  change
    (((s : subgroup N) : Vertex → H) j *
          (g * N.centralHom z ^ j.val)) *
        ((((s : subgroup N) : Vertex → H) j)⁻¹) =
      (h * g * h⁻¹) * N.centralHom (t * z) ^ j.val
  rw [← hs, hallTuple_apply, map_mul, ht]
  exact conjugate_linear_coordinate h a g
    (N.centralHom w ^ j.val.choose 2) (N.centralHom z) u₀ j.val
    ((Subgroup.center H).pow_mem (N.centralHom_mem_center w) _)
    (N.centralHom_mem_center z) hu₀_center
    (pow_mul_eq_commutatorElement_pow_mul a g hu₀_center j.val)

/-- The explicit averaging subgroup is invariant under conjugation by every
Hall--Petresco element. -/
theorem conjugate_averagingElement_mem
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (s : subgroup N) (g : H) (z : Fin N.torusDim → Circle) :
    s * averagingElement N (g, z) * s⁻¹ ∈
      explicitAveragingSubgroup N := by
  obtain ⟨h, a, w, t, hs, ht, hconj⟩ :=
    exists_conjugate_averagingElement N s g
  rw [hconj z, mem_explicitAveragingSubgroup_iff]
  exact ⟨h * g * h⁻¹, t * z, rfl⟩

instance explicitAveragingSubgroup_normal
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    (explicitAveragingSubgroup N).Normal := by
  constructor
  intro x hx s
  rw [mem_explicitAveragingSubgroup_iff] at hx
  rcases hx with ⟨g, z, rfl⟩
  exact conjugate_averagingElement_mem N s g z

/-- The coordinate subgroup `diag(H) · lin(G₂)` is exactly the closed normal
subgroup generated in the quotient construction. -/
theorem explicitAveragingSubgroup_eq_averagingNormalSubgroup
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    explicitAveragingSubgroup N = averagingNormalSubgroup N := by
  apply le_antisymm
  · intro s hs
    rw [mem_explicitAveragingSubgroup_iff] at hs
    rcases hs with ⟨g, z, rfl⟩
    exact (averagingNormalSubgroup N).mul_mem
      (diagonalElement_mem_averagingNormalSubgroup N g)
      (linearCentralElement_mem_averagingNormalSubgroup N z)
  · unfold averagingNormalSubgroup
    apply Subgroup.topologicalClosure_minimal
      (Subgroup.normalClosure (averagingGenerators N))
    · apply Subgroup.normalClosure_le_normal
      rintro s (⟨g, rfl⟩ | ⟨z, rfl⟩)
      · change diagonalElement N g ∈ (averagingHom N).range
        refine ⟨(g, 1), ?_⟩
        apply Subtype.ext
        funext j
        change g * N.centralHom 1 ^ j.val = g
        simp
      · change linearCentralElement N z ∈ (averagingHom N).range
        refine ⟨(1, z), ?_⟩
        apply Subtype.ext
        funext j
        change 1 * N.centralHom z ^ j.val =
          N.centralHom z ^ j.val
        simp
    · exact isClosed_explicitAveragingSubgroup N

/-- The kernel of the projection to the reduced Hall--Petresco group has
the intrinsic Hall-coordinate description used in BHK: the linear
coefficient is in `G₂` and the quadratic coefficient is trivial. -/
theorem reduced_mk_eq_one_iff_extract
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (s : subgroup N) :
    QuotientGroup.mk' (averagingNormalSubgroup N) s =
        (1 : ReducedGroup N) ↔
      extractedLinear ((s : subgroup N) : Vertex → H) ∈
          _root_.commutator H ∧
        extractedQuadratic ((s : subgroup N) : Vertex → H) = 1 := by
  constructor
  · intro hs
    have hs' : s ∈ averagingNormalSubgroup N :=
      (QuotientGroup.eq_one_iff _).mp hs
    rw [← explicitAveragingSubgroup_eq_averagingNormalSubgroup N] at hs'
    exact (mem_explicitAveragingSubgroup_iff_extract N s).mp hs'
  · intro hs
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [← explicitAveragingSubgroup_eq_averagingNormalSubgroup N]
    exact (mem_explicitAveragingSubgroup_iff_extract N s).mpr hs

/-- Two Hall--Petresco elements determine the same reduced-group point
exactly when their relative element has commutator-valued linear coefficient
and trivial quadratic coefficient. -/
theorem reduced_mk_eq_iff_extract
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (s t : subgroup N) :
    QuotientGroup.mk' (averagingNormalSubgroup N) s =
        QuotientGroup.mk' (averagingNormalSubgroup N) t ↔
      extractedLinear
          ((((s⁻¹ * t : subgroup N) : subgroup N)) : Vertex → H) ∈
          _root_.commutator H ∧
        extractedQuadratic
          ((((s⁻¹ * t : subgroup N) : subgroup N)) : Vertex → H) = 1 := by
  constructor
  · intro hst
    apply (reduced_mk_eq_one_iff_extract N (s⁻¹ * t)).mp
    rw [map_mul, map_inv, hst]
    simp
  · intro hst
    have hrel :=
      (reduced_mk_eq_one_iff_extract N (s⁻¹ * t)).mpr hst
    rw [map_mul, map_inv] at hrel
    exact inv_mul_eq_one.mp hrel

end Chapter02.HallPetrescoAveragingSubgroup
