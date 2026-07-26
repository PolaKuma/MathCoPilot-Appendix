import Chapter02.HallPetresco.HallPetrescoLattice
import Chapter02.HallPetresco.HallPetrescoNormalForm

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoCompactQuotient

open Chapter02.HallPetrescoTwoStepGroup
open Chapter02.HallPetrescoLattice
open Chapter02.HallPetrescoNormalForm

universe u v

/-- Every ambient element can be written as a point in the chosen compact
fundamental set times a lattice element. -/
theorem exists_compact_mul_lattice
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    {K : Set H}
    (hcover :
      (QuotientGroup.mk '' K : Set (H ⧸ P.lattice)) = Set.univ)
    (g : H) :
    ∃ k ∈ K, ∃ γ ∈ P.lattice, g = k * γ := by
  have hg :
      (QuotientGroup.mk g : H ⧸ P.lattice) ∈
        (QuotientGroup.mk '' K : Set (H ⧸ P.lattice)) := by
    rw [hcover]
    exact Set.mem_univ _
  rcases hg with ⟨k, hk, hkg⟩
  let γ := k⁻¹ * g
  have hγ : γ ∈ P.lattice := QuotientGroup.eq.mp hkg
  refine ⟨k, hk, γ, hγ, ?_⟩
  dsimp [γ]
  group

/-- A Hall normal-form parameter viewed as an element of the closed
Hall--Petresco subgroup. -/
def subgroupPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (p : Parameters N) :
    subgroup N :=
  ⟨hallTuple N p, hallTuple_mem_subgroup N p⟩

theorem continuous_subgroupPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    Continuous (subgroupPoint N) :=
  (continuous_hallTuple N).subtype_mk _

/-- The quotient point represented by a Hall normal-form parameter. -/
def quotientPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (p : Parameters N) :
    Quotient N P.lattice :=
  QuotientGroup.mk (subgroupPoint N p)

theorem continuous_quotientPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Continuous (quotientPoint N P) :=
  (QuotientGroup.continuous_mk (N := subgroupLattice N P.lattice)).comp
    (continuous_subgroupPoint N)

/-- Parameters whose constant and linear coefficients lie in a fixed
compact fundamental set. -/
def compactParameterSet
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (K : Set H) : Set (Parameters N) :=
  {p | p.1.1 ∈ K ∧ p.1.2 ∈ K}

theorem isCompact_compactParameterSet
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    {K : Set H} (hK : IsCompact K) :
    IsCompact (compactParameterSet N K) := by
  rw [show compactParameterSet N K =
      (K ×ˢ K) ×ˢ (Set.univ : Set (Fin N.torusDim → Circle)) by
    ext p
    simp [compactParameterSet]]
  exact (hK.prod hK).prod isCompact_univ

/-- Every Hall--Petresco quotient point has a representative whose constant
and linear Hall coefficients lie in the chosen compact fundamental set. -/
theorem exists_compactParameter_representative
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    {K : Set H}
    (hcover :
      (QuotientGroup.mk '' K : Set (H ⧸ P.lattice)) = Set.univ)
    (q : Quotient N P.lattice) :
    ∃ p ∈ compactParameterSet N K, quotientPoint N P p = q := by
  refine Quotient.inductionOn' q ?_
  intro s
  have hs_normal :
      (s : Vertex → H) ∈ normalFormSubgroup N := by
    rw [← subgroup_eq_normalFormSubgroup N]
    exact s.property
  rcases hs_normal with ⟨p, hp⟩
  have hps : subgroupPoint N p = s := by
    ext j
    exact congr_fun hp j
  rcases exists_compact_mul_lattice N P hcover p.1.1 with
    ⟨k, hk, γ, hγ, hg⟩
  let diagonalParameter : Parameters N :=
    ((γ⁻¹, 1), (1 : Fin N.torusDim → Circle))
  have hdiagonal :
      hallTuple N diagonalParameter = diagonal γ⁻¹ := by
    exact (diagonal_eq_hallTuple N γ⁻¹).symm
  have hdiagonal_lattice :
      subgroupPoint N diagonalParameter ∈
        subgroupLattice N P.lattice := by
    intro j
    change hallTuple N diagonalParameter j ∈ P.lattice
    rw [hdiagonal]
    exact P.lattice.inv_mem hγ
  rcases exists_hallTuple_mul N p diagonalParameter with ⟨r, hr⟩
  have hr_subgroup :
      subgroupPoint N p * subgroupPoint N diagonalParameter =
        subgroupPoint N r := by
    ext j
    exact congr_fun hr j
  have hr_base : r.1.1 = k := by
    have h0 := congr_fun hr (0 : Vertex)
    simp only [Pi.mul_apply, hallTuple_apply] at h0
    dsimp [diagonalParameter] at h0
    simp only [pow_zero, mul_one] at h0
    rw [hg] at h0
    simpa [mul_assoc] using h0.symm
  rcases exists_compact_mul_lattice N P hcover r.1.2 with
    ⟨l, hl, δ, hδ, ha⟩
  let linearParameter : Parameters N :=
    ((1, δ⁻¹), (1 : Fin N.torusDim → Circle))
  have hlinear :
      hallTuple N linearParameter = linear δ⁻¹ := by
    exact (linear_eq_hallTuple N δ⁻¹).symm
  have hlinear_lattice :
      subgroupPoint N linearParameter ∈
        subgroupLattice N P.lattice := by
    intro j
    change hallTuple N linearParameter j ∈ P.lattice
    rw [hlinear]
    exact P.lattice.pow_mem (P.lattice.inv_mem hδ) j.val
  rcases exists_hallTuple_mul N r linearParameter with ⟨t, ht⟩
  have ht_subgroup :
      subgroupPoint N r * subgroupPoint N linearParameter =
        subgroupPoint N t := by
    ext j
    exact congr_fun ht j
  have ht_base : t.1.1 = r.1.1 := by
    have h0 := congr_fun ht (0 : Vertex)
    simp only [Pi.mul_apply, hallTuple_apply] at h0
    dsimp [linearParameter] at h0
    simp only [pow_zero, mul_one] at h0
    simpa using h0.symm
  have ht_linear : t.1.2 = l := by
    have h1 := congr_fun ht (1 : Vertex)
    simp only [Pi.mul_apply, hallTuple_apply] at h1
    dsimp [linearParameter] at h1
    rw [show Nat.choose 1 2 = 0 by decide] at h1
    simp only [pow_one, pow_zero, mul_one, one_mul] at h1
    calc
      t.1.2 = t.1.1⁻¹ * (t.1.1 * t.1.2) := by group
      _ = t.1.1⁻¹ * ((r.1.1 * r.1.2) * δ⁻¹) := by rw [← h1]
      _ = r.1.1⁻¹ * ((r.1.1 * (l * δ)) * δ⁻¹) := by
        rw [ht_base, ha]
      _ = l := by group
  refine ⟨t, ?_, ?_⟩
  · constructor
    · rw [ht_base, hr_base]
      exact hk
    · rw [ht_linear]
      exact hl
  · calc
      quotientPoint N P t =
          (QuotientGroup.mk (subgroupPoint N t) :
            Quotient N P.lattice) := rfl
      _ = QuotientGroup.mk
          (subgroupPoint N r * subgroupPoint N linearParameter) := by
        rw [ht_subgroup]
      _ = QuotientGroup.mk (subgroupPoint N r) :=
        QuotientGroup.mk_mul_of_mem _ hlinear_lattice
      _ = QuotientGroup.mk
          (subgroupPoint N p * subgroupPoint N diagonalParameter) := by
        rw [hr_subgroup]
      _ = QuotientGroup.mk (subgroupPoint N p) :=
        QuotientGroup.mk_mul_of_mem _ hdiagonal_lattice
      _ = QuotientGroup.mk s := by rw [hps]

/-- The genuine Hall--Petresco lattice quotient is compact. -/
noncomputable def quotientCompactSpace
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    CompactSpace (Quotient N P.lattice) := by
  rcases P.compactFundamentalDomain with ⟨K, hK, hcover⟩
  have himage :
      quotientPoint N P '' compactParameterSet N K =
        (Set.univ : Set (Quotient N P.lattice)) := by
    ext q
    constructor
    · intro
      exact Set.mem_univ q
    · intro
      rcases exists_compactParameter_representative N P hcover q with
        ⟨p, hp, hq⟩
      exact ⟨p, hp, hq⟩
  apply isCompact_univ_iff.mp
  rw [← himage]
  exact (isCompact_compactParameterSet N hK).image
    (continuous_quotientPoint N P)

end Chapter02.HallPetrescoCompactQuotient
