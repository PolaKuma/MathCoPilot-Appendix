import Chapter02.HallPetresco.HallPetrescoAveragingSubgroup
import Chapter02.HallPetresco.HallPetrescoCompactQuotient
import Mathlib.Topology.Algebra.ProperAction.Basic

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoReducedHausdorff

open Chapter02.HallPetrescoTwoStepGroup
open Chapter02.HallPetrescoLattice
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoAveragingSubgroup

universe u v

/-- The compact parameterization of the `Ḡ`-orbit of the identity coset
inside the full Hall--Petresco quotient. -/
def averagingOrbitPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (p : X × (Fin N.torusDim → Circle)) :
    Quotient N P.lattice :=
  linearCentralElement N p.2 • quotientDiagonalPoint N P p.1

theorem continuous_averagingOrbitPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Continuous (averagingOrbitPoint N P) := by
  have hlinear :
      Continuous (fun p : X × (Fin N.torusDim → Circle) ↦
        linearCentralElement N p.2) := by
    apply Continuous.subtype_mk
    rw [continuous_pi_iff]
    intro j
    exact ((N.continuous_centralHom.comp continuous_snd).pow j.val)
  exact continuous_smul.comp
    (hlinear.prodMk
      ((continuous_quotientDiagonalPoint N P).comp continuous_fst))

/-- On a represented point of `X = H/Γ`, the compact orbit
parameterization is exactly the coset of the explicit averaging element. -/
theorem averagingOrbitPoint_representative
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (h : H) (z : Fin N.torusDim → Circle) :
    averagingOrbitPoint N P
        (P.toQuotient.symm
          (QuotientGroup.mk h : H ⧸ P.lattice), z) =
      (QuotientGroup.mk (averagingElement N (h, z)) :
        Quotient N P.lattice) := by
  unfold averagingOrbitPoint quotientDiagonalPoint
  rw [Function.comp_apply, Homeomorph.apply_symm_apply]
  unfold quotientDiagonalCoset
  change
    QuotientGroup.mk
        (linearCentralElement N z * diagonalElement N h) =
      QuotientGroup.mk (averagingElement N (h, z))
  congr 1
  apply Subtype.ext
  funext j
  change N.centralHom z ^ j.val * h =
    h * N.centralHom z ^ j.val
  exact (Subgroup.mem_center_iff.mp
    ((Subgroup.center H).pow_mem
      (N.centralHom_mem_center z) j.val) h).symm

/-- The range of the compact parameterization is precisely the image of
the explicit averaging subgroup in the full lattice quotient. -/
theorem range_averagingOrbitPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Set.range (averagingOrbitPoint N P) =
      QuotientGroup.mk '' (explicitAveragingSubgroup N :
        Set (subgroup N)) := by
  ext q
  constructor
  · rintro ⟨⟨x, z⟩, rfl⟩
    obtain ⟨h, hh⟩ := N.transitive_ambientAction
      (quotientBasePoint N P) x
    have hx :
        x = P.toQuotient.symm
          (QuotientGroup.mk h : H ⧸ P.lattice) := by
      apply P.toQuotient.injective
      rw [Homeomorph.apply_symm_apply, ← hh, P.equivariant]
      simp [quotientBasePoint]
    rw [hx, averagingOrbitPoint_representative]
    exact ⟨averagingElement N (h, z),
      (mem_explicitAveragingSubgroup_iff N _).mpr ⟨h, z, rfl⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    change s ∈ (averagingHom N).range at hs
    rcases hs with ⟨⟨h, z⟩, rfl⟩
    exact ⟨(P.toQuotient.symm
      (QuotientGroup.mk h : H ⧸ P.lattice), z),
      averagingOrbitPoint_representative N P h z⟩

/-- The pullback of the reduced lattice is exactly the pullback of the
compact `Ḡ`-orbit through the full quotient map. -/
theorem preimage_reducedLattice_eq_preimage_averagingOrbit
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    (QuotientGroup.mk' (averagingNormalSubgroup N)) ⁻¹'
        (reducedLattice N P.lattice : Set (ReducedGroup N)) =
      (QuotientGroup.mk : subgroup N → Quotient N P.lattice) ⁻¹'
        Set.range (averagingOrbitPoint N P) := by
  ext s
  constructor
  · intro hs
    change
      QuotientGroup.mk' (averagingNormalSubgroup N) s ∈
        (subgroupLattice N P.lattice).map
          (QuotientGroup.mk' (averagingNormalSubgroup N)) at hs
    rcases hs with ⟨l, hl, hls⟩
    let a : subgroup N := l⁻¹ * s
    have ha : a ∈ averagingNormalSubgroup N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change
        QuotientGroup.mk' (averagingNormalSubgroup N) (l⁻¹ * s) = 1
      rw [map_mul, map_inv, hls]
      simp
    let b : subgroup N := s * l⁻¹
    have hb : b ∈ averagingNormalSubgroup N := by
      have hconj :=
        Subgroup.Normal.conj_mem inferInstance a ha l
      change s * l⁻¹ ∈ averagingNormalSubgroup N
      simpa [a] using hconj
    rw [range_averagingOrbitPoint N P]
    refine ⟨b, ?_, ?_⟩
    · rw [explicitAveragingSubgroup_eq_averagingNormalSubgroup N]
      exact hb
    · apply QuotientGroup.eq.mpr
      change b⁻¹ * s ∈ subgroupLattice N P.lattice
      simpa [b] using hl
  · intro hs
    rw [range_averagingOrbitPoint N P] at hs
    rcases hs with ⟨b, hb, hbs⟩
    let l : subgroup N := b⁻¹ * s
    have hl : l ∈ subgroupLattice N P.lattice := by
      apply QuotientGroup.eq.mp hbs
    change
      QuotientGroup.mk' (averagingNormalSubgroup N) s ∈
        (subgroupLattice N P.lattice).map
          (QuotientGroup.mk' (averagingNormalSubgroup N))
    refine ⟨l, hl, ?_⟩
    change
      QuotientGroup.mk' (averagingNormalSubgroup N) (b⁻¹ * s) =
        QuotientGroup.mk' (averagingNormalSubgroup N) s
    rw [map_mul, map_inv]
    have hb' : b ∈ averagingNormalSubgroup N := by
      rw [← explicitAveragingSubgroup_eq_averagingNormalSubgroup N]
      exact hb
    have hbq :
        QuotientGroup.mk' (averagingNormalSubgroup N) b =
          (1 : ReducedGroup N) :=
      (QuotientGroup.eq_one_iff _).mpr hb'
    rw [hbq]
    simp

/-- The image lattice in the reduced Hall--Petresco group is genuinely
closed.  The proof uses the compact parameterization of its pullback fiber,
not an abstract closedness assumption. -/
theorem isClosed_reducedLattice
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    IsClosed (reducedLattice N P.lattice : Set (ReducedGroup N)) := by
  letI : T2Space (Quotient N P.lattice) :=
    quotientT2Space N P
  have horbitCompact :
      IsCompact (Set.range (averagingOrbitPoint N P)) := by
    simpa only [Set.image_univ] using
      isCompact_univ.image (continuous_averagingOrbitPoint N P)
  have horbitClosed :
      IsClosed (Set.range (averagingOrbitPoint N P)) :=
    horbitCompact.isClosed
  have hpullback :
      IsClosed
        ((QuotientGroup.mk' (averagingNormalSubgroup N)) ⁻¹'
          (reducedLattice N P.lattice : Set (ReducedGroup N))) := by
    rw [preimage_reducedLattice_eq_preimage_averagingOrbit N P]
    exact horbitClosed.preimage QuotientGroup.continuous_mk
  exact
    (QuotientGroup.isQuotientMap_mk
      (averagingNormalSubgroup N)).isClosed_preimage.mp hpullback

/-- Hence the actual reduced Hall--Petresco homogeneous space is Hausdorff. -/
noncomputable def reducedQuotientT2Space
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    T2Space (ReducedQuotient N P.lattice) := by
  letI : IsClosed
      (reducedLattice N P.lattice : Set (ReducedGroup N)) :=
    isClosed_reducedLattice N P
  infer_instance

end Chapter02.HallPetrescoReducedHausdorff
