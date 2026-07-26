import Chapter02.Dynamics.DenseRangeConvergentNet
import Chapter02.HallPetresco.HallPetrescoAbelianLatticeDiscrete
import Chapter02.HallPetresco.HallPetrescoReducedRecurrence
import Chapter02.HallPetresco.LocalHomeomorphLatticeLift

open Classical Filter Set Topology

noncomputable section

namespace Chapter02.HallPetrescoStabilizerAbelianLift

open Chapter02.DenseRangeConvergentNet
open Chapter02.HallPetrescoAbelianLatticeDiscrete
open Chapter02.HallPetrescoCentralExtensionMinimality
open Chapter02.HallPetrescoParryPropertyH
open Chapter02.HallPetrescoReducedAbelianFactor
open Chapter02.HallPetrescoReducedRecurrence
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.LocalHomeomorphLatticeLift

universe u v

/-- Every element of the abelianized reduced group is the limit of actual
orbit-closure stabilizer elements after correction by the genuine abelian
lattice.

The net is nontrivial.  It is selected from the dense stabilizer image in
the common compact abelian quotient and then lifted through the actual
locally homeomorphic quotient map. -/
theorem exists_stabilizer_net_abelian_corrected
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : ReducedQuotient N P.lattice)
    (h : AbelianFactor H) :
    ∃ (ι : Type u) (l : Filter ι),
      l.NeBot ∧
        ∃ k : ι → orbitClosureStabilizer N P.lattice q,
        ∃ γ : ι → abelianLattice P.lattice,
          Tendsto
            (fun i ↦
              reducedLinearAbelianHom N (k i).1 *
                (γ i : AbelianFactor H)⁻¹)
            l (𝓝 h) := by
  let f :
      orbitClosureStabilizer N P.lattice q →
        AbelianQuotient P.lattice :=
    stabilizerToAbelianQuotient N P.lattice q
  obtain ⟨l, hlne, k, hk⟩ :=
    exists_net_tendsto_of_denseRange f
      (denseRange_stabilizerToAbelianQuotient N P q)
      (QuotientGroup.mk h : AbelianQuotient P.lattice)
  let r : Set.range f → AbelianFactor H :=
    fun i ↦ h⁻¹ * reducedLinearAbelianHom N (k i).1
  have hr :
      Tendsto
        (fun i ↦
          (QuotientGroup.mk (r i) :
            AbelianQuotient P.lattice))
        l
        (𝓝
          (QuotientGroup.mk (1 : AbelianFactor H) :
            AbelianQuotient P.lattice)) := by
    have hconst :
        Tendsto
          (fun _ : Set.range f ↦
            (QuotientGroup.mk h :
              AbelianQuotient P.lattice)⁻¹)
          l
          (𝓝
            ((QuotientGroup.mk h :
              AbelianQuotient P.lattice)⁻¹)) :=
      tendsto_const_nhds
    have ht := hconst.mul hk
    change
      Tendsto
        (fun i ↦
          (QuotientGroup.mk h :
              AbelianQuotient P.lattice)⁻¹ *
            f (k i))
        l
        (𝓝
          ((QuotientGroup.mk h :
              AbelianQuotient P.lattice)⁻¹ *
            QuotientGroup.mk h)) at ht
    simpa [r, f, stabilizerToAbelianQuotient,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] using ht
  obtain ⟨γ, hγ⟩ :=
    exists_lattice_correction_tendsto_one
      (abelianLattice P.lattice)
      (abelianQuotient_isLocalHomeomorph N P)
      r hr
  refine ⟨Set.range f, l, hlne, k, γ, ?_⟩
  have hconst :
      Tendsto (fun _ : Set.range f ↦ h) l (𝓝 h) :=
    tendsto_const_nhds
  have ht := hconst.mul hγ
  convert ht using 1
  · funext i
    dsimp only [r]
    group
  · simp

/-- The lattice correction can be chosen in the original lattice itself,
not merely in its image in the abelianization.  This is the form needed
on the genuine reduced Hall--Petresco quotient, because such corrections
come from actual lattice elements. -/
theorem exists_stabilizer_net_originalLattice_corrected
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : ReducedQuotient N P.lattice)
    (h : AbelianFactor H) :
    ∃ (ι : Type u) (l : Filter ι),
      l.NeBot ∧
        ∃ k : ι → orbitClosureStabilizer N P.lattice q,
        ∃ δ : ι → P.lattice,
          Tendsto
            (fun i ↦
              reducedLinearAbelianHom N (k i).1 *
                (reducedLinearAbelianHom N
                  (linearReducedElement N (δ i : H)))⁻¹)
            l (𝓝 h) := by
  obtain ⟨ι, l, hl, k, γ, hγ⟩ :=
    exists_stabilizer_net_abelian_corrected N P q h
  choose δ hδ hmap using fun i ↦ (γ i).property
  let δ' : ι → P.lattice := fun i ↦ ⟨δ i, hδ i⟩
  refine ⟨ι, l, hl, k, δ', ?_⟩
  convert hγ using 1
  funext i
  change
    reducedLinearAbelianHom N (k i).1 *
        (reducedLinearAbelianHom N
          (linearReducedElement N (δ i)))⁻¹ =
      reducedLinearAbelianHom N (k i).1 * ((γ i : AbelianFactor H))⁻¹
  have hm :
      reducedLinearAbelianHom N (linearReducedElement N (δ i)) =
        (γ i : AbelianFactor H) := by
    rw [reducedLinearAbelianHom_linearReducedElement]
    exact hmap i
  rw [hm]

end Chapter02.HallPetrescoStabilizerAbelianLift
