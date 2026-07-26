import Chapter02.Spectral.PontryaginSeparation
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Metrizable.Urysohn

noncomputable section

open Classical MeasureTheory

namespace Chapter02.CompactAbelianSubgroupAnnihilator

universe u

/-- A point outside a closed subgroup of a compact metrizable abelian group
is separated from that subgroup by a continuous circle character.

The proof applies Pontryagin separation to the compact Hausdorff quotient and
pulls the resulting character back along the quotient map. -/
theorem exists_character_trivial_on_closedSubgroup
    {G : Type u} [CommGroup G] [MetricSpace G] [CompactSpace G]
    [IsTopologicalGroup G]
    (K : Subgroup G) (hK : IsClosed (K : Set G))
    {g : G} (hg : g ∉ K) :
    ∃ χ : Chapter02.ContinuousMultiplicativeCircleCharacter G,
      (∀ k ∈ K, χ.toFun k = 1) ∧ χ.toFun g ≠ 1 := by
  let Q := G ⧸ K
  letI : TopologicalSpace.MetrizableSpace Q := inferInstance
  letI : MetricSpace Q := TopologicalSpace.metrizableSpaceMetric Q
  letI : MeasurableSpace Q := borel Q
  letI : BorelSpace Q := ⟨rfl⟩
  let K₀ : TopologicalSpace.PositiveCompacts Q := ⊤
  let m : Measure Q := Measure.haarMeasure K₀
  letI : IsProbabilityMeasure m := by
    apply IsProbabilityMeasure.mk
    simpa [m, K₀] using (Measure.haarMeasure_self (K₀ := K₀))
  have hq : (QuotientGroup.mk g : Q) ≠ 1 := by
    intro heq
    exact hg ((QuotientGroup.eq_one_iff _).mp heq)
  obtain ⟨ψ, hψ⟩ :=
    PontryaginSeparation.exists_character_ne_one m hq
  let χ : Chapter02.ContinuousMultiplicativeCircleCharacter G :=
    { toFun := fun x => ψ.toFun (QuotientGroup.mk x)
      map_one := by simpa using ψ.map_one
      map_mul := by
        intro x y
        simpa using ψ.map_mul (QuotientGroup.mk x) (QuotientGroup.mk y)
      continuous := ψ.continuous.comp QuotientGroup.continuous_mk
      unit_norm := fun x => ψ.unit_norm (QuotientGroup.mk x) }
  refine ⟨χ, ?_, ?_⟩
  · intro k hk
    change ψ.toFun (QuotientGroup.mk k : Q) = 1
    rw [(QuotientGroup.eq_one_iff _).mpr hk]
    exact ψ.map_one
  · exact hψ

end Chapter02.CompactAbelianSubgroupAnnihilator
