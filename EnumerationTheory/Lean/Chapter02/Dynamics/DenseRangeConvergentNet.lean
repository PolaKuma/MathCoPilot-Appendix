import Mathlib.Topology.DenseEmbedding

open Classical Filter Set Topology

noncomputable section

namespace Chapter02.DenseRangeConvergentNet

universe u v

/-- Every point is the limit of a genuine nontrivial net selected from a
dense range.

The index type is the subtype `range f`, equipped with the pullback of the
neighborhood filter at the target point.  Density makes that filter
nontrivial, while choice supplies an actual preimage for every index. -/
theorem exists_net_tendsto_of_denseRange
    {α : Type u} {β : Type v} [TopologicalSpace β]
    (f : α → β) (hf : DenseRange f) (x : β) :
    ∃ l : Filter (Set.range f),
      l.NeBot ∧
        ∃ g : Set.range f → α,
          Tendsto (fun i ↦ f (g i)) l (𝓝 x) := by
  let g : Set.range f → α :=
    fun i ↦ Classical.choose i.property
  have hfg (i : Set.range f) : f (g i) = i.1 :=
    Classical.choose_spec i.property
  let l : Filter (Set.range f) :=
    Filter.comap ((↑) : Set.range f → β) (𝓝 x)
  have hlne : l.NeBot := by
    exact hf.comap_val_nhds_neBot x
  refine ⟨l, hlne, g, ?_⟩
  change
    Tendsto (fun i : Set.range f ↦ f (g i))
      (Filter.comap ((↑) : Set.range f → β) (𝓝 x)) (𝓝 x)
  simpa only [hfg] using
    (show Tendsto ((↑) : Set.range f → β)
        (Filter.comap ((↑) : Set.range f → β) (𝓝 x)) (𝓝 x) from
      Filter.map_comap_le)

end Chapter02.DenseRangeConvergentNet
