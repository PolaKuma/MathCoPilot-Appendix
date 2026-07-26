import Mathlib

open Set

namespace Chapter02.ConnectedCountableRange

universe u v

/-- A continuous map from a connected space to a metric space with
countable range is constant.

This is the topological rigidity input used in the Parry eigenvalue
argument: countable subsets of metric spaces are totally disconnected. -/
theorem eq_of_continuous_of_countable_range
    {A : Type u} {B : Type v}
    [TopologicalSpace A] [ConnectedSpace A] [MetricSpace B]
    (f : A → B) (hf : Continuous f)
    (hcount : Set.Countable (Set.range f)) :
    ∀ x y, f x = f y := by
  have hconnected : IsConnected (range f) :=
    isConnected_range hf
  have hrange : (range f).Subsingleton :=
    Set.Countable.isTotallyDisconnected hcount
      (range f) Subset.rfl hconnected.isPreconnected
  intro x y
  exact hrange ⟨x, rfl⟩ ⟨y, rfl⟩

end Chapter02.ConnectedCountableRange
