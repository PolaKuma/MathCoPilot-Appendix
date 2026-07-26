import Mathlib.Order.Zorn
import Mathlib.Topology.Compactness.Compact

open Classical Set

noncomputable section

namespace Chapter02.CompactForwardMinimalSubset

universe u

/-- The family of nonempty closed forward-invariant subsets of `C`. -/
def ForwardInvariantFamily
    {Y : Type u} [TopologicalSpace Y]
    (T : Y → Y) (C : Set Y) : Set (Set Y) :=
  {D | D.Nonempty ∧ IsClosed D ∧ D ⊆ C ∧ T '' D ⊆ D}

/-- Every nonempty closed forward-invariant subset of a compact space
contains a minimal nonempty closed forward-invariant subset.

This is the Zorn argument needed for pointwise minimality of compact group
extensions.  It is proved here rather than importing the book-level
Chapter 5 theorem, whose current proof is not risk-free. -/
theorem exists_minimal_nonempty_closed_forwardInvariant_subset
    {Y : Type u} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Y) (C : Set Y)
    (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCinv : T '' C ⊆ C) :
    ∃ D : Set Y,
      D ⊆ C ∧ D.Nonempty ∧ IsClosed D ∧ T '' D ⊆ D ∧
        ∀ E : Set Y, E ⊆ D → E.Nonempty → IsClosed E →
          T '' E ⊆ E → D ⊆ E := by
  let 𝓕 := ForwardInvariantFamily T C
  have hCmem : C ∈ 𝓕 :=
    ⟨hCne, hCclosed, Subset.rfl, hCinv⟩
  obtain ⟨D, hDC, hDmin⟩ :=
    zorn_superset_nonempty 𝓕 (fun c hc𝓕 hc hcnonempty ↦ by
      let E : Set Y := ⋂₀ c
      have hEclosed : IsClosed E := by
        exact isClosed_sInter fun s hs ↦ (hc𝓕 hs).2.1
      have hEdirected : DirectedOn (· ⊇ ·) c :=
        IsChain.directedOn hc.symm
      have hEne : E.Nonempty := by
        letI : Nonempty c := hcnonempty.to_subtype
        change (⋂₀ c).Nonempty
        exact
          IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
            hEdirected
            (fun s hs ↦ (hc𝓕 hs).1)
            (fun s hs ↦ (hc𝓕 hs).2.1.isCompact)
            (fun s hs ↦ (hc𝓕 hs).2.1)
      obtain ⟨s₀, hs₀⟩ := hcnonempty
      have hEC : E ⊆ C :=
        (sInter_subset_of_mem hs₀).trans (hc𝓕 hs₀).2.2.1
      have hEinv : T '' E ⊆ E := by
        rintro y ⟨x, hx, rfl⟩
        rw [mem_sInter] at hx ⊢
        intro s hs
        exact (hc𝓕 hs).2.2.2 ⟨x, hx s hs, rfl⟩
      refine ⟨E, ⟨hEne, hEclosed, hEC, hEinv⟩, ?_⟩
      intro s hs
      exact sInter_subset_of_mem hs)
    C hCmem
  refine ⟨D, hDC, (hDmin.1).1, (hDmin.1).2.1,
    (hDmin.1).2.2.2, ?_⟩
  intro E hED hEne hEclosed hEinv
  exact hDmin.2 ⟨hEne, hEclosed,
    hED.trans (hDmin.1).2.2.1, hEinv⟩ hED

end Chapter02.CompactForwardMinimalSubset
