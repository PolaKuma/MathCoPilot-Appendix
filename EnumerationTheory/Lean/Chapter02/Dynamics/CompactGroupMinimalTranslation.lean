import Chapter02.HostKra.HostKraStructuredRecurrence

open Classical Set

noncomputable section

namespace Chapter02.CompactGroupMinimalTranslation

open Chapter02.HostKraStructuredRecurrence

universe u

/-- Left translation by a fixed group element. -/
def leftTranslation
    {G : Type u} [Group G] (a : G) (x : G) : G :=
  a * x

theorem leftTranslation_iterate
    {G : Type u} [Group G] (a : G) (n : ℕ) (x : G) :
    ((leftTranslation a)^[n]) x = a ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [leftTranslation, pow_succ', mul_assoc]

/-- On a topological group, density of the nonnegative powers of `a`
implies minimality of left translation by `a`. -/
theorem everyOrbitHitsOpen_leftTranslation_of_dense_powers
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (a : G)
    (hdense : Dense (Set.range fun n : ℕ ↦ a ^ n)) :
    EveryOrbitHitsOpen (leftTranslation a) := by
  intro x U hU hUne
  let R : G ≃ₜ G := Homeomorph.mulRight x
  let V : Set G := R ⁻¹' U
  have hVopen : IsOpen V := hU.preimage R.continuous
  have hVne : V.Nonempty := by
    obtain ⟨u, hu⟩ := hUne
    refine ⟨R.symm u, ?_⟩
    change R (R.symm u) ∈ U
    simpa using hu
  rw [dense_iff_inter_open] at hdense
  obtain ⟨g, hgV, n, hn⟩ := hdense V hVopen hVne
  refine ⟨n, ?_⟩
  have hn' : a ^ n = g := hn
  rw [leftTranslation_iterate, hn']
  exact hgV

/-- In particular, a dense cyclic semigroup gives the finite open-cover
recurrence form used throughout the BHK reduction on a compact group. -/
theorem hasFiniteOrbitCover_leftTranslation_of_dense_powers
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G]
    (a : G)
    (hdense : Dense (Set.range fun n : ℕ ↦ a ^ n)) :
    HasFiniteOrbitCover (leftTranslation a) := by
  apply hasFiniteOrbitCover_of_compact
  · exact continuous_const.mul continuous_id
  · exact everyOrbitHitsOpen_leftTranslation_of_dense_powers a hdense

end Chapter02.CompactGroupMinimalTranslation
