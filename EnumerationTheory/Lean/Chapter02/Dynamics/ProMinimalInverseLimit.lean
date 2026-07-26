import Chapter02.HostKra.HostKraStructuredRecurrence

open Classical Set

noncomputable section

namespace Chapter02.ProMinimalInverseLimit

open Chapter02.HostKraStructuredRecurrence

universe u

/-- A continuous observable is uniformly approximable by observables
factoring through compact minimal systems.  This is the precise topological
consequence of an inverse-limit presentation needed to obtain a
pro-minimal orbit sequence. -/
def HasUniformMinimalFactorApproximations
    {X : Type u} [TopologicalSpace X]
    (T : X → X) (f : X → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ Y : Type, ∃ _top : TopologicalSpace Y,
    ∃ _compact : CompactSpace Y,
    ∃ S : Y → Y, ∃ π : X → Y, ∃ g : Y → ℝ,
      Continuous S ∧
      EveryOrbitHitsOpen S ∧
      Continuous π ∧
      (∀ x, π (T x) = S (π x)) ∧
      Continuous g ∧
      ∀ x, |f x - g (π x)| < η

/-- Equivariance with one time step propagates to every natural iterate. -/
theorem iterate_factor
    {X : Type u} {Y : Type}
    (T : X → X) (S : Y → Y) (π : X → Y)
    (hequiv : ∀ x, π (T x) = S (π x))
    (n : ℕ) (x : X) :
    π ((T^[n]) x) = (S^[n]) (π x) := by
  induction n generalizing x with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        ih, hequiv]

/-- An orbit observation of any uniformly minimal-factor-approximable
observable is a uniform limit of compact-minimal orbit sequences. -/
theorem isUniformLimitOfMinimalOrbitSequences_orbit
    {X : Type u} [TopologicalSpace X]
    (T : X → X) (f : X → ℝ)
    (happrox : HasUniformMinimalFactorApproximations T f)
    (x : X) :
    IsUniformLimitOfMinimalOrbitSequences
      (fun n ↦ f ((T^[n]) x)) := by
  intro η hη
  obtain ⟨Y, topY, compactY, S, π, g,
      hS, hminimal, hπ, hequiv, hg, hfg⟩ :=
    happrox η hη
  letI : TopologicalSpace Y := topY
  letI : CompactSpace Y := compactY
  let b : ℕ → ℝ := fun n ↦ g ((S^[n]) (π x))
  refine ⟨b, ?_, ?_⟩
  · exact ⟨Y, inferInstance, inferInstance, S, π x, g,
      hS, hminimal, hg, fun n ↦ rfl⟩
  · intro n
    change |f ((T^[n]) x) - g ((S^[n]) (π x))| < η
    rw [← iterate_factor T S π hequiv n x]
    exact hfg ((T^[n]) x)

/-- The class of pro-minimal sequences is closed under uniform limits.
This diagonal argument is the sequence-level form of passing from finite
stages to an inverse limit. -/
theorem isUniformLimitOfMinimalOrbitSequences_of_uniform_limit
    (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ)
    (hb : ∀ k, IsUniformLimitOfMinimalOrbitSequences (b k))
    (hba : ∀ η : ℝ, 0 < η →
      ∃ k : ℕ, ∀ n : ℕ, |a n - b k n| < η) :
    IsUniformLimitOfMinimalOrbitSequences a := by
  intro η hη
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨k, hak⟩ := hba (η / 2) hη2
  obtain ⟨c, hcminimal, hkc⟩ := hb k (η / 2) hη2
  refine ⟨c, hcminimal, fun n ↦ ?_⟩
  have htri : |a n - c n| ≤
      |a n - b k n| + |b k n - c n| := by
    simpa only [sub_add_sub_cancel] using
      abs_add_le (a n - b k n) (b k n - c n)
  calc
    |a n - c n| ≤ |a n - b k n| + |b k n - c n| := htri
    _ < η / 2 + η / 2 := add_lt_add (hak n) (hkc n)
    _ = η := by ring

end Chapter02.ProMinimalInverseLimit
