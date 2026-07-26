import Chapter02.Spectral.AlmostPeriodic

open Classical Filter Set Topology

noncomputable section

namespace Chapter02.AlmostPeriodicIsometry

universe u

lemma iterate_norm
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (n : ℕ) :
    ‖(D.U^[n]) x‖ = ‖x‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', hU, ih]

lemma iterate_sub_norm
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x y : D.H) (n : ℕ) :
    ‖(D.U^[n]) x - (D.U^[n]) y‖ = ‖x - y‖ := by
  have hiter (z : D.H) : (D.U ^ n) z = (D.U^[n]) z := by
    rw [ContinuousLinearMap.coe_pow]
  rw [← hiter, ← hiter, ← map_sub, hiter]
  exact iterate_norm D hU (x - y) n

lemma almostPeriodic_has_return
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (hx : IsAlmostPeriodicVector D x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ‖(D.U^[n]) x - x‖ < ε := by
  obtain ⟨K, hKnon, hK⟩ :=
    AlmostPeriodic.almostPeriodic_orbit_net D x hx (ε / 2) (by positivity)
  let N : ℕ := K.max' hKnon + 1
  obtain ⟨k, hkK, hNk⟩ := hK N
  have hkmax : k ≤ K.max' hKnon := Finset.le_max' K k hkK
  have hkN : k < N := by
    dsimp [N]
    omega
  let n := N - k
  have hn : 0 < n := Nat.sub_pos_of_lt hkN
  refine ⟨n, hn, ?_⟩
  have hshift := iterate_sub_norm D hU ((D.U^[n]) x) x k
  have hsum : k + n = N := by
    dsimp [n]
    omega
  have hrewrite :
      (D.U^[k]) ((D.U^[n]) x) = (D.U^[N]) x := by
    rw [← Function.iterate_add_apply, hsum]
  calc
    ‖(D.U^[n]) x - x‖ =
        ‖(D.U^[k]) ((D.U^[n]) x) - (D.U^[k]) x‖ := hshift.symm
    _ = ‖(D.U^[N]) x - (D.U^[k]) x‖ := by rw [hrewrite]
    _ < 2 * (ε / 2) := hNk
    _ = ε := by ring

/-- For an isometric orbit, almost periodicity gives bounded gaps between
returns to every positive-radius norm neighborhood of the initial vector. -/
lemma almostPeriodic_returns_syndetic
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (hx : IsAlmostPeriodicVector D x)
    (ε : ℝ) (hε : 0 < ε) :
    IsSyndetic {n : ℕ | ‖(D.U^[n]) x - x‖ < ε} := by
  obtain ⟨K, hKnon, hK⟩ :=
    AlmostPeriodic.almostPeriodic_orbit_net D x hx (ε / 2) (by positivity)
  let L : ℕ := K.max' hKnon + 1
  have hL : 0 < L := by
    dsimp [L]
    omega
  refine ⟨L + 1, by omega, ?_⟩
  intro i
  obtain ⟨k, hkK, hclose⟩ := hK (i + L)
  have hkmax : k ≤ K.max' hKnon := Finset.le_max' K k hkK
  have hkL : k < L := by
    dsimp [L]
    omega
  let n : ℕ := i + L - k
  have hkn : k + n = i + L := by
    dsimp [n]
    omega
  have hin : i ≤ n := by
    dsimp [n]
    omega
  have hnlt : n < i + (L + 1) := by
    dsimp [n]
    omega
  refine ⟨n, ?_, hin, hnlt⟩
  have hshift := iterate_sub_norm D hU ((D.U^[n]) x) x k
  have hrewrite :
      (D.U^[k]) ((D.U^[n]) x) = (D.U^[i + L]) x := by
    rw [← Function.iterate_add_apply, hkn]
  calc
    ‖(D.U^[n]) x - x‖ =
        ‖(D.U^[k]) ((D.U^[n]) x) - (D.U^[k]) x‖ := hshift.symm
    _ = ‖(D.U^[i + L]) x - (D.U^[k]) x‖ := by rw [hrewrite]
    _ < 2 * (ε / 2) := hclose
    _ = ε := by ring

/-- A return at time `n` controls every fixed multiple `r * n`, with the
linear loss obtained by telescoping along the isometric orbit. -/
lemma iterate_mul_sub_norm_le
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (n r : ℕ) :
    ‖(D.U^[r * n]) x - x‖ ≤
      (r : ℝ) * ‖(D.U^[n]) x - x‖ := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hsplit :
          (D.U^[(r + 1) * n]) x =
            (D.U^[r * n]) ((D.U^[n]) x) := by
        rw [show (r + 1) * n = r * n + n by
              simpa [Nat.succ_eq_add_one] using Nat.succ_mul r n,
          Function.iterate_add_apply]
      rw [hsplit]
      calc
        ‖(D.U^[r * n]) ((D.U^[n]) x) - x‖ ≤
            ‖(D.U^[r * n]) ((D.U^[n]) x) -
                (D.U^[r * n]) x‖ +
              ‖(D.U^[r * n]) x - x‖ := by
          calc
            _ = ‖((D.U^[r * n]) ((D.U^[n]) x) -
                    (D.U^[r * n]) x) +
                  ((D.U^[r * n]) x - x)‖ := by
                congr 1
                abel
            _ ≤ _ := norm_add_le _ _
        _ = ‖(D.U^[n]) x - x‖ +
              ‖(D.U^[r * n]) x - x‖ := by
          rw [iterate_sub_norm D hU]
        _ ≤ ‖(D.U^[n]) x - x‖ +
              (r : ℝ) * ‖(D.U^[n]) x - x‖ :=
          add_le_add (le_refl _) ih
        _ = ((r + 1 : ℕ) : ℝ) *
              ‖(D.U^[n]) x - x‖ := by
          push_cast
          ring

/-- Almost-periodicity supplies syndetically many simultaneous approximate
returns along every finite progression `n, 2n, ..., ℓn`. -/
lemma almostPeriodic_progression_returns_syndetic
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (hx : IsAlmostPeriodicVector D x)
    (ℓ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    IsSyndetic {n : ℕ |
      ∀ r : ℕ, 0 < r → r ≤ ℓ →
        ‖(D.U^[r * n]) x - x‖ < (r : ℝ) * ε} := by
  obtain ⟨N, hN, hret⟩ :=
    almostPeriodic_returns_syndetic D hU x hx ε hε
  refine ⟨N, hN, ?_⟩
  intro i
  obtain ⟨n, hn, hin, hnN⟩ := hret i
  refine ⟨n, ?_, hin, hnN⟩
  intro r hr _hrℓ
  exact (iterate_mul_sub_norm_le D hU x n r).trans_lt
    (mul_lt_mul_of_pos_left hn (by exact_mod_cast hr))

/-- An isometry is automatically onto on each of its almost-periodic
vectors: recurrence places the vector in the closed range. -/
lemma exists_preimage_of_almostPeriodic
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (hx : IsAlmostPeriodicVector D x) :
    ∃ y : D.H, D.U y = x := by
  let V : D.H →ₗᵢ[ℂ] D.H :=
    { toLinearMap := D.U.toLinearMap
      norm_map' := hU }
  have hclosed : IsClosed (Set.range V) := by
    exact V.isometry.isClosedEmbedding.isClosed_range
  have hxclosure : x ∈ closure (Set.range V) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn, hret⟩ :=
      almostPeriodic_has_return D hU x hx ε hε
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    refine ⟨(D.U^[m + 1]) x, ?_, ?_⟩
    · refine ⟨(D.U^[m]) x, ?_⟩
      simpa [Nat.succ_eq_add_one] using
        (Function.iterate_succ_apply' D.U m x).symm
    · simpa [dist_eq_norm, norm_sub_rev,
        Function.iterate_succ_apply'] using hret
  have hxrange : x ∈ Set.range V := by
    rw [hclosed.closure_eq] at hxclosure
    exact hxclosure
  obtain ⟨y, hy⟩ := hxrange
  exact ⟨y, hy⟩

def almostPeriodicSubmodule (D : HilbertOperatorData.{u}) :
    Submodule ℂ D.H where
  carrier := {x | IsAlmostPeriodicVector D x}
  zero_mem' := AlmostPeriodic.almostPeriodic_zero D
  add_mem' {x y} hx hy := by
    simpa using
      (AlmostPeriodic.almostPeriodic_linear D x y hx hy (1 : ℂ) (1 : ℂ))
  smul_mem' c x hx := by
    simpa using
      (AlmostPeriodic.almostPeriodic_linear D x 0 hx
        (AlmostPeriodic.almostPeriodic_zero D) c 0)

lemma almostPeriodic_closed
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖) :
    IsClosed (almostPeriodicSubmodule D : Set D.H) := by
  apply IsSeqClosed.isClosed
  intro xseq x hxseq hx ε hε
  have hevent : ∀ᶠ n in atTop, ‖xseq n - x‖ < ε / 3 := by
    simpa [dist_eq_norm] using
      ((Metric.tendsto_atTop.1 hx) (ε / 3) (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  obtain ⟨F, hF⟩ := hxseq N (ε / 3) (by positivity)
  refine ⟨F, ?_⟩
  intro n
  obtain ⟨y, hyF, hNy⟩ := hF n
  refine ⟨y, hyF, ?_⟩
  have hNx : ‖xseq N - x‖ < ε / 3 := hN N (le_refl N)
  calc
    ‖(D.U^[n]) x - y‖ =
        ‖((D.U^[n]) x - (D.U^[n]) (xseq N)) +
          ((D.U^[n]) (xseq N) - y)‖ := by congr 1; abel
    _ ≤ ‖(D.U^[n]) x - (D.U^[n]) (xseq N)‖ +
        ‖(D.U^[n]) (xseq N) - y‖ := norm_add_le _ _
    _ = ‖x - xseq N‖ + ‖(D.U^[n]) (xseq N) - y‖ := by
      rw [iterate_sub_norm D hU]
    _ < ε / 3 + ε / 3 := by
      apply add_lt_add _ hNy
      simpa [norm_sub_rev] using hNx
    _ < ε := by linarith

lemma iterate_almostPeriodic
    (D : HilbertOperatorData.{u}) (x : D.H)
    (hx : IsAlmostPeriodicVector D x) (n : ℕ) :
    IsAlmostPeriodicVector D ((D.U^[n]) x) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using
        (AlmostPeriodic.almostPeriodic_iff_map D ((D.U^[n]) x)).mp ih

noncomputable def restrictedOperator
    (D : HilbertOperatorData.{u}) (_hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖) :
    almostPeriodicSubmodule D →L[ℂ] almostPeriodicSubmodule D :=
  { toLinearMap :=
      { toFun := fun x =>
          ⟨D.U x, (AlmostPeriodic.almostPeriodic_iff_map D x).mp x.property⟩
        map_add' := fun x y => by ext; exact D.U.map_add x y
        map_smul' := fun c x => by ext; exact D.U.map_smul c x }
    cont := (D.U.continuous.comp continuous_subtype_val).subtype_mk _ }

noncomputable def restrictedData
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖) :
    HilbertOperatorData.{u} := by
  let S := almostPeriodicSubmodule D
  letI : CompleteSpace S := (almostPeriodic_closed D hU).completeSpace_coe
  exact
    { H := S
      normedAddCommGroup := inferInstance
      innerProductSpace := inferInstance
      completeSpace := inferInstance
      U := restrictedOperator D hU }

@[simp]
lemma restrictedData_apply
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : almostPeriodicSubmodule D) :
    ((restrictedData D hU).U x : almostPeriodicSubmodule D).1 = D.U x := rfl

@[simp]
lemma restrictedOperator_apply
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : almostPeriodicSubmodule D) :
    (restrictedOperator D hU x : D.H) = D.U x := rfl

lemma restrictedData_unitary
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖) :
    IsUnitary (restrictedData D hU) := by
  constructor
  · intro x
    change almostPeriodicSubmodule D at x
    obtain ⟨y, hy⟩ :=
      exists_preimage_of_almostPeriodic D hU (x : D.H) x.property
    have hyap : IsAlmostPeriodicVector D y := by
      apply (AlmostPeriodic.almostPeriodic_iff_map D y).mpr
      rw [hy]
      exact x.property
    exact ⟨⟨y, hyap⟩, Subtype.ext hy⟩
  · intro x
    change almostPeriodicSubmodule D at x
    exact hU (x : D.H)

lemma restrictedData_iterate_apply
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : almostPeriodicSubmodule D) (n : ℕ) :
    (((restrictedOperator D hU)^[n]) x :
      almostPeriodicSubmodule D).1 = (D.U^[n]) (x : D.H) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change D.U ((((restrictedOperator D hU)^[n]) x :
        almostPeriodicSubmodule D) : D.H) = _
      rw [ih]

lemma restrictedVector_almostPeriodic
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : almostPeriodicSubmodule D) :
    IsAlmostPeriodicVector (restrictedData D hU) x := by
  change ∀ ε : ℝ, 0 < ε →
    ∃ F : Finset (almostPeriodicSubmodule D),
      ∀ n : ℕ, ∃ y ∈ F,
        ‖((restrictedOperator D hU)^[n]) x - y‖ < ε
  intro ε hε
  obtain ⟨K, hKnon, hK⟩ :=
    AlmostPeriodic.almostPeriodic_orbit_net D (x : D.H) x.property
      (ε / 2) (by positivity)
  let orbitPoint : ℕ → almostPeriodicSubmodule D := fun n =>
    ⟨(D.U^[n]) (x : D.H), iterate_almostPeriodic D x x.property n⟩
  refine ⟨K.image orbitPoint, ?_⟩
  intro n
  obtain ⟨k, hkK, hdist⟩ := hK n
  refine ⟨orbitPoint k, Finset.mem_image.mpr ⟨k, hkK, rfl⟩, ?_⟩
  change
    ‖((((restrictedOperator D hU)^[n]) x :
        almostPeriodicSubmodule D) : D.H) -
      (orbitPoint k : D.H)‖ < ε
  rw [restrictedData_iterate_apply]
  exact lt_of_lt_of_eq hdist (by ring)

/-- The almost-periodic/discrete-spectrum equivalence only needs an
isometry.  On the closed almost-periodic subspace the isometry is
automatically surjective, so the existing unitary spectral theorem applies. -/
theorem almostPeriodic_implies_discrete
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (hx : IsAlmostPeriodicVector D x) :
    InDiscreteSpectralSubspace D x := by
  let X : almostPeriodicSubmodule D := ⟨x, hx⟩
  have hXap : IsAlmostPeriodicVector (restrictedData D hU) X :=
    restrictedVector_almostPeriodic D hU X
  have hXdisc : InDiscreteSpectralSubspace (restrictedData D hU) X :=
    AlmostPeriodic.almostPeriodic_implies_discrete
      (restrictedData D hU) (restrictedData_unitary D hU) X hXap
  intro ε hε
  obtain ⟨s, hs, c, happrox⟩ := hXdisc ε hε
  change Finset (almostPeriodicSubmodule D) at s
  change (∀ y ∈ s, IsEigenvector (restrictedData D hU) y) at hs
  change (almostPeriodicSubmodule D → ℂ) at c
  let val : almostPeriodicSubmodule D → D.H := fun y => y.1
  have hval : Function.Injective val := Subtype.val_injective
  let t : Finset D.H := s.image val
  let d : D.H → ℂ := fun y => c (Function.invFun val y)
  refine ⟨t, ?_, d, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hzEig := hs z hz
    refine ⟨?_, ?_⟩
    · intro hzero
      apply hzEig.1
      exact Subtype.ext hzero
    · obtain ⟨lam, hlam⟩ := hzEig.2
      refine ⟨lam, ?_⟩
      change restrictedOperator D hU z = lam • z at hlam
      exact congrArg Subtype.val hlam
  · have hsum :
        (∑ y ∈ t, d y • y) =
          ∑ z ∈ s, c z • (z : D.H) := by
      dsimp only [t, d]
      rw [Finset.sum_image hval.injOn]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Function.leftInverse_invFun hval]
    change
      ‖((X - ∑ z ∈ s, c z • z :
        almostPeriodicSubmodule D) : D.H)‖ < ε at happrox
    have hcoe :
        ((X - ∑ z ∈ s, c z • z :
          almostPeriodicSubmodule D) : D.H) =
          x - ∑ z ∈ s, c z • (z : D.H) := by
      simp [X]
    rw [hcoe] at happrox
    rwa [hsum]

/-- A nonzero vector in the discrete spectral subspace has a nontrivial
correlation with an eigenvector. -/
theorem exists_eigenvector_inner_ne_zero_of_discrete
    (D : HilbertOperatorData.{u}) (x : D.H)
    (hx : InDiscreteSpectralSubspace D x) (hx0 : x ≠ 0) :
    ∃ y : D.H, IsEigenvector D y ∧
      @inner ℂ D.H inferInstance x y ≠ 0 := by
  by_contra h
  push_neg at h
  have hxcont : InContinuousSpectralSubspace D x := by
    intro y hy
    exact h y hy
  have hxx :=
    SpectralMeasureType.discrete_orthogonal_continuous D x x hx hxcont
  exact hx0 (inner_self_eq_zero.mp hxx)

/-- A nonzero eigenvalue of a linear isometry lies on the unit circle.
Unlike the older spectral lemma, this does not require surjectivity. -/
lemma eigenvalue_norm_one
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (y : D.H) (hy0 : y ≠ 0) (lam : ℂ) (hy : D.U y = lam • y) :
    ‖lam‖ = 1 := by
  have hn := hU y
  rw [hy, norm_smul] at hn
  have hny : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
  apply mul_right_cancel₀ hny
  simpa using hn

/-- Finite linear combinations of eigenvectors have precompact forward
orbit for every linear isometry. -/
lemma finiteEigenCombination_almostPeriodic
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (s : Finset D.H) (hs : ∀ y ∈ s, IsEigenvector D y)
    (c : D.H → ℂ) :
    IsAlmostPeriodicVector D (∑ y ∈ s, c y • y) := by
  let lam : (y : s) → ℂ := fun y => (hs y.1 y.2).2.choose
  have hlam (y : s) :
      D.U y.1 = lam y • y.1 := (hs y.1 y.2).2.choose_spec
  let e : (y : s) → Circle := fun y =>
    ⟨lam y, mem_sphere_zero_iff_norm.mpr
      (eigenvalue_norm_one D hU y.1 (hs y.1 y.2).1 (lam y) (hlam y))⟩
  let Φ : (s → Circle) → D.H := fun q =>
    ∑ y : s, (((q y : Circle) : ℂ) * c y.1) • y.1
  have hΦ : Continuous Φ := by
    dsimp [Φ]
    fun_prop
  have hcompact : IsCompact (Set.range Φ) := isCompact_range hΦ
  intro ε hε
  obtain ⟨t, htfin, htcover⟩ :=
    Metric.totallyBounded_iff.mp hcompact.totallyBounded ε hε
  refine ⟨htfin.toFinset, ?_⟩
  intro n
  have horbit :
      (D.U^[n]) (∑ y ∈ s, c y • y) = Φ (fun y => e y ^ n) := by
    rw [AlmostPeriodic.iterate_finset_sum]
    dsimp [Φ]
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro y hy
    have hiter (v : D.H) : (D.U ^ n) v = (D.U^[n]) v := by
      rw [ContinuousLinearMap.coe_pow]
    rw [← hiter, map_smul, hiter]
    rw [SpectralPointMass.eigen_iterate D y.1 (lam y) (hlam y)]
    simp only [smul_smul]
    change (c y.1 * lam y ^ n) • y.1 =
      (lam y ^ n * c y.1) • y.1
    rw [mul_comm]
  have hmem : Φ (fun y => e y ^ n) ∈ Set.range Φ := ⟨_, rfl⟩
  have hcover := htcover hmem
  simp only [Set.mem_iUnion, Metric.mem_ball] at hcover
  obtain ⟨y, hyt, hdist⟩ := hcover
  refine ⟨y, (Set.Finite.mem_toFinset htfin).2 hyt, ?_⟩
  simpa [horbit, dist_eq_norm] using hdist

lemma eigenvector_almostPeriodic
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (y : D.H) (hy : IsEigenvector D y) :
    IsAlmostPeriodicVector D y := by
  simpa using
    finiteEigenCombination_almostPeriodic D hU {y}
      (by simpa using hy) (fun _ => 1)

/-- Orthogonal projection onto the closed almost-periodic subspace. -/
noncomputable def almostPeriodicProjection
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) : D.H := by
  let S := almostPeriodicSubmodule D
  letI : CompleteSpace S := (almostPeriodic_closed D hU).completeSpace_coe
  letI : S.HasOrthogonalProjection := inferInstance
  exact S.starProjection x

lemma almostPeriodicProjection_mem
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) :
    IsAlmostPeriodicVector D (almostPeriodicProjection D hU x) := by
  let S := almostPeriodicSubmodule D
  letI : CompleteSpace S := (almostPeriodic_closed D hU).completeSpace_coe
  letI : S.HasOrthogonalProjection := inferInstance
  exact S.starProjection_apply_mem x

lemma sub_almostPeriodicProjection_mem_orthogonal
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) :
    x - almostPeriodicProjection D hU x ∈
      (almostPeriodicSubmodule D)ᗮ := by
  let S := almostPeriodicSubmodule D
  letI : CompleteSpace S := (almostPeriodic_closed D hU).completeSpace_coe
  letI : S.HasOrthogonalProjection := inferInstance
  exact Submodule.sub_starProjection_mem_orthogonal x

/-- The residual after projecting onto the almost-periodic subspace is
orthogonal to every eigenvector, hence lies in the continuous spectral
subspace in the sense used throughout Chapter 2. -/
theorem sub_almostPeriodicProjection_continuous
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) :
    InContinuousSpectralSubspace D
      (x - almostPeriodicProjection D hU x) := by
  intro y hy
  exact inner_eq_zero_symm.mpr
    (sub_almostPeriodicProjection_mem_orthogonal D hU x y
      (eigenvector_almostPeriodic D hU y hy))

/-- A continuous-spectral vector is orthogonal to every almost-periodic
vector.  This upgrades the defining orthogonality against eigenvectors using
the isometric almost-periodic/discrete equivalence. -/
lemma continuous_inner_almostPeriodic_eq_zero
    (D : HilbertOperatorData.{u})
    (hU : ∀ z : D.H, ‖D.U z‖ = ‖z‖)
    (x y : D.H)
    (hx : InContinuousSpectralSubspace D x)
    (hy : IsAlmostPeriodicVector D y) :
    @inner ℂ D.H _ x y = 0 := by
  apply inner_eq_zero_symm.mpr
  exact SpectralMeasureType.discrete_orthogonal_continuous D y x
    (almostPeriodic_implies_discrete D hU y hy) hx

/-- The orthogonal complement of the almost-periodic subspace is forward
invariant under an isometry. -/
lemma map_mem_almostPeriodic_orthogonal
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    {x : D.H} (hx : x ∈ (almostPeriodicSubmodule D)ᗮ) :
    D.U x ∈ (almostPeriodicSubmodule D)ᗮ := by
  intro y hy
  obtain ⟨z, hz⟩ := exists_preimage_of_almostPeriodic D hU y hy
  have hzAP : IsAlmostPeriodicVector D z := by
    apply (AlmostPeriodic.almostPeriodic_iff_map D z).mpr
    rwa [hz]
  let V : D.H →ₗᵢ[ℂ] D.H :=
    { toLinearMap := D.U.toLinearMap
      norm_map' := hU }
  have hi := V.inner_map_map z x
  change @inner ℂ D.H _ (D.U z) (D.U x) =
    @inner ℂ D.H _ z x at hi
  rw [hz, hx z hzAP] at hi
  exact hi

/-- The almost-periodic orthogonal projection intertwines every linear
isometry with its action. -/
lemma almostPeriodicProjection_map
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) :
    almostPeriodicProjection D hU (D.U x) =
      D.U (almostPeriodicProjection D hU x) := by
  let S := almostPeriodicSubmodule D
  letI : CompleteSpace S := (almostPeriodic_closed D hU).completeSpace_coe
  letI : S.HasOrthogonalProjection := inferInstance
  apply S.eq_starProjection_of_mem_orthogonal
  · exact (AlmostPeriodic.almostPeriodic_iff_map D _).mp
      (almostPeriodicProjection_mem D hU x)
  · have hr :=
      map_mem_almostPeriodic_orthogonal D hU
        (sub_almostPeriodicProjection_mem_orthogonal D hU x)
    simpa only [map_sub] using hr

end Chapter02.AlmostPeriodicIsometry
