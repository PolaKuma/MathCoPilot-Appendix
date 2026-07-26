import Chapter02.Dynamics.MinimalFactorOrbitClosure
import Chapter02.Spectral.SpectralWiener
import Chapter02.HallPetresco.ConnectedCountableRange

open Set Filter Topology

noncomputable section

namespace Chapter02.MinimalContinuousEigenfunction

open Chapter02.HostKraStructuredRecurrence
open Chapter02.MinimalFactorOrbitClosure
open Chapter02.SpectralWiener

universe u

/-- On a compact minimal forward system, two continuous eigenfunctions
with the same eigenvalue are equal as soon as they agree at one point.

The proof only uses density of that point's forward orbit. -/
theorem eq_of_same_eigenvalue
    {Y : Type u} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Y) (hminimal : EveryOrbitHitsOpen T)
    (q : Y) (lam : ℂ) (f g : Y → ℂ)
    (hfcontinuous : Continuous f) (hgcontinuous : Continuous g)
    (hf : ∀ y, f (T y) = lam * f y)
    (hg : ∀ y, g (T y) = lam * g y)
    (hq : f q = g q) :
    f = g := by
  let E : Set Y := {y | f y = g y}
  have hEclosed : IsClosed E :=
    isClosed_eq hfcontinuous hgcontinuous
  have horbit :
      Chapter02.HallPetrescoMeasureOrbit.forwardOrbit T q ⊆ E := by
    rintro _ ⟨n, rfl⟩
    change f ((T^[n]) q) = g ((T^[n]) q)
    induction n with
    | zero => simpa using hq
    | succ n ih =>
        rw [Function.iterate_succ_apply', hf, hg, ih]
  have hdense :
      Dense
        (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit T q) :=
    dense_forwardOrbit_of_everyOrbitHitsOpen T hminimal q
  have hall :
      closure
          (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit T q) ⊆ E :=
    closure_minimal horbit hEclosed
  rw [hdense.closure_eq] at hall
  funext y
  exact hall (Set.mem_univ y)

/-- A normalized nonzero continuous function cannot carry two different
eigenvalues for the same dynamics. -/
theorem eigenvalue_eq_of_same_normalized_function
    {Y : Type u} (T : Y → Y) (q : Y)
    (lam xi : ℂ) (f : Y → ℂ)
    (hf : ∀ y, f (T y) = lam * f y)
    (hg : ∀ y, f (T y) = xi * f y)
    (hq : f q = 1) :
    lam = xi := by
  have h := (hf q).symm.trans (hg q)
  simpa [hq] using h

/-- A nontrivial point of the unit circle has a power at distance at least
one from `1`.  The proof is the elementary Cesàro argument. -/
theorem exists_pow_norm_sub_one_ge_one
    (r : ℂ) (hr : ‖r‖ = 1) (hr1 : r ≠ 1) :
    ∃ n : ℕ, 1 ≤ ‖r ^ n - 1‖ := by
  by_contra h
  push_neg at h
  have hre : ∀ n : ℕ, (1 / 2 : ℝ) < (r ^ n).re := by
    intro n
    have hlt := h n
    have hsq : ‖r ^ n - 1‖ ^ 2 < 1 := by
      nlinarith [norm_nonneg (r ^ n - 1)]
    have hnormpow : ‖r ^ n‖ = 1 := by
      simp [norm_pow, hr]
    have hnormSqPow : Complex.normSq (r ^ n) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hnormpow]
      norm_num
    have hnormSqOne : Complex.normSq (1 : ℂ) = 1 := by
      norm_num
    have hformula :
        ‖r ^ n - 1‖ ^ 2 = 2 - 2 * (r ^ n).re := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
      rw [hnormSqPow, hnormSqOne]
      simp only [map_one, mul_one]
      ring
    rw [hformula] at hsq
    nlinarith
  have havg :
      ∀ N : ℕ, 0 < N →
        (1 / 2 : ℝ) < (geometricAverage r N).re := by
    intro N hN
    rw [geometricAverage, if_neg (Nat.ne_of_gt hN)]
    have hsumre :
        (∑ n ∈ Finset.range N, r ^ n).re =
          ∑ n ∈ Finset.range N, (r ^ n).re := by
      exact map_sum Complex.reCLM (fun n : ℕ => r ^ n) (Finset.range N)
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hinvre : ((N : ℂ)⁻¹).re = (N : ℝ)⁻¹ := by
      rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
      rw [Complex.natCast_re]
      rw [norm_natCast]
      field_simp [hNreal.ne']
    have hinvim : ((N : ℂ)⁻¹).im = 0 := by
      rw [Complex.inv_im]
      simp
    rw [Complex.mul_re, hsumre]
    rw [hinvre, hinvim, zero_mul, sub_zero]
    have hsum :
        (N : ℝ) / 2 <
          ∑ n ∈ Finset.range N, (r ^ n).re := by
      have := Finset.sum_lt_sum_of_nonempty
        (s := Finset.range N)
        (f := fun _ : ℕ => (1 / 2 : ℝ))
        (g := fun n : ℕ => (r ^ n).re)
        (by simp [hN.ne'])
        (by
          intro n hn
          exact hre n)
      simpa [div_eq_mul_inv, Finset.sum_const_nat] using this
    calc
      (1 / 2 : ℝ) = (N : ℝ)⁻¹ * ((N : ℝ) / 2) := by
        field_simp [hNreal.ne']
      _ < (N : ℝ)⁻¹ *
          ∑ n ∈ Finset.range N, (r ^ n).re :=
        mul_lt_mul_of_pos_left hsum (inv_pos.mpr hNreal)
  have htend :
      Tendsto (geometricAverage r) atTop (nhds 0) := by
    simpa [hr1] using tendsto_geometricAverage r hr
  obtain ⟨N₀, hN₀⟩ :=
    (Metric.tendsto_atTop.mp htend) (1 / 4) (by norm_num)
  let N := max N₀ 1
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hdist : dist (geometricAverage r N) 0 < 1 / 4 :=
    hN₀ N (le_max_left _ _)
  have hreabs :
      |(geometricAverage r N).re| < 1 / 4 := by
    calc
      |(geometricAverage r N).re| ≤ ‖geometricAverage r N‖ :=
        Complex.abs_re_le_norm _
      _ = dist (geometricAverage r N) 0 := by simp [dist_eq_norm]
      _ < 1 / 4 := hdist
  have := havg N hNpos
  nlinarith [le_abs_self (geometricAverage r N).re]

/-- Iterating a continuous eigenrelation gives the expected power of the
eigenvalue. -/
theorem eigenfunction_iterate
    {Y : Type u} (T : Y → Y) (lam : ℂ) (f : Y → ℂ)
    (hf : ∀ y, f (T y) = lam * f y) :
    ∀ (n : ℕ) (y : Y), f ((T^[n]) y) = lam ^ n * f y := by
  intro n
  induction n with
  | zero =>
      intro y
      simp
  | succ n ih =>
      intro y
      rw [Function.iterate_succ_apply', hf, ih]
      rw [pow_succ]
      ring

/-- Normalized continuous eigenfunctions with distinct unit-modulus
eigenvalues are separated by at least one in the uniform norm. -/
theorem one_le_norm_sub_of_distinct_eigenvalues
    {Y : Type u} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Y) (q : Y)
    (lam xi : ℂ) (hlam : ‖lam‖ = 1) (hxi : ‖xi‖ = 1)
    (hlamxi : lam ≠ xi) (f g : C(Y, ℂ))
    (hf : ∀ y, f (T y) = lam * f y)
    (hg : ∀ y, g (T y) = xi * g y)
    (hfq : f q = 1) (hgq : g q = 1) :
    1 ≤ ‖f - g‖ := by
  have hxi0 : xi ≠ 0 := by
    intro h
    subst xi
    simp at hxi
  let r : ℂ := lam * xi⁻¹
  have hr : ‖r‖ = 1 := by
    simp [r, norm_inv, hlam, hxi]
  have hlam_eq : lam = r * xi := by
    dsimp [r]
    field_simp
  have hr1 : r ≠ 1 := by
    intro hrone
    apply hlamxi
    rw [hlam_eq, hrone, one_mul]
  obtain ⟨n, hn⟩ := exists_pow_norm_sub_one_ge_one r hr hr1
  let y := (T^[n]) q
  have hfy : f y = lam ^ n := by
    rw [eigenfunction_iterate T lam f hf n q, hfq, mul_one]
  have hgy : g y = xi ^ n := by
    rw [eigenfunction_iterate T xi g hg n q, hgq, mul_one]
  have hdiff :
      ‖lam ^ n - xi ^ n‖ = ‖r ^ n - 1‖ := by
    rw [hlam_eq, mul_pow]
    rw [show r ^ n * xi ^ n - xi ^ n =
        xi ^ n * (r ^ n - 1) by ring]
    rw [norm_mul, norm_pow, hxi, one_pow, one_mul]
  calc
    1 ≤ ‖r ^ n - 1‖ := hn
    _ = ‖lam ^ n - xi ^ n‖ := hdiff.symm
    _ = ‖(f - g) y‖ := by simp [hfy, hgy]
    _ ≤ ‖f - g‖ := ContinuousMap.norm_coe_le_norm (f - g) y

/-- A uniformly separated subset of a separable metric space is countable. -/
theorem countable_of_one_le_dist
    {E : Type u} [MetricSpace E] [TopologicalSpace.SeparableSpace E]
    (S : Set E)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ dist x y) :
    S.Countable := by
  obtain ⟨D, hDcount, hDdense⟩ :=
    TopologicalSpace.exists_countable_dense E
  let near : S → D := fun x =>
    ⟨Classical.choose
        (hDdense.exists_dist_lt x (show (0 : ℝ) < 1 / 3 by norm_num)),
      (Classical.choose_spec
        (hDdense.exists_dist_lt x
          (show (0 : ℝ) < 1 / 3 by norm_num))).1⟩
  have hnear (x : S) :
      dist (x : E) ((near x : D) : E) < 1 / 3 :=
    (Classical.choose_spec
      (hDdense.exists_dist_lt x
        (show (0 : ℝ) < 1 / 3 by norm_num))).2
  have hnear_injective : Function.Injective near := by
    intro x y hxy
    apply Subtype.ext
    by_contra hval
    have hlarge : 1 ≤ dist (x : E) y :=
      hsep x x.property y y.property hval
    have htriangle :
        dist (x : E) y ≤
          dist (x : E) ((near x : D) : E) +
            dist ((near x : D) : E) (y : E) :=
      dist_triangle _ _ _
    have hright :
        dist ((near x : D) : E) (y : E) < 1 / 3 := by
      rw [hxy]
      simpa [dist_comm] using hnear y
    nlinarith [hnear x]
  let e : S ↪ D := ⟨near, hnear_injective⟩
  letI : Countable D := Set.countable_coe_iff.mpr hDcount
  exact Set.countable_coe_iff.mp e.countable

/-- A unit-modulus eigenvalue admitting a continuous eigenfunction normalized
at `q`. -/
def IsNormalizedContinuousEigenvalue
    {Y : Type u} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Y) (q : Y) (lam : ℂ) : Prop :=
  ‖lam‖ = 1 ∧
    ∃ f : C(Y, ℂ), (∀ y, f (T y) = lam * f y) ∧ f q = 1

/-- The normalized continuous eigenvalue set of a compact metrizable system
is countable. -/
theorem countable_normalizedContinuousEigenvalues
    {Y : Type u} [TopologicalSpace Y] [CompactSpace Y]
    [T2Space Y] [SecondCountableTopology Y]
    (T : Y → Y) (q : Y) :
    {lam : ℂ | IsNormalizedContinuousEigenvalue T q lam}.Countable := by
  let S : Set ℂ :=
    {lam : ℂ | IsNormalizedContinuousEigenvalue T q lam}
  let efun : S → C(Y, ℂ) := fun a =>
    Classical.choose a.property.2
  have hefun_spec (a : S) :
      (∀ y, efun a (T y) = a * efun a y) ∧ efun a q = 1 :=
    Classical.choose_spec a.property.2
  have hefun_injective : Function.Injective efun := by
    intro a b hab
    apply Subtype.ext
    apply eigenvalue_eq_of_same_normalized_function
        T q a b (efun a)
    · exact (hefun_spec a).1
    · simpa [hab] using (hefun_spec b).1
    · exact (hefun_spec a).2
  let R : Set C(Y, ℂ) := Set.range efun
  have hRsep :
      ∀ f ∈ R, ∀ g ∈ R, f ≠ g → 1 ≤ dist f g := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    have hab' : (a : ℂ) ≠ b := by
      intro h
      apply hab
      apply congrArg efun
      exact Subtype.ext h
    simpa [dist_eq_norm] using
      one_le_norm_sub_of_distinct_eigenvalues
        T q a b a.property.1 b.property.1 hab'
        (efun a) (efun b)
        (hefun_spec a).1 (hefun_spec b).1
        (hefun_spec a).2 (hefun_spec b).2
  have hRcount : R.Countable :=
    countable_of_one_le_dist R hRsep
  letI : Countable R := Set.countable_coe_iff.mpr hRcount
  let e : S ↪ R :=
    ⟨fun a => ⟨efun a, ⟨a, rfl⟩⟩,
      fun a b hab => hefun_injective (congrArg Subtype.val hab)⟩
  change S.Countable
  exact Set.countable_coe_iff.mp e.countable

/-- A continuous family of normalized continuous eigenvalues parametrized by
a connected space is constant. -/
theorem continuous_normalizedEigenvalue_family_constant
    {A : Type u} {Y : Type u}
    [TopologicalSpace A] [ConnectedSpace A]
    [TopologicalSpace Y] [CompactSpace Y]
    [T2Space Y] [SecondCountableTopology Y]
    (T : Y → Y) (q : Y) (lam : A → ℂ)
    (hlam : Continuous lam)
    (heigen :
      ∀ a, IsNormalizedContinuousEigenvalue T q (lam a)) :
    ∀ a b, lam a = lam b := by
  apply
    Chapter02.ConnectedCountableRange.eq_of_continuous_of_countable_range
      lam hlam
  apply
    (countable_normalizedContinuousEigenvalues T q).mono
  rintro z ⟨a, rfl⟩
  exact heigen a

end Chapter02.MinimalContinuousEigenfunction
