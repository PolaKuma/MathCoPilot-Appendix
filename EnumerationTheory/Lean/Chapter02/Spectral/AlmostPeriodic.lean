import Chapter02.Spectral.SpectralMeasureType

open Classical MeasureTheory Filter Topology
open scoped BigOperators ComplexOrder ENNReal

noncomputable section

namespace Chapter02.AlmostPeriodic

universe u

lemma unitary_iterate_norm (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : D.H) (n : ℕ) : ‖(D.U^[n]) x‖ = ‖x‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', hD.2, ih]

lemma unitary_iterate_sub_norm (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x y : D.H) (n : ℕ) :
    ‖(D.U^[n]) x - (D.U^[n]) y‖ = ‖x - y‖ := by
  have hiter (z : D.H) : (D.U ^ n) z = (D.U^[n]) z := by
    rw [ContinuousLinearMap.coe_pow]
  rw [← hiter, ← hiter, ← map_sub]
  rw [hiter]
  exact unitary_iterate_norm D hD (x - y) n

lemma iterate_finset_sum (D : HilbertOperatorData.{u}) (n : ℕ)
    {ι : Type*} (s : Finset ι) (f : ι → D.H) :
    (D.U^[n]) (∑ i ∈ s, f i) = ∑ i ∈ s, (D.U^[n]) (f i) := by
  have hiter (z : D.H) : (D.U ^ n) z = (D.U^[n]) z := by
    rw [ContinuousLinearMap.coe_pow]
  rw [← hiter, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hiter]

noncomputable def eigenvalueOf (D : HilbertOperatorData.{u})
    (y : D.H) (hy : IsEigenvector D y) : ℂ := hy.2.choose

lemma eigenvalueOf_spec (D : HilbertOperatorData.{u})
    (y : D.H) (hy : IsEigenvector D y) :
    D.U y = eigenvalueOf D y hy • y := hy.2.choose_spec

lemma eigenvalueOf_norm (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (y : D.H) (hy : IsEigenvector D y) : ‖eigenvalueOf D y hy‖ = 1 := by
  have heq : ‖y‖ = ‖eigenvalueOf D y hy‖ * ‖y‖ := by
    calc
      ‖y‖ = ‖D.U y‖ := (hD.2 y).symm
      _ = ‖eigenvalueOf D y hy • y‖ := by rw [eigenvalueOf_spec]
      _ = _ := norm_smul _ _
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy.1
  nlinarith

noncomputable def eigenCircle (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (y : D.H) (hy : IsEigenvector D y) : Circle :=
  ⟨eigenvalueOf D y hy,
    mem_sphere_zero_iff_norm.mpr (eigenvalueOf_norm D hD y hy)⟩

lemma finiteEigenCombination_almostPeriodic (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (s : Finset D.H)
    (hs : ∀ y ∈ s, IsEigenvector D y) (c : D.H → ℂ) :
    IsAlmostPeriodicVector D (∑ y ∈ s, c y • y) := by
  let e : (y : s) → Circle := fun y =>
    eigenCircle D hD y.1 (hs y.1 y.2)
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
    rw [iterate_finset_sum]
    dsimp [Φ]
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro y hy
    have hiter (v : D.H) : (D.U ^ n) v = (D.U^[n]) v := by
      rw [ContinuousLinearMap.coe_pow]
    rw [← hiter, map_smul, hiter]
    rw [SpectralPointMass.eigen_iterate D y.1
      (eigenvalueOf D y.1 (hs y.1 y.2))
      (eigenvalueOf_spec D y.1 (hs y.1 y.2))]
    simp only [smul_smul]
    change (c y.1 * eigenvalueOf D y.1 (hs y.1 y.2) ^ n) • y.1 =
      (eigenvalueOf D y.1 (hs y.1 y.2) ^ n * c y.1) • y.1
    rw [mul_comm]
  have hmem : Φ (fun y => e y ^ n) ∈ Set.range Φ := ⟨_, rfl⟩
  have hcover := htcover hmem
  simp only [Set.mem_iUnion, Metric.mem_ball] at hcover
  obtain ⟨y, hyt, hdist⟩ := hcover
  refine ⟨y, (Set.Finite.mem_toFinset htfin).2 hyt, ?_⟩
  simpa [horbit, dist_eq_norm] using hdist

lemma discrete_implies_almostPeriodic (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : D.H) (hx : InDiscreteSpectralSubspace D x) :
    IsAlmostPeriodicVector D x := by
  intro ε hε
  obtain ⟨s, hs, c, hxc⟩ := hx (ε / 3) (by positivity)
  let z : D.H := ∑ y ∈ s, c y • y
  obtain ⟨F, hF⟩ := finiteEigenCombination_almostPeriodic D hD s hs c
    (ε / 3) (by positivity)
  refine ⟨F, ?_⟩
  intro n
  obtain ⟨y, hyF, hzy⟩ := hF n
  refine ⟨y, hyF, ?_⟩
  calc
    ‖(D.U^[n]) x - y‖ =
        ‖((D.U^[n]) x - (D.U^[n]) z) + ((D.U^[n]) z - y)‖ := by
      congr 1
      abel
    _ ≤
        ‖(D.U^[n]) x - (D.U^[n]) z‖ + ‖(D.U^[n]) z - y‖ :=
      norm_add_le _ _
    _ = ‖x - z‖ + ‖(D.U^[n]) z - y‖ := by
      rw [unitary_iterate_sub_norm D hD]
    _ < ε / 3 + ε / 3 := add_lt_add hxc hzy
    _ < ε := by linarith

lemma iterate_add (D : HilbertOperatorData.{u}) (n : ℕ) (x y : D.H) :
    (D.U^[n]) (x + y) = (D.U^[n]) x + (D.U^[n]) y := by
  have hiter (z : D.H) : (D.U ^ n) z = (D.U^[n]) z := by
    rw [ContinuousLinearMap.coe_pow]
  rw [← hiter, map_add, hiter, hiter]

lemma iterate_smul (D : HilbertOperatorData.{u}) (n : ℕ) (c : ℂ) (x : D.H) :
    (D.U^[n]) (c • x) = c • (D.U^[n]) x := by
  have hiter (z : D.H) : (D.U ^ n) z = (D.U^[n]) z := by
    rw [ContinuousLinearMap.coe_pow]
  rw [← hiter, map_smul, hiter]

lemma almostPeriodic_zero (D : HilbertOperatorData.{u}) :
    IsAlmostPeriodicVector D 0 := by
  intro ε hε
  refine ⟨{0}, fun n => ⟨0, by simp, ?_⟩⟩
  simp [hε]

lemma almostPeriodic_linear (D : HilbertOperatorData.{u})
    (x y : D.H) (hx : IsAlmostPeriodicVector D x)
    (hy : IsAlmostPeriodicVector D y) (a b : ℂ) :
    IsAlmostPeriodicVector D (a • x + b • y) := by
  intro ε hε
  let C : ℝ := ‖a‖ + ‖b‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let δ : ℝ := ε / (2 * C)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨Fx, hFx⟩ := hx δ hδ
  obtain ⟨Fy, hFy⟩ := hy δ hδ
  let F : Finset D.H := (Fx.product Fy).image fun p => a • p.1 + b • p.2
  refine ⟨F, ?_⟩
  intro n
  obtain ⟨vx, hvx, hdx⟩ := hFx n
  obtain ⟨vy, hvy, hdy⟩ := hFy n
  refine ⟨a • vx + b • vy, Finset.mem_image.mpr
    ⟨(vx, vy), Finset.mem_product.mpr ⟨hvx, hvy⟩, rfl⟩, ?_⟩
  rw [iterate_add, iterate_smul, iterate_smul]
  have hdecomp :
      a • (D.U^[n]) x + b • (D.U^[n]) y - (a • vx + b • vy) =
        a • ((D.U^[n]) x - vx) + b • ((D.U^[n]) y - vy) := by
    module
  rw [hdecomp]
  calc
    ‖a • ((D.U^[n]) x - vx) + b • ((D.U^[n]) y - vy)‖ ≤
        ‖a‖ * ‖(D.U^[n]) x - vx‖ + ‖b‖ * ‖(D.U^[n]) y - vy‖ := by
      simpa [norm_smul] using norm_add_le
        (a • ((D.U^[n]) x - vx)) (b • ((D.U^[n]) y - vy))
    _ ≤ ‖a‖ * δ + ‖b‖ * δ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hdx.le (norm_nonneg a))
        (mul_le_mul_of_nonneg_left hdy.le (norm_nonneg b))
    _ < ε := by
      dsimp [δ, C]
      have hnon : 0 ≤ ‖a‖ + ‖b‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
      calc
        ‖a‖ * (ε / (2 * (‖a‖ + ‖b‖ + 1))) +
            ‖b‖ * (ε / (2 * (‖a‖ + ‖b‖ + 1))) =
          ε * ((‖a‖ + ‖b‖) / (2 * (‖a‖ + ‖b‖ + 1))) := by ring
        _ < ε * 1 := by
          apply mul_lt_mul_of_pos_left _ hε
          apply (div_lt_one (by positivity)).2
          nlinarith [norm_nonneg a, norm_nonneg b]
        _ = ε := mul_one _

lemma almostPeriodic_closed (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (xseq : ℕ → D.H) (hxseq : ∀ n, IsAlmostPeriodicVector D (xseq n))
    (x : D.H) (hx : Tendsto xseq atTop (nhds x)) :
    IsAlmostPeriodicVector D x := by
  intro ε hε
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
      rw [unitary_iterate_sub_norm D hD]
    _ < ε / 3 + ε / 3 := by
      apply add_lt_add _ hNy
      simpa [norm_sub_rev] using hNx
    _ < ε := by linarith

lemma almostPeriodic_iff_map (D : HilbertOperatorData.{u}) (x : D.H) :
    IsAlmostPeriodicVector D x ↔ IsAlmostPeriodicVector D (D.U x) := by
  constructor
  · intro hx ε hε
    obtain ⟨F, hF⟩ := hx ε hε
    refine ⟨F, fun n => ?_⟩
    simpa [Function.iterate_succ_apply] using hF (n + 1)
  · intro hUx ε hε
    obtain ⟨F, hF⟩ := hUx ε hε
    refine ⟨insert x F, ?_⟩
    intro n
    cases n with
    | zero => exact ⟨x, by simp, by simpa using hε⟩
    | succ n =>
        obtain ⟨y, hyF, hy⟩ := hF n
        exact ⟨y, Finset.mem_insert_of_mem hyF, by
          simpa [Function.iterate_succ_apply] using hy⟩

lemma almostPeriodic_reducing (D : HilbertOperatorData.{u}) (hD : IsUnitary D) :
    IsClosedReducingSubspace D {x | IsAlmostPeriodicVector D x} := by
  refine ⟨almostPeriodic_zero D, ?_, ?_, ?_⟩
  · intro x hx y hy a b
    exact almostPeriodic_linear D x y hx hy a b
  · intro xseq hxseq x hx
    exact almostPeriodic_closed D hD xseq hxseq x hx
  · intro x
    exact almostPeriodic_iff_map D x

lemma cyclic_of_almostPeriodic (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x y : D.H) (hx : IsAlmostPeriodicVector D x)
    (hy : InCyclicSubspace D x y) : IsAlmostPeriodicVector D y := by
  exact hy {z | IsAlmostPeriodicVector D z} (almostPeriodic_reducing D hD) hx

lemma almostPeriodic_orbit_net (D : HilbertOperatorData.{u}) (x : D.H)
    (hx : IsAlmostPeriodicVector D x) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Finset ℕ, K.Nonempty ∧
      ∀ n : ℕ, ∃ k ∈ K, ‖(D.U^[n]) x - (D.U^[k]) x‖ < 2 * ε := by
  obtain ⟨F, hF⟩ := hx ε hε
  let Used : D.H → Prop := fun y => ∃ k : ℕ, ‖(D.U^[k]) x - y‖ < ε
  let idx : D.H → ℕ := fun y => if h : Used y then h.choose else 0
  let K : Finset ℕ := F.image idx
  have hused_idx {y : D.H} (hy : Used y) :
      ‖(D.U^[idx y]) x - y‖ < ε := by
    dsimp [idx]
    rw [dif_pos hy]
    exact hy.choose_spec
  have hKnon : K.Nonempty := by
    obtain ⟨y, hyF, hy⟩ := hF 0
    exact ⟨idx y, Finset.mem_image.mpr ⟨y, hyF, rfl⟩⟩
  refine ⟨K, hKnon, ?_⟩
  intro n
  obtain ⟨y, hyF, hny⟩ := hF n
  have hyused : Used y := ⟨n, hny⟩
  refine ⟨idx y, Finset.mem_image.mpr ⟨y, hyF, rfl⟩, ?_⟩
  calc
    ‖(D.U^[n]) x - (D.U^[idx y]) x‖ =
        ‖((D.U^[n]) x - y) + (y - (D.U^[idx y]) x)‖ := by
      congr 1
      abel
    _ ≤ ‖(D.U^[n]) x - y‖ + ‖y - (D.U^[idx y]) x‖ := norm_add_le _ _
    _ < ε + ε := add_lt_add hny (by
      simpa [norm_sub_rev] using hused_idx hyused)
    _ = 2 * ε := by ring

lemma norm_inner_iterate_shift (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : D.H) (n k : ℕ) (hk : k ≤ n) :
    ‖@inner ℂ D.H _ ((D.U^[n]) x) ((D.U^[k]) x)‖ =
      ‖@inner ℂ D.H _ ((D.U^[n - k]) x) x‖ := by
  let V := SpectralMeasure.unitaryEquiv D hD
  have hit (m : ℕ) : (V ^ m) x = (D.U^[m]) x := by
    simpa [V] using SpectralMeasure.unitaryEquiv_zpow_nat D hD x m
  have hpow : V ^ n = V ^ k * V ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  calc
    ‖@inner ℂ D.H _ ((D.U^[n]) x) ((D.U^[k]) x)‖ =
        ‖@inner ℂ D.H _ ((D.U^[k]) x) ((D.U^[n]) x)‖ := norm_inner_symm _ _
    _ = ‖@inner ℂ D.H _ ((V ^ k) x) ((V ^ k) ((V ^ (n - k)) x))‖ := by
      rw [hit]
      congr 2
      calc
        (D.U^[n]) x = (V ^ n) x := (hit n).symm
        _ = ((V ^ k) * (V ^ (n - k))) x := congrArg (fun W => W x) hpow
        _ = (V ^ k) ((V ^ (n - k)) x) := rfl
    _ = ‖@inner ℂ D.H _ x ((V ^ (n - k)) x)‖ := by
      rw [(V ^ k).inner_map_map]
    _ = ‖@inner ℂ D.H _ ((V ^ (n - k)) x) x‖ := norm_inner_symm _ _
    _ = ‖@inner ℂ D.H _ ((D.U^[n - k]) x) x‖ := by rw [hit]

lemma sum_backward_shift (a : ℕ → ℝ) (k N : ℕ) :
    (∑ n ∈ Finset.range N, if k ≤ n then a (n - k) else 0) =
      ∑ r ∈ Finset.range (N - k), a r := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      by_cases hk : k ≤ N
      · rw [if_pos hk]
        have hsub : N + 1 - k = (N - k) + 1 := by omega
        rw [hsub, Finset.sum_range_succ, ih]
      · have hNk : N < k := Nat.lt_of_not_ge hk
        have hsub : N + 1 - k = 0 := Nat.sub_eq_zero_of_le (Nat.succ_le_iff.mpr hNk)
        rw [if_neg hk, add_zero, hsub]
        simpa [Nat.sub_eq_zero_of_le hNk.le] using ih

lemma cesaroTendsTo_add_real {a b : ℕ → ℝ}
    (ha : cesaroTendsTo a 0) (hb : cesaroTendsTo b 0) :
    cesaroTendsTo (fun n => a n + b n) 0 := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at ha hb ⊢
  have h := ha.add hb
  convert h using 1
  · funext N
    rw [Finset.sum_add_distrib]
    ring
  · simp

lemma cesaro_backward_shift {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hzero : cesaroTendsTo a 0) (k : ℕ) :
    cesaroTendsTo (fun n => if k ≤ n then a (n - k) else 0) 0 := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at hzero ⊢
  apply squeeze_zero
    (f := fun N => (((N + 1 : ℕ) : ℝ)⁻¹ *
      ∑ n ∈ Finset.range (N + 1), if k ≤ n then a (n - k) else 0))
    (g := fun N => (((N + 1 : ℕ) : ℝ)⁻¹ *
      ∑ n ∈ Finset.range (N + 1), a n))
  · intro N
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact ha _
    · exact le_rfl
  · intro N
    rw [sum_backward_shift]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.sub_le (N + 1) k)) (fun i _ _ => ha i)
  · exact hzero

lemma cesaro_finset_backward_sum {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hzero : cesaroTendsTo a 0) (K : Finset ℕ) :
    cesaroTendsTo
      (fun n => ∑ k ∈ K, if k ≤ n then a (n - k) else 0) 0 := by
  induction K using Finset.induction with
  | empty =>
      simpa using (show cesaroTendsTo (fun _ : ℕ => (0 : ℝ)) 0 by
        unfold cesaroTendsTo seqTendsTo cesaroAverage
        simp)
  | @insert k K hk ih =>
      simp only [Finset.sum_insert hk]
      exact cesaroTendsTo_add_real (cesaro_backward_shift ha hzero k) ih

set_option maxHeartbeats 800000 in
lemma continuous_almostPeriodic_eq_zero (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : D.H)
    (hxcont : InContinuousSpectralSubspace D x)
    (hxap : IsAlmostPeriodicVector D x) : x = 0 := by
  by_contra hx0
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let a : ℕ → ℝ := fun n =>
    ‖@inner ℂ D.H _ ((D.U^[n]) x) x‖ ^ 2
  have ha : ∀ n, 0 ≤ a n := fun n => sq_nonneg _
  have ha0 : cesaroTendsTo a 0 := by
    have hw := (SpectralWiener.wienerTheorem D hD x).mp hxcont
    unfold cesaroTendsTo seqTendsTo cesaroAverage
    have hcomp := hw.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun N : ℕ => if N + 1 = 0 then 0 else
      (((N + 1 : ℕ) : ℝ)⁻¹) * ∑ n ∈ Finset.range (N + 1), a n)
      atTop (nhds 0) at hcomp
    simpa [a] using hcomp
  let δ : ℝ := ‖x‖ / 8
  obtain ⟨K, hKnon, hK⟩ := almostPeriodic_orbit_net D x hxap δ (by
    dsimp [δ]
    positivity)
  let L : ℕ := K.max' hKnon
  have hkL {k : ℕ} (hk : k ∈ K) : k ≤ L := Finset.le_max' K k hk
  let b : ℕ → ℝ := fun n =>
    ∑ k ∈ K, if k ≤ n then a (n - k) else 0
  let c : ℝ := ‖x‖ ^ 4 / 4
  have hc : 0 < c := by dsimp [c]; positivity
  have hbnonneg : ∀ n, 0 ≤ b n := by
    intro n
    dsimp [b]
    apply Finset.sum_nonneg
    intro k hk
    split_ifs
    · exact ha _
    · exact le_rfl
  have hblarge : ∀ n, L ≤ n → c ≤ b n := by
    intro n hn
    obtain ⟨k, hkK, hdist⟩ := hK n
    have hkn : k ≤ n := (hkL hkK).trans hn
    have hdiff :
        ‖@inner ℂ D.H _ ((D.U^[n]) x) ((D.U^[k]) x) -
          @inner ℂ D.H _ ((D.U^[k]) x) ((D.U^[k]) x)‖ < ‖x‖ ^ 2 / 4 := by
      calc
        _ = ‖@inner ℂ D.H _ ((D.U^[n]) x - (D.U^[k]) x)
            ((D.U^[k]) x)‖ := by rw [inner_sub_left]
        _ ≤ ‖(D.U^[n]) x - (D.U^[k]) x‖ * ‖(D.U^[k]) x‖ :=
          norm_inner_le_norm _ _
        _ < (2 * δ) * ‖(D.U^[k]) x‖ :=
          mul_lt_mul_of_pos_right hdist (by
            rw [unitary_iterate_norm D hD]
            exact hxnorm)
        _ = ‖x‖ ^ 2 / 4 := by
          rw [unitary_iterate_norm D hD]
          dsimp [δ]
          ring
    have hself :
        ‖@inner ℂ D.H _ ((D.U^[k]) x) ((D.U^[k]) x)‖ = ‖x‖ ^ 2 := by
      let v := (D.U^[k]) x
      have hi : @inner ℂ D.H _ v v = (‖v‖ ^ 2 : ℂ) := by
        apply Complex.ext
        · simp
        · simp
      rw [hi]
      simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg v)]
      rw [unitary_iterate_norm D hD]
    have hcross :
        3 * (‖x‖ ^ 2) / 4 <
          ‖@inner ℂ D.H _ ((D.U^[n]) x) ((D.U^[k]) x)‖ := by
      have htri :
          ‖@inner ℂ D.H _ ((D.U^[k]) x) ((D.U^[k]) x)‖ ≤
            ‖@inner ℂ D.H _ ((D.U^[n]) x) ((D.U^[k]) x) -
              @inner ℂ D.H _ ((D.U^[k]) x) ((D.U^[k]) x)‖ +
            ‖@inner ℂ D.H _ ((D.U^[n]) x) ((D.U^[k]) x)‖ := by
        calc
          _ = ‖(@inner ℂ D.H _ ((D.U^[k]) x) ((D.U^[k]) x) -
                @inner ℂ D.H _ ((D.U^[n]) x) ((D.U^[k]) x)) +
              @inner ℂ D.H _ ((D.U^[n]) x) ((D.U^[k]) x)‖ := by
            congr 1
            ring
          _ ≤ ‖@inner ℂ D.H _ ((D.U^[k]) x) ((D.U^[k]) x) -
                @inner ℂ D.H _ ((D.U^[n]) x) ((D.U^[k]) x)‖ + _ :=
            norm_add_le _ _
          _ = _ := by rw [norm_sub_rev]
      rw [hself] at htri
      nlinarith
    have hshift := norm_inner_iterate_shift D hD x n k hkn
    have haterm : c ≤ a (n - k) := by
      dsimp [a, c]
      rw [← hshift]
      have hcross0 := norm_nonneg
        (@inner ℂ D.H _ ((D.U^[n]) x) ((D.U^[k]) x))
      nlinarith [sq_nonneg (‖x‖ ^ 2)]
    have hsingle :
        (if k ≤ n then a (n - k) else 0) ≤ b n := by
      dsimp [b]
      exact Finset.single_le_sum
        (f := fun j => if j ≤ n then a (n - j) else 0)
        (fun j hj => by
          change 0 ≤ if j ≤ n then a (n - j) else 0
          by_cases hjn : j ≤ n
          · rw [if_pos hjn]
            exact ha _
          · rw [if_neg hjn]) hkK
    rw [if_pos hkn] at hsingle
    exact haterm.trans hsingle
  have hb0 : cesaroTendsTo b 0 := by
    exact cesaro_finset_backward_sum ha ha0 K
  unfold cesaroTendsTo seqTendsTo cesaroAverage at hb0
  obtain ⟨N₀, hN₀dist⟩ :=
    (Metric.tendsto_atTop.1 hb0) (c / 4) (by positivity)
  have hN₀ : ∀ N ≥ N₀,
      (((N + 1 : ℕ) : ℝ)⁻¹) * ∑ n ∈ Finset.range (N + 1), b n < c / 4 := by
    intro N hN
    have hdist := hN₀dist N hN
    rw [Real.dist_eq] at hdist
    rw [sub_zero] at hdist
    exact (abs_lt.mp hdist).2
  let N : ℕ := max N₀ (2 * L)
  have hN0 : N₀ ≤ N := le_max_left _ _
  have hNL : 2 * L ≤ N := le_max_right _ _
  have hLN : L ≤ N := by omega
  have hsmallN := hN₀ N hN0
  have hsubset : Finset.Icc L N ⊆ Finset.range (N + 1) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  have hsumlower : ((Finset.Icc L N).card : ℝ) * c ≤
      ∑ n ∈ Finset.range (N + 1), b n := by
    calc
      ((Finset.Icc L N).card : ℝ) * c = ∑ _n ∈ Finset.Icc L N, c := by simp
      _ ≤ ∑ n ∈ Finset.Icc L N, b n := by
        exact Finset.sum_le_sum fun n hn => hblarge n (Finset.mem_Icc.mp hn).1
      _ ≤ ∑ n ∈ Finset.range (N + 1), b n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun n _ _ => hbnonneg n)
  have hcard : ((N + 1 : ℕ) : ℝ) / 2 ≤ (Finset.Icc L N).card := by
    have hcardNat : N + 1 ≤ 2 * (Finset.Icc L N).card := by
      rw [Nat.card_Icc]
      omega
    have hcardReal : ((N + 1 : ℕ) : ℝ) ≤
        2 * ((Finset.Icc L N).card : ℝ) := by exact_mod_cast hcardNat
    linarith
  have havglower : c / 2 ≤
      (((N + 1 : ℕ) : ℝ)⁻¹) * ∑ n ∈ Finset.range (N + 1), b n := by
    have hq : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
    rw [show (((N + 1 : ℕ) : ℝ)⁻¹) *
        ∑ n ∈ Finset.range (N + 1), b n =
      (∑ n ∈ Finset.range (N + 1), b n) / ((N + 1 : ℕ) : ℝ) by
        rw [div_eq_mul_inv, mul_comm]]
    apply (le_div_iff₀ hq).2
    calc
      c / 2 * ((N + 1 : ℕ) : ℝ) ≤
          ((Finset.Icc L N).card : ℝ) * c := by
        nlinarith
      _ ≤ _ := hsumlower
  nlinarith

lemma almostPeriodic_implies_discrete (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : D.H) (hx : IsAlmostPeriodicVector D x) :
    InDiscreteSpectralSubspace D x := by
  by_cases hx0 : x = 0
  · subst x
    intro ε hε
    exact ⟨∅, by simp, fun _ => 0, by simpa using hε⟩
  obtain ⟨μ, hμz, _⟩ := Herglotz.herglotz
    (SpectralMeasure.vectorCorrelation D hD x)
    (SpectralMeasure.vectorCorrelation_positiveDefinite D hD x)
  have hμ : HasSpectralMeasure D x μ := by
    intro n
    rw [hμz (n : ℤ)]
    exact congrArg (fun v : D.H => @inner ℂ D.H _ x v)
      (SpectralMeasure.unitaryEquiv_zpow_nat D hD x n)
  let C : Set Circle := (SpectralMeasureType.atomSet μ)ᶜ
  have hC : MeasurableSet C := (SpectralMeasureType.atomSet_measurable μ).compl
  let f : Circle → ℂ := C.indicator (fun _ => 1)
  have hf : MemLp f 2 μ.μ :=
    memLp_indicator_const 2 hC 1 (Or.inr (measure_ne_top μ.μ C))
  let F : Lp ℂ 2 μ.μ := hf.toLp f
  let y : D.H := CyclicSpectralModel.cyclicCLM D hD x μ F
  let ν : CircleMeasureData := CyclicMeasureType.vectorDensityMeasure F
  have hν : HasSpectralMeasure D y ν := by
    intro n
    exact CyclicMeasureType.vectorDensityMeasure_moment D hD x μ hμz F n
  have hdensity : CyclicMeasureType.spectralDensity F =ᵐ[μ.μ]
      C.indicator (fun _ => (1 : ENNReal)) := by
    filter_upwards [hf.coeFn_toLp] with w hw
    by_cases hwC : w ∈ C <;>
      simp [CyclicMeasureType.spectralDensity, F, f, hw, hwC]
  have hνmeasure : ν.μ = (SpectralMeasureType.continuousPart μ).μ := by
    change μ.μ.withDensity (CyclicMeasureType.spectralDensity F) = μ.μ.restrict C
    rw [withDensity_congr_ae hdensity]
    simpa only [Pi.one_apply] using (withDensity_indicator_one (μ := μ.μ) hC)
  have hνcont : IsContinuousCircleMeasure ν := by
    intro z
    rw [hνmeasure]
    exact SpectralMeasureType.continuousPart_isContinuous μ z
  have hycont : InContinuousSpectralSubspace D y :=
    SpectralWiener.continuous_measure_implies_continuous_subspace
      D hD y ν hν hνcont
  have hycyclic : InCyclicSubspace D x y :=
    (CyclicSpectralModel.inCyclicSubspace_iff_range D hD x y μ hμz).2 ⟨F, rfl⟩
  have hyap : IsAlmostPeriodicVector D y :=
    cyclic_of_almostPeriodic D hD x y hx hycyclic
  have hy0 : y = 0 := continuous_almostPeriodic_eq_zero D hD y hycont hyap
  have hF0 : F = 0 := by
    apply norm_eq_zero.mp
    rw [← CyclicSpectralModel.cyclicCLM_norm D hD x μ hμz]
    change ‖y‖ = 0
    rw [hy0, norm_zero]
  have hFcoe0 : (fun w => F w) =ᵐ[μ.μ] 0 := by
    rw [hF0]
    exact Lp.coeFn_zero ℂ 2 μ.μ
  have hμC : μ.μ C = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hf.coeFn_toLp, hFcoe0] with w hwF hw0
    intro hwC
    have hfw0 : f w = 0 := by
      rw [← hwF]
      exact hw0
    rw [show f w = 1 by simp [f, hwC]] at hfw0
    exact one_ne_zero hfw0
  have hdisc : IsDiscreteCircleMeasure μ :=
    SpectralMeasureType.discreteMeasure_of_compl_atomSet_zero μ hμC
  exact ((SpectralMeasureType.spectralSubspaceMeasureType D hD x hx0 μ hμ).1).2 hdisc

theorem almostPeriodicVector (D : HilbertOperatorData.{u}) :
    AlmostPeriodicVectorStatement D := by
  intro hD x
  exact ⟨almostPeriodic_implies_discrete D hD x,
    discrete_implies_almostPeriodic D hD x⟩

end Chapter02.AlmostPeriodic
