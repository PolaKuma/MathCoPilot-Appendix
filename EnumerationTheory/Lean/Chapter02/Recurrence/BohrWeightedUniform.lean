import Chapter02.Recurrence.MultipleKhintchineUniform
import Chapter02.Ergodic.VanDerCorputPairLimits

open Classical Filter
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Chapter02.BohrWeightedUniform

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The complex `N + 1` Cesàro convention used for phase-modulated
Hilbert-space correlations. -/
def complexCesaroAverage (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  (((N + 1 : ℕ) : ℂ)⁻¹) *
    ∑ n ∈ Finset.range (N + 1), a n

/-- A pointwise norm bound also bounds every complex Cesàro average. -/
lemma norm_complexCesaroAverage_le
    (a : ℕ → ℂ) (C : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ C) (N : ℕ) :
    ‖complexCesaroAverage a N‖ ≤ C := by
  unfold complexCesaroAverage
  rw [norm_mul]
  calc
    ‖(((N + 1 : ℕ) : ℂ)⁻¹)‖ *
          ‖∑ n ∈ Finset.range (N + 1), a n‖ ≤
        ‖(((N + 1 : ℕ) : ℂ)⁻¹)‖ *
          ∑ n ∈ Finset.range (N + 1), ‖a n‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ ‖(((N + 1 : ℕ) : ℂ)⁻¹)‖ *
          ∑ _n ∈ Finset.range (N + 1), C := by
      gcongr with n hn
      exact ha n
    _ = C := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        norm_inv, Complex.norm_natCast]
      have hN : (0 : ℝ) < N + 1 := by positivity
      rw [inv_mul_eq_div]
      field_simp

/-- Translated-uniform complex Cesàro convergence to zero. -/
def HasUniformComplexCesaroZero (a : ℕ → ℂ) : Prop :=
  ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
    ‖complexCesaroAverage (fun n ↦ a (i + n)) N‖ < ε

/-- The zero scalar sequence has translated-uniform Cesàro mean zero. -/
lemma hasUniformComplexCesaroZero_zero :
    HasUniformComplexCesaroZero (fun _ ↦ 0) := by
  intro ε hε
  filter_upwards
  intro N i
  simpa [complexCesaroAverage] using hε

/-- Translated-uniform complex Cesàro-null sequences are closed under
addition. -/
lemma HasUniformComplexCesaroZero.add
    {a b : ℕ → ℂ}
    (ha : HasUniformComplexCesaroZero a)
    (hb : HasUniformComplexCesaroZero b) :
    HasUniformComplexCesaroZero (fun n ↦ a n + b n) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [ha (ε / 2) hε2, hb (ε / 2) hε2] with N haN hbN
  intro i
  have heq :
      complexCesaroAverage
          (fun n ↦ a (i + n) + b (i + n)) N =
        complexCesaroAverage (fun n ↦ a (i + n)) N +
          complexCesaroAverage (fun n ↦ b (i + n)) N := by
    unfold complexCesaroAverage
    rw [Finset.sum_add_distrib]
    ring
  rw [heq]
  calc
    ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (haN i) (hbN i)
    _ = ε := by ring

/-- Translated-uniform complex Cesàro-null sequences are closed under
multiplication by a fixed complex scalar. -/
lemma HasUniformComplexCesaroZero.const_mul
    {a : ℕ → ℂ}
    (ha : HasUniformComplexCesaroZero a)
    (c : ℂ) :
    HasUniformComplexCesaroZero (fun n ↦ c * a n) := by
  intro ε hε
  let δ : ℝ := ε / (‖c‖ + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  filter_upwards [ha δ hδ] with N hN
  intro i
  have heq :
      complexCesaroAverage (fun n ↦ c * a (i + n)) N =
        c * complexCesaroAverage (fun n ↦ a (i + n)) N := by
    unfold complexCesaroAverage
    rw [← Finset.mul_sum]
    ring
  rw [heq, norm_mul]
  calc
    ‖c‖ * ‖complexCesaroAverage (fun n ↦ a (i + n)) N‖ ≤
        ‖c‖ * δ := by
      exact mul_le_mul_of_nonneg_left (hN i).le (norm_nonneg c)
    _ < (‖c‖ + 1) * δ := by
      exact mul_lt_mul_of_pos_right (by linarith) hδ
    _ = ε := by
      dsimp [δ]
      field_simp

/-- A finite sum of translated-uniform complex Cesàro-null sequences is
again translated-uniform Cesàro-null. -/
lemma hasUniformComplexCesaroZero_finset_sum
    {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℂ)
    (ha : ∀ j ∈ s, HasUniformComplexCesaroZero (a j)) :
    HasUniformComplexCesaroZero (fun n ↦ ∑ j ∈ s, a j n) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using hasUniformComplexCesaroZero_zero
  | @insert j s hj ih =>
      have hjzero : HasUniformComplexCesaroZero (a j) :=
        ha j (by simp)
      have hs :
          HasUniformComplexCesaroZero
            (fun n ↦ ∑ k ∈ s, a k n) :=
        ih (fun k hk ↦ ha k (by simp [hk]))
      simpa [hj] using hjzero.add hs

/-- A finite circle-character polynomial on the natural numbers. -/
def finiteCirclePolynomial
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (phase : ι → Circle)
    (n : ℕ) : ℂ :=
  ∑ j ∈ s, c j * (phase j : ℂ) ^ n

/-- A scalar sequence given exactly by one finite circle-character
polynomial. -/
def IsFiniteCirclePolynomial (p : ℕ → ℂ) : Prop :=
  ∃ (k : ℕ) (c : Fin k → ℂ) (phase : Fin k → Circle),
    ∀ n,
      p n =
        finiteCirclePolynomial (Finset.univ : Finset (Fin k))
          c phase n

/-- The same finite polynomial notation with an arbitrary finite index
type. -/
def fintypeCirclePolynomial
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (phase : ι → Circle)
    (n : ℕ) : ℂ :=
  ∑ j : ι, c j * (phase j : ℂ) ^ n

/-- Every finite-index presentation can be reindexed by `Fin k`. -/
lemma isFiniteCirclePolynomial_fintype
    {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (phase : ι → Circle) :
    IsFiniteCirclePolynomial (fintypeCirclePolynomial c phase) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι,
    (fun j ↦ c (e.symm j)), (fun j ↦ phase (e.symm j)), ?_⟩
  intro n
  unfold fintypeCirclePolynomial finiteCirclePolynomial
  change
    (∑ i : ι, c i * (phase i : ℂ) ^ n) =
      ∑ j : Fin (Fintype.card ι),
        c (e.symm j) * (phase (e.symm j) : ℂ) ^ n
  exact
    (Fintype.sum_equiv e.symm
      (fun j ↦ c (e.symm j) * (phase (e.symm j) : ℂ) ^ n)
      (fun i ↦ c i * (phase i : ℂ) ^ n) (by simp)).symm

/-- Exact finite circle polynomials are closed under addition. -/
lemma IsFiniteCirclePolynomial.add
    {p q : ℕ → ℂ}
    (hp : IsFiniteCirclePolynomial p)
    (hq : IsFiniteCirclePolynomial q) :
    IsFiniteCirclePolynomial (fun n ↦ p n + q n) := by
  classical
  obtain ⟨k, cp, phasep, hpEq⟩ := hp
  obtain ⟨l, cq, phaseq, hqEq⟩ := hq
  let c : Fin k ⊕ Fin l → ℂ := Sum.elim cp cq
  let phase : Fin k ⊕ Fin l → Circle := Sum.elim phasep phaseq
  have hfinite := isFiniteCirclePolynomial_fintype c phase
  convert hfinite using 1
  funext n
  rw [hpEq, hqEq]
  simp [fintypeCirclePolynomial, finiteCirclePolynomial, c, phase]

/-- Exact finite circle polynomials are closed under multiplication. -/
lemma IsFiniteCirclePolynomial.mul
    {p q : ℕ → ℂ}
    (hp : IsFiniteCirclePolynomial p)
    (hq : IsFiniteCirclePolynomial q) :
    IsFiniteCirclePolynomial (fun n ↦ p n * q n) := by
  classical
  obtain ⟨k, cp, phasep, hpEq⟩ := hp
  obtain ⟨l, cq, phaseq, hqEq⟩ := hq
  let c : Fin k × Fin l → ℂ := fun j ↦ cp j.1 * cq j.2
  let phase : Fin k × Fin l → Circle := fun j ↦ phasep j.1 * phaseq j.2
  have hfinite := isFiniteCirclePolynomial_fintype c phase
  convert hfinite using 1
  funext n
  rw [hpEq, hqEq]
  simp only [finiteCirclePolynomial, fintypeCirclePolynomial,
    Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  dsimp [c, phase]
  rw [mul_pow]
  ring

/-- Exact finite circle polynomials are closed under complex conjugation. -/
lemma IsFiniteCirclePolynomial.star
    {p : ℕ → ℂ}
    (hp : IsFiniteCirclePolynomial p) :
    IsFiniteCirclePolynomial (fun n ↦ star (p n)) := by
  classical
  obtain ⟨k, c, phase, hpEq⟩ := hp
  let cs : Fin k → ℂ := fun j ↦ conj (c j)
  let phases : Fin k → Circle :=
    fun j ↦ IsometryWiener.circleConj (phase j)
  have hfinite := isFiniteCirclePolynomial_fintype cs phases
  convert hfinite using 1
  funext n
  rw [hpEq]
  unfold finiteCirclePolynomial fintypeCirclePolynomial
  change
    conj (∑ j : Fin k, c j * (phase j : ℂ) ^ n) =
      ∑ j : Fin k, cs j * (phases j : ℂ) ^ n
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [cs, phases]
  rw [map_mul, map_pow]

/-- Every constant complex sequence is an exact finite circle polynomial. -/
lemma isFiniteCirclePolynomial_const (a : ℂ) :
    IsFiniteCirclePolynomial (fun _ ↦ a) := by
  let c : Fin 1 → ℂ := fun _ ↦ a
  let phase : Fin 1 → Circle := fun _ ↦ 1
  convert isFiniteCirclePolynomial_fintype c phase using 1
  funext n
  simp [fintypeCirclePolynomial, c, phase]

/-- A scalar sequence is Bohr almost periodic when it is uniformly
approximable on `ℕ` by finite circle-character polynomials. -/
def IsUniformLimitOfFiniteCirclePolynomials (w : ℕ → ℂ) : Prop :=
  ∀ δ > 0,
    ∃ p : ℕ → ℂ, IsFiniteCirclePolynomial p ∧
      ∀ n, ‖w n - p n‖ < δ

/-- An exact finite circle polynomial is, tautologically, a uniform limit
of such polynomials. -/
lemma IsFiniteCirclePolynomial.isUniformLimit
    {p : ℕ → ℂ} (hp : IsFiniteCirclePolynomial p) :
    IsUniformLimitOfFiniteCirclePolynomials p := by
  intro δ hδ
  exact ⟨p, hp, fun n ↦ by simpa using hδ⟩

/-- Every uniformly approximable circle-polynomial sequence is globally
bounded. -/
lemma IsUniformLimitOfFiniteCirclePolynomials.bounded
    {w : ℕ → ℂ}
    (hw : IsUniformLimitOfFiniteCirclePolynomials w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖w n‖ ≤ C := by
  obtain ⟨p, hp, hwp⟩ := hw 1 (by norm_num)
  obtain ⟨k, c, phase, hpEq⟩ := hp
  let C : ℝ := 1 + ∑ j : Fin k, ‖c j‖
  refine ⟨C, by positivity, ?_⟩
  intro n
  calc
    ‖w n‖ = ‖(w n - p n) + p n‖ := by rw [sub_add_cancel]
    _ ≤ ‖w n - p n‖ + ‖p n‖ := norm_add_le _ _
    _ ≤ 1 + ∑ j : Fin k, ‖c j‖ := by
      have hpNorm :
          ‖p n‖ ≤ ∑ j : Fin k, ‖c j‖ := by
        rw [hpEq]
        unfold finiteCirclePolynomial
        calc
          ‖∑ j : Fin k, c j * (phase j : ℂ) ^ n‖ ≤
              ∑ j : Fin k, ‖c j * (phase j : ℂ) ^ n‖ :=
            norm_sum_le _ _
          _ = ∑ j : Fin k, ‖c j‖ := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [norm_mul, norm_pow, Circle.norm_coe, one_pow, mul_one]
      linarith [hwp n]
    _ = C := rfl

/-- Uniform limits of finite circle polynomials are closed under
addition. -/
lemma IsUniformLimitOfFiniteCirclePolynomials.add
    {p q : ℕ → ℂ}
    (hp : IsUniformLimitOfFiniteCirclePolynomials p)
    (hq : IsUniformLimitOfFiniteCirclePolynomials q) :
    IsUniformLimitOfFiniteCirclePolynomials (fun n ↦ p n + q n) := by
  intro δ hδ
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨P, hPfinite, hP⟩ := hp (δ / 2) hδ2
  obtain ⟨Q, hQfinite, hQ⟩ := hq (δ / 2) hδ2
  refine ⟨fun n ↦ P n + Q n, hPfinite.add hQfinite, ?_⟩
  intro n
  calc
    ‖p n + q n - (P n + Q n)‖ =
        ‖(p n - P n) + (q n - Q n)‖ := by ring_nf
    _ ≤ ‖p n - P n‖ + ‖q n - Q n‖ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := add_lt_add (hP n) (hQ n)
    _ = δ := by ring

/-- Uniform limits of finite circle polynomials are closed under complex
conjugation. -/
lemma IsUniformLimitOfFiniteCirclePolynomials.star
    {p : ℕ → ℂ}
    (hp : IsUniformLimitOfFiniteCirclePolynomials p) :
    IsUniformLimitOfFiniteCirclePolynomials (fun n ↦ conj (p n)) := by
  intro δ hδ
  obtain ⟨P, hPfinite, hP⟩ := hp δ hδ
  refine ⟨fun n ↦ conj (P n), hPfinite.star, ?_⟩
  intro n
  have heq :
      conj (p n) - conj (P n) = conj (p n - P n) := by
    rw [map_sub]
  rw [heq]
  change ‖Star.star (p n - P n)‖ < δ
  rw [norm_star]
  exact hP n

/-- Uniform limits of finite circle polynomials are closed under pointwise
multiplication. -/
lemma IsUniformLimitOfFiniteCirclePolynomials.mul
    {p q : ℕ → ℂ}
    (hp : IsUniformLimitOfFiniteCirclePolynomials p)
    (hq : IsUniformLimitOfFiniteCirclePolynomials q) :
    IsUniformLimitOfFiniteCirclePolynomials (fun n ↦ p n * q n) := by
  obtain ⟨Cp, hCp, hpBound⟩ := hp.bounded
  obtain ⟨Cq, hCq, hqBound⟩ := hq.bounded
  intro ε hε
  let S : ℝ := Cp + Cq + 2
  have hS : 0 < S := by
    dsimp [S]
    linarith
  let δ : ℝ := min 1 (ε / (2 * S))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (div_pos hε (by positivity))
  have hδone : δ ≤ 1 := min_le_left _ _
  have hδS : δ * S ≤ ε / 2 := by
    calc
      δ * S ≤ (ε / (2 * S)) * S := by
        exact mul_le_mul_of_nonneg_right (min_le_right _ _) hS.le
      _ = ε / 2 := by field_simp
  obtain ⟨P, hPfinite, hP⟩ := hp δ hδ
  obtain ⟨Q, hQfinite, hQ⟩ := hq δ hδ
  refine ⟨fun n ↦ P n * Q n, hPfinite.mul hQfinite, ?_⟩
  intro n
  have hPbound : ‖P n‖ ≤ Cp + 1 := by
    calc
      ‖P n‖ = ‖(P n - p n) + p n‖ := by rw [sub_add_cancel]
      _ ≤ ‖P n - p n‖ + ‖p n‖ := norm_add_le _ _
      _ ≤ δ + Cp := by
        exact add_le_add (by simpa [norm_sub_rev] using (hP n).le)
          (hpBound n)
      _ ≤ Cp + 1 := by linarith
  have hprod :
      ‖p n * q n - P n * Q n‖ ≤ δ * (Cp + Cq + 1) := by
    calc
      ‖p n * q n - P n * Q n‖ =
          ‖(p n - P n) * q n + P n * (q n - Q n)‖ := by
        congr 1
        ring
      _ ≤ ‖(p n - P n) * q n‖ +
          ‖P n * (q n - Q n)‖ := norm_add_le _ _
      _ = ‖p n - P n‖ * ‖q n‖ +
          ‖P n‖ * ‖q n - Q n‖ := by rw [norm_mul, norm_mul]
      _ ≤ δ * Cq + (Cp + 1) * δ := by
        exact add_le_add
          (mul_le_mul (hP n).le (hqBound n) (norm_nonneg _) hδ.le)
          (mul_le_mul hPbound (hQ n).le (norm_nonneg _) (by positivity))
      _ = δ * (Cp + Cq + 1) := by ring
  calc
    ‖p n * q n - P n * Q n‖ ≤ δ * (Cp + Cq + 1) := hprod
    _ < δ * S := by
      exact mul_lt_mul_of_pos_left (by dsimp [S]; linarith) hδ
    _ ≤ ε / 2 := hδS
    _ < ε := by linarith

/-- Constant scalar sequences are uniformly approximable finite circle
polynomials. -/
lemma isUniformLimitOfFiniteCirclePolynomials_const (c : ℂ) :
    IsUniformLimitOfFiniteCirclePolynomials (fun _ ↦ c) :=
  (isFiniteCirclePolynomial_const c).isUniformLimit

/-- Uniform limits of finite circle polynomials are closed under
multiplication by a constant scalar. -/
lemma IsUniformLimitOfFiniteCirclePolynomials.const_mul
    {p : ℕ → ℂ}
    (hp : IsUniformLimitOfFiniteCirclePolynomials p)
    (c : ℂ) :
    IsUniformLimitOfFiniteCirclePolynomials (fun n ↦ c * p n) := by
  exact (isUniformLimitOfFiniteCirclePolynomials_const c).mul hp

/-- Uniform limits of finite circle polynomials are closed under natural
powers. -/
lemma IsUniformLimitOfFiniteCirclePolynomials.pow
    {p : ℕ → ℂ}
    (hp : IsUniformLimitOfFiniteCirclePolynomials p)
    (k : ℕ) :
    IsUniformLimitOfFiniteCirclePolynomials (fun n ↦ (p n) ^ k) := by
  induction k with
  | zero =>
      simpa using isUniformLimitOfFiniteCirclePolynomials_const 1
  | succ k ih =>
      simpa [pow_succ] using ih.mul hp

/-- Cancellation against every circle character implies cancellation
against every finite circle-character polynomial. -/
lemma hasUniformComplexCesaroZero_finiteCirclePolynomial_mul
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (phase : ι → Circle)
    (e : ℕ → ℂ)
    (he :
      ∀ z : Circle,
        HasUniformComplexCesaroZero
          (fun n ↦ (z : ℂ) ^ n * e n)) :
    HasUniformComplexCesaroZero
      (fun n ↦ finiteCirclePolynomial s c phase n * e n) := by
  classical
  have hs :=
    hasUniformComplexCesaroZero_finset_sum s
      (fun j n ↦ c j * ((phase j : ℂ) ^ n * e n))
      (fun j hj ↦ (he (phase j)).const_mul (c j))
  convert hs using 1
  funext n
  unfold finiteCirclePolynomial
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Character cancellation extends from finite circle polynomials to their
uniform limits, provided the error sequence is uniformly bounded. -/
lemma hasUniformComplexCesaroZero_uniformLimit_weight_mul
    (w e : ℕ → ℂ)
    (hw : IsUniformLimitOfFiniteCirclePolynomials w)
    (C : ℝ) (hC : 0 ≤ C)
    (heBound : ∀ n, ‖e n‖ ≤ C)
    (heChar :
      ∀ z : Circle,
        HasUniformComplexCesaroZero
          (fun n ↦ (z : ℂ) ^ n * e n)) :
    HasUniformComplexCesaroZero (fun n ↦ w n * e n) := by
  intro ε hε
  let δ : ℝ := ε / (2 * (C + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨p, hpFinite, happ⟩ := hw δ hδ
  obtain ⟨k, c, phase, hpEq⟩ := hpFinite
  have hp :
      HasUniformComplexCesaroZero (fun n ↦ p n * e n) := by
    convert
      hasUniformComplexCesaroZero_finiteCirclePolynomial_mul
        (Finset.univ : Finset (Fin k)) c phase e heChar using 1
    funext n
    rw [hpEq]
  have hε2 : 0 < ε / 2 := by positivity
  have hδC : δ * C < ε / 2 := by
    have hden : 0 < 2 * (C + 1) := by positivity
    dsimp [δ]
    calc
      ε / (2 * (C + 1)) * C <
          ε / (2 * (C + 1)) * (C + 1) := by
        exact mul_lt_mul_of_pos_left (by linarith) (div_pos hε hden)
      _ = ε / 2 := by
        field_simp
  filter_upwards [hp (ε / 2) hε2] with N hpN
  intro i
  let d : ℕ → ℂ :=
    fun n ↦ (w (i + n) - p (i + n)) * e (i + n)
  have hdPoint (n : ℕ) : ‖d n‖ ≤ δ * C := by
    dsimp [d]
    rw [norm_mul]
    exact
      mul_le_mul (happ (i + n)).le (heBound (i + n))
        (norm_nonneg _) hδ.le
  have hd :
      ‖complexCesaroAverage d N‖ ≤ δ * C :=
    norm_complexCesaroAverage_le d (δ * C) hdPoint N
  have heq :
      complexCesaroAverage
          (fun n ↦ w (i + n) * e (i + n)) N =
        complexCesaroAverage
            (fun n ↦ p (i + n) * e (i + n)) N +
          complexCesaroAverage d N := by
    unfold complexCesaroAverage
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 2
    funext n
    dsimp [d]
    ring
  rw [heq]
  calc
    ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
    _ ≤ ‖complexCesaroAverage
            (fun n ↦ p (i + n) * e (i + n)) N‖ + δ * C :=
      add_le_add_right hd _
    _ < ε / 2 + ε / 2 := add_lt_add (hpN i) hδC
    _ = ε := by ring

/-- Uniform translated convergence of all complex pair correlations. -/
def HasUniformComplexPairLimits
    (v : ℕ → E) (Q : ℕ → ℕ → ℂ) : Prop :=
  ∀ h k : ℕ, ∀ ρ : ℝ, 0 < ρ →
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      ‖complexCesaroAverage
          (fun n ↦
            @inner ℂ E _
              (v (i + (n + k))) (v (i + (n + h)))) N -
        Q h k‖ < ρ

/-- The absolute pair-limit blocks can be made arbitrarily small.  This
form is stable under multiplication by unit-circle phases. -/
def HasSmallAbsolutePairLimitBlocks (Q : ℕ → ℕ → ℂ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ H : ℕ, 0 < H ∧
      (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, ‖Q h k‖) <
        δ * (H : ℝ) ^ 2

/-- Common time phases cancel from a pair correlation, leaving only the
fixed offset phase. -/
lemma circle_phase_pair
    (z : Circle) (i n h k : ℕ) :
    (z : ℂ) ^ (i + (n + h)) *
        star ((z : ℂ) ^ (i + (n + k))) =
      (z : ℂ) ^ h * star ((z : ℂ) ^ k) := by
  have hz : (z : ℂ) * star (z : ℂ) = 1 := by
    change (z : ℂ) * conj (z : ℂ) = 1
    rw [← Circle.coe_inv_eq_conj]
    simp
  have hleft :
      (z : ℂ) ^ (i + (n + h)) =
        (z : ℂ) ^ (i + n) * (z : ℂ) ^ h := by
    rw [show i + (n + h) = (i + n) + h by omega, pow_add]
  have hright :
      star ((z : ℂ) ^ (i + (n + k))) =
        star (z : ℂ) ^ (i + n) * star (z : ℂ) ^ k := by
    change
      conj ((z : ℂ) ^ (i + (n + k))) =
        conj (z : ℂ) ^ (i + n) * conj (z : ℂ) ^ k
    rw [show i + (n + k) = (i + n) + k by omega,
      pow_add, map_mul, map_pow, map_pow]
  rw [hleft, hright]
  calc
    (z : ℂ) ^ (i + n) * (z : ℂ) ^ h *
        (star (z : ℂ) ^ (i + n) * star (z : ℂ) ^ k) =
      (((z : ℂ) ^ (i + n)) * (star (z : ℂ) ^ (i + n))) *
        ((z : ℂ) ^ h * star (z : ℂ) ^ k) := by ring
    _ = (((z : ℂ) * star (z : ℂ)) ^ (i + n)) *
        ((z : ℂ) ^ h * star (z : ℂ) ^ k) := by
      rw [mul_pow]
    _ = (z : ℂ) ^ h * star ((z : ℂ) ^ k) := by
      rw [hz, one_pow, one_mul]
      change (z : ℂ) ^ h * conj (z : ℂ) ^ k =
        (z : ℂ) ^ h * conj ((z : ℂ) ^ k)
      rw [map_pow]

/-- The pair correlation of a circle-modulated vector sequence is the
unmodulated pair correlation times a phase depending only on the two
offsets. -/
lemma inner_circle_modulated
    (v : ℕ → E) (z : Circle) (i n h k : ℕ) :
    @inner ℂ E _
        (((z : ℂ) ^ (i + (n + k))) • v (i + (n + k)))
        (((z : ℂ) ^ (i + (n + h))) • v (i + (n + h))) =
      ((z : ℂ) ^ h * star ((z : ℂ) ^ k)) *
        @inner ℂ E _
          (v (i + (n + k))) (v (i + (n + h))) := by
  rw [inner_smul_left, inner_smul_right]
  calc
    star ((z : ℂ) ^ (i + (n + k))) *
        ((z : ℂ) ^ (i + (n + h)) *
          @inner ℂ E _
            (v (i + (n + k))) (v (i + (n + h)))) =
      ((z : ℂ) ^ (i + (n + h)) *
        star ((z : ℂ) ^ (i + (n + k)))) *
          @inner ℂ E _
            (v (i + (n + k))) (v (i + (n + h))) := by ring
    _ = _ := by rw [circle_phase_pair z i n h k]

/-- Pulling the fixed offset phase outside a complex Cesàro average. -/
lemma complexCesaroAverage_inner_circle_modulated
    (v : ℕ → E) (z : Circle) (i h k N : ℕ) :
    complexCesaroAverage
        (fun n ↦
          @inner ℂ E _
            (((z : ℂ) ^ (i + (n + k))) • v (i + (n + k)))
            (((z : ℂ) ^ (i + (n + h))) • v (i + (n + h)))) N =
      ((z : ℂ) ^ h * star ((z : ℂ) ^ k)) *
        complexCesaroAverage
          (fun n ↦
            @inner ℂ E _
              (v (i + (n + k))) (v (i + (n + h)))) N := by
  unfold complexCesaroAverage
  simp_rw [inner_circle_modulated]
  rw [← Finset.mul_sum]
  ring

/-- Uniform complex pair limits survive circle modulation; their real
limits are obtained by applying the corresponding fixed offset phase. -/
lemma circleModulated_hasUniformPairLimits
    (v : ℕ → E) (Q : ℕ → ℕ → ℂ)
    (hQ : HasUniformComplexPairLimits v Q) (z : Circle) :
    VanDerCorput.HasUniformPairLimits
      (fun n ↦ ((z : ℂ) ^ n) • v n)
      (fun h k ↦
        (((z : ℂ) ^ h * star ((z : ℂ) ^ k)) * Q h k).re) := by
  intro h k ρ hρ
  filter_upwards [hQ h k ρ hρ] with N hN
  intro i
  let c : ℂ := (z : ℂ) ^ h * star ((z : ℂ) ^ k)
  let A : ℂ :=
    complexCesaroAverage
      (fun n ↦
        @inner ℂ E _
          (v (i + (n + k))) (v (i + (n + h)))) N
  have hc : ‖c‖ = 1 := by
    dsimp [c]
    simp
  have havg :
      cesaroAverage
          (fun n ↦
            (@inner ℂ E _
              (((z : ℂ) ^ (i + (n + k))) • v (i + (n + k)))
              (((z : ℂ) ^ (i + (n + h))) • v (i + (n + h)))).re) N =
        (c * A).re := by
    rw [MultipleKhintchineUniform.cesaroAverage_re_eq]
    exact congrArg Complex.re
      (complexCesaroAverage_inner_circle_modulated
        v z i h k N)
  rw [havg]
  calc
    |(c * A).re - (c * Q h k).re| =
        |(c * (A - Q h k)).re| := by
          congr 1
          rw [mul_sub, Complex.sub_re]
    _ ≤ ‖c * (A - Q h k)‖ := Complex.abs_re_le_norm _
    _ = ‖A - Q h k‖ := by rw [norm_mul, hc, one_mul]
    _ < ρ := hN i

/-- Absolute smallness of complex pair-limit blocks implies smallness of
the real pair-limit blocks after any unit-circle modulation. -/
lemma circleModulated_hasSmallPairLimitBlocks
    (Q : ℕ → ℕ → ℂ) (hQ : HasSmallAbsolutePairLimitBlocks Q)
    (z : Circle) :
    VanDerCorput.HasSmallPairLimitBlocks
      (fun h k ↦
        (((z : ℂ) ^ h * star ((z : ℂ) ^ k)) * Q h k).re) := by
  intro δ hδ
  obtain ⟨H, hH, hsmall⟩ := hQ δ hδ
  refine ⟨H, hH, ?_⟩
  calc
    (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
        (((z : ℂ) ^ h * star ((z : ℂ) ^ k)) * Q h k).re) ≤
      ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
        ‖Q h k‖ := by
          gcongr with h hh k hk
          calc
            ((((z : ℂ) ^ h * star ((z : ℂ) ^ k)) * Q h k).re) ≤
                ‖((z : ℂ) ^ h * star ((z : ℂ) ^ k)) * Q h k‖ :=
              (le_abs_self _).trans (Complex.abs_re_le_norm _)
            _ = ‖Q h k‖ := by simp
    _ < δ * (H : ℝ) ^ 2 := hsmall

/-- A bounded sequence with uniformly convergent complex pair limits and
small absolute pair-limit blocks has translated-uniform Cesàro mean zero
after multiplication by every circle character. -/
theorem circleModulated_uniform_cesaro_zero
    (v : ℕ → E) (Q : ℕ → ℕ → ℂ)
    (M : ℝ) (hv : ∀ n, ‖v n‖ ≤ M)
    (hlimits : HasUniformComplexPairLimits v Q)
    (hsmall : HasSmallAbsolutePairLimitBlocks Q)
    (z : Circle) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1),
            ((z : ℂ) ^ (i + n)) • v (i + n)‖ < ε := by
  apply VanDerCorput.vectorCesaro_uniform_tendsto_zero_of_blockDecay
    (fun n ↦ ((z : ℂ) ^ n) • v n) M
  · intro n
    rw [norm_smul, norm_pow, Circle.norm_coe, one_pow, one_mul]
    exact hv n
  · exact
      VanDerCorput.hasUniformVanDerCorputBlockDecay_of_pairLimits
        (fun n ↦ ((z : ℂ) ^ n) • v n)
        (fun h k ↦
          (((z : ℂ) ^ h * star ((z : ℂ) ^ k)) * Q h k).re)
        (circleModulated_hasUniformPairLimits v Q hlimits z)
        (circleModulated_hasSmallPairLimitBlocks Q hsmall z)

/-- The complex pair-limit array of a bilinear Koopman progression in an
ergodic system. -/
noncomputable def doubleKoopmanPairLimit
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (h k : ℕ) : ℂ :=
  productOfMeans M
    (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)
    (fun x ↦ star
      (MultipleKhintchineCharacteristic.leftPairFunction M hM F h k x))

/-- The bilinear progression has uniform translated complex pair limits,
not just convergence of their real parts. -/
lemma doubleKoopmanProduct_hasUniformComplexPairLimits
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (hErg : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MeasureTheory.MemLp (fun x ↦ G x) ⊤ M.μ) :
    HasUniformComplexPairLimits
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F G hFtop)
      (doubleKoopmanPairLimit M hM F G) := by
  intro h k ρ hρ
  have hu :=
    MultipleKhintchineUniform.ergodic_uniform_shifted_cesaroFunctionCorrelations
      M hM hErg
      (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)
      (fun x ↦ star
        (MultipleKhintchineCharacteristic.leftPairFunction M hM F h k x))
      (MultipleKhintchineCharacteristic.rightPairFunction_memLp
        M hM G hGtop h k)
      (MultipleKhintchineCharacteristic.star_leftPairFunction_memLp
        M hM F hFtop h k)
      ρ hρ
  have hu' := (tendsto_add_atTop_nat 1).eventually hu
  filter_upwards [hu'] with N hN
  intro i
  have hc := hN i
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false] at hc
  let b : ℕ → ℂ := fun n ↦
    @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F G hFtop (i + (n + k)))
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F G hFtop (i + (n + h)))
  have hb (n : ℕ) :
      b n =
        functionCorrelation M
          (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)
          (fun x ↦ star
            (MultipleKhintchineCharacteristic.leftPairFunction
              M hM F h k x))
          (i + n) := by
    dsimp only [b]
    rw [show i + (n + k) = (i + n) + k by omega,
      show i + (n + h) = (i + n) + h by omega,
      MultipleKhintchineCharacteristic.inner_doubleKoopmanProduct_add
        M hM F G hFtop (i + n) h k,
      MultipleKhintchineCharacteristic.inner_shiftedProducts_eq_functionCorrelation
        M hM F G hFtop (i + n) h k]
  change
    ‖complexCesaroAverage b N -
      doubleKoopmanPairLimit M hM F G h k‖ < ρ
  rw [show complexCesaroAverage b N =
      (((N + 1 : ℕ) : ℂ)⁻¹) *
        ∑ n ∈ Finset.range (N + 1),
          functionCorrelation M
            (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)
            (fun x ↦ star
              (MultipleKhintchineCharacteristic.leftPairFunction
                M hM F h k x))
            (i + n) by
    unfold complexCesaroAverage
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    exact hb n]
  rw [← dist_eq_norm]
  simpa only [doubleKoopmanPairLimit] using hc

/-- If the second dynamic factor is continuous-spectral, the absolute
complex pair-limit blocks are arbitrarily small. -/
lemma doubleKoopmanPairLimit_hasSmallAbsoluteBlocks
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (hGcont :
      InContinuousSpectralSubspace
        (MultipleKhintchineCharacteristic.KData M hM) G) :
    HasSmallAbsolutePairLimitBlocks
      (doubleKoopmanPairLimit M hM F G) := by
  intro δ hδ
  let η : ℝ := δ / (4 * (C ^ 2 + 1))
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨H, hH, heven⟩ :=
    MultipleKhintchineCharacteristic.exists_small_evenAutocorrelation_sum
      M hM G hGcont η hη
  refine ⟨H, hH, ?_⟩
  have hsumBound :=
    MultipleKhintchineCharacteristic.sum_pairLimit_norm_le
      M hM F G C hC hFbound H
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
        ‖doubleKoopmanPairLimit M hM F G h k‖) ≤
      2 * (H : ℝ) * C ^ 2 *
        (Finset.range H).sum
          (MultipleKhintchineCharacteristic.evenAutocorrelationNorm
            M hM G) := by
              simpa only [doubleKoopmanPairLimit] using hsumBound
    _ ≤ 2 * (H : ℝ) * C ^ 2 * (η * (H : ℝ)) := by
      have hcoef : 0 ≤ 2 * (H : ℝ) * C ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left heven.le hcoef
    _ < δ * (H : ℝ) ^ 2 := by
      have hratio : 2 * C ^ 2 * η < δ := by
        dsimp [η]
        have hden : 0 < 4 * (C ^ 2 + 1) := by positivity
        rw [div_eq_mul_inv]
        calc
          2 * C ^ 2 * (δ * (4 * (C ^ 2 + 1))⁻¹) =
              δ * (2 * C ^ 2 / (4 * (C ^ 2 + 1))) := by ring
          _ < δ * 1 := by
            apply mul_lt_mul_of_pos_left _ hδ
            rw [div_lt_one hden]
            nlinarith [sq_nonneg C]
          _ = δ := mul_one _
      nlinarith [sq_pos_of_pos hHreal]

/-- Symmetrically, continuity of the first dynamic factor makes the
absolute complex pair-limit blocks small. -/
lemma doubleKoopmanPairLimit_hasSmallAbsoluteBlocks_left
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ C)
    (hFcont :
      InContinuousSpectralSubspace
        (MultipleKhintchineCharacteristic.KData M hM) F) :
    HasSmallAbsolutePairLimitBlocks
      (doubleKoopmanPairLimit M hM F G) := by
  intro δ hδ
  let η : ℝ := δ / (4 * (C ^ 2 + 1))
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨H, hH, hcorr⟩ :=
    MultipleKhintchineCharacteristic.exists_small_autocorrelation_sum
      M hM F hFcont η hη
  refine ⟨H, hH, ?_⟩
  have hsumBound :=
    MultipleKhintchineCharacteristic.sum_pairLimit_norm_le_left
      M hM F G C hC hGbound H
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
        ‖doubleKoopmanPairLimit M hM F G h k‖) ≤
      2 * (H : ℝ) * C ^ 2 *
        (Finset.range H).sum
          (MultipleKhintchineCharacteristic.autocorrelationNorm
            M hM F) := by
              simpa only [doubleKoopmanPairLimit] using hsumBound
    _ ≤ 2 * (H : ℝ) * C ^ 2 * (η * (H : ℝ)) := by
      have hcoef : 0 ≤ 2 * (H : ℝ) * C ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left hcorr.le hcoef
    _ < δ * (H : ℝ) ^ 2 := by
      have hratio : 2 * C ^ 2 * η < δ := by
        dsimp [η]
        have hden : 0 < 4 * (C ^ 2 + 1) := by positivity
        rw [div_eq_mul_inv]
        calc
          2 * C ^ 2 * (δ * (4 * (C ^ 2 + 1))⁻¹) =
              δ * (2 * C ^ 2 / (4 * (C ^ 2 + 1))) := by ring
          _ < δ * 1 := by
            apply mul_lt_mul_of_pos_left _ hδ
            rw [div_lt_one hden]
            nlinarith [sq_nonneg C]
          _ = δ := mul_one _
      nlinarith [sq_pos_of_pos hHreal]

/-- Every character modulation of a bilinear progression with a
continuous-spectral second factor has translated-uniform Cesàro mean zero. -/
theorem doubleKoopmanProduct_circleModulated_uniform_cesaro_zero
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (hErg : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MeasureTheory.MemLp (fun x ↦ G x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (hGcont :
      InContinuousSpectralSubspace
        (MultipleKhintchineCharacteristic.KData M hM) G)
    (z : Circle) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1),
            ((z : ℂ) ^ (i + n)) •
              MultipleKhintchineCharacteristic.doubleKoopmanProduct
                M hM F G hFtop (i + n)‖ < ε := by
  exact circleModulated_uniform_cesaro_zero
    (MultipleKhintchineCharacteristic.doubleKoopmanProduct
      M hM F G hFtop)
    (doubleKoopmanPairLimit M hM F G)
    (C * ‖G‖)
    (MultipleKhintchineCharacteristic.norm_doubleKoopmanProduct_le
      M hM F G hFtop C hC hFbound)
    (doubleKoopmanProduct_hasUniformComplexPairLimits
      M hM hErg F G hFtop hGtop)
    (doubleKoopmanPairLimit_hasSmallAbsoluteBlocks
      M hM F G C hC hFbound hGcont)
    z

/-- The preceding phase-modulated cancellation also holds when the first
dynamic factor is continuous-spectral. -/
theorem doubleKoopmanProduct_circleModulated_uniform_cesaro_zero_left
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (hErg : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MeasureTheory.MemLp (fun x ↦ G x) ⊤ M.μ)
    (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ CF)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ CG)
    (hFcont :
      InContinuousSpectralSubspace
        (MultipleKhintchineCharacteristic.KData M hM) F)
    (z : Circle) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1),
            ((z : ℂ) ^ (i + n)) •
              MultipleKhintchineCharacteristic.doubleKoopmanProduct
                M hM F G hFtop (i + n)‖ < ε := by
  exact circleModulated_uniform_cesaro_zero
    (MultipleKhintchineCharacteristic.doubleKoopmanProduct
      M hM F G hFtop)
    (doubleKoopmanPairLimit M hM F G)
    (CF * ‖G‖)
    (MultipleKhintchineCharacteristic.norm_doubleKoopmanProduct_le
      M hM F G hFtop CF hCF hFbound)
    (doubleKoopmanProduct_hasUniformComplexPairLimits
      M hM hErg F G hFtop hGtop)
    (doubleKoopmanPairLimit_hasSmallAbsoluteBlocks_left
      M hM F G CG hCG hGbound hFcont)
    z

/-- Applying a fixed complex inner-product functional preserves
translated-uniform complex Cesàro convergence to zero. -/
lemma uniform_complexCesaro_inner_of_vector
    (F : E) (v : ℕ → E)
    (hv :
      ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
            ∑ n ∈ Finset.range (N + 1), v (i + n)‖ < ε) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      ‖complexCesaroAverage
          (fun n ↦ @inner ℂ E _ F (v (i + n))) N‖ < ε := by
  intro ε hε
  let δ : ℝ := ε / (‖F‖ + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  filter_upwards [hv δ hδ] with N hN
  intro i
  let V : E :=
    (((N + 1 : ℕ) : ℂ)⁻¹) •
      ∑ n ∈ Finset.range (N + 1), v (i + n)
  have heq :
      complexCesaroAverage
          (fun n ↦ @inner ℂ E _ F (v (i + n))) N =
        @inner ℂ E _ F V := by
    unfold complexCesaroAverage V
    rw [inner_smul_right, inner_sum]
  rw [heq]
  calc
    ‖@inner ℂ E _ F V‖ ≤ ‖F‖ * ‖V‖ := norm_inner_le_norm _ _
    _ ≤ ‖F‖ * δ := by
      exact mul_le_mul_of_nonneg_left (hN i).le (norm_nonneg F)
    _ < (‖F‖ + 1) * δ := by
      exact mul_lt_mul_of_pos_right (by linarith) hδ
    _ = ε := by
      dsimp [δ]
      field_simp

/-- A fixed inner-product functional preserves one prescribed circle
modulation of translated-uniform vector Cesàro cancellation. -/
lemma uniform_complexCesaro_inner_circleModulated
    (F : E) (v : ℕ → E) (z : Circle)
    (hv :
      ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
            ∑ n ∈ Finset.range (N + 1),
              ((z : ℂ) ^ (i + n)) • v (i + n)‖ < ε) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      ‖complexCesaroAverage
          (fun n ↦
            (z : ℂ) ^ (i + n) *
              @inner ℂ E _ F (v (i + n))) N‖ < ε := by
  simpa only [inner_smul_right] using
    (uniform_complexCesaro_inner_of_vector F
      (fun n ↦ ((z : ℂ) ^ n) • v n) hv)

/-- A phase times the real part of a complex scalar is the half-sum of
the phase-modulated scalar and the conjugate of its oppositely modulated
counterpart.  The identity is recorded at the Cesàro-average level. -/
lemma complexCesaroAverage_phase_mul_re
    (q : ℕ → ℂ) (z : Circle) (i N : ℕ) :
    complexCesaroAverage
        (fun n ↦
          (z : ℂ) ^ (i + n) * ((q (i + n)).re : ℂ)) N =
      (complexCesaroAverage
          (fun n ↦ (z : ℂ) ^ (i + n) * q (i + n)) N +
        star (complexCesaroAverage
          (fun n ↦
            (IsometryWiener.circleConj z : ℂ) ^ (i + n) *
              q (i + n)) N)) / 2 := by
  have hterm (n : ℕ) :
      (z : ℂ) ^ (i + n) * ((q (i + n)).re : ℂ) =
        ((z : ℂ) ^ (i + n) * q (i + n) +
          star
            ((IsometryWiener.circleConj z : ℂ) ^ (i + n) *
              q (i + n))) / 2 := by
    change
      (z : ℂ) ^ (i + n) * ((q (i + n)).re : ℂ) =
        ((z : ℂ) ^ (i + n) * q (i + n) +
          conj
            ((IsometryWiener.circleConj z : ℂ) ^ (i + n) *
              q (i + n))) / 2
    rw [IsometryWiener.circleConj_coe, map_mul, map_pow]
    change
      (z : ℂ) ^ (i + n) * ((q (i + n)).re : ℂ) =
        ((z : ℂ) ^ (i + n) * q (i + n) +
          star (star (z : ℂ)) ^ (i + n) * star (q (i + n))) / 2
    rw [star_star]
    apply Complex.ext
    · simp [Complex.mul_re]
    · simp [Complex.mul_im]
      ring
  unfold complexCesaroAverage
  simp_rw [hterm]
  rw [← Finset.sum_div]
  rw [Finset.sum_add_distrib]
  change
    _ =
      (_ +
        conj
          ((((N + 1 : ℕ) : ℂ)⁻¹) *
            ∑ x ∈ Finset.range (N + 1),
              (IsometryWiener.circleConj z : ℂ) ^ (i + x) *
                q (i + x))) / 2
  have hscalar :
      (starRingEnd ℂ) ((((N + 1 : ℕ) : ℂ)⁻¹)) =
        (((N + 1 : ℕ) : ℂ)⁻¹) := by simp
  rw [map_mul, hscalar, map_sum]
  have hbridge (x : ℕ) :
      star
          ((IsometryWiener.circleConj z : ℂ) ^ (i + x) *
            q (i + x)) =
        (starRingEnd ℂ)
          ((IsometryWiener.circleConj z : ℂ) ^ (i + x) *
            q (i + x)) := rfl
  simp_rw [hbridge]
  ring

/-- If every character modulation of a complex scalar sequence has
translated-uniform mean zero, then the same is true after first taking the
real part. -/
lemma uniform_complexCesaro_phase_mul_re
    (q : ℕ → ℂ)
    (hq :
      ∀ z : Circle, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        ‖complexCesaroAverage
            (fun n ↦ (z : ℂ) ^ (i + n) * q (i + n)) N‖ < ε)
    (z : Circle) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      ‖complexCesaroAverage
          (fun n ↦
            (z : ℂ) ^ (i + n) * ((q (i + n)).re : ℂ)) N‖ < ε := by
  intro ε hε
  filter_upwards [
    hq z ε hε,
    hq (IsometryWiener.circleConj z) ε hε] with N hzN hczN
  intro i
  let A : ℂ :=
    complexCesaroAverage
      (fun n ↦ (z : ℂ) ^ (i + n) * q (i + n)) N
  let B : ℂ :=
    complexCesaroAverage
      (fun n ↦
        (IsometryWiener.circleConj z : ℂ) ^ (i + n) * q (i + n)) N
  rw [complexCesaroAverage_phase_mul_re q z i N]
  calc
    ‖(A + star B) / 2‖ ≤ (‖A‖ + ‖B‖) / 2 := by
      rw [norm_div]
      have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [htwo]
      exact div_le_div_of_nonneg_right
        (by simpa using norm_add_le A (star B)) (by norm_num)
    _ < (ε + ε) / 2 := by
      gcongr
      · exact hzN i
      · exact hczN i
    _ = ε := by ring

/-- Fixed inner products and real parts preserve cancellation against all
circle characters. -/
lemma uniform_complexCesaro_phase_mul_re_inner
    (F : E) (v : ℕ → E)
    (hv :
      ∀ z : Circle, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
            ∑ n ∈ Finset.range (N + 1),
              ((z : ℂ) ^ (i + n)) • v (i + n)‖ < ε)
    (z : Circle) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      ‖complexCesaroAverage
          (fun n ↦
            (z : ℂ) ^ (i + n) *
              ((@inner ℂ E _ F (v (i + n))).re : ℂ)) N‖ < ε := by
  let q : ℕ → ℂ := fun n ↦ @inner ℂ E _ F (v n)
  have hq :
      ∀ w : Circle, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        ‖complexCesaroAverage
            (fun n ↦ (w : ℂ) ^ (i + n) * q (i + n)) N‖ < ε := by
    intro w
    exact uniform_complexCesaro_inner_circleModulated F v w (hv w)
  change
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      ‖complexCesaroAverage
          (fun n ↦
            (z : ℂ) ^ (i + n) * ((q (i + n)).re : ℂ)) N‖ < ε
  exact uniform_complexCesaro_phase_mul_re q hq z

/-- The triple characteristic-factor error cancels uniformly on translated
blocks after multiplication by any circle character.  This is the spectral
input needed for nonnegative Bohr localization. -/
theorem tripleCharacteristic_circleModulated_uniform_cesaro_zero
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (z : Circle) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      ‖complexCesaroAverage
          (fun n ↦
            (z : ℂ) ^ (i + n) *
              ((MultipleKhintchineSyndetic.tripleCorrelation
                    M A (i + n) -
                  ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
                    M hM A hA (i + n) : ℝ) : ℂ)) N‖ < ε := by
  let F := MultipleKhintchineCharacteristic.indicatorLp M hM.1 A hA
  let G :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  let R := F - G
  have hFtop :=
    MultipleKhintchineCharacteristic.indicatorLp_mem_top M hM.1 A hA
  have hGtop :=
    MultipleKhintchineCharacteristic.forwardKroneckerIndicatorLp_mem_top
      M hM A hA
  have hRtop :=
    MultipleKhintchineCharacteristic.indicatorResidual_mem_top M hM A hA
  have hRcont :=
    MultipleKhintchineCharacteristic.indicator_sub_forwardKronecker_continuous
      M hM A hA
  have hright :
      ∀ w : Circle, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
            ∑ n ∈ Finset.range (N + 1),
              ((w : ℂ) ^ (i + n)) •
                MultipleKhintchineCharacteristic.doubleKoopmanProduct
                  M hM.1 F R hFtop (i + n)‖ < ε := by
    intro w
    exact
      doubleKoopmanProduct_circleModulated_uniform_cesaro_zero
        M hM.1 hM F R hFtop hRtop 1 (by norm_num)
        (MultipleKhintchineCharacteristic.indicatorLp_norm_le_one
          M hM.1 A hA)
        hRcont w
  have hleft :
      ∀ w : Circle, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
            ∑ n ∈ Finset.range (N + 1),
              ((w : ℂ) ^ (i + n)) •
                MultipleKhintchineCharacteristic.doubleKoopmanProduct
                  M hM.1 R G hRtop (i + n)‖ < ε := by
    intro w
    exact
      doubleKoopmanProduct_circleModulated_uniform_cesaro_zero_left
        M hM.1 hM R G hRtop hGtop 2 1
        (by norm_num) (by norm_num)
        (MultipleKhintchineCharacteristic.indicatorResidual_norm_le_two
          M hM A hA)
        (MultipleKhintchineCharacteristic.forwardKroneckerIndicatorLp_norm_le_one
          M hM A hA)
        hRcont w
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hr :=
    uniform_complexCesaro_phase_mul_re_inner F
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM.1 F R hFtop) hright z (ε / 2) hε2
  have hl :=
    uniform_complexCesaro_phase_mul_re_inner F
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM.1 R G hRtop) hleft z (ε / 2) hε2
  filter_upwards [hr, hl] with N hrN hlN
  intro i
  have hid :
      complexCesaroAverage
          (fun n ↦
            (z : ℂ) ^ (i + n) *
              ((MultipleKhintchineSyndetic.tripleCorrelation
                    M A (i + n) -
                  ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
                    M hM A hA (i + n) : ℝ) : ℂ)) N =
        complexCesaroAverage
            (fun n ↦
              (z : ℂ) ^ (i + n) *
                ((@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F
                  (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                    M hM.1 F R hFtop (i + n))).re : ℂ)) N +
          complexCesaroAverage
            (fun n ↦
              (z : ℂ) ^ (i + n) *
                ((@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F
                  (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                    M hM.1 R G hRtop (i + n))).re : ℂ)) N := by
    unfold complexCesaroAverage
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 2
    funext n
    change
      (z : ℂ) ^ (i + n) *
          ((MultipleKhintchineSyndetic.tripleCorrelation M A (i + n) -
            ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
              M hM A hA (i + n) : ℝ) : ℂ) =
        (z : ℂ) ^ (i + n) *
            ((@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F
              (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                M hM.1 F R hFtop (i + n))).re : ℂ) +
          (z : ℂ) ^ (i + n) *
            ((@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F
              (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                M hM.1 R G hRtop (i + n))).re : ℂ)
    rw [MultipleKhintchineCharacteristic.tripleCorrelation_sub_forwardKronecker
      M hM A hA (i + n)]
    push_cast
    ring
  rw [hid]
  calc
    ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hrN i) (hlN i)
    _ = ε := by ring

/-- Predicate form of circle-character cancellation for the triple
characteristic-factor error. -/
theorem tripleCharacteristic_circleModulated_hasUniformComplexCesaroZero
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (z : Circle) :
    HasUniformComplexCesaroZero
      (fun n ↦
        (z : ℂ) ^ n *
          ((MultipleKhintchineSyndetic.tripleCorrelation M A n -
            ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
              M hM A hA n : ℝ) : ℂ)) := by
  exact
    tripleCharacteristic_circleModulated_uniform_cesaro_zero
      M hM A hA z

/-- The triple characteristic-factor error has the uniform numerical bound
`4`; this deliberately coarse bound is sufficient for uniform-limit
closure of Bohr weights. -/
lemma norm_tripleCharacteristicError_le_four
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) :
    ‖((MultipleKhintchineSyndetic.tripleCorrelation M A n -
        ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
          M hM A hA n : ℝ) : ℂ)‖ ≤ 4 := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  let F := MultipleKhintchineCharacteristic.indicatorLp M hM.1 A hA
  let G :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  let R := F - G
  have hFtop :=
    MultipleKhintchineCharacteristic.indicatorLp_mem_top M hM.1 A hA
  have hRtop :=
    MultipleKhintchineCharacteristic.indicatorResidual_mem_top M hM A hA
  have hμ : MeasureTheory.measureUnivNNReal M.μ = 1 := by
    apply NNReal.eq
    simp [MeasureTheory.measureUnivNNReal]
  have hF_norm : ‖F‖ ≤ 1 := by
    simpa [hμ] using
      (MeasureTheory.Lp.norm_le_of_ae_bound (p := (2 : ENNReal))
        (f := F) (by norm_num)
        (MultipleKhintchineCharacteristic.indicatorLp_norm_le_one
          M hM.1 A hA))
  have hG_norm : ‖G‖ ≤ 1 := by
    simpa [hμ] using
      (MeasureTheory.Lp.norm_le_of_ae_bound (p := (2 : ENNReal))
        (f := G) (by norm_num)
        (MultipleKhintchineCharacteristic.forwardKroneckerIndicatorLp_norm_le_one
          M hM A hA))
  have hR_norm : ‖R‖ ≤ 2 := by
    simpa [hμ] using
      (MeasureTheory.Lp.norm_le_of_ae_bound (p := (2 : ENNReal))
        (f := R) (by norm_num)
        (MultipleKhintchineCharacteristic.indicatorResidual_norm_le_two
          M hM A hA))
  let PFR :=
    MultipleKhintchineCharacteristic.doubleKoopmanProduct
      M hM.1 F R hFtop n
  let PRG :=
    MultipleKhintchineCharacteristic.doubleKoopmanProduct
      M hM.1 R G hRtop n
  have hPFR_norm : ‖PFR‖ ≤ 2 := by
    calc
      ‖PFR‖ ≤ 1 * ‖R‖ := by
        exact
          MultipleKhintchineCharacteristic.norm_doubleKoopmanProduct_le
            M hM.1 F R hFtop 1 (by norm_num)
            (MultipleKhintchineCharacteristic.indicatorLp_norm_le_one
              M hM.1 A hA) n
      _ ≤ 1 * 2 := mul_le_mul_of_nonneg_left hR_norm (by norm_num)
      _ = 2 := by norm_num
  have hPRG_norm : ‖PRG‖ ≤ 2 := by
    calc
      ‖PRG‖ ≤ 2 * ‖G‖ := by
        exact
          MultipleKhintchineCharacteristic.norm_doubleKoopmanProduct_le
            M hM.1 R G hRtop 2 (by norm_num)
            (MultipleKhintchineCharacteristic.indicatorResidual_norm_le_two
              M hM A hA) n
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hG_norm (by norm_num)
      _ = 2 := by norm_num
  have hright :
      |(@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F PFR).re| ≤ 2 := by
    calc
      |(@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F PFR).re| ≤
          ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F PFR‖ :=
        Complex.abs_re_le_norm _
      _ ≤ ‖F‖ * ‖PFR‖ := norm_inner_le_norm _ _
      _ ≤ 1 * 2 :=
        mul_le_mul hF_norm hPFR_norm (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  have hleft :
      |(@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F PRG).re| ≤ 2 := by
    calc
      |(@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F PRG).re| ≤
          ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F PRG‖ :=
        Complex.abs_re_le_norm _
      _ ≤ ‖F‖ * ‖PRG‖ := norm_inner_le_norm _ _
      _ ≤ 1 * 2 :=
        mul_le_mul hF_norm hPRG_norm (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  rw [MultipleKhintchineCharacteristic.tripleCorrelation_sub_forwardKronecker
    M hM A hA n]
  change
    ‖(((@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F PFR).re +
      (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F PRG).re : ℝ) : ℂ)‖ ≤ 4
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (abs_add_le _ _).trans (by linarith)

/-- The triple characteristic-factor error cancels against every finite
circle-character polynomial, uniformly on translated blocks. -/
theorem tripleCharacteristic_finiteCirclePolynomial_uniform_cesaro_zero
    {ι : Type*}
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (s : Finset ι) (c : ι → ℂ) (phase : ι → Circle) :
    HasUniformComplexCesaroZero
      (fun n ↦
        finiteCirclePolynomial s c phase n *
          ((MultipleKhintchineSyndetic.tripleCorrelation M A n -
            ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
              M hM A hA n : ℝ) : ℂ)) := by
  exact
    hasUniformComplexCesaroZero_finiteCirclePolynomial_mul
      s c phase
      (fun n ↦
        ((MultipleKhintchineSyndetic.tripleCorrelation M A n -
          ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
            M hM A hA n : ℝ) : ℂ))
      (tripleCharacteristic_circleModulated_hasUniformComplexCesaroZero
        M hM A hA)

/-- Every uniformly approximable Bohr weight kills the bounded triple
characteristic-factor error on translated Cesàro blocks. -/
theorem tripleCharacteristic_uniformLimitWeight_uniform_cesaro_zero
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (w : ℕ → ℂ)
    (hw : IsUniformLimitOfFiniteCirclePolynomials w) :
    HasUniformComplexCesaroZero
      (fun n ↦
        w n *
          ((MultipleKhintchineSyndetic.tripleCorrelation M A n -
            ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
              M hM A hA n : ℝ) : ℂ)) := by
  exact
    hasUniformComplexCesaroZero_uniformLimit_weight_mul
      w
      (fun n ↦
        ((MultipleKhintchineSyndetic.tripleCorrelation M A n -
          ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
            M hM A hA n : ℝ) : ℂ))
      hw 4 (by norm_num)
      (norm_tripleCharacteristicError_le_four M hM A hA)
      (tripleCharacteristic_circleModulated_hasUniformComplexCesaroZero
        M hM A hA)

end Chapter02.BohrWeightedUniform
