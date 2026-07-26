import Chapter02.HostKra.HostKraU3FourTermReversal

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HostKraU3OptimalProgressionDecay

universe u

open HostKraCubeSeminorm
open Chapter02.HostKraU4ProgressionDecay

/-- Sharp quantitative block-correlation estimate for a bilinear
progression.  Unlike the order-raised estimate in
`HostKraU4ProgressionDecay`, the controlling quantity here is the exact
`U²` power of the second factor. -/
lemma doubleKoopmanProduct_uniform_blockCorrelation_lt_hostKraU2Power
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (η : ℝ) (hη : 0 < η) :
    ∃ L : ℕ, 0 < L ∧
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        cesaroAverage
          (fun n ↦ ∑ h ∈ Finset.range L, ∑ k ∈ Finset.range L,
            (@inner ℂ (Lp ℂ 2 M.μ) _
              (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                M hM F G hFtop (i + (n + k)))
              (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                M hM F G hFtop (i + (n + h)))).re) N <
          (2 * C ^ 2 *
              Real.sqrt (2 *
                (hostKraU2Power M hM (fun x ↦ G x) hGtop + η)) + η) *
            (L : ℝ) ^ 2 := by
  obtain ⟨L, hL, heven⟩ :=
    exists_evenAutocorrelationNorm_sq_lt_hostKraU2Power
      M hM hErg G hGtop η hη
  let P : ℝ := hostKraU2Power M hM (fun x ↦ G x) hGtop
  let R : ℝ := Real.sqrt (2 * (P + η))
  let S : ℝ :=
    (Finset.range L).sum
      (MultipleKhintchineCharacteristic.evenAutocorrelationNorm M hM G)
  have hP : 0 ≤ P := by
    exact hostKraU2Power_nonneg M hM _ _
  have hRarg : 0 < 2 * (P + η) := by positivity
  have hRsq : R ^ 2 = 2 * (P + η) := by
    exact Real.sq_sqrt hRarg.le
  have hR : 0 < R := Real.sqrt_pos.2 hRarg
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun r hr ↦ norm_nonneg _
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hSL : S < (L : ℝ) * R := by
    have heven' : S ^ 2 < ((L : ℝ) * R) ^ 2 := by
      calc
        S ^ 2 < 2 * (L : ℝ) ^ 2 * (P + η) := by
          simpa only [S, P] using heven
        _ = ((L : ℝ) * R) ^ 2 := by
          rw [mul_pow, hRsq]
          ring
    have hLR : 0 < (L : ℝ) * R := mul_pos hLreal hR
    nlinarith
  let Qlim : ℝ :=
    (Finset.range L).sum (fun h ↦
      (Finset.range L).sum (fun k ↦
        (productOfMeans M
          (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)
          (fun x ↦ star
            (MultipleKhintchineCharacteristic.leftPairFunction
              M hM F h k x))).re))
  have hQnorm :
      Qlim ≤ (Finset.range L).sum (fun h ↦
        (Finset.range L).sum (fun k ↦
          ‖productOfMeans M
            (MultipleKhintchineCharacteristic.rightPairFunction
              M hM G h k)
            (fun x ↦ star
              (MultipleKhintchineCharacteristic.leftPairFunction
                M hM F h k x))‖)) := by
    dsimp only [Qlim]
    gcongr with h hh k hk
    exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hsumBound :=
    MultipleKhintchineCharacteristic.sum_pairLimit_norm_le
      M hM F G C hC hFbound L
  have hQbound :
      Qlim ≤ 2 * (L : ℝ) ^ 2 * C ^ 2 * R := by
    calc
      Qlim ≤ (Finset.range L).sum (fun h ↦
          (Finset.range L).sum (fun k ↦
            ‖productOfMeans M
              (MultipleKhintchineCharacteristic.rightPairFunction
                M hM G h k)
              (fun x ↦ star
                (MultipleKhintchineCharacteristic.leftPairFunction
                  M hM F h k x))‖)) := hQnorm
      _ ≤ 2 * (L : ℝ) * C ^ 2 * S := by
        simpa only [S] using hsumBound
      _ ≤ 2 * (L : ℝ) ^ 2 * C ^ 2 * R := by
        have hcoef : 0 ≤ 2 * (L : ℝ) * C ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_left hSL.le hcoef
        nlinarith
  let ρ : ℝ := η / 2
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    positivity
  have hall :
      ∀ᶠ N : ℕ in atTop,
        ∀ h ∈ Finset.range L, ∀ k ∈ Finset.range L, ∀ i : ℕ,
          |cesaroAverage
              (fun n ↦
                (@inner ℂ (Lp ℂ 2 M.μ) _
                  (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                    M hM F G hFtop (i + (n + k)))
                  (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                    M hM F G hFtop (i + (n + h)))).re) N -
            (productOfMeans M
              (MultipleKhintchineCharacteristic.rightPairFunction
                M hM G h k)
              (fun x ↦ star
                (MultipleKhintchineCharacteristic.leftPairFunction
                  M hM F h k x))).re| < ρ := by
    rw [Filter.eventually_all_finset]
    intro h hh
    rw [Filter.eventually_all_finset]
    intro k hk
    exact
      MultipleKhintchineUniform.uniform_shifted_cesaro_re_inner_doubleKoopmanProduct
        M hM hErg F G hFtop hGtop h k ρ hρ
  refine ⟨L, hL, ?_⟩
  filter_upwards [hall] with N hN
  intro i
  let A : ℕ → ℕ → ℝ := fun h k ↦
    cesaroAverage
      (fun n ↦
        (@inner ℂ (Lp ℂ 2 M.μ) _
          (MultipleKhintchineCharacteristic.doubleKoopmanProduct
            M hM F G hFtop (i + (n + k)))
          (MultipleKhintchineCharacteristic.doubleKoopmanProduct
            M hM F G hFtop (i + (n + h)))).re) N
  let Qpair : ℕ → ℕ → ℝ := fun h k ↦
    (productOfMeans M
      (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)
      (fun x ↦ star
        (MultipleKhintchineCharacteristic.leftPairFunction
          M hM F h k x))).re
  have hdecomp :
      cesaroAverage
        (fun n ↦ ∑ h ∈ Finset.range L, ∑ k ∈ Finset.range L,
          (@inner ℂ (Lp ℂ 2 M.μ) _
            (MultipleKhintchineCharacteristic.doubleKoopmanProduct
              M hM F G hFtop (i + (n + k)))
            (MultipleKhintchineCharacteristic.doubleKoopmanProduct
              M hM F G hFtop (i + (n + h)))).re) N =
        ∑ h ∈ Finset.range L, ∑ k ∈ Finset.range L, A h k := by
    unfold A cesaroAverage
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h hh
    rw [Finset.sum_comm]
  have hdiff :
      |(∑ h ∈ Finset.range L, ∑ k ∈ Finset.range L, A h k) - Qlim| ≤
        (L : ℝ) ^ 2 * ρ := by
    have hQ :
        Qlim = ∑ h ∈ Finset.range L, ∑ k ∈ Finset.range L, Qpair h k := by
      rfl
    rw [hQ, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    calc
      |∑ h ∈ Finset.range L,
          ∑ k ∈ Finset.range L, (A h k - Qpair h k)| ≤
          ∑ h ∈ Finset.range L,
            |∑ k ∈ Finset.range L, (A h k - Qpair h k)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h ∈ Finset.range L,
          ∑ k ∈ Finset.range L, |A h k - Qpair h k| := by
        gcongr with h hh
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h ∈ Finset.range L,
          ∑ _k ∈ Finset.range L, ρ := by
        gcongr with h hh k hk
        exact (hN h hh k hk i).le
      _ = (L : ℝ) ^ 2 * ρ := by
        simp
        ring
  rw [hdecomp]
  have hupper :=
    (le_abs_self
      ((∑ h ∈ Finset.range L, ∑ k ∈ Finset.range L, A h k) - Qlim))
  dsimp only [ρ, R, P] at hdiff hQbound ⊢
  nlinarith [sq_pos_of_pos hLreal]

/-- Sharp quantitative generalized von Neumann estimate for a bilinear
progression, uniform over translated intervals and controlled by the
exact `U²` power of the second factor. -/
lemma doubleKoopmanProduct_uniform_cesaro_norm_lt_hostKraU2Power
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1),
            MultipleKhintchineCharacteristic.doubleKoopmanProduct
              M hM F G hFtop (i + n)‖ <
        Real.sqrt
          (2 * C ^ 2 *
              Real.sqrt (2 *
                (hostKraU2Power M hM (fun x ↦ G x) hGtop + η)) + η) +
          η := by
  let B : ℝ :=
    2 * C ^ 2 *
      Real.sqrt (2 *
        (hostKraU2Power M hM (fun x ↦ G x) hGtop + η)) + η
  have hB : 0 < B := by
    dsimp only [B]
    have houter : 0 ≤ Real.sqrt
        (2 * (hostKraU2Power M hM (fun x ↦ G x) hGtop + η)) :=
      Real.sqrt_nonneg _
    positivity
  obtain ⟨L, hL, hcorr⟩ :=
    doubleKoopmanProduct_uniform_blockCorrelation_lt_hostKraU2Power
      M hM hErg F G hFtop hGtop C hC hFbound η hη
  rw [Filter.eventually_atTop] at hcorr
  obtain ⟨Nb, hNb⟩ := hcorr
  let M₀ : ℝ := C * ‖G‖
  have hM₀ : 0 ≤ M₀ := mul_nonneg hC (norm_nonneg G)
  obtain ⟨N₀ : ℕ, hN₀⟩ :=
    exists_nat_gt (2 * (L : ℝ) * M₀ / η)
  refine Filter.eventually_atTop.2 ⟨max Nb N₀, ?_⟩
  intro N hN i
  have hNbN : Nb ≤ N := le_trans (le_max_left _ _) hN
  have hN₀N : N₀ ≤ N := le_trans (le_max_right _ _) hN
  have hCavg := hNb N hNbN i
  let u : ℕ → Lp ℂ 2 M.μ := fun n ↦
    MultipleKhintchineCharacteristic.doubleKoopmanProduct
      M hM F G hFtop n
  let v : ℕ → Lp ℂ 2 M.μ := fun n ↦ u (i + n)
  let Craw : ℝ :=
    ∑ n ∈ Finset.range (N + 1),
      ∑ h ∈ Finset.range L,
        ∑ k ∈ Finset.range L,
          (@inner ℂ (Lp ℂ 2 M.μ) _
            (v (n + k)) (v (n + h))).re
  have hNpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hCavg' :
      (((N + 1 : ℕ) : ℝ)⁻¹) * Craw <
        B * (L : ℝ) ^ 2 := by
    simpa only [cesaroAverage, Craw, v, u, B, Nat.add_assoc] using hCavg
  have hCraw :
      Craw < ((N + 1 : ℕ) : ℝ) * (B * (L : ℝ) ^ 2) := by
    calc
      Craw = ((N + 1 : ℕ) : ℝ) *
          ((((N + 1 : ℕ) : ℝ)⁻¹) * Craw) := by field_simp
      _ < ((N + 1 : ℕ) : ℝ) * (B * (L : ℝ) ^ 2) :=
        mul_lt_mul_of_pos_left hCavg' hNpos
  let Block : Lp ℂ 2 M.μ := ∑ n ∈ Finset.range (N + 1),
    ∑ h ∈ Finset.range L, v (n + h)
  have hblockSq : ‖Block‖ ^ 2 ≤ ((N + 1 : ℕ) : ℝ) * Craw :=
    VanDerCorput.norm_sum_forwardBlocks_sq_le v L (N + 1)
  have hNC : 0 ≤ ((N + 1 : ℕ) : ℝ) * Craw :=
    (sq_nonneg ‖Block‖).trans hblockSq
  have hsqrtSq :
      (Real.sqrt (((N + 1 : ℕ) : ℝ) * Craw)) ^ 2 =
        ((N + 1 : ℕ) : ℝ) * Craw :=
    Real.sq_sqrt hNC
  have hsqrtB :
      (Real.sqrt B) ^ 2 = B :=
    Real.sq_sqrt hB.le
  have hroot :
      Real.sqrt (((N + 1 : ℕ) : ℝ) * Craw) <
        Real.sqrt B * (L : ℝ) * ((N + 1 : ℕ) : ℝ) := by
    have hupper :
        ((N + 1 : ℕ) : ℝ) * Craw <
          (Real.sqrt B * (L : ℝ) * ((N + 1 : ℕ) : ℝ)) ^ 2 := by
      have hfirst :
          ((N + 1 : ℕ) : ℝ) * Craw <
            ((N + 1 : ℕ) : ℝ) *
              (((N + 1 : ℕ) : ℝ) * (B * (L : ℝ) ^ 2)) :=
        mul_lt_mul_of_pos_left hCraw hNpos
      calc
        ((N + 1 : ℕ) : ℝ) * Craw <
            ((N + 1 : ℕ) : ℝ) *
              (((N + 1 : ℕ) : ℝ) * (B * (L : ℝ) ^ 2)) := hfirst
        _ = (Real.sqrt B * (L : ℝ) *
              ((N + 1 : ℕ) : ℝ)) ^ 2 := by
          rw [mul_pow, mul_pow, hsqrtB]
          ring
    have hsqrtNonneg :=
      Real.sqrt_nonneg (((N + 1 : ℕ) : ℝ) * Craw)
    have hrhspos :
        0 < Real.sqrt B * (L : ℝ) * ((N + 1 : ℕ) : ℝ) := by
      have : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
      positivity
    nlinarith
  have hboundary :
      2 * (L : ℝ) ^ 2 * M₀ <
        η * (L : ℝ) * ((N + 1 : ℕ) : ℝ) := by
    have hN₀real : (2 * (L : ℝ) * M₀ / η) < (N₀ : ℝ) := hN₀
    have hNreal : (N₀ : ℝ) ≤ N := by exact_mod_cast hN₀N
    have hratio :
        2 * (L : ℝ) * M₀ / η <
          ((N + 1 : ℕ) : ℝ) := by
      calc
        2 * (L : ℝ) * M₀ / η < (N₀ : ℝ) := hN₀real
        _ ≤ (N : ℝ) := hNreal
        _ < ((N + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.lt_succ_self N
    have hlarge :
        2 * (L : ℝ) * M₀ <
          η * ((N + 1 : ℕ) : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hη).1 hratio
    nlinarith [sq_pos_of_pos hLreal]
  have hu : ∀ n, ‖v n‖ ≤ M₀ := by
    intro n
    exact MultipleKhintchineCharacteristic.norm_doubleKoopmanProduct_le
      M hM F G hFtop C hC hFbound (i + n)
  have hvdc :=
    VanDerCorput.finite_vanDerCorput v M₀ L (N + 1) hu
  change (L : ℝ) *
      ‖∑ n ∈ Finset.range (N + 1), v n‖ ≤
    Real.sqrt (((N + 1 : ℕ) : ℝ) * Craw) +
      2 * (L : ℝ) ^ 2 * M₀ at hvdc
  change
    ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
      ∑ n ∈ Finset.range (N + 1), v n‖ <
        Real.sqrt B + η
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  have hsum :
      ‖∑ n ∈ Finset.range (N + 1), v n‖ <
        (Real.sqrt B + η) * ((N + 1 : ℕ) : ℝ) := by
    nlinarith [sq_pos_of_pos hLreal]
  rw [inv_mul_lt_iff₀ hNpos]
  simpa only [mul_comm] using hsum

/-- The nested-root estimate at the sharp `U²` scale. -/
lemma nested_sqrt_hostKraU2_bound
    (C t p : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : 0 ≤ p) (hpt : p ≤ t ^ 4) :
    Real.sqrt
        (2 * C ^ 2 * Real.sqrt (2 * (p + t ^ 4)) + t ^ 4) +
        t ^ 4 ≤
      (Real.sqrt (4 * C ^ 2 + 1) + 1) * t := by
  have ht2 : t ^ 2 ≤ t := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1)]
  have ht2one : t ^ 2 ≤ 1 := le_trans ht2 ht1
  have ht4 : t ^ 4 ≤ t ^ 2 := by
    nlinarith [sq_nonneg (t ^ 2), mul_nonneg (sq_nonneg t)
      (sub_nonneg.mpr ht2one)]
  have ht4t : t ^ 4 ≤ t := le_trans ht4 ht2
  have hinnerArg : 0 ≤ 2 * (p + t ^ 4) := by positivity
  have hinnerSq :
      (Real.sqrt (2 * (p + t ^ 4))) ^ 2 =
        2 * (p + t ^ 4) :=
    Real.sq_sqrt hinnerArg
  have hinner :
      Real.sqrt (2 * (p + t ^ 4)) ≤ 2 * t ^ 2 := by
    have hsqrtNonneg := Real.sqrt_nonneg (2 * (p + t ^ 4))
    nlinarith [sq_nonneg (t ^ 2)]
  let Y : ℝ :=
    2 * C ^ 2 * Real.sqrt (2 * (p + t ^ 4)) + t ^ 4
  have hY : 0 ≤ Y := by
    dsimp only [Y]
    positivity
  have hYle : Y ≤ (4 * C ^ 2 + 1) * t ^ 2 := by
    dsimp only [Y]
    have hC : 0 ≤ 2 * C ^ 2 := by positivity
    have hmul :=
      mul_le_mul_of_nonneg_left hinner hC
    nlinarith
  have hcoef : 0 ≤ 4 * C ^ 2 + 1 := by positivity
  have hcoefSqrtSq :
      (Real.sqrt (4 * C ^ 2 + 1)) ^ 2 =
        4 * C ^ 2 + 1 :=
    Real.sq_sqrt hcoef
  have hsqrtY :
      Real.sqrt Y ≤ Real.sqrt (4 * C ^ 2 + 1) * t := by
    have hsqrtYSq : (Real.sqrt Y) ^ 2 = Y := Real.sq_sqrt hY
    have hsqrtYnonneg := Real.sqrt_nonneg Y
    have hcoefSqrtNonneg := Real.sqrt_nonneg (4 * C ^ 2 + 1)
    have hrhsNonneg :
        0 ≤ Real.sqrt (4 * C ^ 2 + 1) * t :=
      mul_nonneg hcoefSqrtNonneg ht
    have hrhsSq :
        (Real.sqrt (4 * C ^ 2 + 1) * t) ^ 2 =
          (4 * C ^ 2 + 1) * t ^ 2 := by
      rw [mul_pow, hcoefSqrtSq]
    nlinarith
  dsimp only [Y] at hsqrtY ⊢
  nlinarith

/-- The four-vertex alternating lift is multiplicative. -/
lemma cubeLiftTwo_mul
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f g : M.X → ℂ) :
    cubeLiftTwo M hM (fun x ↦ f x * g x) =
      fun p ↦ cubeLiftTwo M hM f p * cubeLiftTwo M hM g p := by
  funext p
  simp only [cubeLiftTwo, cubeLiftOne, cubeLift, star_mul]
  ring

/-- The four-vertex lift commutes with pointwise conjugation. -/
lemma cubeLiftTwo_star
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) :
    cubeLiftTwo M hM (fun x ↦ star (f x)) =
      fun p ↦ star (cubeLiftTwo M hM f p) := by
  funext p
  simp only [cubeLiftTwo, cubeLiftOne, cubeLift, star_mul, star_star]
  ring

/-- The four-vertex lift intertwines every forward base iterate with the
corresponding second-cube iterate. -/
lemma cubeLiftTwo_iter
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (n : ℕ) :
    cubeLiftTwo M hM (f ∘ (M.T^[n])) =
      cubeLiftTwo M hM f ∘
        ((HostKraStandardRelativeJoining.relativeCubeSystemTwo M hM).T^[n]) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [show f ∘ (M.T^[n + 1]) = (f ∘ (M.T^[n])) ∘ M.T by
        funext x
        simp only [Function.comp_apply, Function.iterate_succ_apply]]
      rw [HostKraCubeSeminormDynamics.cubeLiftTwo_comp, ih]
      funext p
      simp only [Function.comp_apply, Function.iterate_succ_apply]

/-- Lifting a canonical multiplicative derivative through two cube
directions gives the self-correlation integrand of the four-vertex lift. -/
lemma cubeLiftTwo_cubeDerivative_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ) (n : ℕ) :
    cubeLiftTwo M hM (HostKraCubeTwo.cubeDerivative M hM Q n)
      =ᵐ[(HostKraStandardRelativeJoining.relativeCubeSystemTwo M hM).μ]
    fun p ↦
      cubeLiftTwo M hM (fun x ↦ Q x)
          (((HostKraStandardRelativeJoining.relativeCubeSystemTwo
            M hM).T^[n]) p) *
        star (cubeLiftTwo M hM (fun x ↦ Q x) p) := by
  let C1 :=
    HostKraStandardRelativeJoining.relativeCubeSystemOne M hM
  let hC1 :=
    HostKraStandardRelativeJoining.relativeCubeSystemOne_mps M hM
  have hbase :=
    HostKraCubeTwo.cubeDerivative_ae_eq M hM Q n
  have hliftOne :=
    Chapter02.HostKraU3Nullspace.cubeLift_congr_ae M hM hbase
  have hliftTwo :=
    Chapter02.HostKraU3Nullspace.cubeLift_congr_ae
      C1 hC1 hliftOne
  have hpoint :
      cubeLiftTwo M hM
          (fun x ↦ Q ((M.T^[n]) x) * star (Q x)) =
        fun p ↦
          cubeLiftTwo M hM (fun x ↦ Q x)
              (((HostKraStandardRelativeJoining.relativeCubeSystemTwo
                M hM).T^[n]) p) *
            star (cubeLiftTwo M hM (fun x ↦ Q x) p) := by
    rw [cubeLiftTwo_mul]
    change
      (fun p ↦
        cubeLiftTwo M hM ((fun x ↦ Q x) ∘ (M.T^[n])) p *
          cubeLiftTwo M hM (fun x ↦ star (Q x)) p) = _
    rw [cubeLiftTwo_iter, cubeLiftTwo_star]
    rfl
  have hliftTwo' :
      cubeLiftTwo M hM (HostKraCubeTwo.cubeDerivative M hM Q n)
        =ᵐ[(HostKraStandardRelativeJoining.relativeCubeSystemTwo M hM).μ]
      cubeLiftTwo M hM
        (fun x ↦ Q ((M.T^[n]) x) * star (Q x)) := by
    simpa only [cubeLiftTwo] using hliftTwo
  exact hliftTwo'.trans
    (Filter.Eventually.of_forall (fun p ↦ congrFun hpoint p))

/-- The quantitative `U²` power depends only on the almost-everywhere
class of a bounded representative. -/
lemma hostKraU2Power_congr_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f g : M.X → ℂ) (hf : MemLp f ⊤ M.μ) (hg : MemLp g ⊤ M.μ)
    (hfg : f =ᵐ[M.μ] g) :
    hostKraU2Power M hM f hf = hostKraU2Power M hM g hg := by
  let C := HostKraStandardRelativeJoining.relativeCubeSystemOne M hM
  let hC :=
    HostKraStandardRelativeJoining.relativeCubeSystemOne_mps M hM
  let F := cubeLiftOne M hM f
  let G := cubeLiftOne M hM g
  let hF := cubeLiftOne_memLp_two M hM f hf
  let hG := cubeLiftOne_memLp_two M hM g hg
  have hFG : hF.toLp F = hG.toLp G :=
    MemLp.toLp_congr hF hG
      (Chapter02.HostKraU3Nullspace.cubeLift_congr_ae M hM hfg)
  unfold hostKraU2Power
  change
    HostKraCubeSeminorm.invariantEnergy C hC F hF =
      HostKraCubeSeminorm.invariantEnergy C hC G hG
  unfold HostKraCubeSeminorm.invariantEnergy
  rw [HostKraRelativeMean.invariantMeanLp_eq_fixedProjection,
    HostKraRelativeMean.invariantMeanLp_eq_fixedProjection]
  change
    ‖((LinearMap.eqLocus
      (MultipleKhintchineCharacteristic.KData C hC).U
      (1 : Lp ℂ 2 C.μ →L[ℂ] Lp ℂ 2 C.μ)).orthogonalProjection
        (hF.toLp F)).val‖ ^ 2 =
      ‖((LinearMap.eqLocus
        (MultipleKhintchineCharacteristic.KData C hC).U
        (1 : Lp ℂ 2 C.μ →L[ℂ] Lp ℂ 2 C.μ)).orthogonalProjection
          (hG.toLp G)).val‖ ^ 2
  rw [hFG]

/-- Exact recursive identity: the `U²` power of the canonical derivative
at edge `n` is the self-correlation at time `n` of the four-vertex lift. -/
lemma ofReal_hostKraU2Power_cubeDerivativeLp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (n : ℕ) :
    ((hostKraU2Power M hM
      (fun x ↦ HostKraCubeThree.cubeDerivativeLp
        M hM Q hQtop n x)
      (HostKraCubeThree.cubeDerivativeLp_memLp_top
        M hM Q hQtop n) : ℝ) : ℂ) =
      functionCorrelation
        (HostKraStandardRelativeJoining.relativeCubeSystemTwo M hM)
        (cubeLiftTwo M hM (fun x ↦ Q x))
        (cubeLiftTwo M hM (fun x ↦ Q x)) n := by
  let D := HostKraCubeTwo.cubeDerivative M hM Q n
  let hDtop :=
    HostKraCubeTwo.cubeDerivative_memLp_top M hM Q hQtop n
  have hpower :
      hostKraU2Power M hM
          (fun x ↦ HostKraCubeThree.cubeDerivativeLp
            M hM Q hQtop n x)
          (HostKraCubeThree.cubeDerivativeLp_memLp_top
            M hM Q hQtop n) =
        hostKraU2Power M hM D hDtop :=
    hostKraU2Power_congr_ae M hM _ _ _ _
      (HostKraCubeThree.cubeDerivativeLp_coe M hM Q hQtop n)
  let C1 :=
    HostKraStandardRelativeJoining.relativeCubeSystemOne M hM
  let hC1 :=
    HostKraStandardRelativeJoining.relativeCubeSystemOne_mps M hM
  have henergy :=
    Chapter02.HostKraRelativeJoiningComplex.integral_cubeLift_eq_invariantEnergy
      C1 hC1
      (cubeLiftOne M hM D)
      (cubeLiftOne_memLp_top M hM D hDtop)
  calc
    _ = ((hostKraU2Power M hM D hDtop : ℝ) : ℂ) := by
      exact congrArg (fun r : ℝ ↦ (r : ℂ)) hpower
    _ = ∫ p, cubeLiftTwo M hM D p
          ∂(HostKraStandardRelativeJoining.relativeCubeSystemTwo M hM).μ := by
      simpa only [hostKraU2Power, cubeLiftTwo, C1, hC1] using henergy.symm
    _ = functionCorrelation
          (HostKraStandardRelativeJoining.relativeCubeSystemTwo M hM)
          (cubeLiftTwo M hM (fun x ↦ Q x))
          (cubeLiftTwo M hM (fun x ↦ Q x)) n := by
      unfold functionCorrelation
      exact integral_congr_ae
        (cubeLiftTwo_cubeDerivative_ae M hM Q n)

/-- If `Q` is `U³`-null, translated Cesàro averages of the `U²` powers
of all canonical multiplicative derivatives converge uniformly to zero. -/
lemma hasZeroHostKraU3_uniform_cubeDerivativeU2Power_zero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (hzero : HasZeroHostKraU3 M hM (fun x ↦ Q x) hQtop) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
              ((hostKraU2Power M hM
                (fun x ↦ HostKraCubeThree.cubeDerivativeLp
                  M hM Q hQtop (i + n) x)
                (HostKraCubeThree.cubeDerivativeLp_memLp_top
                  M hM Q hQtop (i + n)) : ℝ) : ℂ))
          0 < ε := by
  intro ε hε
  have hlimit :=
    Chapter02.HostKraCubeSeminormRecursion.hasZeroHostKraU3_uniform_cubeCorrelation_zero
      M hM (fun x ↦ Q x) hQtop hzero ε hε
  filter_upwards [hlimit] with N hN
  intro i
  simpa only [ofReal_hostKraU2Power_cubeDerivativeLp] using hN i

/-- Real-valued unshifted form of the preceding derivative-power limit. -/
lemma cubeDerivativeU2Power_average_tendsto_zero_of_hasZeroHostKraU3
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (hzero : HasZeroHostKraU3 M hM (fun x ↦ Q x) hQtop) :
    Tendsto
      (fun N : ℕ ↦ if N = 0 then 0 else
        ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
          hostKraU2Power M hM
            (fun x ↦ HostKraCubeThree.cubeDerivativeLp
              M hM Q hQtop n x)
            (HostKraCubeThree.cubeDerivativeLp_memLp_top
              M hM Q hQtop n))
      atTop (nhds 0) := by
  have huniform :=
    hasZeroHostKraU3_uniform_cubeDerivativeU2Power_zero
      M hM Q hQtop hzero
  have hcomplex :
      Tendsto
        (fun N : ℕ ↦ if N = 0 then 0 else
          ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
            ((hostKraU2Power M hM
              (fun x ↦ HostKraCubeThree.cubeDerivativeLp
                M hM Q hQtop n x)
              (HostKraCubeThree.cubeDerivativeLp_memLp_top
                M hM Q hQtop n) : ℝ) : ℂ))
        atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ :=
      eventually_atTop.1 (huniform ε hε)
    refine ⟨N, ?_⟩
    intro n hn
    simpa using hN n hn 0
  rw [show
      (fun N : ℕ ↦ if N = 0 then 0 else
        ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
          ((hostKraU2Power M hM
            (fun x ↦ HostKraCubeThree.cubeDerivativeLp
              M hM Q hQtop n x)
            (HostKraCubeThree.cubeDerivativeLp_memLp_top
              M hM Q hQtop n) : ℝ) : ℂ)) =
        fun N : ℕ ↦ ((if N = 0 then 0 else
          ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
            hostKraU2Power M hM
              (fun x ↦ HostKraCubeThree.cubeDerivativeLp
                M hM Q hQtop n x)
              (HostKraCubeThree.cubeDerivativeLp_memLp_top
                M hM Q hQtop n) : ℝ) : ℂ) by
    funext N
    by_cases hN : N = 0
    · simp [hN]
    · simp only [hN, if_false]
      push_cast
      rfl] at hcomplex
  simpa only [Function.comp_apply, Complex.ofReal_re, Complex.zero_re] using
    (Complex.continuous_re.continuousAt.tendsto.comp hcomplex)

/-- A `U³`-null vector has arbitrarily small finite sums of derivative
`U²` powers at the triple times needed by the `(1,2,3)` progression. -/
lemma exists_three_cubeDerivativeU2Power_sum_lt_of_hasZeroHostKraU3
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (hzero : HasZeroHostKraU3 M hM (fun x ↦ Q x) hQtop)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ H : ℕ, 0 < H ∧
      (Finset.range H).sum (fun r ↦
        hostKraU2Power M hM
          (fun x ↦ HostKraCubeThree.cubeDerivativeLp
            M hM Q hQtop (3 * r) x)
          (HostKraCubeThree.cubeDerivativeLp_memLp_top
            M hM Q hQtop (3 * r))) < δ * (H : ℝ) := by
  let a : ℕ → ℝ := fun n ↦
    hostKraU2Power M hM
      (fun x ↦ HostKraCubeThree.cubeDerivativeLp
        M hM Q hQtop n x)
      (HostKraCubeThree.cubeDerivativeLp_memLp_top
        M hM Q hQtop n)
  have ha : ∀ n, 0 ≤ a n := by
    intro n
    exact hostKraU2Power_nonneg M hM _ _
  have htend :
      Tendsto
        (fun N : ℕ ↦ if N = 0 then 0 else
          ((N : ℝ)⁻¹) * (Finset.range N).sum a)
        atTop (nhds 0) := by
    simpa only [a] using
      cubeDerivativeU2Power_average_tendsto_zero_of_hasZeroHostKraU3
        M hM Q hQtop hzero
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N₀, hN₀⟩ := htend (δ / 3) (by positivity)
  let H := N₀ + 1
  have hH : 0 < H := by
    dsimp only [H]
    omega
  have hlarge : N₀ ≤ 3 * H := by
    dsimp only [H]
    omega
  have havgdist := hN₀ (3 * H) hlarge
  have hthreeH : 3 * H ≠ 0 := by omega
  have havg_nonneg :
      0 ≤ (((3 * H : ℕ) : ℝ)⁻¹) *
        (Finset.range (3 * H)).sum a := by
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun n hn ↦ ha n)
  have havg :
      (((3 * H : ℕ) : ℝ)⁻¹) *
          (Finset.range (3 * H)).sum a < δ / 3 := by
    simpa only [hthreeH, if_false, Real.dist_eq, sub_zero,
      abs_of_nonneg havg_nonneg] using havgdist
  have hsub :
      (Finset.range H).sum (fun r ↦ a (3 * r)) ≤
        (Finset.range (3 * H)).sum a := by
    let e : ℕ → ℕ := fun r ↦ 3 * r
    have hinj : Set.InjOn e (Finset.range H) := by
      intro x hx y hy hxy
      dsimp only [e] at hxy
      omega
    have himage :
        (Finset.range H).image e ⊆ Finset.range (3 * H) := by
      intro n hn
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hn
      apply Finset.mem_range.mpr
      have hrH := Finset.mem_range.mp hr
      dsimp only [e]
      omega
    calc
      (Finset.range H).sum (fun r ↦ a (3 * r)) =
          ((Finset.range H).image e).sum a := by
        rw [Finset.sum_image hinj]
      _ ≤ (Finset.range (3 * H)).sum a :=
        Finset.sum_le_sum_of_subset_of_nonneg himage
          (fun n hn hnot ↦ ha n)
  refine ⟨H, hH, ?_⟩
  have hthreeHreal : (0 : ℝ) < (3 * H : ℕ) := by
    exact_mod_cast Nat.mul_pos (by omega) hH
  rw [inv_mul_lt_iff₀ hthreeHreal] at havg
  have hfull :
      (Finset.range (3 * H)).sum a < δ * (H : ℝ) := by
    have hcast : (((3 * H : ℕ) : ℝ)) = 3 * (H : ℝ) := by
      exact Nat.cast_mul 3 H
    rw [hcast] at havg
    nlinarith
  exact lt_of_le_of_lt hsub hfull

/-- The one-step cube lift intertwines pointwise conjugation with
conjugation on the relative square. -/
lemma cubeLiftOne_star
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) :
    cubeLiftOne M hM (fun x ↦ star (f x)) =
      fun p ↦ star (cubeLiftOne M hM f p) := by
  funext p
  simp only [cubeLiftOne, cubeLift, star_mul, star_star]
  ring

/-- The quantitative `U²` power is invariant under pointwise complex
conjugation. -/
lemma hostKraU2Power_star
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    hostKraU2Power M hM (fun x ↦ star (f x)) hf.star =
      hostKraU2Power M hM f hf := by
  unfold hostKraU2Power
  let C := HostKraStandardRelativeJoining.relativeCubeSystemOne M hM
  let hC :=
    HostKraStandardRelativeJoining.relativeCubeSystemOne_mps M hM
  change
    invariantEnergy C hC
        (cubeLiftOne M hM (fun x ↦ star (f x))) _ =
      invariantEnergy C hC (cubeLiftOne M hM f) _
  simpa only [cubeLiftOne_star] using
    invariantEnergy_star C hC
      (cubeLiftOne M hM f)
      (cubeLiftOne_memLp_two M hM f hf)

/-- The quantitative `U²` power is invariant under every forward
iterate. -/
lemma hostKraU2Power_iter
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) (n : ℕ) :
    let hfn : MemLp (f ∘ (M.T^[n])) ⊤ M.μ :=
      hf.comp_measurePreserving (hM.2.iterate n)
    hostKraU2Power M hM (f ∘ (M.T^[n])) hfn =
      hostKraU2Power M hM f hf := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let hfn : MemLp (f ∘ (M.T^[n])) ⊤ M.μ :=
        hf.comp_measurePreserving (hM.2.iterate n)
      have hstep :=
        HostKraCubeSeminormDynamics.hostKraU2Power_comp
          M hM (f ∘ (M.T^[n])) hfn
      simpa only [Function.comp_apply, Function.iterate_succ_apply'] using
        hstep.trans ih

/-- For ordered times, the `U²` power of a two-time multiplicative
derivative depends only on their distance. -/
lemma hostKraU2Power_koopmanMultiplicativeDerivative_of_le
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (a b : ℕ) (hab : a ≤ b) :
    hostKraU2Power M hM
        (fun x ↦ koopmanMultiplicativeDerivative
          M hM Q hQtop a b x)
        (koopmanMultiplicativeDerivative_memLp_top
          M hM Q hQtop a b) =
      hostKraU2Power M hM
        (fun x ↦ HostKraCubeThree.cubeDerivativeLp
          M hM Q hQtop (b - a) x)
        (HostKraCubeThree.cubeDerivativeLp_memLp_top
          M hM Q hQtop (b - a)) := by
  let D :=
    HostKraCubeThree.cubeDerivativeLp M hM Q hQtop (b - a)
  let hDtop :=
    HostKraCubeThree.cubeDerivativeLp_memLp_top
      M hM Q hQtop (b - a)
  let hDiter :=
    hDtop.comp_measurePreserving (hM.2.iterate a)
  have hLp :=
    koopmanMultiplicativeDerivative_eq_iter_cubeDerivativeLp_of_le
      M hM Q hQtop a b hab
  have hcoe :
      (fun x ↦ koopmanMultiplicativeDerivative
        M hM Q hQtop a b x) =ᵐ[M.μ]
        (fun x ↦ D ((M.T^[a]) x)) := by
    filter_upwards [
      MultipleKhintchineKronecker.koopmanData_iter_ae
      M hM a D] with x hx
    rw [show
      koopmanMultiplicativeDerivative M hM Q hQtop a b x =
        (show Lp ℂ 2 M.μ from ((KData M hM).U^[a]) D) x by
          exact congrFun (congrArg
            (fun F : Lp ℂ 2 M.μ ↦ fun y ↦ F y) hLp) x]
    exact hx
  calc
    _ = hostKraU2Power M hM
          (fun x ↦ D ((M.T^[a]) x)) hDiter :=
      hostKraU2Power_congr_ae M hM _ _ _ _ hcoe
    _ = hostKraU2Power M hM (fun x ↦ D x) hDtop := by
      simpa only [Function.comp_apply] using
        hostKraU2Power_iter M hM (fun x ↦ D x) hDtop a

/-- In the reverse order the same `U²` distance formula follows through
pointwise conjugation, still using only forward iterates. -/
lemma hostKraU2Power_koopmanMultiplicativeDerivative_of_ge
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (a b : ℕ) (hba : b ≤ a) :
    hostKraU2Power M hM
        (fun x ↦ koopmanMultiplicativeDerivative
          M hM Q hQtop a b x)
        (koopmanMultiplicativeDerivative_memLp_top
          M hM Q hQtop a b) =
      hostKraU2Power M hM
        (fun x ↦ HostKraCubeThree.cubeDerivativeLp
          M hM Q hQtop (a - b) x)
        (HostKraCubeThree.cubeDerivativeLp_memLp_top
          M hM Q hQtop (a - b)) := by
  let D :=
    HostKraCubeThree.cubeDerivativeLp M hM Q hQtop (a - b)
  let hDtop :=
    HostKraCubeThree.cubeDerivativeLp_memLp_top
      M hM Q hQtop (a - b)
  let S := ForwardKroneckerFactor.lpStar M D
  let hStop :=
    HostKraDualFunction.lpStar_memLp_top M D hDtop
  let hSiter :=
    hStop.comp_measurePreserving (hM.2.iterate b)
  have hLp :=
    koopmanMultiplicativeDerivative_eq_iter_star_cubeDerivativeLp_of_le
      M hM Q hQtop a b hba
  have hcoe :
      (fun x ↦ koopmanMultiplicativeDerivative
        M hM Q hQtop a b x) =ᵐ[M.μ]
        (fun x ↦ S ((M.T^[b]) x)) := by
    filter_upwards [
      MultipleKhintchineKronecker.koopmanData_iter_ae
        M hM b S] with x hx
    rw [show
      koopmanMultiplicativeDerivative M hM Q hQtop a b x =
        (show Lp ℂ 2 M.μ from ((KData M hM).U^[b]) S) x by
          exact congrFun (congrArg
            (fun F : Lp ℂ 2 M.μ ↦ fun y ↦ F y) hLp) x]
    exact hx
  calc
    _ = hostKraU2Power M hM
          (fun x ↦ S ((M.T^[b]) x)) hSiter :=
      hostKraU2Power_congr_ae M hM _ _ _ _ hcoe
    _ = hostKraU2Power M hM (fun x ↦ S x) hStop := by
      simpa only [Function.comp_apply] using
        hostKraU2Power_iter M hM (fun x ↦ S x) hStop b
    _ = hostKraU2Power M hM
          (fun x ↦ star (D x)) hDtop.star :=
      hostKraU2Power_congr_ae M hM _ _ _ _
        (ForwardKroneckerFactor.lpStar_coe M D)
    _ = hostKraU2Power M hM (fun x ↦ D x) hDtop :=
      hostKraU2Power_star M hM (fun x ↦ D x) hDtop

/-- A finite row of two-time derivative `U²` powers is controlled by
twice the canonical distance sum. -/
lemma sum_hostKraU2Power_koopmanMultiplicativeDerivative_mul_le
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (c H h : ℕ) (hh : h < H) :
    (Finset.range H).sum (fun k ↦
        hostKraU2Power M hM
          (fun x ↦ koopmanMultiplicativeDerivative
            M hM Q hQtop (c * k) (c * h) x)
          (koopmanMultiplicativeDerivative_memLp_top
            M hM Q hQtop (c * k) (c * h))) ≤
      2 * (Finset.range H).sum (fun r ↦
        hostKraU2Power M hM
          (fun x ↦ HostKraCubeThree.cubeDerivativeLp
            M hM Q hQtop (c * r) x)
          (HostKraCubeThree.cubeDerivativeLp_memLp_top
            M hM Q hQtop (c * r))) := by
  let a : ℕ → ℝ := fun r ↦
    hostKraU2Power M hM
      (fun x ↦ HostKraCubeThree.cubeDerivativeLp
        M hM Q hQtop (c * r) x)
      (HostKraCubeThree.cubeDerivativeLp_memLp_top
        M hM Q hQtop (c * r))
  have ha : ∀ r, 0 ≤ a r := by
    intro r
    exact hostKraU2Power_nonneg M hM _ _
  calc
    (Finset.range H).sum (fun k ↦
        hostKraU2Power M hM
          (fun x ↦ koopmanMultiplicativeDerivative
            M hM Q hQtop (c * k) (c * h) x)
          (koopmanMultiplicativeDerivative_memLp_top
            M hM Q hQtop (c * k) (c * h))) =
      (Finset.range H).sum (fun k ↦
        if k ≤ h then a (h - k) else a (k - h)) := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hkh : k ≤ h
          · rw [if_pos hkh]
            have hmul : c * k ≤ c * h :=
              Nat.mul_le_mul_left c hkh
            simpa only [a, Nat.mul_sub_left_distrib] using
              hostKraU2Power_koopmanMultiplicativeDerivative_of_le
                M hM Q hQtop (c * k) (c * h) hmul
          · rw [if_neg hkh]
            have hhk : h ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hkh)
            have hmul : c * h ≤ c * k :=
              Nat.mul_le_mul_left c hhk
            simpa only [a, Nat.mul_sub_left_distrib] using
              hostKraU2Power_koopmanMultiplicativeDerivative_of_ge
                M hM Q hQtop (c * k) (c * h) hmul
    _ ≤ 2 * (Finset.range H).sum a :=
      MultipleKhintchineCharacteristic.sum_range_split_distance_le
        a ha H h hh

/-- Under `U³` nullity, one finite block makes every row of triple-time
derivative `U²` powers uniformly small. -/
lemma exists_uniform_three_derivativeU2Power_row_sum_lt
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (hzero : HasZeroHostKraU3 M hM (fun x ↦ Q x) hQtop)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ H : ℕ, 0 < H ∧ ∀ h < H,
      (Finset.range H).sum (fun k ↦
        hostKraU2Power M hM
          (fun x ↦ koopmanMultiplicativeDerivative
            M hM Q hQtop (3 * k) (3 * h) x)
          (koopmanMultiplicativeDerivative_memLp_top
            M hM Q hQtop (3 * k) (3 * h))) <
        2 * δ * (H : ℝ) := by
  obtain ⟨H, hH, hsmall⟩ :=
    exists_three_cubeDerivativeU2Power_sum_lt_of_hasZeroHostKraU3
      M hM Q hQtop hzero δ hδ
  refine ⟨H, hH, ?_⟩
  intro h hh
  have hrow :=
    sum_hostKraU2Power_koopmanMultiplicativeDerivative_mul_le
      M hM Q hQtop 3 H h hh
  calc
    _ ≤ 2 * (Finset.range H).sum (fun r ↦
          hostKraU2Power M hM
            (fun x ↦ HostKraCubeThree.cubeDerivativeLp
              M hM Q hQtop (3 * r) x)
            (HostKraCubeThree.cubeDerivativeLp_memLp_top
              M hM Q hQtop (3 * r))) := hrow
    _ < 2 * δ * (H : ℝ) := by nlinarith

/-- If the `U²` power of the third multiplicative derivative is at most
`t⁴`, its scalar triple-progression block correlation is uniformly
`O(t)`. -/
lemma cesaroAverage_re_inner_tripleKoopmanProduct_block_lt_of_u2_le
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ)
    (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ CF)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ CG)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (h k : ℕ)
    (hpower :
      hostKraU2Power M hM
          (fun x ↦
            koopmanMultiplicativeDerivative
              M hM H hHtop (3 * k) (3 * h) x)
          (koopmanMultiplicativeDerivative_memLp_top
            M hM H hHtop (3 * k) (3 * h)) ≤
        t ^ 4) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      cesaroAverage
        (fun n ↦
          (@inner ℂ (Lp ℂ 2 M.μ) _
            (tripleKoopmanProduct M hM F G H hFtop hGtop
              (i + (n + k)))
            (tripleKoopmanProduct M hM F G H hFtop hGtop
              (i + (n + h)))).re) N <
        (CF * ‖F‖ + 1) *
          (Real.sqrt (4 * (CG ^ 2) ^ 2 + 1) + 1) * t := by
  let DG : Lp ℂ 2 M.μ :=
    koopmanMultiplicativeDerivative M hM G hGtop (2 * k) (2 * h)
  let DH : Lp ℂ 2 M.μ :=
    koopmanMultiplicativeDerivative M hM H hHtop (3 * k) (3 * h)
  let A : Lp ℂ 2 M.μ :=
    ForwardKroneckerFactor.lpStar M
      (koopmanMultiplicativeDerivative M hM F hFtop k h)
  let hDGtop : MemLp (fun x ↦ DG x) ⊤ M.μ :=
    koopmanMultiplicativeDerivative_memLp_top
      M hM G hGtop (2 * k) (2 * h)
  let hDHtop : MemLp (fun x ↦ DH x) ⊤ M.μ :=
    koopmanMultiplicativeDerivative_memLp_top
      M hM H hHtop (3 * k) (3 * h)
  have hη : 0 < t ^ 4 := pow_pos ht 4
  have hquant :=
    doubleKoopmanProduct_uniform_cesaro_norm_lt_hostKraU2Power
      M hM hErg DG DH hDGtop hDHtop
      (CG ^ 2) (sq_nonneg CG)
      (by
        simpa only [DG] using
          koopmanMultiplicativeDerivative_norm_le
            M hM G hGtop CG hCG hGbound (2 * k) (2 * h))
      (t ^ 4) hη
  filter_upwards [hquant] with N hN
  intro i
  let v : ℕ → Lp ℂ 2 M.μ := fun n ↦
    MultipleKhintchineCharacteristic.doubleKoopmanProduct
      M hM DG DH hDGtop (i + n)
  have havg :
      cesaroAverage
        (fun n ↦
          (@inner ℂ (Lp ℂ 2 M.μ) _
            (tripleKoopmanProduct M hM F G H hFtop hGtop
              (i + (n + k)))
            (tripleKoopmanProduct M hM F G H hFtop hGtop
              (i + (n + h)))).re) N =
        (@inner ℂ (Lp ℂ 2 M.μ) _ A
          ((((N + 1 : ℕ) : ℂ)⁻¹) •
            ∑ n ∈ Finset.range (N + 1), v n)).re := by
    calc
      _ = cesaroAverage
          (fun n ↦ (@inner ℂ (Lp ℂ 2 M.μ) _ A (v n)).re) N := by
        apply congrArg (fun q : ℕ → ℝ ↦ cesaroAverage q N)
        funext n
        simpa only [A, v, DG, DH, hDGtop] using
          congrArg Complex.re
            (inner_tripleKoopmanProduct_block_eq_derivative_doubleKoopmanProduct
              M hM F G H hFtop hGtop hHtop i n h k)
      _ = _ := cesaroAverage_re_inner_right M A v N
  rw [havg]
  have hAnorm : ‖A‖ ≤ CF * ‖F‖ := by
    dsimp only [A]
    rw [ForwardKroneckerFactor.norm_lpStar]
    exact norm_koopmanMultiplicativeDerivative_le
      M hM F hFtop CF hCF hFbound k h
  have hD : 0 ≤ CF * ‖F‖ := mul_nonneg hCF (norm_nonneg F)
  have hpnonneg :
      0 ≤ hostKraU2Power M hM (fun x ↦ DH x) hDHtop :=
    hostKraU2Power_nonneg M hM (fun x ↦ DH x) hDHtop
  have hnested :=
    nested_sqrt_hostKraU2_bound
      (CG ^ 2) t
      (hostKraU2Power M hM (fun x ↦ DH x) hDHtop)
      ht.le ht1 hpnonneg (by simpa only [DH, hDHtop] using hpower)
  have hvec := hN i
  have hKt :
      0 < (Real.sqrt (4 * (CG ^ 2) ^ 2 + 1) + 1) * t := by
    positivity
  calc
    (@inner ℂ (Lp ℂ 2 M.μ) _ A
        ((((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1), v n)).re ≤
        ‖@inner ℂ (Lp ℂ 2 M.μ) _ A
          ((((N + 1 : ℕ) : ℂ)⁻¹) •
            ∑ n ∈ Finset.range (N + 1), v n)‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    _ ≤ ‖A‖ *
        ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1), v n‖ :=
      norm_inner_le_norm _ _
    _ ≤ (CF * ‖F‖) *
        ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1), v n‖ :=
      mul_le_mul_of_nonneg_right hAnorm (norm_nonneg _)
    _ ≤ (CF * ‖F‖) *
        ((Real.sqrt (4 * (CG ^ 2) ^ 2 + 1) + 1) * t) := by
      exact mul_le_mul_of_nonneg_left
        (hvec.le.trans hnested) hD
    _ < (CF * ‖F‖ + 1) *
        (Real.sqrt (4 * (CG ^ 2) ^ 2 + 1) + 1) * t := by
      nlinarith

/-- `U³` nullity of the third factor gives uniform van der Corput
block-correlation decay for the `(1,2,3)` progression. -/
lemma tripleKoopmanProduct_hasUniformVanDerCorputBlockDecay_of_hasZeroHostKraU3
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ)
    (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ CF)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ CG)
    (hzero : HasZeroHostKraU3 M hM (fun x ↦ H x) hHtop) :
    VanDerCorput.HasUniformVanDerCorputBlockDecay
      (tripleKoopmanProduct M hM F G H hFtop hGtop) := by
  intro δ hδ
  let K : ℝ :=
    (CF * ‖F‖ + 1) *
      (Real.sqrt (4 * (CG ^ 2) ^ 2 + 1) + 1)
  let B : ℝ := ((CF * CG) * ‖H‖) ^ 2
  have hK : 0 < K := by
    dsimp only [K]
    have hCFnorm : 0 ≤ CF * ‖F‖ :=
      mul_nonneg hCF (norm_nonneg F)
    positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  let t : ℝ := min 1 (δ / (8 * K))
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have htK : K * t ≤ δ / 8 := by
    have htupper : t ≤ δ / (8 * K) := min_le_right _ _
    rw [le_div_iff₀ (by positivity : 0 < (8 : ℝ))]
    calc
      K * t * 8 = (8 * K) * t := by ring
      _ ≤ (8 * K) * (δ / (8 * K)) :=
        mul_le_mul_of_nonneg_left htupper (by positivity)
      _ = δ := by field_simp
  have ht4 : 0 < t ^ 4 := pow_pos ht 4
  let α : ℝ := δ * t ^ 4 / (16 * (B + 1))
  have hα : 0 < α := by
    dsimp only [α]
    positivity
  obtain ⟨L, hL, hrow⟩ :=
    exists_uniform_three_derivativeU2Power_row_sum_lt
      M hM H hHtop hzero α hα
  refine ⟨L, hL, ?_⟩
  let p : ℕ → ℕ → ℝ := fun h k ↦
    hostKraU2Power M hM
      (fun x ↦ koopmanMultiplicativeDerivative
        M hM H hHtop (3 * k) (3 * h) x)
      (koopmanMultiplicativeDerivative_memLp_top
        M hM H hHtop (3 * k) (3 * h))
  have hpnonneg : ∀ h k, 0 ≤ p h k := by
    intro h k
    exact hostKraU2Power_nonneg M hM _ _
  have hall :
      ∀ᶠ N : ℕ in atTop,
        ∀ h ∈ Finset.range L, ∀ k ∈ Finset.range L, ∀ i : ℕ,
          cesaroAverage
            (fun n ↦
              (@inner ℂ (Lp ℂ 2 M.μ) _
                (tripleKoopmanProduct M hM F G H hFtop hGtop
                  (i + (n + k)))
                (tripleKoopmanProduct M hM F G H hFtop hGtop
                  (i + (n + h)))).re) N ≤
            if t ^ 4 ≤ p h k then B else K * t := by
    rw [Filter.eventually_all_finset]
    intro h hh
    rw [Filter.eventually_all_finset]
    intro k hk
    by_cases hbad : t ^ 4 ≤ p h k
    · exact Filter.Eventually.of_forall fun N i ↦ by
        rw [if_pos hbad]
        dsimp only [B]
        exact cesaroAverage_re_inner_tripleKoopmanProduct_block_le
          M hM F G H hFtop hGtop CF CG hCF hCG
          hFbound hGbound N i h k
    · have hgood : p h k ≤ t ^ 4 :=
        le_of_lt (lt_of_not_ge hbad)
      have hevent :=
        cesaroAverage_re_inner_tripleKoopmanProduct_block_lt_of_u2_le
          M hM hErg F G H hFtop hGtop hHtop
          CF CG hCF hCG hFbound hGbound t ht ht1 h k
          (by simpa only [p] using hgood)
      filter_upwards [hevent] with N hN
      intro i
      rw [if_neg hbad]
      simpa only [K, mul_assoc] using (hN i).le
  filter_upwards [hall] with N hN
  intro i
  rw [cesaroAverage_sum_range_two]
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hgoodrow : 0 ≤ K * t := mul_nonneg hK.le ht.le
  have hrowBound (h : ℕ) (hh : h < L) :
      (Finset.range L).sum (fun k ↦
        cesaroAverage
          (fun n ↦
            (@inner ℂ (Lp ℂ 2 M.μ) _
              (tripleKoopmanProduct M hM F G H hFtop hGtop
                (i + (n + k)))
              (tripleKoopmanProduct M hM F G H hFtop hGtop
                (i + (n + h)))).re) N) <
        δ / 4 * (L : ℝ) := by
    let Bad := (Finset.range L).filter (fun k ↦ t ^ 4 ≤ p h k)
    have hsum :=
      sum_range_le_good_add_bad
        (fun k ↦
          cesaroAverage
            (fun n ↦
              (@inner ℂ (Lp ℂ 2 M.μ) _
                (tripleKoopmanProduct M hM F G H hFtop hGtop
                  (i + (n + k)))
                (tripleKoopmanProduct M hM F G H hFtop hGtop
                  (i + (n + h)))).re) N)
        (p h) L (t ^ 4) (K * t) B hgoodrow
        (fun k hk ↦ hN h (Finset.mem_range.mpr hh)
          k (Finset.mem_range.mpr hk) i)
    have hmark :
        (Bad.card : ℝ) * t ^ 4 < (2 * α) * (L : ℝ) := by
      apply card_filter_threshold_mul_lt_of_sum_lt
        (p h) (hpnonneg h) L (t ^ 4) (2 * α)
      simpa only [p, Bad, mul_assoc] using hrow h hh
    have hbadScaled :
        (Bad.card : ℝ) * B < δ / 8 * (L : ℝ) := by
      by_cases hBzero : B = 0
      · simp only [hBzero, mul_zero]
        positivity
      · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBzero)
        have hmul :
            ((Bad.card : ℝ) * t ^ 4) * B <
              ((2 * α) * (L : ℝ)) * B :=
          mul_lt_mul_of_pos_right hmark hBpos
        have hratio : B / (B + 1) ≤ 1 := by
          exact (div_le_one (by positivity : 0 < B + 1)).2 (by linarith)
        have hcoef :
            2 * α * B ≤ δ / 8 * t ^ 4 := by
          calc
            2 * α * B =
                (δ * t ^ 4 / 8) * (B / (B + 1)) := by
              dsimp only [α]
              field_simp
              norm_num
            _ ≤ (δ * t ^ 4 / 8) * 1 :=
              mul_le_mul_of_nonneg_left hratio (by positivity)
            _ = δ / 8 * t ^ 4 := by ring
        have hscaled :
            ((Bad.card : ℝ) * B) * t ^ 4 <
              (δ / 8 * (L : ℝ)) * t ^ 4 := by
          calc
            ((Bad.card : ℝ) * B) * t ^ 4 =
                ((Bad.card : ℝ) * t ^ 4) * B := by ring
            _ < ((2 * α) * (L : ℝ)) * B := hmul
            _ = (2 * α * B) * (L : ℝ) := by ring
            _ ≤ (δ / 8 * t ^ 4) * (L : ℝ) :=
              mul_le_mul_of_nonneg_right hcoef hLreal.le
            _ = (δ / 8 * (L : ℝ)) * t ^ 4 := by ring
        nlinarith [hscaled]
    calc
      _ ≤ (L : ℝ) * (K * t) + (Bad.card : ℝ) * B := by
        simpa only [Bad] using hsum
      _ < δ / 4 * (L : ℝ) := by
        have hgoodScaled :
            (L : ℝ) * (K * t) ≤ δ / 8 * (L : ℝ) := by
          nlinarith
        nlinarith
  calc
    ∑ h ∈ Finset.range L, ∑ k ∈ Finset.range L,
        cesaroAverage
          (fun n ↦
            (@inner ℂ (Lp ℂ 2 M.μ) _
              (tripleKoopmanProduct M hM F G H hFtop hGtop
                (i + (n + k)))
              (tripleKoopmanProduct M hM F G H hFtop hGtop
                (i + (n + h)))).re) N <
        ∑ _h ∈ Finset.range L, δ / 4 * (L : ℝ) := by
      apply Finset.sum_lt_sum
      · intro h hh
        exact (hrowBound h (Finset.mem_range.mp hh)).le
      · exact ⟨0, Finset.mem_range.mpr hL,
          hrowBound 0 hL⟩
    _ = δ / 4 * (L : ℝ) ^ 2 := by
      simp
      ring
    _ < δ * (L : ℝ) ^ 2 := by
      nlinarith [sq_pos_of_pos hLreal]

/-- Uniform translated `L²` decay of the three-factor progression when
its third factor is `U³`-null. -/
lemma tripleKoopmanProduct_uniform_cesaro_norm_zero_of_hasZeroHostKraU3
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ)
    (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ CF)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ CG)
    (hzero : HasZeroHostKraU3 M hM (fun x ↦ H x) hHtop) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1),
            tripleKoopmanProduct M hM F G H hFtop hGtop (i + n)‖ < ε := by
  exact VanDerCorput.vectorCesaro_uniform_tendsto_zero_of_blockDecay
    (tripleKoopmanProduct M hM F G H hFtop hGtop)
    ((CF * CG) * ‖H‖)
    (norm_tripleKoopmanProduct_le
      M hM F G H hFtop hGtop CF CG hCF hCG hFbound hGbound)
    (tripleKoopmanProduct_hasUniformVanDerCorputBlockDecay_of_hasZeroHostKraU3
      M hM hErg F G H hFtop hGtop hHtop
      CF CG hCF hCG hFbound hGbound hzero)

/-- Pairing the checked vector decay with a fixed zeroth factor gives
complex (not merely real-part) uniform cancellation of the scalar
four-term progression. -/
theorem integral_quadruple_uniform_complex_zero_of_hasZeroHostKraU3
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F₀ F₁ F₂ F₃ : Lp ℂ 2 M.μ)
    (hF₁top : MemLp (fun x ↦ F₁ x) ⊤ M.μ)
    (hF₂top : MemLp (fun x ↦ F₂ x) ⊤ M.μ)
    (hF₃top : MemLp (fun x ↦ F₃ x) ⊤ M.μ)
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hF₁bound : ∀ᵐ x ∂M.μ, ‖F₁ x‖ ≤ C₁)
    (hF₂bound : ∀ᵐ x ∂M.μ, ‖F₂ x‖ ≤ C₂)
    (hzero : HasZeroHostKraU3 M hM (fun x ↦ F₃ x) hF₃top) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        ‖(((N + 1 : ℕ) : ℂ)⁻¹) *
          ∑ n ∈ Finset.range (N + 1),
            ∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
              (fun x ↦ F₀ x) (fun x ↦ F₁ x)
              (fun x ↦ F₂ x) (fun x ↦ F₃ x)
              (i + n) x ∂M.μ‖ < ε := by
  intro ε hε
  let A := ForwardKroneckerFactor.lpStar M F₀
  let v : ℕ → Lp ℂ 2 M.μ := fun n ↦
    tripleKoopmanProduct M hM F₁ F₂ F₃ hF₁top hF₂top n
  let δ : ℝ := ε / (‖A‖ + 1)
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hvec :=
    tripleKoopmanProduct_uniform_cesaro_norm_zero_of_hasZeroHostKraU3
      M hM hErg F₁ F₂ F₃ hF₁top hF₂top hF₃top
      C₁ C₂ hC₁ hC₂ hF₁bound hF₂bound hzero δ hδ
  filter_upwards [hvec] with N hN
  intro i
  let V : Lp ℂ 2 M.μ :=
    (((N + 1 : ℕ) : ℂ)⁻¹) •
      ∑ n ∈ Finset.range (N + 1), v (i + n)
  have heq :
      (((N + 1 : ℕ) : ℂ)⁻¹) *
          ∑ n ∈ Finset.range (N + 1),
            ∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
              (fun x ↦ F₀ x) (fun x ↦ F₁ x)
              (fun x ↦ F₂ x) (fun x ↦ F₃ x)
              (i + n) x ∂M.μ =
        @inner ℂ (Lp ℂ 2 M.μ) _ A V := by
    dsimp only [A, V, v]
    simp only [
      ← Chapter02.HostKraU4Characteristic.inner_lpStar_tripleKoopmanProduct_eq_integral_quadruple
        M hM F₀ F₁ F₂ F₃ hF₁top hF₂top,
      inner_smul_right, inner_sum, Finset.mul_sum]
  rw [heq]
  have hinner :
      ‖@inner ℂ (Lp ℂ 2 M.μ) _ A V‖ ≤ ‖A‖ * ‖V‖ :=
    norm_inner_le_norm _ _
  have hV : ‖V‖ < δ := by
    simpa only [V, v] using hN i
  have hmul : ‖A‖ * ‖V‖ < ε := by
    calc
      ‖A‖ * ‖V‖ ≤ ‖A‖ * δ :=
        mul_le_mul_of_nonneg_left hV.le (norm_nonneg A)
      _ < (‖A‖ + 1) * δ :=
        mul_lt_mul_of_pos_right (by linarith) hδ
      _ = ε := by
        dsimp only [δ]
        field_simp
  exact lt_of_le_of_lt hinner hmul

/-- Function-valued form of the preceding theorem.  This is convenient
for ergodic components, where the same bounded representatives are used
with different component measures. -/
theorem integral_quadruple_uniform_complex_zero_of_hasZeroHostKraU3_fun
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (hf₀ : MemLp f₀ ⊤ M.μ)
    (hf₁ : MemLp f₁ ⊤ M.μ)
    (hf₂ : MemLp f₂ ⊤ M.μ)
    (hf₃ : MemLp f₃ ⊤ M.μ)
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hf₁bound : ∀ᵐ x ∂M.μ, ‖f₁ x‖ ≤ C₁)
    (hf₂bound : ∀ᵐ x ∂M.μ, ‖f₂ x‖ ≤ C₂)
    (hzero : HasZeroHostKraU3 M hM f₃ hf₃) :
    HostKraU3FourTermReversal.HasUniformFourTermIntegralDecay
      M f₀ f₁ f₂ f₃ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let hf₀two : M.lpMember 2 f₀ := hf₀.mono_exponent (by simp)
  let hf₁two : M.lpMember 2 f₁ := hf₁.mono_exponent (by simp)
  let hf₂two : M.lpMember 2 f₂ := hf₂.mono_exponent (by simp)
  let hf₃two : M.lpMember 2 f₃ := hf₃.mono_exponent (by simp)
  let F₀ := hf₀two.toLp f₀
  let F₁ := hf₁two.toLp f₁
  let F₂ := hf₂two.toLp f₂
  let F₃ := hf₃two.toLp f₃
  have hF₁top : MemLp (fun x ↦ F₁ x) ⊤ M.μ :=
    (memLp_congr_ae hf₁two.coeFn_toLp).2 hf₁
  have hF₂top : MemLp (fun x ↦ F₂ x) ⊤ M.μ :=
    (memLp_congr_ae hf₂two.coeFn_toLp).2 hf₂
  have hF₃top : MemLp (fun x ↦ F₃ x) ⊤ M.μ :=
    (memLp_congr_ae hf₃two.coeFn_toLp).2 hf₃
  have hF₁bound : ∀ᵐ x ∂M.μ, ‖F₁ x‖ ≤ C₁ := by
    filter_upwards [hf₁two.coeFn_toLp, hf₁bound] with x hx hb
    rw [hx]
    exact hb
  have hF₂bound : ∀ᵐ x ∂M.μ, ‖F₂ x‖ ≤ C₂ := by
    filter_upwards [hf₂two.coeFn_toLp, hf₂bound] with x hx hb
    rw [hx]
    exact hb
  have hF₃zero :
      HasZeroHostKraU3 M hM (fun x ↦ F₃ x) hF₃top := by
    unfold HasZeroHostKraU3 at hzero ⊢
    rw [hostKraU3Power_congr_ae M hM
      (fun x ↦ F₃ x) f₃ hF₃top hf₃ hf₃two.coeFn_toLp]
    exact hzero
  have hdecay :=
    integral_quadruple_uniform_complex_zero_of_hasZeroHostKraU3
      M hM hErg F₀ F₁ F₂ F₃ hF₁top hF₂top hF₃top
      C₁ C₂ hC₁ hC₂ hF₁bound hF₂bound hF₃zero
  intro ε hε
  filter_upwards [hdecay ε hε] with N hN
  intro i
  have hint (n : ℕ) :
      (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
        f₀ f₁ f₂ f₃ n x ∂M.μ) =
      ∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
        (fun x ↦ F₀ x) (fun x ↦ F₁ x)
        (fun x ↦ F₂ x) (fun x ↦ F₃ x) n x ∂M.μ := by
    apply integral_congr_ae
    filter_upwards [
      hf₀two.coeFn_toLp,
      (hM.2.iterate n).quasiMeasurePreserving.ae_eq
        hf₁two.coeFn_toLp,
      (hM.2.iterate (2 * n)).quasiMeasurePreserving.ae_eq
        hf₂two.coeFn_toLp,
      (hM.2.iterate (3 * n)).quasiMeasurePreserving.ae_eq
        hf₃two.coeFn_toLp] with x h₀ h₁ h₂ h₃
    simp only [MultipleKhintchineCartesian.quadrupleIntegrand]
    have h₁' : F₁ ((M.T^[n]) x) = f₁ ((M.T^[n]) x) := by
      simpa only [Function.comp_apply] using h₁
    have h₂' : F₂ ((M.T^[2 * n]) x) = f₂ ((M.T^[2 * n]) x) := by
      simpa only [Function.comp_apply] using h₂
    have h₃' : F₃ ((M.T^[3 * n]) x) = f₃ ((M.T^[3 * n]) x) := by
      simpa only [Function.comp_apply] using h₃
    rw [← h₀, ← h₁', ← h₂', ← h₃']
  simpa only [hint] using hN i

end Chapter02.HostKraU3OptimalProgressionDecay
