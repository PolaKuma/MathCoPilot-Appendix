import Chapter00.Renewal.RenewalEnergy

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter00
namespace Renewal

def natSigmaAntidiagonalEquivProd :
    (Σ n : ℕ, {x // x ∈ Finset.antidiagonal n}) ≃ ℕ × ℕ where
  toFun x := x.2.1
  invFun x := ⟨x.1 + x.2, x, by simp⟩
  left_inv x := by
    rcases x with ⟨n, ⟨⟨a, b⟩, hab⟩⟩
    simp only [Finset.mem_antidiagonal] at hab
    subst n
    rfl
  right_inv x := rfl

@[simp] lemma natSigmaAntidiagonalEquivProd_apply
    (x : (Σ n : ℕ, {x // x ∈ Finset.antidiagonal n})) :
    natSigmaAntidiagonalEquivProd x = x.2.1 := rfl

lemma tsum_ofReal_stepTail {p : ℕ → ℝ}
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p) :
    (∑' k, ENNReal.ofReal (stepTail p k)) =
      ∑' n, ((n + 1 : ℕ) : ENNReal) * ENNReal.ofReal (p n) := by
  have htail (k : ℕ) : ENNReal.ofReal (stepTail p k) =
      ∑' n, ENNReal.ofReal (p (n + k)) := by
    unfold stepTail
    exact ENNReal.ofReal_tsum_of_nonneg
      (fun n ↦ hp (n + k)) ((summable_nat_add_iff k).2 hs)
  simp_rw [htail]
  rw [← ENNReal.tsum_prod (f := fun k n ↦ ENNReal.ofReal (p (n + k)))]
  rw [← Equiv.tsum_eq natSigmaAntidiagonalEquivProd
    (fun x : ℕ × ℕ ↦ ENNReal.ofReal (p (x.2 + x.1)))]
  calc
    _ = ∑' c : (Σ n : ℕ, {x // x ∈ Finset.antidiagonal n}),
        ENNReal.ofReal (p c.1) := by
      apply tsum_congr
      rintro ⟨n, ⟨⟨a, b⟩, hab⟩⟩
      simp only [natSigmaAntidiagonalEquivProd_apply]
      rw [Finset.mem_antidiagonal] at hab
      rw [add_comm, hab]
    _ = _ := by
      rw [ENNReal.tsum_sigma' (fun c :
        (Σ n : ℕ, {x // x ∈ Finset.antidiagonal n}) ↦ ENNReal.ofReal (p c.1))]
      apply tsum_congr
      intro n
      simp

lemma tendsto_renewalResponse {p e : ℕ → ℝ}
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p)
    (ht : ∑' n, p n = 1)
    (haper : ∀ q : ℕ,
      (∀ n, 0 < shiftedWeights p n → q ∣ n) → q = 1)
    (he0 : ∀ n, 0 ≤ e n) (he : Summable e) :
    Tendsto (renewalResponse p e) atTop
      (nhds (ENNReal.toReal
        ((∑' n, ENNReal.ofReal (e n)) /
          (∑' n, ENNReal.ofReal (stepTail p n))))) := by
  have hr := tendsto_renewalMass hp hs ht haper
  have hrBound : ∀ n, |renewalMass p n| ≤ 1 := by
    intro n
    rw [abs_of_nonneg (renewalMass_nonneg_le_one hp hs ht n).1]
    exact (renewalMass_nonneg_le_one hp hs ht n).2
  have hconv := tendsto_natConvolution_of_summable he0 he hrBound hr
  rw [renewalResponse_eq_convolution]
  convert hconv using 1
  have heOf : ENNReal.ofReal (∑' n, e n) =
      ∑' n, ENNReal.ofReal (e n) :=
    ENNReal.ofReal_tsum_of_nonneg he0 he
  by_cases hQ : Summable (stepTail p)
  · have hQOf : ENNReal.ofReal (∑' n, stepTail p n) =
        ∑' n, ENNReal.ofReal (stepTail p n) :=
      ENNReal.ofReal_tsum_of_nonneg (stepTail_nonneg hp) hQ
    have henumTop : (∑' n, ENNReal.ofReal (e n)) ≠ ⊤ := by
      rw [← heOf]
      exact ENNReal.ofReal_ne_top
    have hdenTop : (∑' n, ENNReal.ofReal (stepTail p n)) ≠ ⊤ := by
      rw [← hQOf]
      exact ENNReal.ofReal_ne_top
    rw [← heOf, ← hQOf, ENNReal.toReal_div, ENNReal.toReal_ofReal,
      ENNReal.toReal_ofReal]
    · ring
    · exact tsum_nonneg (stepTail_nonneg hp)
    · exact tsum_nonneg he0
  · have htop : (∑' n, ENNReal.ofReal (stepTail p n)) = ⊤ := by
      by_contra hne
      have hsReal := ENNReal.summable_toReal hne
      apply hQ
      simpa [ENNReal.toReal_ofReal (stepTail_nonneg hp _)] using hsReal
    rw [htop, ENNReal.div_top, ENNReal.toReal_zero,
      tsum_eq_zero_of_not_summable hQ, div_zero, mul_zero]

lemma tsum_ofReal_normalizedForcing {c d : ℕ → ℝ}
    (hc0 : c 0 < 1) :
    (∑' n, ENNReal.ofReal (normalizedForcing c d n)) =
      (∑' n, ENNReal.ofReal (d n)) / ENNReal.ofReal (1 - c 0) := by
  have ha : 0 < 1 - c 0 := sub_pos.mpr hc0
  simp_rw [normalizedForcing, ENNReal.ofReal_div_of_pos ha, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right]

lemma tsum_ofReal_normalizedStepTail {c : ℕ → ℝ}
    (hc : ∀ n, 0 ≤ c n) (hcs : Summable c) (hc0 : c 0 < 1) :
    (∑' k, ENNReal.ofReal (stepTail (normalizedStepWeights c) k)) =
      (∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * c n)) /
        ENNReal.ofReal (1 - c 0) := by
  have ha : 0 < 1 - c 0 := sub_pos.mpr hc0
  rw [tsum_ofReal_stepTail (normalizedStepWeights_nonneg hc hc0)
    (summable_normalizedStepWeights hcs)]
  have hterm (n : ℕ) :
      ((n + 1 : ℕ) : ENNReal) *
          ENNReal.ofReal (normalizedStepWeights c n) =
        ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * c (n + 1)) /
          ENNReal.ofReal (1 - c 0) := by
    rw [normalizedStepWeights, ENNReal.ofReal_div_of_pos ha,
      ← ENNReal.ofReal_natCast, ← mul_div_assoc,
      ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  rw [show
    (fun n : ℕ ↦ ((n + 1 : ℕ) : ENNReal) *
        ENNReal.ofReal (normalizedStepWeights c n)) =
      (fun n : ℕ ↦ ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * c (n + 1)) /
        ENNReal.ofReal (1 - c 0)) from funext hterm]
  simp_rw [div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right]
  congr 1
  have hsplit := tsum_eq_zero_add'
    (f := fun n : ℕ ↦ ENNReal.ofReal ((n : ℝ) * c n)) ENNReal.summable
  simpa only [Nat.cast_zero, zero_mul, ENNReal.ofReal_zero, zero_add] using hsplit.symm

lemma toReal_div_div_cancel_right {D M A : ENNReal}
    (hA0 : A ≠ 0) (hAtop : A ≠ ⊤) :
    ENNReal.toReal ((D / A) / (M / A)) = ENNReal.toReal (D / M) := by
  simp_rw [ENNReal.toReal_div]
  exact div_div_div_cancel_right₀ ((ENNReal.toReal_ne_zero).2 ⟨hA0, hAtop⟩) _ _

lemma renewalTheorem_core (c d u : ℕ → ℝ)
    (hdata : ∀ n, 0 ≤ c n ∧ c n ≤ 1 ∧ 0 ≤ d n)
    (haper : ∀ q : ℕ, (∀ n, 0 < c n → q ∣ n) → q = 1)
    (hrec : ∀ n, u n = d n +
      (Finset.range (n + 1)).sum fun j ↦ c j * u (n - j))
    (hctsum : (∑' n : ℕ, ENNReal.ofReal (c n)) = 1)
    (hdtsum : (∑' n : ℕ, ENNReal.ofReal (d n)) < (⊤ : ENNReal)) :
    Tendsto u atTop (nhds
      (ENNReal.toReal ((∑' n : ℕ, ENNReal.ofReal (d n)) /
        (∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * c n))))) := by
  have hc (n : ℕ) : 0 ≤ c n := (hdata n).1
  have hd (n : ℕ) : 0 ≤ d n := (hdata n).2.2
  have hc0 : c 0 < 1 := coefficient_zero_lt_one haper hctsum
  have ha : 0 < 1 - c 0 := sub_pos.mpr hc0
  have hcs : Summable c := summable_of_ofReal_tsum_ne_top hc (by simp [hctsum])
  have hds : Summable d :=
    summable_of_ofReal_tsum_ne_top hd (ne_of_lt hdtsum)
  have hct : ∑' n : ℕ, c n = 1 :=
    tsum_eq_one_of_ofReal_tsum_eq_one hc hctsum
  have hp0 (n : ℕ) : 0 ≤ normalizedStepWeights c n :=
    normalizedStepWeights_nonneg hc hc0 n
  have hps : Summable (normalizedStepWeights c) :=
    summable_normalizedStepWeights hcs
  have hpt : ∑' n : ℕ, normalizedStepWeights c n = 1 :=
    tsum_normalizedStepWeights hc0 hcs hct
  have hpAper : ∀ q : ℕ,
      (∀ n, 0 < shiftedWeights (normalizedStepWeights c) n → q ∣ n) → q = 1 := by
    intro q hq
    apply haper q
    intro n hn
    cases n with
    | zero => simp
    | succ n =>
        apply hq (n + 1)
        simpa [shiftedWeights, normalizedStepWeights] using div_pos hn ha
  have he0 (n : ℕ) : 0 ≤ normalizedForcing c d n := by
    exact div_nonneg (hd n) ha.le
  have hes : Summable (normalizedForcing c d) := by
    unfold normalizedForcing
    exact hds.div_const _
  obtain ⟨hu0, hurec⟩ := normalized_renewal_recurrence hc0 hrec
  have hu : u = renewalResponse (normalizedStepWeights c) (normalizedForcing c d) :=
    eq_renewalResponse_of_recurrence hu0 hurec
  have hlim := tendsto_renewalResponse hp0 hps hpt hpAper he0 hes
  rw [tsum_ofReal_normalizedForcing hc0,
    tsum_ofReal_normalizedStepTail hc hcs hc0] at hlim
  have hA0 : ENNReal.ofReal (1 - c 0) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 ha
  have hAtop : ENNReal.ofReal (1 - c 0) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [toReal_div_div_cancel_right hA0 hAtop] at hlim
  simpa only [hu] using hlim

end Renewal
end Chapter00
