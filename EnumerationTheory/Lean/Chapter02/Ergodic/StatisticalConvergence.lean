import Chapter02.Ergodic.ZeroDensity

noncomputable section

open Filter

namespace Chapter02
namespace StatisticalConvergence

lemma cesaroTendsTo_zero_iff_densityOne_lt
    (x : ℕ → ℝ) (C : ℝ)
    (hx0 : ∀ n, 0 ≤ x n) (hC0 : 0 ≤ C) (hxC : ∀ n, x n ≤ C) :
    cesaroTendsTo x 0 ↔
      ∀ ε : ℝ, 0 < ε →
        Chapter00.lowerAsymptoticDensity {n | x n < ε} = 1 := by
  constructor
  · intro h ε hε
    let J : Set ℕ := {n | ε ≤ x n}
    have hJdens : Tendsto (Chapter00.natInitialDensity J) atTop (nhds 0) :=
      ZeroDensity.threshold_density_tendsto_zero x hx0 h hε
    have hJupp : Chapter00.upperAsymptoticDensity J = 0 := by
      rw [Chapter00.upperAsymptoticDensity_eq_limsup]
      exact hJdens.limsup_eq
    have hcompl := Chapter00.upperAsymptoticDensity_compl J
    have hgood : Chapter00.lowerAsymptoticDensity Jᶜ = 1 := by
      rw [hJupp] at hcompl
      linarith
    have hsets : Jᶜ = {n | x n < ε} := by
      ext n
      simp [J]
    rwa [hsets] at hgood
  · intro hstat
    unfold cesaroTendsTo seqTendsTo
    rw [tendsto_order]
    constructor
    · intro b hb
      filter_upwards [] with N
      have havg0 : 0 ≤ cesaroAverage x N := by
        unfold cesaroAverage
        exact mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => hx0 n)
      linarith
    · intro δ hδ
      let η : ℝ := δ / 3
      let J : Set ℕ := {n | η ≤ x n}
      have hη : 0 < η := by dsimp [η]; linarith
      have hgood := hstat η hη
      have hJupp : Chapter00.upperAsymptoticDensity J = 0 := by
        have hcompl := Chapter00.upperAsymptoticDensity_compl J
        have hcomp_eq : Jᶜ = {n | x n < η} := by
          ext n
          simp [J]
        rw [hcomp_eq, hgood] at hcompl
        linarith
      have hJlow : Chapter00.lowerAsymptoticDensity J = 0 := by
        have hle := Chapter00.lowerAsymptoticDensity_le_upperAsymptoticDensity J
        have hnonneg := Chapter00.lowerAsymptoticDensity_nonneg J
        rw [hJupp] at hle
        linarith
      have hJdens : Tendsto (Chapter00.natInitialDensity J) atTop (nhds 0) :=
        ZeroDensity.tendsto_natInitialDensity_of_lower_upper_eq_zero J hJlow hJupp
      have hdens : ∀ᶠ N in atTop,
          Chapter00.natInitialDensity J (N + 1) < δ / (3 * (C + 1)) := by
        have hpos : 0 < δ / (3 * (C + 1)) := by positivity
        exact (Filter.tendsto_add_atTop_iff_nat 1).mpr hJdens |>.eventually
          (eventually_lt_nhds hpos)
      filter_upwards [hdens] with N hNdens
      have hsmall : ∀ n, 0 ≤ n → n ∉ J → x n ≤ η := by
        intro n hn hnJ
        exact le_of_not_ge hnJ
      have hbound := ZeroDensity.cesaroAverage_le_density_add_tail
        x J C η 0 N hC0 hη.le hxC hsmall
      have hCdens : C * Chapter00.natInitialDensity J (N + 1) < δ / 3 := by
        rcases hC0.eq_or_lt with hCeq | hCpos
        · simp [← hCeq, hδ]
        · have hmul := mul_lt_mul_of_pos_left hNdens hCpos
          have hratio : C * (δ / (3 * (C + 1))) < δ / 3 := by
            field_simp
            nlinarith
          exact hmul.trans hratio
      dsimp [η] at hbound
      norm_num at hbound
      linarith

lemma familyConvergesTo_densityOne_iff_threshold
    (y : ℕ → ℝ) (a : ℝ) :
    FamilyConvergesTo Chapter00.densityOneFamily y a ↔
      ∀ ε : ℝ, 0 < ε →
        Chapter00.lowerAsymptoticDensity {n | |y n - a| < ε} = 1 := by
  constructor
  · intro h ε hε
    have hball := h (Metric.ball a ε) Metric.isOpen_ball
      (Metric.mem_ball_self hε)
    simpa [Chapter00.densityOneFamily, Real.dist_eq] using hball
  · intro hstat U hU haU
    rcases Metric.isOpen_iff.mp hU a haU with ⟨ε, hε, hball⟩
    have hsmall := hstat ε hε
    change Chapter00.lowerAsymptoticDensity {n | y n ∈ U} = 1
    apply le_antisymm (Chapter00.lowerAsymptoticDensity_le_one _)
    calc
      1 = Chapter00.lowerAsymptoticDensity {n | |y n - a| < ε} := hsmall.symm
      _ ≤ Chapter00.lowerAsymptoticDensity {n | y n ∈ U} := by
        apply Chapter00.lowerAsymptoticDensity_mono
        intro n hn
        apply hball
        simpa [Real.dist_eq] using hn

lemma familyConvergesTo_cofinite_iff_tendsto
    (y : ℕ → ℝ) (a : ℝ) :
    FamilyConvergesTo {E : Set ℕ | Eᶜ.Finite} y a ↔
      Tendsto y atTop (nhds a) := by
  constructor
  · intro h
    rw [← Nat.cofinite_eq_atTop]
    rw [tendsto_def]
    intro U hU
    rcases mem_nhds_iff.mp hU with ⟨V, hVU, hVopen, haV⟩
    have hV := h V hVopen haV
    change {n | y n ∈ V}ᶜ.Finite at hV
    rw [Filter.mem_cofinite]
    exact hV.subset (Set.compl_subset_compl.mpr (Set.preimage_mono hVU))
  · intro hy U hU haU
    have hcof : Tendsto y cofinite (nhds a) := by
      simpa only [Nat.cofinite_eq_atTop] using hy
    have hev := hcof.eventually (hU.mem_nhds haU)
    rwa [Filter.eventually_cofinite] at hev

end StatisticalConvergence
end Chapter02
