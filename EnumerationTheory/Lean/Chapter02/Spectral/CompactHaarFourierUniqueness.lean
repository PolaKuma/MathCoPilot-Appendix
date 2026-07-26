import Chapter02.Spectral.CompactHaarCharacters

open Classical MeasureTheory

noncomputable section

namespace Chapter02.CompactHaarFourierUniqueness

open Chapter02.CompactHaarCharacters

universe u

variable {G : Type u} [CommGroup G] [MetricSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- A continuous complex function on a compact abelian group is constant
equal to its Haar mean if all of its nontrivial Fourier coefficients
vanish. -/
theorem continuous_eq_haarMean_of_nontrivial_fourier_zero
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (D : C(G, ℂ))
    (hfourier :
      ∀ χ : Character G, (¬ ∀ z, χ.toFun z = 1) →
        ∫ z, star (χ.toFun z) * D z ∂m = 0) :
    ∀ z, D z = ∫ w, D w ∂m := by
  let c : ℂ := ∫ w, D w ∂m
  let H : G → ℂ := fun z ↦ D z - c
  have hHcontinuous : Continuous H :=
    D.continuous.sub continuous_const
  have hH : MemLp H 2 m := by
    apply (memLp_top_of_bound hHcontinuous.aestronglyMeasurable
      (‖D‖ + ‖c‖) ?_).mono_exponent
      (by simp)
    filter_upwards with z
    calc
      ‖H z‖ = ‖D z - c‖ := rfl
      _ ≤ ‖D z‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ ‖D‖ + ‖c‖ :=
        add_le_add (ContinuousMap.norm_coe_le_norm D z) le_rfl
  let HLp : Lp ℂ 2 m := hH.toLp H
  have hinner :
      ∀ χ : Character G,
        @inner ℂ (Lp ℂ 2 m) _ (characterLp m χ) HLp = 0 := by
    intro χ
    rw [L2.inner_def]
    have hχcoe := characterLp_coeFn m χ
    have hHcoe := hH.coeFn_toLp
    have heq :
        (∫ z, @inner ℂ ℂ _ (characterLp m χ z) (HLp z) ∂m) =
          ∫ z, star (χ.toFun z) * H z ∂m := by
      apply integral_congr_ae
      filter_upwards [hχcoe, hHcoe] with z hzχ hzH
      rw [hzχ, hzH, RCLike.inner_apply]
      simp only [starRingEnd_apply, mul_comm]
    rw [heq]
    by_cases hχ : ∀ z, χ.toFun z = 1
    · have hpoint :
          (fun z ↦ star (χ.toFun z) * H z) = H := by
        funext z
        rw [hχ z]
        simp
      rw [hpoint]
      change (∫ z, D z - c ∂m) = 0
      rw [integral_sub]
      · simp [c]
      · rw [← integrableOn_univ]
        exact ContinuousOn.integrableOn_compact
          (μ := m) isCompact_univ D.continuous.continuousOn
      · exact integrable_const c
    · have hχstar :
          ¬ ∀ z, (characterConj χ).toFun z = 1 := by
        intro hs
        apply hχ
        intro z
        have hz := hs z
        change star (χ.toFun z) = 1 at hz
        have := congrArg star hz
        simpa using this
      change
        (∫ z, star (χ.toFun z) * (D z - c) ∂m) = 0
      have hsplit :
          (∫ z, star (χ.toFun z) * (D z - c) ∂m) =
            (∫ z, star (χ.toFun z) * D z ∂m) -
              c * ∫ z, star (χ.toFun z) ∂m := by
        simp_rw [mul_sub, mul_comm (star (χ.toFun _)) c]
        rw [integral_sub]
        · rw [integral_const_mul]
        · rw [← integrableOn_univ]
          exact ContinuousOn.integrableOn_compact
            (μ := m) isCompact_univ
            (χ.continuous.star.mul D.continuous).continuousOn
        · rw [← integrableOn_univ]
          exact ContinuousOn.integrableOn_compact
            (μ := m) isCompact_univ
            (continuous_const.mul χ.continuous.star).continuousOn
      rw [hsplit, hfourier χ hχ]
      have hstarzero :
          ∫ z, star (χ.toFun z) ∂m = 0 := by
        exact integral_character_eq_zero_of_nontrivial
          m (characterConj χ) hχstar
      rw [hstarzero]
      simp
  have hzero : HLp = 0 :=
    eq_zero_of_inner_characterLp_eq_zero m HLp hinner
  have hae : H =ᵐ[m] 0 := by
    have hcoe := hH.coeFn_toLp
    change hH.toLp H = 0 at hzero
    have hzeroCoe :
        (fun z ↦ (hH.toLp H) z) =ᵐ[m] (0 : G → ℂ) := by
      rw [hzero]
      filter_upwards with z
      simp
    exact hcoe.symm.trans hzeroCoe
  have hfun : H = fun _ : G ↦ (0 : ℂ) :=
    Measure.eq_of_ae_eq hae hHcontinuous continuous_zero
  intro z
  have hz := congrFun hfun z
  change D z - c = 0 at hz
  exact sub_eq_zero.mp hz

end Chapter02.CompactHaarFourierUniqueness
