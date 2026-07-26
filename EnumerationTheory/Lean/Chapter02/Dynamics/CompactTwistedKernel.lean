import Chapter02.Spectral.CompactKernelConsequences

open Classical Set

noncomputable section

namespace Chapter02.HilbertSchmidtConsequences

universe u

/-- A compact operator which intertwines an isometry up to a unit-modulus
scalar still has almost-periodic range.  The extra scalar powers live on the
compact unit circle, so the orbit is contained in the continuous image of a
compact product. -/
theorem compact_twistedCommutant_range_almostPeriodic
    (D : HilbertOperatorData.{u})
    (hD : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (K : D.H →L[ℂ] D.H) (hK : HasCompactClosedBallImage K)
    (lam : ℂ) (hlam : ‖lam‖ = 1)
    (hcomm : ∀ x, D.U (K x) = lam • K (D.U x))
    (x : D.H) :
    IsAlmostPeriodicVector D (K x) := by
  have hiter : ∀ n : ℕ,
      (D.U^[n]) (K x) = lam ^ n • K ((D.U^[n]) x) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          ih, map_smul, hcomm, pow_succ, mul_smul]
  obtain ⟨C, hCcompact, hC⟩ := hK ‖x‖
  let S : Set ℂ := Metric.sphere 0 1
  let Q : Set D.H :=
    (fun p : ℂ × D.H ↦ p.1 • p.2) '' (S ×ˢ C)
  have hScompact : IsCompact S := by
    exact isCompact_sphere (0 : ℂ) 1
  have hsmul_cont : Continuous (fun p : ℂ × D.H ↦ p.1 • p.2) :=
    continuous_fst.smul continuous_snd
  have hQcompact : IsCompact Q :=
    (hScompact.prod hCcompact).image hsmul_cont
  intro ε hε
  obtain ⟨t, htfin, htcover⟩ :=
    Metric.totallyBounded_iff.mp hQcompact.totallyBounded ε hε
  refine ⟨htfin.toFinset, ?_⟩
  intro n
  have hUnorm : ‖(D.U^[n]) x‖ = ‖x‖ := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', hD, ih]
  have hlamPow : lam ^ n ∈ S := by
    change dist (lam ^ n) 0 = 1
    simp [dist_eq_norm, norm_pow, hlam]
  have hKorbit : K ((D.U^[n]) x) ∈ C := by
    apply hC
    exact ⟨(D.U^[n]) x, by simp [hUnorm], rfl⟩
  have horbit : (D.U^[n]) (K x) ∈ Q := by
    rw [hiter]
    exact ⟨(lam ^ n, K ((D.U^[n]) x)), ⟨hlamPow, hKorbit⟩, rfl⟩
  have hcover := htcover horbit
  simp only [Set.mem_iUnion, Metric.mem_ball] at hcover
  obtain ⟨y, hyt, hdist⟩ := hcover
  exact ⟨y, (Set.Finite.mem_toFinset htfin).2 hyt,
    by simpa [dist_eq_norm] using hdist⟩

end Chapter02.HilbertSchmidtConsequences
