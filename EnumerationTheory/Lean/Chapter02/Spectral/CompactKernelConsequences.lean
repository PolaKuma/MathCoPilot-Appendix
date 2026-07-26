import Chapter02.Spectral.HilbertSchmidtConsequences
import Chapter02.Spectral.CompactDiscrete

open Classical Filter Set MeasureTheory

noncomputable section

namespace Chapter02.HilbertSchmidtConsequences

universe u

theorem compact_commutant_range_almostPeriodic
    (D : HilbertOperatorData.{u}) (hD : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (K : D.H →L[ℂ] D.H) (hK : HasCompactClosedBallImage K)
    (hcomm : ∀ x, D.U (K x) = K (D.U x)) (x : D.H) :
    IsAlmostPeriodicVector D (K x) := by
  have hiter : ∀ n : ℕ, (D.U^[n]) (K x) = K ((D.U^[n]) x) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hcomm]
  obtain ⟨C, hCcompact, hC⟩ := hK ‖x‖
  intro ε hε
  obtain ⟨t, htfin, htcover⟩ :=
    Metric.totallyBounded_iff.mp hCcompact.totallyBounded ε hε
  refine ⟨htfin.toFinset, ?_⟩
  intro n
  have hUnorm : ‖(D.U^[n]) x‖ = ‖x‖ := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', hD, ih]
  have horbit : (D.U^[n]) (K x) ∈ C := by
    rw [hiter]
    apply hC
    exact ⟨(D.U^[n]) x, by simp [hUnorm], rfl⟩
  have hcover := htcover horbit
  simp only [Set.mem_iUnion, Metric.mem_ball] at hcover
  obtain ⟨y, hyt, hdist⟩ := hcover
  exact ⟨y, (Set.Finite.mem_toFinset htfin).2 hyt,
    by simpa [dist_eq_norm] using hdist⟩

theorem compact_commutant_range_discrete
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (K : D.H →L[ℂ] D.H) (hK : HasCompactClosedBallImage K)
    (hcomm : ∀ x, D.U (K x) = K (D.U x)) (x : D.H) :
    InDiscreteSpectralSubspace D (K x) := by
  exact (AlmostPeriodic.almostPeriodicVector D hD (K x)).mp
    (compact_commutant_range_almostPeriodic D hD.2 K hK hcomm x)

end Chapter02.HilbertSchmidtConsequences
