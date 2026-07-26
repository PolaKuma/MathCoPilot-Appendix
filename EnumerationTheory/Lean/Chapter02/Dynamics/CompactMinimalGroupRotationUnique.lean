import Chapter02.Dynamics.CompactUniqueErgodicCesaro
import Chapter02.Dynamics.MinimalFactorOrbitClosure

open Classical Filter MeasureTheory Set

noncomputable section

namespace Chapter02.CompactMinimalGroupRotationUnique

universe u

variable {G : Type u} [CommGroup G] [MetricSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- Invariance under one rotation extends to invariance under each
nonnegative power of its translating element. -/
theorem integral_mul_pow_eq
    (a : G) (ν : ProbabilityMeasure G)
    (hν : Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
      (fun x ↦ a * x) ν)
    (n : ℕ) (f : C(G, ℝ)) :
    (∫ x, f (a ^ n * x) ∂(ν : Measure G)) =
      ∫ x, f x ∂(ν : Measure G) := by
  induction n with
  | zero => simp
  | succ n ih =>
      let g : C(G, ℝ) :=
        ⟨fun x ↦ f (a ^ n * x),
          f.continuous.comp (continuous_const.mul continuous_id)⟩
      calc
        (∫ x, f (a ^ (n + 1) * x) ∂(ν : Measure G)) =
            ∫ x, g (a * x) ∂(ν : Measure G) := by
              apply integral_congr_ae
              filter_upwards with x
              dsimp only [g, ContinuousMap.coe_mk]
              rw [pow_succ]
              congr 1
              ac_rfl
        _ = ∫ x, g x ∂(ν : Measure G) := hν g
        _ = ∫ x, f x ∂(ν : Measure G) := ih

/-- If the nonnegative powers of `a` are dense, invariance under
translation by `a` extends, at the level of continuous integrals, to every
group translation. -/
theorem integral_mul_eq_of_dense_powers
    (a : G)
    (hdense : DenseRange (fun n : ℕ ↦ a ^ n))
    (ν : ProbabilityMeasure G)
    (hν : Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
      (fun x ↦ a * x) ν)
    (g : G) (f : C(G, ℝ)) :
    (∫ x, f (g * x) ∂(ν : Measure G)) =
      ∫ x, f x ∂(ν : Measure G) := by
  let F : G → ℝ := fun b ↦ ∫ x, f (b * x) ∂(ν : Measure G)
  have hF : Continuous F := by
    have h :=
      continuous_parametric_integral_of_continuous
        (μ := (ν : Measure G))
        (f := fun b : G ↦ fun x : G ↦ f (b * x))
        (f.continuous.comp (continuous_fst.mul continuous_snd))
        isCompact_univ
    simpa only [F, Measure.restrict_univ] using h
  have heq :
      F = fun _ : G ↦ ∫ x, f x ∂(ν : Measure G) := by
    apply hdense.equalizer hF continuous_const
    funext n
    exact integral_mul_pow_eq a ν hν n f
  exact congrFun heq g

/-- Two probability measures invariant under a compact abelian rotation
with dense forward powers have identical continuous real integrals.  The
proof averages `f (x*y)` in the two orders. -/
theorem invariant_integrals_eq_of_dense_powers
    (a : G)
    (hdense : DenseRange (fun n : ℕ ↦ a ^ n))
    (ρ σ : ProbabilityMeasure G)
    (hρ : Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
      (fun x ↦ a * x) ρ)
    (hσ : Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
      (fun x ↦ a * x) σ)
    (f : C(G, ℝ)) :
    (∫ x, f x ∂(ρ : Measure G)) =
      ∫ x, f x ∂(σ : Measure G) := by
  have hprod :
      Integrable (fun p : G × G ↦ f (p.1 * p.2))
        ((ρ : Measure G).prod (σ : Measure G)) := by
    have hc : Continuous (fun p : G × G ↦ f (p.1 * p.2)) :=
      f.continuous.comp (continuous_fst.mul continuous_snd)
    simpa using
      (ContinuousOn.integrableOn_compact
        (μ := (ρ : Measure G).prod (σ : Measure G))
        isCompact_univ hc.continuousOn)
  have hy (y : G) :
      (∫ x, f (x * y) ∂(ρ : Measure G)) =
        ∫ x, f x ∂(ρ : Measure G) := by
    simpa only [mul_comm] using
      integral_mul_eq_of_dense_powers a hdense ρ hρ y f
  calc
    (∫ x, f x ∂(ρ : Measure G)) =
        ∫ y, ∫ x, f (x * y) ∂(ρ : Measure G)
          ∂(σ : Measure G) := by
            simp_rw [hy]
            simp
    _ = ∫ x, ∫ y, f (x * y) ∂(σ : Measure G)
          ∂(ρ : Measure G) :=
      (integral_integral_swap hprod).symm
    _ = ∫ x, f x ∂(σ : Measure G) := by
      simp_rw [integral_mul_eq_of_dense_powers a hdense σ hσ]
      simp

/-- A compact abelian rotation whose forward powers are dense has a unique
integral-invariant probability measure. -/
theorem hasUniqueIntegralInvariant_of_dense_powers
    (a : G)
    (hdense : DenseRange (fun n : ℕ ↦ a ^ n))
    (ν : ProbabilityMeasure G)
    (hν : Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
      (fun x ↦ a * x) ν) :
    Chapter02.CompactUniqueErgodicCesaro.HasUniqueIntegralInvariant
      (fun x ↦ a * x) ν := by
  apply
    Chapter02.CompactUniqueErgodicCesaro.hasUniqueIntegralInvariant_of_integral_eq
      (fun x ↦ a * x) ν hν
  intro ρ hρ f
  exact invariant_integrals_eq_of_dense_powers
    a hdense ρ ν hρ hν f

/-- Topological minimality of a compact group rotation makes the
nonnegative powers of its translating element dense. -/
theorem denseRange_powers_of_everyOrbitHitsOpen
    (a : G)
    (hminimal :
      Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen
        (fun x : G ↦ a * x)) :
    DenseRange (fun n : ℕ ↦ a ^ n) := by
  have hdense :
      Dense
        (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
          (fun x : G ↦ a * x) 1) :=
    Chapter02.MinimalFactorOrbitClosure.dense_forwardOrbit_of_everyOrbitHitsOpen
      (fun x : G ↦ a * x) hminimal 1
  have heq :
      Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
          (fun x : G ↦ a * x) 1 =
        Set.range (fun n : ℕ ↦ a ^ n) := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨n, ?_⟩
      induction n with
      | zero => simp
      | succ n ih =>
          change a ^ (n + 1) =
            ((fun x : G ↦ a * x)^[n + 1]) 1
          have ih' : a ^ n =
              ((fun x : G ↦ a * x)^[n]) 1 := by
            simpa only using ih
          rw [Function.iterate_succ_apply', ← ih', pow_succ]
          ac_rfl
    · rintro ⟨n, rfl⟩
      refine ⟨n, ?_⟩
      induction n with
      | zero => simp
      | succ n ih =>
          change ((fun x : G ↦ a * x)^[n + 1]) 1 =
            a ^ (n + 1)
          have ih' : ((fun x : G ↦ a * x)^[n]) 1 =
              a ^ n := by
            simpa only using ih
          rw [Function.iterate_succ_apply', ih', pow_succ]
          ac_rfl
  rw [heq] at hdense
  exact hdense

/-- Minimal compact abelian rotations are uniquely ergodic in the
continuous-integral sense. -/
theorem hasUniqueIntegralInvariant_of_everyOrbitHitsOpen
    (a : G)
    (hminimal :
      Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen
        (fun x : G ↦ a * x))
    (ν : ProbabilityMeasure G)
    (hν : Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
      (fun x ↦ a * x) ν) :
    Chapter02.CompactUniqueErgodicCesaro.HasUniqueIntegralInvariant
      (fun x ↦ a * x) ν :=
  hasUniqueIntegralInvariant_of_dense_powers
    a (denseRange_powers_of_everyOrbitHitsOpen a hminimal) ν hν

end Chapter02.CompactMinimalGroupRotationUnique
