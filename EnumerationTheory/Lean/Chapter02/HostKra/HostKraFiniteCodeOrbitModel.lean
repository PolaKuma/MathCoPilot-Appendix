import Chapter02.Dynamics.CompactConfigurationMeasureOrbit
import Chapter02.HostKra.HostKraContinuousCylinderReduction
import Chapter02.Dynamics.MinimalOrbitUniverseLowering
import Mathlib.Topology.MetricSpace.PiNat

open Classical MeasureTheory Set
open scoped PiCountable

noncomputable section

namespace Chapter02.HostKraFiniteCodeOrbitModel

universe u

open Chapter02.HallPetrescoTwoStepGroup

/-- The compact symbolic carrier which records both the forward Bool
itinerary of `A` and the forward itinerary of a finite fifteen-dual code. -/
abbrev JointCodeSpace
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)) :=
  (ℕ → Bool) ×
    (ℕ → HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t)

/-- The Bool orbit name of a measurable set. -/
def setOrbitName
    (M : System.{u}) (A : Set M.X) (x : M.X) : ℕ → Bool :=
  fun n ↦ decide ((M.T^[n]) x ∈ A)

/-- The forward orbit of a finite fifteen-dual code. -/
def finiteCodeOrbitName
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (x : M.X) :
    ℕ → HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t :=
  fun n ↦ HostKraFiniteCylinderDensity.finiteCode M hM t ((M.T^[n]) x)

/-- The joint compact orbit code used by a continuous finite cylinder. -/
def jointCode
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (x : M.X) : JointCodeSpace M hM t :=
  (setOrbitName M A x, finiteCodeOrbitName M hM t x)

theorem jointCode_measurable
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)) :
    Measurable (jointCode M hM A t) := by
  apply Measurable.prod
  · rw [measurable_pi_iff]
    intro n
    apply measurable_to_bool
    have heq :
        (fun x ↦ decide ((M.T^[n]) x ∈ A)) ⁻¹' ({true} : Set Bool) =
          (M.T^[n]) ⁻¹' A := by
      ext x
      simp
    change MeasurableSet
      ((fun x ↦ decide ((M.T^[n]) x ∈ A)) ⁻¹' ({true} : Set Bool))
    rw [heq]
    exact hA.preimage (hM.2.measurable.iterate n)
  · rw [measurable_pi_iff]
    intro n
    exact
      (HostKraFiniteCylinderDensity.finiteCode_measurable M hM t).comp
        (hM.2.measurable.iterate n)

/-- Left shift on both components of the joint code. -/
def jointShift
    {M : System.{u}} [StandardBorelSpace M.X]
    {hM : Chapter01.IsMeasurePreservingSystem M}
    {t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)}
    (y : JointCodeSpace M hM t) : JointCodeSpace M hM t :=
  (fun n ↦ y.1 (n + 1), fun n ↦ y.2 (n + 1))

theorem continuous_jointShift
    {M : System.{u}} [StandardBorelSpace M.X]
    {hM : Chapter01.IsMeasurePreservingSystem M}
    {t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)} :
    Continuous (jointShift :
      JointCodeSpace M hM t → JointCodeSpace M hM t) := by
  apply Continuous.prodMk
  · rw [continuous_pi_iff]
    intro n
    exact (continuous_apply (n + 1)).comp continuous_fst
  · rw [continuous_pi_iff]
    intro n
    exact (continuous_apply (n + 1)).comp continuous_snd

theorem jointCode_intertwines
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (x : M.X) :
    jointCode M hM A t (M.T x) =
      jointShift (jointCode M hM A t x) := by
  apply Prod.ext
  · funext n
    simp only [jointCode, setOrbitName, jointShift]
    rw [Function.iterate_succ_apply]
  · funext n
    simp only [jointCode, finiteCodeOrbitName, jointShift]
    rw [Function.iterate_succ_apply]

theorem jointShift_iterate_jointCode
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (x : M.X) (n : ℕ) :
    (jointShift^[n]) (jointCode M hM A t x) =
      jointCode M hM A t ((M.T^[n]) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simpa only [Function.iterate_succ_apply'] using
        (jointCode_intertwines M hM A t ((M.T^[n]) x)).symm

/-- The continuous coordinate-zero indicator observation. -/
def indicatorObservation
    {M : System.{u}} [StandardBorelSpace M.X]
    {hM : Chapter01.IsMeasurePreservingSystem M}
    {t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)}
    (y : JointCodeSpace M hM t) : ℂ :=
  if y.1 0 then 1 else 0

theorem continuous_indicatorObservation
    {M : System.{u}} [StandardBorelSpace M.X]
    {hM : Chapter01.IsMeasurePreservingSystem M}
    {t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)} :
    Continuous (indicatorObservation :
      JointCodeSpace M hM t → ℂ) := by
  exact
    (continuous_of_discreteTopology :
      Continuous fun b : Bool ↦ if b then (1 : ℂ) else 0)
      |>.comp ((continuous_apply 0).comp continuous_fst)

/-- A continuous finite cylinder observed at time zero of the code orbit. -/
def finiteObservation
    {M : System.{u}} [StandardBorelSpace M.X]
    {hM : Chapter01.IsMeasurePreservingSystem M}
    {t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)}
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ))
    (y : JointCodeSpace M hM t) : ℂ :=
  φ (y.2 0)

theorem continuous_finiteObservation
    {M : System.{u}} [StandardBorelSpace M.X]
    {hM : Chapter01.IsMeasurePreservingSystem M}
    {t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)}
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ)) :
    Continuous (finiteObservation φ :
      JointCodeSpace M hM t → ℂ) :=
  φ.continuous.comp ((continuous_apply 0).comp continuous_snd)

/-- The product of three Bool observations and the continuous
finite-cylinder observation in the fourth coordinate. -/
def complexConfigurationObservation
    {M : System.{u}} [StandardBorelSpace M.X]
    {hM : Chapter01.IsMeasurePreservingSystem M}
    {t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)}
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ)) :
    C(Vertex → JointCodeSpace M hM t, ℂ) where
  toFun := fun y ↦
    indicatorObservation (y 0) *
      indicatorObservation (y 1) *
      indicatorObservation (y 2) *
      finiteObservation φ (y 3)
  continuous_toFun := by
    have h0 : Continuous fun y : Vertex → JointCodeSpace M hM t ↦
        indicatorObservation (y 0) :=
      continuous_indicatorObservation.comp (continuous_apply 0)
    have h1 : Continuous fun y : Vertex → JointCodeSpace M hM t ↦
        indicatorObservation (y 1) :=
      continuous_indicatorObservation.comp (continuous_apply 1)
    have h2 : Continuous fun y : Vertex → JointCodeSpace M hM t ↦
        indicatorObservation (y 2) :=
      continuous_indicatorObservation.comp (continuous_apply 2)
    have h3 : Continuous fun y : Vertex → JointCodeSpace M hM t ↦
        finiteObservation φ (y 3) :=
      (continuous_finiteObservation φ).comp (continuous_apply 3)
    exact ((h0.mul h1).mul h2).mul h3

/-- The real part of the complex four-configuration observation. -/
def configurationObservation
    {M : System.{u}} [StandardBorelSpace M.X]
    {hM : Chapter01.IsMeasurePreservingSystem M}
    {t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)}
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ)) :
    C(Vertex → JointCodeSpace M hM t, ℝ) where
  toFun := fun y ↦ (complexConfigurationObservation φ y).re
  continuous_toFun :=
    Complex.continuous_re.comp
      (complexConfigurationObservation φ).continuous

/-- The pushforward law of the joint orbit code. -/
def jointCodeProbabilityMeasure
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)) :
    ProbabilityMeasure (JointCodeSpace M hM t) :=
  letI : IsProbabilityMeasure M.μ := hM.1
  ProbabilityMeasure.map
    (⟨M.μ, inferInstance⟩ : ProbabilityMeasure M.X)
    (jointCode_measurable M hM A hA t).aemeasurable

/-- The `L²` pullback of a continuous finite-code cylinder. -/
def finiteCylinderLp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (ht : t.Finite)
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ)) :
    Lp ℂ 2 M.μ :=
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : Fintype t := ht.fintype
  letI : IsFiniteMeasure
      (Measure.map
        (HostKraFiniteCylinderDensity.finiteCode M hM t) M.μ) :=
    Measure.isFiniteMeasure_map M.μ
      (HostKraFiniteCylinderDensity.finiteCode M hM t)
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
    (HostKraFiniteCylinderDensity.finiteCode M hM t)
    ⟨HostKraFiniteCylinderDensity.finiteCode_measurable M hM t, rfl⟩
    (ContinuousMap.toLp 2
      (Measure.map
        (HostKraFiniteCylinderDensity.finiteCode M hM t) M.μ)
      ℂ φ)

theorem finiteCylinderLp_ae_eq
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (ht : t.Finite)
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ)) :
    (fun x ↦ finiteCylinderLp M hM t ht φ x) =ᵐ[M.μ]
      fun x ↦ φ (HostKraFiniteCylinderDensity.finiteCode M hM t x) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : Fintype t := ht.fintype
  let code := HostKraFiniteCylinderDensity.finiteCode M hM t
  let ν : Measure
      (HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
    Measure.map code M.μ
  letI : IsFiniteMeasure ν := Measure.isFiniteMeasure_map M.μ code
  let hmp : MeasurePreserving code M.μ ν :=
    ⟨HostKraFiniteCylinderDensity.finiteCode_measurable M hM t, rfl⟩
  let G : Lp ℂ 2 ν := ContinuousMap.toLp 2 ν ℂ φ
  have hpull :
      (fun x ↦
        (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ code hmp G) x) =ᵐ[M.μ]
        fun x ↦ G (code x) :=
    MeasureTheory.Lp.coeFn_compMeasurePreserving G hmp
  have hG : (fun y ↦ G y) =ᵐ[ν] fun y ↦ φ y :=
    ContinuousMap.coeFn_toLp (p := (2 : ENNReal)) (𝕜 := ℂ) ν φ
  have hGcomp :
      (fun x ↦ G (code x)) =ᵐ[M.μ] fun x ↦ φ (code x) :=
    hmp.quasiMeasurePreserving.ae_eq_comp hG
  simpa only [finiteCylinderLp, code, ν, G, hmp] using hpull.trans hGcomp

/-- Pointwise evaluation of the compact configuration observation is the
expected three-indicator/one-cylinder progression integrand. -/
theorem complexConfigurationObservation_configurationMap
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ))
    (x : M.X) (n : ℕ) :
    complexConfigurationObservation φ
        (CompactConfigurationMeasureOrbit.configurationMap
          (jointShift :
            JointCodeSpace M hM t → JointCodeSpace M hM t)
          n (jointCode M hM A t x)) =
      (CorrelationMean.indicatorComplex A x *
        CorrelationMean.indicatorComplex A ((M.T^[n]) x) *
        CorrelationMean.indicatorComplex A ((M.T^[2 * n]) x) *
        φ (HostKraFiniteCylinderDensity.finiteCode M hM t
          ((M.T^[3 * n]) x))) := by
  simp only [complexConfigurationObservation, ContinuousMap.coe_mk,
    CompactConfigurationMeasureOrbit.configurationMap,
    Fin.isValue, Fin.val_zero, zero_mul, Function.iterate_zero_apply,
    Fin.val_one, one_mul,
    show (2 : Vertex).val = 2 by decide,
    show (3 : Vertex).val = 3 by decide]
  rw [jointShift_iterate_jointCode M hM A t x n,
    jointShift_iterate_jointCode M hM A t x (2 * n),
    jointShift_iterate_jointCode M hM A t x (3 * n)]
  simp only [indicatorObservation, finiteObservation, jointCode,
    setOrbitName, finiteCodeOrbitName]
  by_cases hx0 : x ∈ A
  · by_cases hx1 : (M.T^[n]) x ∈ A
    · by_cases hx2 : (M.T^[2 * n]) x ∈ A
      · simp [CorrelationMean.indicatorComplex, Set.indicator,
          hx0, hx1, hx2]
      · simp [CorrelationMean.indicatorComplex, Set.indicator,
          hx0, hx1, hx2]
    · simp [CorrelationMean.indicatorComplex, Set.indicator, hx0, hx1]
  · simp [CorrelationMean.indicatorComplex, Set.indicator, hx0]

theorem configurationObservation_configurationMap
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ))
    (x : M.X) (n : ℕ) :
    configurationObservation φ
        (CompactConfigurationMeasureOrbit.configurationMap
          (jointShift :
            JointCodeSpace M hM t → JointCodeSpace M hM t)
          n (jointCode M hM A t x)) =
      (CorrelationMean.indicatorComplex A x *
        CorrelationMean.indicatorComplex A ((M.T^[n]) x) *
        CorrelationMean.indicatorComplex A ((M.T^[2 * n]) x) *
        φ (HostKraFiniteCylinderDensity.finiteCode M hM t
          ((M.T^[3 * n]) x))).re := by
  exact congrArg Complex.re
    (complexConfigurationObservation_configurationMap
      M hM A t φ x n)

set_option maxHeartbeats 800000

/-- The genuine compact configuration-measure orbit correlation attached
to a continuous finite fifteen-dual cylinder. -/
def finiteCylinderConfigurationCorrelation
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (ht : t.Finite)
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ))
    (n : ℕ) : ℝ :=
  letI : Fintype t := ht.fintype
  letI : MetricSpace
      (HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
    inferInstance
  letI : ∀ _ : ℕ, MetricSpace
      (HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
    fun _ ↦ inferInstance
  letI : MetricSpace
      (ℕ → HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
    PiCountable.metricSpace
  letI : MetricSpace (ℕ → Bool) := PiNat.metricSpace
  letI : MetricSpace (JointCodeSpace M hM t) := inferInstance
  CompactConfigurationMeasureOrbit.configurationCorrelation
    ((jointCodeProbabilityMeasure M hM A hA t :
      ProbabilityMeasure (JointCodeSpace M hM t)) : Measure
        (JointCodeSpace M hM t))
    (jointShift : JointCodeSpace M hM t → JointCodeSpace M hM t)
    continuous_jointShift (configurationObservation φ) n

set_option maxHeartbeats 200000

set_option maxHeartbeats 800000

/-- The compact configuration-measure orbit computes the original
three-indicator/one-cylinder integral exactly. -/
theorem finiteCylinderConfigurationCorrelation_eq_integral
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (ht : t.Finite)
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ))
    (n : ℕ) :
    finiteCylinderConfigurationCorrelation M hM A hA t ht φ n =
      ∫ x,
        (CorrelationMean.indicatorComplex A x *
          CorrelationMean.indicatorComplex A ((M.T^[n]) x) *
          CorrelationMean.indicatorComplex A ((M.T^[2 * n]) x) *
          φ (HostKraFiniteCylinderDensity.finiteCode M hM t
            ((M.T^[3 * n]) x))).re ∂M.μ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : Fintype t := ht.fintype
  letI : MetricSpace
      (HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
    inferInstance
  letI : ∀ _ : ℕ, MetricSpace
      (HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
    fun _ ↦ inferInstance
  letI : MetricSpace
      (ℕ → HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
    PiCountable.metricSpace
  letI : MetricSpace (ℕ → Bool) := PiNat.metricSpace
  letI : MetricSpace (JointCodeSpace M hM t) := inferInstance
  let ν := jointCodeProbabilityMeasure M hM A hA t
  let R : JointCodeSpace M hM t → JointCodeSpace M hM t := jointShift
  let G := configurationObservation φ
  calc
    finiteCylinderConfigurationCorrelation M hM A hA t ht φ n =
        ∫ y, G (CompactConfigurationMeasureOrbit.configurationMap
          R n y) ∂(ν : Measure (JointCodeSpace M hM t)) := by
      exact
        CompactConfigurationMeasureOrbit.configurationCorrelation_eq_integral
          (ν : Measure (JointCodeSpace M hM t))
          R continuous_jointShift G n
    _ = ∫ x, G (CompactConfigurationMeasureOrbit.configurationMap
          R n (jointCode M hM A t x)) ∂M.μ := by
      dsimp only [ν]
      rw [jointCodeProbabilityMeasure, ProbabilityMeasure.toMeasure_map]
      exact MeasureTheory.integral_map
        (jointCode_measurable M hM A hA t).aemeasurable
        ((G.continuous.comp
          (CompactConfigurationMeasureOrbit.continuous_configurationMap
            R continuous_jointShift n)).aestronglyMeasurable)
    _ = ∫ x,
        (CorrelationMean.indicatorComplex A x *
          CorrelationMean.indicatorComplex A ((M.T^[n]) x) *
          CorrelationMean.indicatorComplex A ((M.T^[2 * n]) x) *
          φ (HostKraFiniteCylinderDensity.finiteCode M hM t
            ((M.T^[3 * n]) x))).re ∂M.μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦
        configurationObservation_configurationMap M hM A t φ x n

set_option maxHeartbeats 200000

set_option maxHeartbeats 800000

/-- The complex finite-cylinder progression integrand is integrable.  This
is proved on the compact joint code and then pulled back along its
measure-preserving coding map. -/
theorem complexFiniteCylinderIntegrable
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (ht : t.Finite)
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ))
    (n : ℕ) :
    Integrable
      (fun x ↦
        CorrelationMean.indicatorComplex A x *
          CorrelationMean.indicatorComplex A ((M.T^[n]) x) *
          CorrelationMean.indicatorComplex A ((M.T^[2 * n]) x) *
          φ (HostKraFiniteCylinderDensity.finiteCode M hM t
            ((M.T^[3 * n]) x)))
      M.μ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : Fintype t := ht.fintype
  letI : MetricSpace
      (HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
    inferInstance
  letI : ∀ _ : ℕ, MetricSpace
      (HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
    fun _ ↦ inferInstance
  letI : MetricSpace
      (ℕ → HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
    PiCountable.metricSpace
  letI : MetricSpace (ℕ → Bool) := PiNat.metricSpace
  letI : MetricSpace (JointCodeSpace M hM t) := inferInstance
  let ν := jointCodeProbabilityMeasure M hM A hA t
  let R : JointCodeSpace M hM t → JointCodeSpace M hM t := jointShift
  let H : C(JointCodeSpace M hM t, ℂ) :=
    (complexConfigurationObservation φ).comp
      ⟨CompactConfigurationMeasureOrbit.configurationMap R n,
        CompactConfigurationMeasureOrbit.continuous_configurationMap
          R continuous_jointShift n⟩
  have hHmem :
      MemLp (fun y ↦ H y) 1
        (ν : Measure (JointCodeSpace M hM t)) :=
    (Lp.memLp (ContinuousMap.toLp 1
      (ν : Measure (JointCodeSpace M hM t)) ℂ H)).ae_eq
        (ContinuousMap.coeFn_toLp (p := (1 : ENNReal)) (𝕜 := ℂ)
          (ν : Measure (JointCodeSpace M hM t)) H)
  have hHint :
      Integrable (fun y ↦ H y)
        (ν : Measure (JointCodeSpace M hM t)) :=
    hHmem.integrable (by norm_num)
  have hHintMap :
      Integrable (fun y ↦ H y)
        (Measure.map (jointCode M hM A t) M.μ) := by
    simpa only [ν, jointCodeProbabilityMeasure,
      ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk] using hHint
  have hpull :
      Integrable (fun x ↦ H (jointCode M hM A t x)) M.μ :=
    hHintMap.comp_measurable (jointCode_measurable M hM A hA t)
  exact hpull.congr
    (Filter.Eventually.of_forall fun x ↦
      (by
        simpa only [H, ContinuousMap.comp_apply] using
          (complexConfigurationObservation_configurationMap
            M hM A t φ x n)))

/-- The genuine compact configuration-measure correlation is exactly the
`lastSlotCorrelation` of the continuous finite-cylinder `L²` pullback. -/
theorem finiteCylinderConfigurationCorrelation_eq_lastSlotCorrelation
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (ht : t.Finite)
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ))
    (n : ℕ) :
    finiteCylinderConfigurationCorrelation M hM A hA t ht φ n =
      HostKraStructuredApproximation.lastSlotCorrelation
        M hM A hA (finiteCylinderLp M hM t ht φ) n := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let F := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  let Q := finiteCylinderLp M hM t ht φ
  have hF0 :
      (fun x ↦ F x) =ᵐ[M.μ]
        CorrelationMean.indicatorComplex A :=
    MultipleKhintchineCharacteristic.indicatorLp_coe M hM A hA
  have hF1 :
      (fun x ↦ F ((M.T^[n]) x)) =ᵐ[M.μ]
        fun x ↦ CorrelationMean.indicatorComplex A ((M.T^[n]) x) :=
    (hM.2.iterate n).quasiMeasurePreserving.ae_eq hF0
  have hF2 :
      (fun x ↦ F ((M.T^[2 * n]) x)) =ᵐ[M.μ]
        fun x ↦ CorrelationMean.indicatorComplex A ((M.T^[2 * n]) x) :=
    (hM.2.iterate (2 * n)).quasiMeasurePreserving.ae_eq hF0
  have hQ0 :
      (fun x ↦ Q x) =ᵐ[M.μ]
        fun x ↦ φ (HostKraFiniteCylinderDensity.finiteCode M hM t x) :=
    finiteCylinderLp_ae_eq M hM t ht φ
  have hQ3 :
      (fun x ↦ Q ((M.T^[3 * n]) x)) =ᵐ[M.μ]
        fun x ↦ φ (HostKraFiniteCylinderDensity.finiteCode M hM t
          ((M.T^[3 * n]) x)) :=
    (hM.2.iterate (3 * n)).quasiMeasurePreserving.ae_eq hQ0
  have hintegrand :
      (fun x ↦ MultipleKhintchineCartesian.quadrupleIntegrand M
        (fun x ↦ F x) (fun x ↦ F x) (fun x ↦ F x)
        (fun x ↦ Q x) n x) =ᵐ[M.μ]
      fun x ↦
        CorrelationMean.indicatorComplex A x *
          CorrelationMean.indicatorComplex A ((M.T^[n]) x) *
          CorrelationMean.indicatorComplex A ((M.T^[2 * n]) x) *
          φ (HostKraFiniteCylinderDensity.finiteCode M hM t
            ((M.T^[3 * n]) x)) := by
    filter_upwards [hF0, hF1, hF2, hQ3] with x hx0 hx1 hx2 hx3
    simp only [MultipleKhintchineCartesian.quadrupleIntegrand]
    rw [hx0, hx1, hx2, hx3]
  rw [finiteCylinderConfigurationCorrelation_eq_integral]
  change
    (∫ x, RCLike.re
      (CorrelationMean.indicatorComplex A x *
        CorrelationMean.indicatorComplex A ((M.T^[n]) x) *
        CorrelationMean.indicatorComplex A ((M.T^[2 * n]) x) *
        φ (HostKraFiniteCylinderDensity.finiteCode M hM t
          ((M.T^[3 * n]) x))) ∂M.μ) =
      HostKraStructuredApproximation.lastSlotCorrelation
        M hM A hA (finiteCylinderLp M hM t ht φ) n
  rw [integral_re
    (complexFiniteCylinderIntegrable M hM A hA t ht φ n)]
  unfold HostKraStructuredApproximation.lastSlotCorrelation
  exact congrArg Complex.re (integral_congr_ae hintegrand.symm)

set_option maxHeartbeats 200000

/-- A concrete strong sufficient condition in terms of the actual joint
symbolic code and its actual diagonal configuration-measure orbit closure.
It is intentionally kept separate from the final Host--Kra theorem:
arbitrary set-itinerary coordinates need not have homogeneous orbit
closures, so the genuine proof must first split off their UD-null part. -/
def FiniteFifteenDualConfigurationOrbitHomogeneity : Prop :=
  ∀ (M : System.{u}) [StandardBorelSpace M.X],
    ∀ (hM : Chapter01.IsMeasurePreservingSystem M),
    IsErgodic M →
    ∀ (A : Set M.X) (hA : MeasurableSet A),
    ∀ (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)),
    ∀ (ht : t.Finite),
      letI : IsProbabilityMeasure M.μ := hM.1
      letI : Fintype t := ht.fintype
      letI : MetricSpace
          (HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
        inferInstance
      letI : ∀ _ : ℕ, MetricSpace
          (HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
        fun _ ↦ inferInstance
      letI : MetricSpace
          (ℕ → HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
        PiCountable.metricSpace
      letI : MetricSpace (ℕ → Bool) := PiNat.metricSpace
      letI : MetricSpace (JointCodeSpace M hM t) := inferInstance
      CompactConfigurationMeasureOrbit.HasHomogeneousConfigurationMeasureOrbit
        ((jointCodeProbabilityMeasure M hM A hA t :
          ProbabilityMeasure (JointCodeSpace M hM t)) :
            Measure (JointCodeSpace M hM t))
        (jointShift : JointCodeSpace M hM t → JointCodeSpace M hM t)
        continuous_jointShift

set_option maxHeartbeats 800000

/-- Under the preceding strong homogeneity condition, the genuine
finite-code configuration-measure orbit supplies exact continuous-cylinder
minimality. -/
theorem continuousFiniteFifteenDualMinimality
    (hhom : FiniteFifteenDualConfigurationOrbitHomogeneity.{u}) :
    HostKraContinuousCylinderReduction.ContinuousFiniteFifteenDualMinimality.{u} := by
  intro M instSB hM hErg A hA t ht φ
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : Fintype t := ht.fintype
  letI : IsFiniteMeasure
      (Measure.map
        (HostKraFiniteCylinderDensity.finiteCode M hM t) M.μ) :=
    Measure.isFiniteMeasure_map M.μ
      (HostKraFiniteCylinderDensity.finiteCode M hM t)
  letI : MetricSpace
      (HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
    inferInstance
  letI : ∀ _ : ℕ, MetricSpace
      (HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
    fun _ ↦ inferInstance
  letI : MetricSpace
      (ℕ → HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
    PiCountable.metricSpace
  letI : MetricSpace (ℕ → Bool) := PiNat.metricSpace
  letI : MetricSpace (JointCodeSpace M hM t) := inferInstance
  have horbit :=
    CompactConfigurationMeasureOrbit.isMinimalOrbitSequence_configurationCorrelation_of_homogeneous
        ((jointCodeProbabilityMeasure M hM A hA t :
          ProbabilityMeasure (JointCodeSpace M hM t)) :
            Measure (JointCodeSpace M hM t))
        (jointShift : JointCodeSpace M hM t → JointCodeSpace M hM t)
        continuous_jointShift
        (hhom M hM hErg A hA t ht)
        (configurationObservation φ)
  have heq :
      finiteCylinderConfigurationCorrelation M hM A hA t ht φ =
        HostKraStructuredApproximation.lastSlotCorrelation
          M hM A hA (finiteCylinderLp M hM t ht φ) := by
    funext n
    exact finiteCylinderConfigurationCorrelation_eq_lastSlotCorrelation
      M hM A hA t ht φ n
  change
    HostKraStructuredRecurrence.IsMinimalOrbitSequence
      (finiteCylinderConfigurationCorrelation M hM A hA t ht φ) at horbit
  rw [heq] at horbit
  have horbit0 :=
    MinimalOrbitUniverseLowering.isMinimalOrbitSequence_zero_of horbit
  simpa only [finiteCylinderLp] using horbit0

/-- The strong concrete configuration-orbit condition is sufficient for
the first multiple-Khintchine clause. -/
theorem multipleKhintchineStatement_firstClause
    (hhom : FiniteFifteenDualConfigurationOrbitHomogeneity.{u})
    (M : System.{u}) :
    IsErgodic M →
      ∀ A : Set M.X, MeasurableSet A → 0 < M.μ A →
      ∀ ε : ℝ, 0 < ε →
        IsSyndetic {n : ℕ |
          realMeasure M
              (A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A) >
            (realMeasure M A) ^ 3 - ε} ∧
        IsSyndetic {n : ℕ |
          realMeasure M
              (A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A ∩
                preimageIter M (3 * n) A) >
            (realMeasure M A) ^ 4 - ε} :=
  HostKraContinuousCylinderReduction.multipleKhintchineStatement_firstClause_of_minimality
    (continuousFiniteFifteenDualMinimality hhom) M

set_option maxHeartbeats 200000

end Chapter02.HostKraFiniteCodeOrbitModel
