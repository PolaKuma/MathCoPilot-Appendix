import Chapter02.HostKra.HostKraFiniteCodeOrbitModel

open Classical MeasureTheory Set
open scoped PiCountable

noncomputable section

namespace Chapter02.HostKraFullyStructuredFiniteCode

universe u

open Chapter02.HallPetrescoTwoStepGroup

/-- The compact forward-name space of one finite family of canonical
fifteen-dual coordinates.  Unlike `JointCodeSpace`, it contains no arbitrary
set-itinerary coordinate. -/
abbrev CodeOrbitSpace
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)) :=
  ℕ → HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t

/-- Left shift on the finite-code forward-name space. -/
def codeShift
    {M : System.{u}} [StandardBorelSpace M.X]
    {hM : Chapter01.IsMeasurePreservingSystem M}
    {t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)}
    (y : CodeOrbitSpace M hM t) : CodeOrbitSpace M hM t :=
  fun n ↦ y (n + 1)

theorem continuous_codeShift
    {M : System.{u}} [StandardBorelSpace M.X]
    {hM : Chapter01.IsMeasurePreservingSystem M}
    {t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)} :
    Continuous (codeShift : CodeOrbitSpace M hM t → CodeOrbitSpace M hM t) := by
  rw [continuous_pi_iff]
  intro n
  exact continuous_apply (n + 1)

theorem finiteCodeOrbitName_measurable
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)) :
    Measurable
      (HostKraFiniteCodeOrbitModel.finiteCodeOrbitName M hM t) := by
  rw [measurable_pi_iff]
  intro n
  exact
    (HostKraFiniteCylinderDensity.finiteCode_measurable M hM t).comp
      (hM.2.measurable.iterate n)

theorem finiteCodeOrbitName_intertwines
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (x : M.X) :
    HostKraFiniteCodeOrbitModel.finiteCodeOrbitName M hM t (M.T x) =
      codeShift
        (HostKraFiniteCodeOrbitModel.finiteCodeOrbitName M hM t x) := by
  funext n
  simp only [HostKraFiniteCodeOrbitModel.finiteCodeOrbitName, codeShift]
  rw [Function.iterate_succ_apply]

theorem codeShift_iterate_finiteCodeOrbitName
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (x : M.X) (n : ℕ) :
    (codeShift^[n])
        (HostKraFiniteCodeOrbitModel.finiteCodeOrbitName M hM t x) =
      HostKraFiniteCodeOrbitModel.finiteCodeOrbitName M hM t
        ((M.T^[n]) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simpa only [Function.iterate_succ_apply'] using
        (finiteCodeOrbitName_intertwines M hM t ((M.T^[n]) x)).symm

/-- The pushforward law of the pure finite-code orbit name. -/
def codeOrbitProbabilityMeasure
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)) :
    ProbabilityMeasure (CodeOrbitSpace M hM t) :=
  letI : IsProbabilityMeasure M.μ := hM.1
  ProbabilityMeasure.map
    (⟨M.μ, inferInstance⟩ : ProbabilityMeasure M.X)
    (finiteCodeOrbitName_measurable M hM t).aemeasurable

/-- Observe a continuous finite cylinder at time zero of its pure code
orbit. -/
def codeObservation
    {M : System.{u}} [StandardBorelSpace M.X]
    {hM : Chapter01.IsMeasurePreservingSystem M}
    {t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)}
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ))
    (y : CodeOrbitSpace M hM t) : ℂ :=
  φ (y 0)

theorem continuous_codeObservation
    {M : System.{u}} [StandardBorelSpace M.X]
    {hM : Chapter01.IsMeasurePreservingSystem M}
    {t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)}
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ)) :
    Continuous (codeObservation φ : CodeOrbitSpace M hM t → ℂ) :=
  φ.continuous.comp (continuous_apply 0)

/-- The product observation in which all four progression slots are the
same continuous finite fifteen-dual cylinder. -/
def complexFullyStructuredObservation
    {M : System.{u}} [StandardBorelSpace M.X]
    {hM : Chapter01.IsMeasurePreservingSystem M}
    {t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)}
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ)) :
    C(Vertex → CodeOrbitSpace M hM t, ℂ) where
  toFun := fun y ↦
    codeObservation φ (y 0) *
      codeObservation φ (y 1) *
      codeObservation φ (y 2) *
      codeObservation φ (y 3)
  continuous_toFun := by
    have h0 : Continuous fun y : Vertex → CodeOrbitSpace M hM t ↦
        codeObservation φ (y 0) :=
      (continuous_codeObservation φ).comp (continuous_apply 0)
    have h1 : Continuous fun y : Vertex → CodeOrbitSpace M hM t ↦
        codeObservation φ (y 1) :=
      (continuous_codeObservation φ).comp (continuous_apply 1)
    have h2 : Continuous fun y : Vertex → CodeOrbitSpace M hM t ↦
        codeObservation φ (y 2) :=
      (continuous_codeObservation φ).comp (continuous_apply 2)
    have h3 : Continuous fun y : Vertex → CodeOrbitSpace M hM t ↦
        codeObservation φ (y 3) :=
      (continuous_codeObservation φ).comp (continuous_apply 3)
    exact ((h0.mul h1).mul h2).mul h3

/-- The real part of the fully structured complex observation. -/
def fullyStructuredObservation
    {M : System.{u}} [StandardBorelSpace M.X]
    {hM : Chapter01.IsMeasurePreservingSystem M}
    {t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM)}
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ)) :
    C(Vertex → CodeOrbitSpace M hM t, ℝ) where
  toFun := fun y ↦ (complexFullyStructuredObservation φ y).re
  continuous_toFun :=
    Complex.continuous_re.comp
      (complexFullyStructuredObservation φ).continuous

theorem complexFullyStructuredObservation_configurationMap
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ))
    (x : M.X) (n : ℕ) :
    complexFullyStructuredObservation φ
        (CompactConfigurationMeasureOrbit.configurationMap
          (codeShift : CodeOrbitSpace M hM t → CodeOrbitSpace M hM t)
          n
          (HostKraFiniteCodeOrbitModel.finiteCodeOrbitName M hM t x)) =
      (φ (HostKraFiniteCylinderDensity.finiteCode M hM t x) *
        φ (HostKraFiniteCylinderDensity.finiteCode M hM t
          ((M.T^[n]) x)) *
        φ (HostKraFiniteCylinderDensity.finiteCode M hM t
          ((M.T^[2 * n]) x)) *
        φ (HostKraFiniteCylinderDensity.finiteCode M hM t
          ((M.T^[3 * n]) x))) := by
  simp only [complexFullyStructuredObservation, ContinuousMap.coe_mk,
    CompactConfigurationMeasureOrbit.configurationMap,
    Fin.isValue, Fin.val_zero, zero_mul, Function.iterate_zero_apply,
    Fin.val_one, one_mul,
    show (2 : Vertex).val = 2 by decide,
    show (3 : Vertex).val = 3 by decide]
  rw [codeShift_iterate_finiteCodeOrbitName M hM t x n,
    codeShift_iterate_finiteCodeOrbitName M hM t x (2 * n),
    codeShift_iterate_finiteCodeOrbitName M hM t x (3 * n)]
  rfl

theorem fullyStructuredObservation_configurationMap
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ))
    (x : M.X) (n : ℕ) :
    fullyStructuredObservation φ
        (CompactConfigurationMeasureOrbit.configurationMap
          (codeShift : CodeOrbitSpace M hM t → CodeOrbitSpace M hM t)
          n
          (HostKraFiniteCodeOrbitModel.finiteCodeOrbitName M hM t x)) =
      (φ (HostKraFiniteCylinderDensity.finiteCode M hM t x) *
        φ (HostKraFiniteCylinderDensity.finiteCode M hM t
          ((M.T^[n]) x)) *
        φ (HostKraFiniteCylinderDensity.finiteCode M hM t
          ((M.T^[2 * n]) x)) *
        φ (HostKraFiniteCylinderDensity.finiteCode M hM t
          ((M.T^[3 * n]) x))).re := by
  exact congrArg Complex.re
    (complexFullyStructuredObservation_configurationMap M hM t φ x n)

set_option maxHeartbeats 800000

/-- The genuine configuration-measure correlation of the pure finite code,
with no arbitrary measurable-set itinerary left in the carrier. -/
def finiteCylinderFullyStructuredCorrelation
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
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
  letI : MetricSpace (CodeOrbitSpace M hM t) :=
    PiCountable.metricSpace
  CompactConfigurationMeasureOrbit.configurationCorrelation
    ((codeOrbitProbabilityMeasure M hM t :
      ProbabilityMeasure (CodeOrbitSpace M hM t)) :
        Measure (CodeOrbitSpace M hM t))
    (codeShift : CodeOrbitSpace M hM t → CodeOrbitSpace M hM t)
    continuous_codeShift (fullyStructuredObservation φ) n

set_option maxHeartbeats 200000

set_option maxHeartbeats 800000

theorem finiteCylinderFullyStructuredCorrelation_eq_integral
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (ht : t.Finite)
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ))
    (n : ℕ) :
    finiteCylinderFullyStructuredCorrelation M hM t ht φ n =
      ∫ x,
        (φ (HostKraFiniteCylinderDensity.finiteCode M hM t x) *
          φ (HostKraFiniteCylinderDensity.finiteCode M hM t
            ((M.T^[n]) x)) *
          φ (HostKraFiniteCylinderDensity.finiteCode M hM t
            ((M.T^[2 * n]) x)) *
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
  letI : MetricSpace (CodeOrbitSpace M hM t) :=
    PiCountable.metricSpace
  let ν := codeOrbitProbabilityMeasure M hM t
  let R : CodeOrbitSpace M hM t → CodeOrbitSpace M hM t := codeShift
  let G := fullyStructuredObservation φ
  calc
    finiteCylinderFullyStructuredCorrelation M hM t ht φ n =
        ∫ y, G (CompactConfigurationMeasureOrbit.configurationMap
          R n y) ∂(ν : Measure (CodeOrbitSpace M hM t)) := by
      exact
        CompactConfigurationMeasureOrbit.configurationCorrelation_eq_integral
          (ν : Measure (CodeOrbitSpace M hM t))
          R continuous_codeShift G n
    _ = ∫ x, G (CompactConfigurationMeasureOrbit.configurationMap
          R n
          (HostKraFiniteCodeOrbitModel.finiteCodeOrbitName M hM t x))
          ∂M.μ := by
      dsimp only [ν]
      rw [codeOrbitProbabilityMeasure, ProbabilityMeasure.toMeasure_map]
      exact MeasureTheory.integral_map
        (finiteCodeOrbitName_measurable M hM t).aemeasurable
        ((G.continuous.comp
          (CompactConfigurationMeasureOrbit.continuous_configurationMap
            R continuous_codeShift n)).aestronglyMeasurable)
    _ = ∫ x,
        (φ (HostKraFiniteCylinderDensity.finiteCode M hM t x) *
          φ (HostKraFiniteCylinderDensity.finiteCode M hM t
            ((M.T^[n]) x)) *
          φ (HostKraFiniteCylinderDensity.finiteCode M hM t
            ((M.T^[2 * n]) x)) *
          φ (HostKraFiniteCylinderDensity.finiteCode M hM t
            ((M.T^[3 * n]) x))).re ∂M.μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦
        fullyStructuredObservation_configurationMap M hM t φ x n

set_option maxHeartbeats 200000

set_option maxHeartbeats 800000

/-- The complex four-cylinder integrand is integrable, proved on the
compact pure code space and pulled back along the coding map. -/
theorem complexFiniteCylinderFullyStructuredIntegrable
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (ht : t.Finite)
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ))
    (n : ℕ) :
    Integrable
      (fun x ↦
        φ (HostKraFiniteCylinderDensity.finiteCode M hM t x) *
          φ (HostKraFiniteCylinderDensity.finiteCode M hM t
            ((M.T^[n]) x)) *
          φ (HostKraFiniteCylinderDensity.finiteCode M hM t
            ((M.T^[2 * n]) x)) *
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
  letI : MetricSpace (CodeOrbitSpace M hM t) :=
    PiCountable.metricSpace
  let ν := codeOrbitProbabilityMeasure M hM t
  let R : CodeOrbitSpace M hM t → CodeOrbitSpace M hM t := codeShift
  let H : C(CodeOrbitSpace M hM t, ℂ) :=
    (complexFullyStructuredObservation φ).comp
      ⟨CompactConfigurationMeasureOrbit.configurationMap R n,
        CompactConfigurationMeasureOrbit.continuous_configurationMap
          R continuous_codeShift n⟩
  have hHmem :
      MemLp (fun y ↦ H y) 1
        (ν : Measure (CodeOrbitSpace M hM t)) :=
    (Lp.memLp (ContinuousMap.toLp 1
      (ν : Measure (CodeOrbitSpace M hM t)) ℂ H)).ae_eq
        (ContinuousMap.coeFn_toLp (p := (1 : ENNReal)) (𝕜 := ℂ)
          (ν : Measure (CodeOrbitSpace M hM t)) H)
  have hHint :
      Integrable (fun y ↦ H y)
        (ν : Measure (CodeOrbitSpace M hM t)) :=
    hHmem.integrable (by norm_num)
  have hHintMap :
      Integrable (fun y ↦ H y)
        (Measure.map
          (HostKraFiniteCodeOrbitModel.finiteCodeOrbitName M hM t)
          M.μ) := by
    simpa only [ν, codeOrbitProbabilityMeasure,
      ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk] using hHint
  have hpull :
      Integrable
        (fun x ↦ H
          (HostKraFiniteCodeOrbitModel.finiteCodeOrbitName M hM t x))
        M.μ :=
    hHintMap.comp_measurable (finiteCodeOrbitName_measurable M hM t)
  exact hpull.congr
    (Filter.Eventually.of_forall fun x ↦
      (by
        simpa only [H, ContinuousMap.comp_apply] using
          (complexFullyStructuredObservation_configurationMap
            M hM t φ x n)))

set_option maxHeartbeats 200000

set_option maxHeartbeats 800000

/-- The pure-code configuration correlation is exactly the fourfold
progression integral of the pulled-back finite cylinder in every slot. -/
theorem finiteCylinderFullyStructuredCorrelation_eq_quadrupleIntegral
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (ht : t.Finite)
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ))
    (n : ℕ) :
    let Q :=
      HostKraFiniteCodeOrbitModel.finiteCylinderLp M hM t ht φ
    finiteCylinderFullyStructuredCorrelation M hM t ht φ n =
      (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
        (fun x ↦ Q x) (fun x ↦ Q x)
        (fun x ↦ Q x) (fun x ↦ Q x) n x ∂M.μ).re := by
  dsimp only
  letI : IsProbabilityMeasure M.μ := hM.1
  let Q :=
    HostKraFiniteCodeOrbitModel.finiteCylinderLp M hM t ht φ
  have hQ0 :
      (fun x ↦ Q x) =ᵐ[M.μ]
        fun x ↦ φ (HostKraFiniteCylinderDensity.finiteCode M hM t x) :=
    HostKraFiniteCodeOrbitModel.finiteCylinderLp_ae_eq M hM t ht φ
  have hQ1 :
      (fun x ↦ Q ((M.T^[n]) x)) =ᵐ[M.μ]
        fun x ↦ φ (HostKraFiniteCylinderDensity.finiteCode M hM t
          ((M.T^[n]) x)) :=
    (hM.2.iterate n).quasiMeasurePreserving.ae_eq hQ0
  have hQ2 :
      (fun x ↦ Q ((M.T^[2 * n]) x)) =ᵐ[M.μ]
        fun x ↦ φ (HostKraFiniteCylinderDensity.finiteCode M hM t
          ((M.T^[2 * n]) x)) :=
    (hM.2.iterate (2 * n)).quasiMeasurePreserving.ae_eq hQ0
  have hQ3 :
      (fun x ↦ Q ((M.T^[3 * n]) x)) =ᵐ[M.μ]
        fun x ↦ φ (HostKraFiniteCylinderDensity.finiteCode M hM t
          ((M.T^[3 * n]) x)) :=
    (hM.2.iterate (3 * n)).quasiMeasurePreserving.ae_eq hQ0
  have hintegrand :
      (fun x ↦ MultipleKhintchineCartesian.quadrupleIntegrand M
        (fun x ↦ Q x) (fun x ↦ Q x)
        (fun x ↦ Q x) (fun x ↦ Q x) n x) =ᵐ[M.μ]
      fun x ↦
        φ (HostKraFiniteCylinderDensity.finiteCode M hM t x) *
          φ (HostKraFiniteCylinderDensity.finiteCode M hM t
            ((M.T^[n]) x)) *
          φ (HostKraFiniteCylinderDensity.finiteCode M hM t
            ((M.T^[2 * n]) x)) *
          φ (HostKraFiniteCylinderDensity.finiteCode M hM t
            ((M.T^[3 * n]) x)) := by
    filter_upwards [hQ0, hQ1, hQ2, hQ3] with x hx0 hx1 hx2 hx3
    simp only [MultipleKhintchineCartesian.quadrupleIntegrand]
    rw [hx0, hx1, hx2, hx3]
  rw [finiteCylinderFullyStructuredCorrelation_eq_integral]
  change
    (∫ x, RCLike.re
      (φ (HostKraFiniteCylinderDensity.finiteCode M hM t x) *
        φ (HostKraFiniteCylinderDensity.finiteCode M hM t
          ((M.T^[n]) x)) *
        φ (HostKraFiniteCylinderDensity.finiteCode M hM t
          ((M.T^[2 * n]) x)) *
        φ (HostKraFiniteCylinderDensity.finiteCode M hM t
          ((M.T^[3 * n]) x))) ∂M.μ) =
      (∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
        (fun x ↦ Q x) (fun x ↦ Q x)
        (fun x ↦ Q x) (fun x ↦ Q x) n x ∂M.μ).re
  rw [integral_re
    (complexFiniteCylinderFullyStructuredIntegrable
      M hM t ht φ n)]
  exact congrArg Complex.re (integral_congr_ae hintegrand.symm)

set_option maxHeartbeats 200000

/-- The exact remaining topological input for a finite cylinder after all
four slots have been structurally projected: homogeneity of the actual
pure-code configuration-measure orbit closure. -/
def FiniteCodeConfigurationOrbitHomogeneity : Prop :=
  ∀ (M : System.{u}) [StandardBorelSpace M.X],
    ∀ (hM : Chapter01.IsMeasurePreservingSystem M),
    IsErgodic M →
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
      letI : MetricSpace (CodeOrbitSpace M hM t) :=
        PiCountable.metricSpace
      CompactConfigurationMeasureOrbit.HasHomogeneousConfigurationMeasureOrbit
        ((codeOrbitProbabilityMeasure M hM t :
          ProbabilityMeasure (CodeOrbitSpace M hM t)) :
            Measure (CodeOrbitSpace M hM t))
        (codeShift : CodeOrbitSpace M hM t → CodeOrbitSpace M hM t)
        continuous_codeShift

/-- Under genuine pure-code orbit homogeneity, every four-slot finite
cylinder correlation is a compact-minimal orbit sequence. -/
theorem finiteCylinderFullyStructured_isMinimalOrbitSequence
    (hhom : FiniteCodeConfigurationOrbitHomogeneity.{u})
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (t : Set
      (HostKraFifteenDualFactor.parityFifteenDualRepresentatives M hM))
    (ht : t.Finite)
    (φ : C(HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t, ℂ)) :
    HostKraStructuredRecurrence.IsMinimalOrbitSequence.{0}
      (finiteCylinderFullyStructuredCorrelation M hM t ht φ) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : Fintype t := ht.fintype
  letI : MetricSpace
      (HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
    inferInstance
  letI : ∀ _ : ℕ, MetricSpace
      (HostKraFiniteCylinderDensity.FiniteCodeSpace M hM t) :=
    fun _ ↦ inferInstance
  letI : MetricSpace (CodeOrbitSpace M hM t) :=
    PiCountable.metricSpace
  have horbit :=
    CompactConfigurationMeasureOrbit.isMinimalOrbitSequence_configurationCorrelation_of_homogeneous
      ((codeOrbitProbabilityMeasure M hM t :
        ProbabilityMeasure (CodeOrbitSpace M hM t)) :
          Measure (CodeOrbitSpace M hM t))
      (codeShift : CodeOrbitSpace M hM t → CodeOrbitSpace M hM t)
      continuous_codeShift
      (hhom M hM hErg t ht)
      (fullyStructuredObservation φ)
  change
    HostKraStructuredRecurrence.IsMinimalOrbitSequence
      (finiteCylinderFullyStructuredCorrelation M hM t ht φ) at horbit
  exact
    MinimalOrbitUniverseLowering.isMinimalOrbitSequence_zero_of horbit

end Chapter02.HostKraFullyStructuredFiniteCode
