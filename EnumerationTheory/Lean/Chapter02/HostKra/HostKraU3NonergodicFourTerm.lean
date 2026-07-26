import Chapter02.HostKra.HostKraU3OptimalProgressionDecay
import Chapter02.HostKra.HostKraU3Component
import Chapter02.HostKra.HostKraUniformComponentIntegration

open Classical Filter MeasureTheory Set

noncomputable section

namespace Chapter02.HostKraU3NonergodicFourTerm

universe u

open HostKraErgodicDecomposition

/-- A bounded four-term progression integrand remains essentially
bounded. -/
lemma quadrupleIntegrand_memLp_top
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (hf₀ : MemLp f₀ ⊤ M.μ)
    (hf₁ : MemLp f₁ ⊤ M.μ)
    (hf₂ : MemLp f₂ ⊤ M.μ)
    (hf₃ : MemLp f₃ ⊤ M.μ)
    (n : ℕ) :
    MemLp
      (MultipleKhintchineCartesian.quadrupleIntegrand
        M f₀ f₁ f₂ f₃ n) ⊤ M.μ := by
  let h₁ := hf₁.comp_measurePreserving (hM.2.iterate n)
  let h₂ := hf₂.comp_measurePreserving (hM.2.iterate (2 * n))
  let h₃ := hf₃.comp_measurePreserving (hM.2.iterate (3 * n))
  simpa only [MultipleKhintchineCartesian.quadrupleIntegrand] using
    h₃.mul (r := ⊤) (h₂.mul (r := ⊤) (h₁.mul (r := ⊤) hf₀))

/-- The complex average of one translated four-term block, as a
pointwise function before integration. -/
def fourTermBlock
    (M : System.{u}) (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (N i : ℕ) : M.X → ℂ :=
  fun y ↦ (((N + 1 : ℕ) : ℂ)⁻¹) *
    ∑ n ∈ Finset.range (N + 1),
      MultipleKhintchineCartesian.quadrupleIntegrand
        M f₀ f₁ f₂ f₃ (i + n) y

/-- A bounded four-term block is integrable on a probability-preserving
system. -/
lemma fourTermBlock_integrable
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (hf₀ : MemLp f₀ ⊤ M.μ)
    (hf₁ : MemLp f₁ ⊤ M.μ)
    (hf₂ : MemLp f₂ ⊤ M.μ)
    (hf₃ : MemLp f₃ ⊤ M.μ)
    (N i : ℕ) :
    Integrable (fourTermBlock M f₀ f₁ f₂ f₃ N i) M.μ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  have hsum :
      MemLp
        (fun y ↦ ∑ n ∈ Finset.range (N + 1),
          MultipleKhintchineCartesian.quadrupleIntegrand
            M f₀ f₁ f₂ f₃ (i + n) y) ⊤ M.μ := by
    induction Finset.range (N + 1) using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using
          (MemLp.zero : MemLp (0 : M.X → ℂ) ⊤ M.μ)
    | @insert n s hn ih =>
        have hterm := quadrupleIntegrand_memLp_top
          M hM f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂ hf₃ (i + n)
        simpa [Finset.sum_insert hn] using hterm.add ih
  have hblock :
      MemLp (fourTermBlock M f₀ f₁ f₂ f₃ N i) ⊤ M.μ := by
    simpa only [fourTermBlock, Pi.smul_apply, smul_eq_mul] using
      hsum.const_smul (((N + 1 : ℕ) : ℂ)⁻¹)
  exact hblock.integrable (by simp)

/-- Integration commutes with the finite average defining a four-term
block. -/
lemma integral_fourTermBlock
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (hf₀ : MemLp f₀ ⊤ M.μ)
    (hf₁ : MemLp f₁ ⊤ M.μ)
    (hf₂ : MemLp f₂ ⊤ M.μ)
    (hf₃ : MemLp f₃ ⊤ M.μ)
    (N i : ℕ) :
    (∫ y, fourTermBlock M f₀ f₁ f₂ f₃ N i y ∂M.μ) =
      (((N + 1 : ℕ) : ℂ)⁻¹) *
        ∑ n ∈ Finset.range (N + 1),
          ∫ y, MultipleKhintchineCartesian.quadrupleIntegrand
            M f₀ f₁ f₂ f₃ (i + n) y ∂M.μ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  unfold fourTermBlock
  rw [integral_const_mul]
  congr 1
  rw [integral_finset_sum]
  intro n hn
  exact (quadrupleIntegrand_memLp_top
    M hM f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂ hf₃ (i + n)).integrable
      (by simp)

/-- A translated four-term block is bounded by the product of the four
essential bounds, uniformly in its length and starting point. -/
lemma fourTermBlock_norm_le
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (C₀ C₁ C₂ C₃ : ℝ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (_hC₃ : 0 ≤ C₃)
    (hf₀ : ∀ᵐ x ∂M.μ, ‖f₀ x‖ ≤ C₀)
    (hf₁ : ∀ᵐ x ∂M.μ, ‖f₁ x‖ ≤ C₁)
    (hf₂ : ∀ᵐ x ∂M.μ, ‖f₂ x‖ ≤ C₂)
    (hf₃ : ∀ᵐ x ∂M.μ, ‖f₃ x‖ ≤ C₃)
    (N i : ℕ) :
    ∀ᵐ y ∂M.μ,
      ‖fourTermBlock M f₀ f₁ f₂ f₃ N i y‖ ≤
        C₀ * C₁ * C₂ * C₃ := by
  have hall :
      ∀ n ∈ Finset.range (N + 1), ∀ᵐ y ∂M.μ,
        ‖MultipleKhintchineCartesian.quadrupleIntegrand
          M f₀ f₁ f₂ f₃ (i + n) y‖ ≤ C₀ * C₁ * C₂ * C₃ := by
    intro n hn
    filter_upwards [
      hf₀,
      (hM.2.iterate (i + n)).quasiMeasurePreserving.ae hf₁,
      (hM.2.iterate (2 * (i + n))).quasiMeasurePreserving.ae hf₂,
      (hM.2.iterate (3 * (i + n))).quasiMeasurePreserving.ae hf₃]
        with y h₀ h₁ h₂ h₃
    simp only [MultipleKhintchineCartesian.quadrupleIntegrand,
      norm_mul]
    exact mul_le_mul
      (mul_le_mul (mul_le_mul h₀ h₁ (norm_nonneg _) hC₀)
        h₂ (norm_nonneg _) (mul_nonneg hC₀ hC₁))
      h₃ (norm_nonneg _) (mul_nonneg (mul_nonneg hC₀ hC₁) hC₂)
  have hall' :
      ∀ᵐ y ∂M.μ, ∀ n ∈ Finset.range (N + 1),
        ‖MultipleKhintchineCartesian.quadrupleIntegrand
          M f₀ f₁ f₂ f₃ (i + n) y‖ ≤ C₀ * C₁ * C₂ * C₃ := by
    rw [Filter.eventually_all_finset]
    exact hall
  filter_upwards [hall'] with y hy
  unfold fourTermBlock
  rw [norm_mul]
  calc
    ‖((↑(N + 1) : ℂ)⁻¹)‖ *
        ‖∑ n ∈ Finset.range (N + 1),
          MultipleKhintchineCartesian.quadrupleIntegrand
            M f₀ f₁ f₂ f₃ (i + n) y‖ ≤
      ‖((↑(N + 1) : ℂ)⁻¹)‖ *
        ∑ n ∈ Finset.range (N + 1),
          ‖MultipleKhintchineCartesian.quadrupleIntegrand
            M f₀ f₁ f₂ f₃ (i + n) y‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖((↑(N + 1) : ℂ)⁻¹)‖ *
        ∑ _n ∈ Finset.range (N + 1), C₀ * C₁ * C₂ * C₃ := by
      gcongr with n hn
      exact hy n hn
    _ = C₀ * C₁ * C₂ * C₃ := by
      simp only [norm_inv, Nat.cast_add,
        Nat.cast_one, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hnorm : ‖((N : ℂ) + 1)‖ = (N : ℝ) + 1 := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (Complex.norm_natCast (N + 1))
      rw [hnorm]
      field_simp

/-- An ambient almost-everywhere assertion holds almost everywhere in
almost every conditional component. -/
lemma ae_ae_conditionalComponent
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (p : M.X → Prop)
    (hp : ∀ᵐ y ∂M.μ, p y) :
    ∀ᵐ x ∂M.μ, ∀ᵐ y ∂(D.measureAt x), p y := by
  have hbad : M.μ {y | ¬ p y} = 0 := by
    rw [← ae_iff]
    exact hp
  obtain ⟨N, hsub, hNmeas, hNzero⟩ :=
    exists_measurable_superset_of_null hbad
  filter_upwards [
    coreConditionalMeasure_null_ae
      M hM E D hE hD N hNmeas hNzero] with x hx
  rw [ae_iff]
  exact measure_mono_null hsub hx

/-- Essential boundedness with respect to the ambient measure passes to
almost every conditional component. -/
lemma memLp_top_ae_conditionalComponent
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    ∀ᵐ x ∂M.μ, MemLp f ⊤ (D.measureAt x) := by
  let g := hf.aestronglyMeasurable.mk f
  have hg : StronglyMeasurable g :=
    hf.aestronglyMeasurable.stronglyMeasurable_mk
  have heq :=
    ae_ae_conditionalComponent M hM E D hE hD
      (fun y ↦ f y = g y) hf.aestronglyMeasurable.ae_eq_mk
  have hbound :=
    ae_ae_conditionalComponent M hM E D hE hD
      (fun y ↦ ‖f y‖ ≤ lpNorm f ⊤ M.μ)
      (ae_le_lpNorm_exponent_top hf)
  filter_upwards [heq, hbound] with x hxEq hxBound
  exact memLp_top_of_bound
    (μ := D.measureAt x) ⟨g, hg, hxEq⟩ (lpNorm f ⊤ M.μ) hxBound

/-- Conditional disintegration represents each bounded four-term block
integral by the corresponding component integral. -/
lemma condExp_fourTermBlock_ae_eq_componentIntegral
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (_hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (hf₀ : MemLp f₀ ⊤ M.μ)
    (hf₁ : MemLp f₁ ⊤ M.μ)
    (hf₂ : MemLp f₂ ⊤ M.μ)
    (hf₃ : MemLp f₃ ⊤ M.μ)
    (N i : ℕ) :
    E.op (fourTermBlock M f₀ f₁ f₂ f₃ N i) =ᵐ[M.μ]
      fun x ↦ ∫ y, fourTermBlock M f₀ f₁ f₂ f₃ N i y
        ∂(D.measureAt x) := by
  exact hD.2.2.2.2 _
    (fourTermBlock_integrable
      M hM f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂ hf₃ N i)

/-- The component block-integral function is strongly measurable modulo
the ambient measure. -/
lemma componentIntegral_fourTermBlock_aestronglyMeasurable
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (hf₀ : MemLp f₀ ⊤ M.μ)
    (hf₁ : MemLp f₁ ⊤ M.μ)
    (hf₂ : MemLp f₂ ⊤ M.μ)
    (hf₃ : MemLp f₃ ⊤ M.μ)
    (N i : ℕ) :
    AEStronglyMeasurable
      (fun x ↦ ∫ y, fourTermBlock M f₀ f₁ f₂ f₃ N i y
        ∂(D.measureAt x)) M.μ := by
  let g := fourTermBlock M f₀ f₁ f₂ f₃ N i
  have hg := fourTermBlock_integrable
    M hM f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂ hf₃ N i
  have hEint : Integrable (E.op g) M.μ := (hE g hg).2.1
  exact hEint.aestronglyMeasurable.congr
    (condExp_fourTermBlock_ae_eq_componentIntegral
      M hM E D hE hD f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂ hf₃ N i)

/-- Integrating the component block integrals recovers the original block
integral. -/
lemma integral_componentIntegral_fourTermBlock
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (hf₀ : MemLp f₀ ⊤ M.μ)
    (hf₁ : MemLp f₁ ⊤ M.μ)
    (hf₂ : MemLp f₂ ⊤ M.μ)
    (hf₃ : MemLp f₃ ⊤ M.μ)
    (N i : ℕ) :
    (∫ x, ∫ y, fourTermBlock M f₀ f₁ f₂ f₃ N i y
        ∂(D.measureAt x) ∂M.μ) =
      ∫ y, fourTermBlock M f₀ f₁ f₂ f₃ N i y ∂M.μ := by
  let g := fourTermBlock M f₀ f₁ f₂ f₃ N i
  have hg := fourTermBlock_integrable
    M hM f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂ hf₃ N i
  have hrep :=
    condExp_fourTermBlock_ae_eq_componentIntegral
      M hM E D hE hD f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂ hf₃ N i
  calc
    _ = ∫ x, E.op g x ∂M.μ := integral_congr_ae hrep.symm
    _ = ∫ y, g y ∂M.μ := by
      simpa only [Measure.restrict_univ] using
        (hE g hg).2.2 Set.univ
          (invariantCoreSigmaAlgebra_isSigma M hM).1

/-- Vanishing of the third Host--Kra seminorm implies translated-uniform
four-term cancellation on an arbitrary probability-preserving system. -/
theorem hasUniformFourTermIntegralDecay_of_hasZeroHostKraU3
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (hf₀ : MemLp f₀ ⊤ M.μ)
    (hf₁ : MemLp f₁ ⊤ M.μ)
    (hf₂ : MemLp f₂ ⊤ M.μ)
    (hf₃ : MemLp f₃ ⊤ M.μ)
    (hzero : HostKraCubeSeminorm.HasZeroHostKraU3 M hM f₃ hf₃) :
    HostKraU3FourTermReversal.HasUniformFourTermIntegralDecay
      M f₀ f₁ f₂ f₃ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  obtain ⟨E, D, hE, hD, hproper, hsame⟩ :=
    invariantCoreConditionalMeasure_exists M hM
  let C₀ : ℝ := lpNorm f₀ ⊤ M.μ
  let C₁ : ℝ := lpNorm f₁ ⊤ M.μ
  let C₂ : ℝ := lpNorm f₂ ⊤ M.μ
  let C₃ : ℝ := lpNorm f₃ ⊤ M.μ
  let K : ℝ := C₀ * C₁ * C₂ * C₃
  let b : ℕ → ℕ → M.X → ℂ := fun N i x ↦
    ∫ y, fourTermBlock M f₀ f₁ f₂ f₃ N i y ∂(D.measureAt x)
  have hC₀ : 0 ≤ C₀ := lpNorm_nonneg
  have hC₁ : 0 ≤ C₁ := lpNorm_nonneg
  have hC₂ : 0 ≤ C₂ := lpNorm_nonneg
  have hC₃ : 0 ≤ C₃ := lpNorm_nonneg
  have hf₀bound : ∀ᵐ y ∂M.μ, ‖f₀ y‖ ≤ C₀ :=
    ae_le_lpNorm_exponent_top hf₀
  have hf₁bound : ∀ᵐ y ∂M.μ, ‖f₁ y‖ ≤ C₁ :=
    ae_le_lpNorm_exponent_top hf₁
  have hf₂bound : ∀ᵐ y ∂M.μ, ‖f₂ y‖ ≤ C₂ :=
    ae_le_lpNorm_exponent_top hf₂
  have hf₃bound : ∀ᵐ y ∂M.μ, ‖f₃ y‖ ≤ C₃ :=
    ae_le_lpNorm_exponent_top hf₃
  have hf₀boundC :=
    ae_ae_conditionalComponent M hM E D hE hD
      (fun y ↦ ‖f₀ y‖ ≤ C₀) hf₀bound
  have hf₁boundC :=
    ae_ae_conditionalComponent M hM E D hE hD
      (fun y ↦ ‖f₁ y‖ ≤ C₁) hf₁bound
  have hf₂boundC :=
    ae_ae_conditionalComponent M hM E D hE hD
      (fun y ↦ ‖f₂ y‖ ≤ C₂) hf₂bound
  have hf₃boundC :=
    ae_ae_conditionalComponent M hM E D hE hD
      (fun y ↦ ‖f₃ y‖ ≤ C₃) hf₃bound
  have hbmeas : ∀ N i, AEStronglyMeasurable (b N i) M.μ := by
    intro N i
    exact componentIntegral_fourTermBlock_aestronglyMeasurable
      M hM E D hE hD f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂ hf₃ N i
  have hbound : ∀ N i, ∀ᵐ x ∂M.μ, ‖b N i x‖ ≤ K := by
    intro N i
    filter_upwards [
      conditionalComponentSystem_mps_ae M hM E D hE hD,
      hf₀boundC, hf₁boundC, hf₂boundC, hf₃boundC
    ] with x hxMps hx₀ hx₁ hx₂ hx₃
    letI instComponent : IsProbabilityMeasure
        (conditionalComponentSystem M hM D x).μ := hxMps.1
    letI instMeasureAt : IsProbabilityMeasure (D.measureAt x) := hxMps.1
    have hblock := fourTermBlock_norm_le
      (conditionalComponentSystem M hM D x) hxMps
      f₀ f₁ f₂ f₃ C₀ C₁ C₂ C₃
      hC₀ hC₁ hC₂ hC₃ hx₀ hx₁ hx₂ hx₃ N i
    simpa only [b, K, conditionalComponentSystem, probReal_univ, mul_one] using
      (MeasureTheory.norm_integral_le_of_norm_le_const hblock)
  have hzeroC :=
    HostKraCubeDisintegration.hasZeroHostKraU3_ae_component
      M hM E D hE hD hproper hsame f₃ hf₃ hzero
  have hpoint :
      ∀ᵐ x ∂M.μ, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ‖b N i x‖ < ε := by
    filter_upwards [
      conditionalComponentSystem_mps_ae M hM E D hE hD,
      conditionalComponent_isErgodic_ae
        M hM E D hE hD hproper hsame,
      memLp_top_ae_conditionalComponent M hM E D hE hD f₀ hf₀,
      memLp_top_ae_conditionalComponent M hM E D hE hD f₁ hf₁,
      memLp_top_ae_conditionalComponent M hM E D hE hD f₂ hf₂,
      memLp_top_ae_conditionalComponent M hM E D hE hD f₃ hf₃,
      hf₁boundC, hf₂boundC, hzeroC
    ] with x hxMps hxErg hx₀ hx₁ hx₂ hx₃ hx₁b hx₂b hxzero
    letI : StandardBorelSpace
        (conditionalComponentSystem M hM D x).X := by
      change StandardBorelSpace M.X
      infer_instance
    have hdecay :=
      Chapter02.HostKraU3OptimalProgressionDecay.integral_quadruple_uniform_complex_zero_of_hasZeroHostKraU3_fun
        (conditionalComponentSystem M hM D x) hxMps hxErg
        f₀ f₁ f₂ f₃ hx₀ hx₁ hx₂ hx₃
        C₁ C₂ hC₁ hC₂ hx₁b hx₂b (hxzero hxMps hx₃)
    intro ε hε
    filter_upwards [hdecay ε hε] with N hN
    intro i
    change ‖∫ y, fourTermBlock
      (conditionalComponentSystem M hM D x)
      f₀ f₁ f₂ f₃ N i y ∂(D.measureAt x)‖ < ε
    have hni := hN i
    rw [← integral_fourTermBlock
        (conditionalComponentSystem M hM D x) hxMps
        f₀ f₁ f₂ f₃ hx₀ hx₁ hx₂ hx₃ N i] at hni
    simpa only [conditionalComponentSystem] using hni
  have hglobal :=
    HostKraUniformComponentIntegration.integral_uniform_tendsto_zero_of_ae
      M.μ b (fun _ ↦ K) hbmeas hbound
      (MeasureTheory.integrable_const K) hpoint
  intro ε hε
  filter_upwards [hglobal ε hε] with N hN
  intro i
  have hi := hN i
  dsimp only [b] at hi
  calc
    _ = ‖∫ y, fourTermBlock M f₀ f₁ f₂ f₃ N i y ∂M.μ‖ := by
      rw [integral_fourTermBlock
        M hM f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂ hf₃ N i]
    _ = ‖∫ x, ∫ y, fourTermBlock M f₀ f₁ f₂ f₃ N i y
          ∂(D.measureAt x) ∂M.μ‖ := by
      exact congrArg norm (integral_componentIntegral_fourTermBlock
        M hM E D hE hD f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂ hf₃ N i).symm
    _ < ε := hi

end Chapter02.HostKraU3NonergodicFourTerm
