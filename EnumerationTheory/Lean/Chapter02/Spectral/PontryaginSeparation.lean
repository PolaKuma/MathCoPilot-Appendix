import Chapter02.Spectral.CompactAbelianPeterWeyl
import Chapter02.Spectral.CompactFredholm
import Chapter02.Spectral.SeparatedKernelDensity
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

noncomputable section

open Classical MeasureTheory

namespace Chapter02.PontryaginSeparation

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The project's concrete compact-image formulation implies Mathlib's
`IsCompactOperator`. -/
lemma isCompactOperator_of_hasCompactClosedBallImage
    (K : E →L[ℂ] E)
    (hK : HilbertSchmidtConsequences.HasCompactClosedBallImage K) :
    IsCompactOperator K := by
  exact (isCompactOperator_iff_image_closedBall_subset_compact
    (K : E →ₗ[ℂ] E) zero_lt_one).2 (hK 1)

/-- Every nonzero eigenspace of a compact operator is finite-dimensional.
This is the part of the compact spectral theorem needed below and only uses
the compactness of the identity on the eigenspace. -/
lemma finiteDimensional_eigenspace_of_compact
    (K : E →L[ℂ] E) (hK : IsCompactOperator K)
    (μ : ℂ) (hμ : μ ≠ 0) :
    FiniteDimensional ℂ (Module.End.eigenspace K.toLinearMap μ) := by
  have hKV : ∀ v ∈ Module.End.eigenspace K.toLinearMap μ,
      K.toLinearMap v ∈ Module.End.eigenspace K.toLinearMap μ := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [hv, map_smul, hv]
  have hVclosed : IsClosed
      (Module.End.eigenspace K.toLinearMap μ : Set E) := by
    rw [Module.End.eigenspace_def]
    change IsClosed
      (LinearMap.ker
        ((K - μ • ContinuousLinearMap.id ℂ E).toLinearMap) : Set E)
    exact ContinuousLinearMap.isClosed_ker _
  letI : CompleteSpace (Module.End.eigenspace K.toLinearMap μ) :=
    IsClosed.completeSpace_coe
  have hKr : IsCompactOperator (K.toLinearMap.restrict hKV) :=
    hK.restrict' hKV
  have hr_eq :
      K.toLinearMap.restrict hKV =
        μ • LinearMap.id := by
    ext v
    exact Module.End.mem_eigenspace_iff.mp v.property
  have hid : IsCompactOperator (id :
      (Module.End.eigenspace K.toLinearMap μ) →
        Module.End.eigenspace K.toLinearMap μ) := by
    rw [hr_eq, LinearMap.coe_smul, IsCompactOperator.smul_iff₀ hμ] at hKr
    simpa using hKr
  obtain ⟨C, hC, hsub⟩ :=
    (isCompactOperator_iff_image_closedBall_subset_compact
      (LinearMap.id :
        (Module.End.eigenspace K.toLinearMap μ) →ₗ[ℂ]
          (Module.End.eigenspace K.toLinearMap μ))
      zero_lt_one).mp hid
  apply FiniteDimensional.of_isCompact_closedBall₀ ℂ zero_lt_one
  apply hC.of_isClosed_subset Metric.isClosed_closedBall
  simpa using hsub

/-- A nonzero compact symmetric operator has a nonzero eigenvalue. -/
lemma exists_nonzero_eigenvalue_of_compact_symmetric
    (K : E →L[ℂ] E) (hK : IsCompactOperator K)
    (hKs : K.IsSymmetric) (hK0 : K ≠ 0) :
    ∃ μ : ℂ, μ ≠ 0 ∧
      Module.End.HasEigenvalue K.toLinearMap μ := by
  have hzero :
      (∀ μ, Module.End.HasEigenvalue K.toLinearMap μ → μ = 0) ↔
        K = 0 := by
    rw [← nnnorm_eq_zero, ← ENNReal.coe_eq_zero,
      ← IsSelfAdjoint.spectralRadius_eq_nnnorm hKs.isSelfAdjoint,
      spectralRadius, ← not_iff_not, ENNReal.iSup_eq_zero]
    push Not
    apply exists_congr
    intro μ
    by_cases hμ : μ = 0
    · simp [hμ]
    · simpa [hμ] using
        (CompactFredholm.hasEigenvalue_iff_mem_spectrum
          hK hμ)
  by_contra! h
  apply hK0
  apply hzero.mp
  intro μ hμ
  by_contra hμ0
  exact h μ hμ0 hμ

set_option maxHeartbeats 2000000 in
/-- A commuting family of symmetric endomorphisms of a nonzero
finite-dimensional complex inner-product space has a common eigenvector. -/
lemma exists_common_eigenvector_of_commuting_symmetric
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V]
    {ι : Type*} (f : ι → Module.End ℂ V)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (hsym : ∀ i, (f i).IsSymmetric) :
    ∃ χ : ι → ℂ, ∃ v : V, v ≠ 0 ∧
      ∀ i, f i v = χ i • v := by
  have htop :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f hcomm (fun i ↦ Module.End.iSup_maxGenEigenspace_eq_top (f i))
  have hsemisimple :
      ∀ i μ, (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    fun i μ ↦ (hsym i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  simp_rw [hsemisimple] at htop
  have hexists :
      ∃ χ : ι → ℂ, (⨅ i, (f i).eigenspace (χ i)) ≠ ⊥ := by
    by_contra h
    push_neg at h
    have : (⨆ χ : ι → ℂ, ⨅ i, (f i).eigenspace (χ i)) = ⊥ := by
      simp only [h, iSup_bot]
    rw [this] at htop
    exact (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) htop
  obtain ⟨χ, hχ⟩ := hexists
  obtain ⟨v, hv, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have hv' : ∀ i, v ∈ (f i).eigenspace (χ i) := by
    exact (Submodule.mem_iInf
      (fun i ↦ (f i).eigenspace (χ i))).mp hv
  refine ⟨χ, v, hv0, ?_⟩
  intro i
  exact Module.End.mem_eigenspace_iff.mp (hv' i)

section HaarTranslations

variable {G : Type u} [CommGroup G] [MetricSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

noncomputable def haarIdentitySystem (m : Measure G) : System where
  X := G
  measurableSpace := inferInstance
  μ := m
  T := id

lemma haarIdentitySystem_measurePreserving
    (m : Measure G) [IsProbabilityMeasure m] :
    Chapter01.IsMeasurePreservingSystem (haarIdentitySystem m) := by
  refine ⟨?_, MeasurePreserving.id m⟩
  exact (inferInstance : IsProbabilityMeasure m)

/-- Left translation on Haar `L²`, represented by precomposition
`F ↦ (x ↦ F (a*x))`. -/
noncomputable def leftTranslation
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (a : G) : Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x : G ↦ a * x)
    (measurePreserving_mul_left m a)).toContinuousLinearMap

noncomputable def leftTranslationIsometry
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (a : G) : Lp ℂ 2 m →ₗᵢ[ℂ] Lp ℂ 2 m :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : G ↦ a * x)
    (measurePreserving_mul_left m a)

lemma leftTranslation_norm
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (a : G) (F : Lp ℂ 2 m) :
    ‖leftTranslation m a F‖ = ‖F‖ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x : G ↦ a * x)
    (measurePreserving_mul_left m a)).norm_map F

lemma leftTranslation_mul
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (a b : G) :
    (leftTranslation m (a * b)).toLinearMap =
      (leftTranslation m b).toLinearMap.comp
        (leftTranslation m a).toLinearMap := by
  ext F
  change
    ↑↑(Lp.compMeasurePreserving (fun x : G ↦ (a * b) * x)
      (measurePreserving_mul_left m (a * b)) F) =ᶠ[ae m]
    ↑↑(Lp.compMeasurePreserving (fun x : G ↦ b * x)
      (measurePreserving_mul_left m b)
      (Lp.compMeasurePreserving (fun x : G ↦ a * x)
        (measurePreserving_mul_left m a) F))
  filter_upwards
    [Lp.coeFn_compMeasurePreserving F
      (measurePreserving_mul_left m (a * b)),
     Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (fun x : G ↦ a * x)
        (measurePreserving_mul_left m a) F)
      (measurePreserving_mul_left m b),
     (measurePreserving_mul_left m b).quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_compMeasurePreserving F
        (measurePreserving_mul_left m a))] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  change (F : G → ℂ) ((a * b) * x) = (F : G → ℂ) (a * (b * x))
  apply congrArg (fun y : G ↦ (F : G → ℂ) y)
  ac_rfl

lemma leftTranslation_mul_clm
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (a b : G) :
    leftTranslation m (a * b) =
      (leftTranslation m b).comp (leftTranslation m a) := by
  apply ContinuousLinearMap.ext
  intro F
  exact LinearMap.congr_fun (leftTranslation_mul m a b) F

lemma leftTranslation_one
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure] :
    leftTranslation m 1 = 1 := by
  ext F
  filter_upwards
    [Lp.coeFn_compMeasurePreserving F
      (measurePreserving_mul_left m 1)] with x hx
  change (Lp.compMeasurePreserving (fun x : G ↦ 1 * x)
      (measurePreserving_mul_left m 1) F : G → ℂ) x = (F : G → ℂ) x
  rw [hx]
  simp

lemma leftTranslation_inv_comp
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (a : G) :
    (leftTranslation m a).comp (leftTranslation m a⁻¹) = 1 := by
  rw [← leftTranslation_mul_clm m a⁻¹ a]
  rw [show a⁻¹ * a = 1 by group, leftTranslation_one]

lemma leftTranslation_inner
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (a : G) (F H : Lp ℂ 2 m) :
    @inner ℂ (Lp ℂ 2 m) _ (leftTranslation m a F)
      (leftTranslation m a H) =
      @inner ℂ (Lp ℂ 2 m) _ F H := by
  exact (leftTranslationIsometry m a).inner_map_map F H

lemma leftTranslation_adjoint
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (a : G) :
    ContinuousLinearMap.adjoint (leftTranslation m a) =
      leftTranslation m a⁻¹ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro F H
  rw [← leftTranslation_inner m a]
  rw [show leftTranslation m a (leftTranslation m a⁻¹ F) = F by
    exact congrArg (fun U : Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m ↦ U F)
      (leftTranslation_inv_comp m a)]

lemma leftTranslation_commute
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (a b : G) :
    Commute (leftTranslation m a) (leftTranslation m b) := by
  rw [Commute]
  change (leftTranslation m a).comp (leftTranslation m b) =
    (leftTranslation m b).comp (leftTranslation m a)
  rw [← leftTranslation_mul_clm m b a,
    ← leftTranslation_mul_clm m a b, mul_comm]

/-- The real and imaginary self-adjoint parts of all translations. -/
noncomputable def symmetricTranslation
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure] :
    G ⊕ G → Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m
  | Sum.inl a => leftTranslation m a + leftTranslation m a⁻¹
  | Sum.inr a => Complex.I •
      (leftTranslation m a - leftTranslation m a⁻¹)

lemma symmetricTranslation_symmetric
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (i : G ⊕ G) :
    (symmetricTranslation m i).IsSymmetric := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
  cases i with
  | inl a =>
      simpa only [symmetricTranslation,
        ContinuousLinearMap.star_eq_adjoint,
        leftTranslation_adjoint] using
        IsSelfAdjoint.add_star_self (leftTranslation m a)
  | inr a =>
      change IsSelfAdjoint
        (Complex.I • (leftTranslation m a - leftTranslation m a⁻¹))
      rw [isSelfAdjoint_iff]
      simp only [star_smul, star_sub,
        ContinuousLinearMap.star_eq_adjoint,
        leftTranslation_adjoint]
      have hinvinv : (a⁻¹)⁻¹ = a := by group
      rw [hinvinv]
      simp
      module

lemma symmetricTranslation_commute
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure] :
    Pairwise fun i j : G ⊕ G ↦
      Commute (symmetricTranslation m i) (symmetricTranslation m j) := by
  intro i j hij
  have hbase (a b : G) :
      Commute (leftTranslation m a) (leftTranslation m b) :=
    leftTranslation_commute m a b
  cases i with
  | inl a =>
      cases j with
      | inl b =>
          exact ((hbase a b).add_right (hbase a b⁻¹)).add_left
            ((hbase a⁻¹ b).add_right (hbase a⁻¹ b⁻¹))
      | inr b =>
          exact (((hbase a b).sub_right (hbase a b⁻¹)).add_left
            ((hbase a⁻¹ b).sub_right (hbase a⁻¹ b⁻¹))).smul_right Complex.I
  | inr a =>
      cases j with
      | inl b =>
          exact (((hbase a b).add_right (hbase a b⁻¹)).sub_left
            ((hbase a⁻¹ b).add_right (hbase a⁻¹ b⁻¹))).smul_left Complex.I
      | inr b =>
          exact ((((hbase a b).sub_right (hbase a b⁻¹)).sub_left
            ((hbase a⁻¹ b).sub_right (hbase a⁻¹ b⁻¹))).smul_left
              Complex.I).smul_right Complex.I

/-- A continuous convolution kernel on a compact group. -/
def convolutionKernel (h : C(G, ℂ)) : G × G → ℂ :=
  fun p ↦ h (p.1 * p.2⁻¹)

lemma continuous_convolutionKernel (h : C(G, ℂ)) :
    Continuous (convolutionKernel h) := by
  unfold convolutionKernel
  fun_prop

lemma convolutionKernel_memLp
    (m : Measure G) [IsProbabilityMeasure m] (h : C(G, ℂ)) :
    MemLp (convolutionKernel h) 2 (m.prod m) := by
  exact (continuous_convolutionKernel h).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The Hilbert--Schmidt convolution operator associated to a continuous
kernel `h(xy⁻¹)`. -/
noncomputable def convolutionOperator
    (m : Measure G) [IsProbabilityMeasure m] (h : C(G, ℂ)) :
    Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m :=
  HilbertSchmidtConsequences.kernelOperator
    (haarIdentitySystem m)
    (haarIdentitySystem_measurePreserving m)
    (convolutionKernel (G := G) h)
    (convolutionKernel_memLp (G := G) m h)

lemma convolutionOperator_compact
    (m : Measure G) [IsProbabilityMeasure m] (h : C(G, ℂ)) :
    IsCompactOperator (convolutionOperator m h) := by
  apply isCompactOperator_of_hasCompactClosedBallImage
  exact SeparatedKernelDensity.kernelOperator_hasCompactClosedBallImage
    (haarIdentitySystem m)
    (haarIdentitySystem_measurePreserving m)
    (convolutionKernel (G := G) h)
    (convolutionKernel_memLp (G := G) m h)

lemma kernelAction_convolution_leftTranslation
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (h : C(G, ℂ)) (a x : G) (F : Lp ℂ 2 m) :
    kernelAction (haarIdentitySystem m) (convolutionKernel (G := G) h)
        (leftTranslation m a F) x =
      kernelAction (haarIdentitySystem m) (convolutionKernel (G := G) h)
        F (a * x) := by
  have hF := Lp.coeFn_compMeasurePreserving F
    (measurePreserving_mul_left m a)
  simp only [kernelAction, convolutionKernel]
  calc
    (∫ y, h (x * y⁻¹) * (leftTranslation m a F : G → ℂ) y ∂m) =
        ∫ y, h (x * y⁻¹) * (F : G → ℂ) (a * y) ∂m := by
      apply integral_congr_ae
      filter_upwards [hF] with y hy
      rw [show (leftTranslation m a F : G → ℂ) y =
          (F : G → ℂ) (a * y) by
        exact hy]
    _ = ∫ y, h (a * x * y⁻¹) * (F : G → ℂ) y ∂m := by
      rw [← integral_mul_left_eq_self
        (fun y ↦ h (a * x * y⁻¹) * (F : G → ℂ) y) a]
      apply integral_congr_ae
      exact .of_forall fun y ↦ by
        change h (x * y⁻¹) * (F : G → ℂ) (a * y) =
          h (a * x * (a * y)⁻¹) * (F : G → ℂ) (a * y)
        have heq : x * y⁻¹ = a * x * (a * y)⁻¹ := by
          symm
          calc
            a * x * (a * y)⁻¹ = a * x * (y⁻¹ * a⁻¹) := by
              rw [mul_inv_rev]
            _ = (a * a⁻¹) * (x * y⁻¹) := by ac_rfl
            _ = x * y⁻¹ := by simp
        rw [heq]
    _ = ∫ y, h (a * x * y⁻¹) * (F : G → ℂ) y ∂m := rfl

lemma leftTranslation_convolutionOperator
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (h : C(G, ℂ)) (a : G) :
    (leftTranslation m a).comp (convolutionOperator m h) =
      (convolutionOperator m h).comp (leftTranslation m a) := by
  ext F
  let hM := haarIdentitySystem_measurePreserving m
  let hH := convolutionKernel_memLp (G := G) m h
  let hKF := HilbertSchmidtConsequences.kernelAction_memLp_two
    (haarIdentitySystem m) hM (convolutionKernel (G := G) h) hH F (Lp.memLp F)
  let hKUF := HilbertSchmidtConsequences.kernelAction_memLp_two
    (haarIdentitySystem m) hM (convolutionKernel (G := G) h) hH
      (leftTranslation m a F) (Lp.memLp (leftTranslation m a F))
  filter_upwards
    [Lp.coeFn_compMeasurePreserving
      (convolutionOperator m h F)
      (measurePreserving_mul_left m a),
     hKF.coeFn_toLp,
     hKUF.coeFn_toLp,
     (measurePreserving_mul_left m a).quasiMeasurePreserving.ae_eq_comp
      hKF.coeFn_toLp] with x hleft hKF₀ hKUF₀ hKFa
  simp only [ContinuousLinearMap.comp_apply]
  rw [show (leftTranslation m a (convolutionOperator m h F) : G → ℂ) x =
      (convolutionOperator m h F : G → ℂ) (a * x) by exact hleft]
  simp only [convolutionOperator,
    HilbertSchmidtConsequences.kernelOperator_apply]
  change (hKF.toLp _ : G → ℂ) (a * x) = (hKUF.toLp _ : G → ℂ) x
  calc
    (hKF.toLp _ : G → ℂ) (a * x) =
        kernelAction (haarIdentitySystem m)
          (convolutionKernel (G := G) h) F (a * x) := hKFa
    _ = kernelAction (haarIdentitySystem m)
          (convolutionKernel (G := G) h)
          (leftTranslation m a F) x :=
      (kernelAction_convolution_leftTranslation m h a x F).symm
    _ = (hKUF.toLp _ : G → ℂ) x := hKUF₀.symm

/-- Convolution of two continuous functions, retained as a continuous
function rather than only as an `L²` class. -/
noncomputable def convolutionContinuousMap
    (m : Measure G) [IsProbabilityMeasure m]
    (h f : C(G, ℂ)) : C(G, ℂ) where
  toFun x := ∫ y, h (x * y⁻¹) * f y ∂m
  continuous_toFun := by
    rw [← continuousOn_univ]
    apply continuousOn_integral_of_compact_support
      (k := (Set.univ : Set G)) isCompact_univ
    · apply Continuous.continuousOn
      fun_prop
    · intro p y hp hy
      exact (hy (Set.mem_univ y)).elim

lemma convolutionOperator_apply_continuous
    (m : Measure G) [IsProbabilityMeasure m]
    (h f : C(G, ℂ)) :
    convolutionOperator m h (ContinuousMap.toLp 2 m ℂ f) =
      ContinuousMap.toLp 2 m ℂ (convolutionContinuousMap m h f) := by
  let hM := haarIdentitySystem_measurePreserving m
  let hH := convolutionKernel_memLp (G := G) m h
  let F : Lp ℂ 2 m := ContinuousMap.toLp 2 m ℂ f
  let hKF := HilbertSchmidtConsequences.kernelAction_memLp_two
    (haarIdentitySystem m) hM (convolutionKernel (G := G) h) hH
      F (Lp.memLp F)
  rw [show ContinuousMap.toLp 2 m ℂ f = F by rfl]
  simp only [convolutionOperator,
    HilbertSchmidtConsequences.kernelOperator_apply]
  change hKF.toLp _ =
    ContinuousMap.toLp 2 m ℂ (convolutionContinuousMap m h f)
  apply Lp.ext
  have hF : (F : G → ℂ) =ᶠ[ae m] f :=
    ContinuousMap.coeFn_toLp m f
  have haction :
      kernelAction (haarIdentitySystem m)
          (convolutionKernel (G := G) h) F =
        convolutionContinuousMap m h f := by
    rw [HilbertSchmidtConsequences.kernelAction_congr_ae
      (haarIdentitySystem m) (convolutionKernel (G := G) h) hF]
    rfl
  filter_upwards
    [hKF.coeFn_toLp,
     ContinuousMap.coeFn_toLp (p := (2 : ENNReal)) (𝕜 := ℂ)
      m (convolutionContinuousMap m h f)] with
      x hx hy
  rw [hx, hy, haction]

/-- The continuous test function `y ↦ star (h(y⁻¹))`. -/
def reflectedKernelTest (h : C(G, ℂ)) : C(G, ℂ) where
  toFun y := star (h y⁻¹)
  continuous_toFun := by fun_prop

lemma convolutionContinuousMap_reflected_at_one
    (m : Measure G) [IsProbabilityMeasure m] (h : C(G, ℂ)) :
    convolutionContinuousMap m h (reflectedKernelTest h) 1 =
      (∫ y, Complex.normSq (h y⁻¹) ∂m : ℝ) := by
  change (∫ y, h (1 * y⁻¹) * (starRingEnd ℂ) (h y⁻¹) ∂m) =
    (∫ y, Complex.normSq (h y⁻¹) ∂m : ℝ)
  simp only [one_mul, Complex.mul_conj]
  exact integral_complex_ofReal (μ := m)

lemma convolutionOperator_ne_zero_of_ne_zero
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (h : C(G, ℂ)) (hh : h ≠ 0) :
    convolutionOperator m h ≠ 0 := by
  obtain ⟨z, hz⟩ : ∃ z, h z ≠ 0 := by
    simpa [DFunLike.ext_iff] using hh
  let q : G → ℝ := fun y ↦ Complex.normSq (h y⁻¹)
  have hqcont : Continuous q := by
    dsimp only [q]
    fun_prop
  have hqnonneg : 0 ≤ q := fun y ↦ Complex.normSq_nonneg _
  have hqz : q z⁻¹ ≠ 0 := by
    dsimp only [q]
    rw [inv_inv]
    intro hzsq
    exact hz (Complex.normSq_eq_zero.mp hzsq)
  have hqpos : 0 < ∫ y, q y ∂m :=
    hqcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) hqnonneg hqz
  intro hzero
  have happ := convolutionOperator_apply_continuous
    (G := G) m h (reflectedKernelTest h)
  rw [hzero, ContinuousLinearMap.zero_apply] at happ
  have hmapzero :
      convolutionContinuousMap m h (reflectedKernelTest h) = 0 := by
    apply (ContinuousMap.toLp_injective (p := (2 : ENNReal))
      (𝕜 := ℂ) m)
    simpa using happ.symm
  have hone := congrArg
    (fun f : C(G, ℂ) ↦ f 1) hmapzero
  change convolutionContinuousMap m h (reflectedKernelTest h) 1 =
    (0 : C(G, ℂ)) 1 at hone
  rw [convolutionContinuousMap_reflected_at_one] at hone
  simp only [ContinuousMap.zero_apply] at hone
  have : (∫ y, q y ∂m) = 0 := by
    exact_mod_cast hone
  exact hqpos.ne' this

/-- Left translate a continuous scalar function on the group. -/
def leftShiftContinuousMap (a : G) (h : C(G, ℂ)) : C(G, ℂ) where
  toFun z := h (a * z)
  continuous_toFun := h.continuous.comp (continuous_const.mul continuous_id)

lemma kernelAction_leftShift
    (m : Measure G) [IsProbabilityMeasure m]
    (h : C(G, ℂ)) (a x : G) (F : Lp ℂ 2 m) :
    kernelAction (haarIdentitySystem m)
        (convolutionKernel (G := G) (leftShiftContinuousMap a h)) F x =
      kernelAction (haarIdentitySystem m)
        (convolutionKernel (G := G) h) F (a * x) := by
  simp only [kernelAction, convolutionKernel, leftShiftContinuousMap]
  apply integral_congr_ae
  exact .of_forall fun (y : G) ↦ by
    change h (a * (x * y⁻¹)) * (F : G → ℂ) y =
      h ((a * x) * y⁻¹) * (F : G → ℂ) y
    rw [mul_assoc]

lemma convolutionOperator_leftShift
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (h : C(G, ℂ)) (a : G) :
    convolutionOperator m (leftShiftContinuousMap a h) =
      (leftTranslation m a).comp (convolutionOperator m h) := by
  ext F
  let hM := haarIdentitySystem_measurePreserving m
  let hH := convolutionKernel_memLp (G := G) m h
  let hHs := convolutionKernel_memLp (G := G) m
    (leftShiftContinuousMap a h)
  let hKF := HilbertSchmidtConsequences.kernelAction_memLp_two
    (haarIdentitySystem m) hM (convolutionKernel (G := G) h) hH
      F (Lp.memLp F)
  let hKsF := HilbertSchmidtConsequences.kernelAction_memLp_two
    (haarIdentitySystem m) hM
      (convolutionKernel (G := G) (leftShiftContinuousMap a h)) hHs
      F (Lp.memLp F)
  filter_upwards
    [hKsF.coeFn_toLp,
     Lp.coeFn_compMeasurePreserving
      (convolutionOperator m h F)
      (measurePreserving_mul_left m a),
     (measurePreserving_mul_left m a).quasiMeasurePreserving.ae_eq_comp
      hKF.coeFn_toLp] with x hKs hxtrans hKFa
  simp only [ContinuousLinearMap.comp_apply, convolutionOperator,
    HilbertSchmidtConsequences.kernelOperator_apply]
  change (hKsF.toLp _ : G → ℂ) x =
    (leftTranslation m a (hKF.toLp _) : G → ℂ) x
  calc
    (hKsF.toLp _ : G → ℂ) x =
        kernelAction (haarIdentitySystem m)
          (convolutionKernel (G := G) (leftShiftContinuousMap a h)) F x := hKs
    _ = kernelAction (haarIdentitySystem m)
          (convolutionKernel (G := G) h) F (a * x) :=
      kernelAction_leftShift m h a x F
    _ = (hKF.toLp _ : G → ℂ) (a * x) := hKFa.symm
    _ = (leftTranslation m a (hKF.toLp _) : G → ℂ) x := hxtrans.symm

lemma convolutionOperator_sub
    (m : Measure G) [IsProbabilityMeasure m]
    (h k : C(G, ℂ)) :
    convolutionOperator m (h - k) =
      convolutionOperator m h - convolutionOperator m k := by
  symm
  apply HilbertSchmidtConsequences.kernelOperator_sub

/-- A fixed continuous function which detects the identity. -/
def distanceFromOne : C(G, ℂ) where
  toFun z := (dist z 1 : ℂ)
  continuous_toFun := by fun_prop

/-- For `g ≠ 1`, this continuous difference is nonzero and records the
failure of invariance under translation by `g`. -/
def pointSeparatingKernel (g : G) : C(G, ℂ) :=
  leftShiftContinuousMap g distanceFromOne - distanceFromOne

@[simp]
lemma pointSeparatingKernel_apply (g z : G) :
    pointSeparatingKernel g z =
      (dist (g * z) 1 : ℂ) - (dist z 1 : ℂ) :=
  rfl

lemma pointSeparatingKernel_ne_zero {g : G} (hg : g ≠ 1) :
    pointSeparatingKernel g ≠ 0 := by
  intro hzero
  have hone := congrArg (fun h : C(G, ℂ) ↦ h 1) hzero
  simp only [pointSeparatingKernel_apply, mul_one,
    ContinuousMap.zero_apply] at hone
  have hone' : ((dist g 1 : ℝ) : ℂ) = 0 := by
    simpa using hone
  have hd : dist g 1 = 0 := by exact_mod_cast hone'
  exact hg (dist_eq_zero.mp hd)

/-- The compact convolution operator tailored to the point `g`. -/
noncomputable def separatingOperator
    (m : Measure G) [IsProbabilityMeasure m] (g : G) :
    Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m :=
  convolutionOperator m (pointSeparatingKernel g)

lemma separatingOperator_compact
    (m : Measure G) [IsProbabilityMeasure m] (g : G) :
    IsCompactOperator (separatingOperator m g) :=
  convolutionOperator_compact m (pointSeparatingKernel g)

lemma separatingOperator_ne_zero
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    {g : G} (hg : g ≠ 1) :
    separatingOperator m g ≠ 0 :=
  convolutionOperator_ne_zero_of_ne_zero m
    (pointSeparatingKernel g) (pointSeparatingKernel_ne_zero hg)

lemma separatingOperator_factor
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (g : G) :
    separatingOperator m g =
      (leftTranslation m g).comp
          (convolutionOperator m distanceFromOne) -
        convolutionOperator m distanceFromOne := by
  rw [separatingOperator, pointSeparatingKernel,
    convolutionOperator_sub, convolutionOperator_leftShift]

/-- The positive compact operator `T†T` associated to the separating
convolution operator. -/
noncomputable def separatingPositiveOperator
    (m : Measure G) [IsProbabilityMeasure m] (g : G) :
    Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m :=
  star (separatingOperator m g) * separatingOperator m g

lemma separatingPositiveOperator_compact
    (m : Measure G) [IsProbabilityMeasure m] (g : G) :
    IsCompactOperator (separatingPositiveOperator m g) := by
  let T := separatingOperator m g
  have hT : IsCompactOperator T := separatingOperator_compact m g
  have hcomp := hT.clm_comp (star T)
  simpa only [separatingPositiveOperator, T,
    ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.mul_apply, Function.comp_apply] using hcomp

lemma separatingPositiveOperator_symmetric
    (m : Measure G) [IsProbabilityMeasure m] (g : G) :
    (separatingPositiveOperator m g).IsSymmetric := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
  exact IsSelfAdjoint.star_mul_self (separatingOperator m g)

lemma separatingPositiveOperator_ne_zero
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    {g : G} (hg : g ≠ 1) :
    separatingPositiveOperator m g ≠ 0 := by
  let T := separatingOperator m g
  have hT : T ≠ 0 := separatingOperator_ne_zero m hg
  obtain ⟨F, hTF⟩ : ∃ F, T F ≠ 0 := by
    simpa [ContinuousLinearMap.ext_iff] using hT
  intro hzero
  have hAF := congrArg
    (fun A : Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m ↦ A F) hzero
  have hinner := congrArg
    (fun H : Lp ℂ 2 m ↦ @inner ℂ (Lp ℂ 2 m) _ H F) hAF
  simp only [separatingPositiveOperator,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.zero_apply, inner_zero_left] at hinner
  rw [ContinuousLinearMap.adjoint_inner_left] at hinner
  exact hTF (inner_self_eq_zero.mp hinner)

lemma separatingPositiveOperator_commutes
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (g a : G) :
    (leftTranslation m a).comp (separatingPositiveOperator m g) =
      (separatingPositiveOperator m g).comp (leftTranslation m a) := by
  let T := separatingOperator m g
  let U := leftTranslation m a
  have hUT : U.comp T = T.comp U :=
    leftTranslation_convolutionOperator m (pointSeparatingKernel g) a
  have hUTinv :
      (leftTranslation m a⁻¹).comp T =
        T.comp (leftTranslation m a⁻¹) :=
    leftTranslation_convolutionOperator m (pointSeparatingKernel g) a⁻¹
  have hadj := congrArg ContinuousLinearMap.adjoint hUTinv
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp,
    leftTranslation_adjoint] at hadj
  have hinvinv : (a⁻¹)⁻¹ = a := by group
  rw [hinvinv] at hadj
  have hUadj :
      U.comp (ContinuousLinearMap.adjoint T) =
        (ContinuousLinearMap.adjoint T).comp U := hadj.symm
  simp only [separatingPositiveOperator,
    ContinuousLinearMap.star_eq_adjoint]
  change U.comp ((ContinuousLinearMap.adjoint T).comp T) =
    ((ContinuousLinearMap.adjoint T).comp T).comp U
  calc
    U.comp ((ContinuousLinearMap.adjoint T).comp T) =
        (U.comp (ContinuousLinearMap.adjoint T)).comp T := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = ((ContinuousLinearMap.adjoint T).comp U).comp T := by rw [hUadj]
    _ = (ContinuousLinearMap.adjoint T).comp (U.comp T) := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = (ContinuousLinearMap.adjoint T).comp (T.comp U) := by rw [hUT]
    _ = ((ContinuousLinearMap.adjoint T).comp T).comp U := by
      rw [ContinuousLinearMap.comp_assoc]

set_option maxHeartbeats 1200000 in
lemma exists_translation_eigenvector
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    {g : G} (hg : g ≠ 1) :
    ∃ μ : ℂ, μ ≠ 0 ∧ ∃ w : Lp ℂ 2 m, w ≠ 0 ∧
      separatingPositiveOperator m g w = μ • w ∧
      ∃ c : G → ℂ, ∀ a, leftTranslation m a w = c a • w := by
  let A := separatingPositiveOperator m g
  obtain ⟨μ, hμ, hAμ⟩ :=
    exists_nonzero_eigenvalue_of_compact_symmetric A
      (separatingPositiveOperator_compact m g)
      (separatingPositiveOperator_symmetric m g)
      (separatingPositiveOperator_ne_zero m hg)
  let V : Submodule ℂ (Lp ℂ 2 m) :=
    Module.End.eigenspace A.toLinearMap μ
  letI : FiniteDimensional ℂ V :=
    finiteDimensional_eigenspace_of_compact A
      (separatingPositiveOperator_compact m g) μ hμ
  letI : Nontrivial V :=
    Submodule.nontrivial_iff_ne_bot.mpr hAμ
  have hUinv (a : G) :
      ∀ v ∈ V, (leftTranslation m a).toLinearMap v ∈ V := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    change separatingPositiveOperator m g v = μ • v at hv
    change separatingPositiveOperator m g (leftTranslation m a v) =
      μ • leftTranslation m a v
    have hcomm := separatingPositiveOperator_commutes m g a
    have happ := congrArg
      (fun T : Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m ↦ T v) hcomm
    simp only [ContinuousLinearMap.comp_apply] at happ
    calc
      A (leftTranslation m a v) =
          leftTranslation m a (A v) := happ.symm
      _ = μ • leftTranslation m a v := by
        change leftTranslation m a
          (separatingPositiveOperator m g v) =
          μ • leftTranslation m a v
        rw [hv, map_smul]
  have hSinv (i : G ⊕ G) :
      ∀ v ∈ V, (symmetricTranslation m i).toLinearMap v ∈ V := by
    intro v hv
    cases i with
    | inl a =>
        exact V.add_mem (hUinv a v hv) (hUinv a⁻¹ v hv)
    | inr a =>
        exact V.smul_mem Complex.I
          (V.sub_mem (hUinv a v hv) (hUinv a⁻¹ v hv))
  let S : G ⊕ G → Module.End ℂ V :=
    fun i ↦ (symmetricTranslation m i).toLinearMap.restrict (hSinv i)
  have hSsym (i : G ⊕ G) : (S i).IsSymmetric := by
    exact (symmetricTranslation_symmetric m i).restrict_invariant (hSinv i)
  have hScomm : Pairwise fun i j ↦ Commute (S i) (S j) := by
    intro i j hij
    rw [Commute]
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have hc := (symmetricTranslation_commute m hij).eq
    exact congrArg
      (fun T : Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m ↦ T v.1) hc
  obtain ⟨α, v, hv0, hv⟩ :=
    exists_common_eigenvector_of_commuting_symmetric S hScomm hSsym
  let w : Lp ℂ 2 m := v.1
  have hw0 : w ≠ 0 := by
    intro hw
    apply hv0
    exact Subtype.ext hw
  have hwA : A w = μ • w :=
    Module.End.mem_eigenspace_iff.mp v.property
  let c : G → ℂ := fun a ↦
    (2 : ℂ)⁻¹ * (α (Sum.inl a) - Complex.I * α (Sum.inr a))
  have hwc (a : G) : leftTranslation m a w = c a • w := by
    have hre := congrArg Subtype.val (hv (Sum.inl a))
    have him := congrArg Subtype.val (hv (Sum.inr a))
    change leftTranslation m a w + leftTranslation m a⁻¹ w =
      α (Sum.inl a) • w at hre
    change Complex.I •
        (leftTranslation m a w - leftTranslation m a⁻¹ w) =
      α (Sum.inr a) • w at him
    have him' :
        leftTranslation m a w - leftTranslation m a⁻¹ w =
          (-Complex.I * α (Sum.inr a)) • w := by
      calc
        leftTranslation m a w - leftTranslation m a⁻¹ w =
            (-Complex.I) •
              (Complex.I •
                (leftTranslation m a w - leftTranslation m a⁻¹ w)) := by
                  simp only [smul_smul]
                  norm_num
        _ = (-Complex.I) • (α (Sum.inr a) • w) := by rw [him]
        _ = (-Complex.I * α (Sum.inr a)) • w := by rw [smul_smul]
    dsimp only [c]
    let u := leftTranslation m a w
    let q := leftTranslation m a⁻¹ w
    have hsum : (u + q) + (u - q) = (2 : ℂ) • u := by
      module
    calc
      u = (2 : ℂ)⁻¹ • ((2 : ℂ) • u) := by
        simp [smul_smul]
      _ = (2 : ℂ)⁻¹ • ((u + q) + (u - q)) := by rw [hsum]
      _ = (2 : ℂ)⁻¹ •
          (α (Sum.inl a) • w +
            (-Complex.I * α (Sum.inr a)) • w) := by
        rw [show u + q = α (Sum.inl a) • w from hre,
          show u - q = (-Complex.I * α (Sum.inr a)) • w from him']
      _ = ((2 : ℂ)⁻¹ *
          (α (Sum.inl a) - Complex.I * α (Sum.inr a))) • w := by
        simp only [smul_add, smul_smul]
        rw [← add_smul]
        congr 1
        ring
  exact ⟨μ, hμ, w, hw0, hwA, c, hwc⟩

lemma continuous_leftTranslation
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (F : Lp ℂ 2 m) :
    Continuous fun a : G ↦ leftTranslation m a F := by
  let φ : G → C(G, G) := fun a ↦
    { toFun := fun x ↦ a * x
      continuous_toFun := continuous_const.mul continuous_id }
  have hφ : Continuous φ := by
    let Φ : C(G × G, G) :=
      { toFun := fun p ↦ p.1 * p.2
        continuous_toFun := by fun_prop }
    have hφeq : φ = ContinuousMap.curry Φ := rfl
    rw [hφeq]
    exact (ContinuousMap.curry Φ).continuous
  have hcont := Continuous.compMeasurePreservingLp
    (μ := m) (ν := m) (p := (2 : ENNReal))
    (f := fun _ : G ↦ F) (g := φ)
    continuous_const hφ
    (fun a ↦ measurePreserving_mul_left m a) (by norm_num)
  simpa only [leftTranslation, φ,
    LinearIsometry.coe_toContinuousLinearMap] using hcont

/-- The scalar recovered continuously from a common translation
eigenvector. -/
noncomputable def translationEigenCoefficient
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (w : Lp ℂ 2 m) (a : G) : ℂ :=
  @inner ℂ (Lp ℂ 2 m) _ w (leftTranslation m a w) /
    @inner ℂ (Lp ℂ 2 m) _ w w

lemma continuous_translationEigenCoefficient
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (w : Lp ℂ 2 m) :
    Continuous (translationEigenCoefficient m w) := by
  apply Continuous.div_const
  exact continuous_const.inner (continuous_leftTranslation m w)

lemma translationEigenCoefficient_eq
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    {w : Lp ℂ 2 m} (hw : w ≠ 0) {a : G} {z : ℂ}
    (hz : leftTranslation m a w = z • w) :
    translationEigenCoefficient m w a = z := by
  rw [translationEigenCoefficient, hz, inner_smul_right]
  exact div_eq_iff (inner_self_ne_zero.mpr hw) |>.2 rfl

lemma translationEigenCoefficient_eigen
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    {w : Lp ℂ 2 m} (hw : w ≠ 0)
    (hcommon : ∃ c : G → ℂ, ∀ a, leftTranslation m a w = c a • w) :
    ∀ a, leftTranslation m a w =
      translationEigenCoefficient m w a • w := by
  obtain ⟨c, hc⟩ := hcommon
  intro a
  rw [translationEigenCoefficient_eq m hw (hc a)]
  exact hc a

noncomputable def translationEigenCharacter
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (w : Lp ℂ 2 m) : G → ℂ :=
  translationEigenCoefficient m w

noncomputable def translationEigenCharacter_spec
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    {w : Lp ℂ 2 m} (hw : w ≠ 0)
    (hcommon : ∃ c : G → ℂ, ∀ a, leftTranslation m a w = c a • w) :
    Chapter02.ContinuousMultiplicativeCircleCharacter G := by
  let χ : G → ℂ := translationEigenCharacter m w
  have heig : ∀ a, leftTranslation m a w = χ a • w :=
    translationEigenCoefficient_eigen m hw hcommon
  have hcancel : Function.Injective fun z : ℂ ↦ z • w :=
    smul_left_injective ℂ hw
  refine
    { toFun := χ
      map_one := ?_
      map_mul := ?_
      continuous := continuous_translationEigenCoefficient m w
      unit_norm := ?_ }
  · apply hcancel
    change χ 1 • w = (1 : ℂ) • w
    rw [← heig 1, leftTranslation_one]
    simp
  · intro a b
    apply hcancel
    change χ (a * b) • w = (χ a * χ b) • w
    rw [← heig (a * b)]
    have hmul := leftTranslation_mul_clm m a b
    have happ := congrArg
      (fun U : Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m ↦ U w) hmul
    rw [show leftTranslation m (a * b) w =
        leftTranslation m b (leftTranslation m a w) by
      simpa only [ContinuousLinearMap.comp_apply] using happ]
    rw [heig a, map_smul, heig b, smul_smul]
  · intro a
    have hnorm := leftTranslation_norm m a w
    rw [heig a, norm_smul] at hnorm
    nlinarith [norm_pos_iff.mpr hw]

theorem exists_character_ne_one
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    {g : G} (hg : g ≠ 1) :
    ∃ χ : Chapter02.ContinuousMultiplicativeCircleCharacter G,
      χ.toFun g ≠ 1 := by
  obtain ⟨μ, hμ, w, hw0, hwA, c, hwc⟩ :=
    exists_translation_eigenvector m hg
  let hcommon :
      ∃ c : G → ℂ, ∀ a, leftTranslation m a w = c a • w :=
    ⟨c, hwc⟩
  let χ := translationEigenCharacter_spec m hw0 hcommon
  refine ⟨χ, ?_⟩
  intro hχg
  have heig :=
    translationEigenCoefficient_eigen m hw0 hcommon
  have hwg : leftTranslation m g w = w := by
    rw [heig g]
    change χ.toFun g • w = w
    rw [hχg, one_smul]
  let K := convolutionOperator m (distanceFromOne (G := G))
  let T := separatingOperator m g
  have hfactor := congrArg
    (fun S : Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m ↦ S w)
    (separatingOperator_factor m g)
  have hcommK := leftTranslation_convolutionOperator
    m (distanceFromOne (G := G)) g
  have hcommKw := congrArg
    (fun S : Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m ↦ S w) hcommK
  have hTw : T w = 0 := by
    calc
      T w = leftTranslation m g (K w) - K w := by
        simpa only [T, K, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.sub_apply] using hfactor
      _ = K (leftTranslation m g w) - K w := by
        rw [show leftTranslation m g (K w) =
            K (leftTranslation m g w) by
          simpa only [K, ContinuousLinearMap.comp_apply] using hcommKw]
      _ = K w - K w := by rw [hwg]
      _ = 0 := sub_self _
  have hAw0 : separatingPositiveOperator m g w = 0 := by
    change star (separatingOperator m g)
      (separatingOperator m g w) = 0
    rw [hTw, map_zero]
  have hmuw0 : μ • w = 0 := by
    calc
      μ • w = separatingPositiveOperator m g w := hwA.symm
      _ = 0 := hAw0
  exact (smul_ne_zero hμ hw0) hmuw0

theorem characters_separate_points
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure] :
    ∀ x y : G, x ≠ y →
      ∃ χ : Chapter02.ContinuousMultiplicativeCircleCharacter G,
        χ.toFun x ≠ χ.toFun y := by
  intro x y hxy
  have hg : x * y⁻¹ ≠ 1 := by
    intro h
    apply hxy
    calc
      x = (x * y⁻¹) * y := by group
      _ = y := by rw [h, one_mul]
  obtain ⟨χ, hχ⟩ := exists_character_ne_one m hg
  refine ⟨χ, ?_⟩
  intro hxyχ
  have hy0 : χ.toFun y ≠ 0 := by
    intro hy
    have := χ.unit_norm y
    rw [hy, norm_zero] at this
    norm_num at this
  have hinv : χ.toFun y⁻¹ = (χ.toFun y)⁻¹ := by
    apply (mul_right_cancel₀ hy0)
    calc
      χ.toFun y⁻¹ * χ.toFun y = χ.toFun (y⁻¹ * y) :=
        (χ.map_mul y⁻¹ y).symm
      _ = χ.toFun 1 := by
        congr 1
        group
      _ = 1 := χ.map_one
      _ = (χ.toFun y)⁻¹ * χ.toFun y :=
        (inv_mul_cancel₀ hy0).symm
  apply hχ
  rw [χ.map_mul, hxyχ, hinv, mul_inv_cancel₀ hy0]

theorem character_span_dense
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure] :
    Dense
      (CompactAbelianPeterWeyl.lpCharacterSpan m :
        Set (Lp ℂ 2 m)) :=
  CompactAbelianPeterWeyl.character_span_dense_of_separates
    m (characters_separate_points m)

end HaarTranslations

end Chapter02.PontryaginSeparation
