import Chapter02.HostKra.HostKraCubeSeminormDynamics

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraRelativeJoiningComplex

universe u

open HostKraRelativeJoining
open HostKraCubeFactors HostKraStandardRelativeJoining

attribute [local instance]
  Lp.simpleFunc.smul
  Lp.simpleFunc.module
  Lp.simpleFunc.isBoundedSMul
  Lp.simpleFunc.normedSpace

/-- The real invariant conditional probability of a measurable set,
embedded canonically into complex `L²`. -/
def invariantIndicatorComplexLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) : Lp ℂ 2 M.μ :=
  ((Lp.memLp (invariantIndicatorLp M hM A hA)).ofReal).toLp
    (fun x ↦ Complex.ofReal (invariantIndicatorLp M hM A hA x))

lemma invariantIndicatorComplexLp_coe
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    (fun x ↦ invariantIndicatorComplexLp M hM A hA x) =ᵐ[M.μ]
      fun x ↦ Complex.ofReal (invariantIndicatorLp M hM A hA x) := by
  exact ((Lp.memLp (invariantIndicatorLp M hM A hA)).ofReal).coeFn_toLp

/-- On an indicator, the complex invariant mean is exactly the
complexification of the real conditional probability used to construct the
relative joining. -/
theorem invariantMeanLp_indicatorComplex
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    HostKraRelativeMean.invariantMeanLp M hM
        (CorrelationMean.indicatorComplex A)
        (CorrelationMean.indicatorComplex_memLp M hM A hA 2) =
      invariantIndicatorComplexLp M hM A hA := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let mI := invariantMeasurableSpace M
  let r : M.X → ℝ := indicatorReal A
  have hrint : Integrable r M.μ :=
    (indicatorReal_memLp M hM A hA).integrable (by norm_num)
  have hcomm :
      Complex.ofRealCLM ∘ condExp mI M.μ r =ᵐ[M.μ]
        condExp mI M.μ (Complex.ofRealCLM ∘ r) :=
    Complex.ofRealCLM.comp_condExp_comm hrint
  have hraw :
      (Complex.ofRealCLM ∘ r) =
        CorrelationMean.indicatorComplex A := by
    funext x
    by_cases hx : x ∈ A <;>
      simp [r, indicatorReal, CorrelationMean.indicatorComplex,
        Set.indicator, hx]
  have hleft :=
    HostKraCubeSeminormDynamics.invariantMeanLp_coe_condExp
      M hM (CorrelationMean.indicatorComplex A)
      (CorrelationMean.indicatorComplex_memLp M hM A hA 2)
  have hright := invariantIndicatorComplexLp_coe M hM A hA
  have hreal := invariantIndicatorLp_coe M hM A hA
  apply Lp.ext
  filter_upwards [hleft, hright, hreal, hcomm] with x hl hr hri hc
  rw [hl, hr, hri]
  simpa only [mI, r, hraw, Function.comp_apply] using hc.symm

/-- The relative-joining inner product identity on measurable indicator
rectangles, in the complex `L²` spaces used by the cube recursion. -/
theorem inner_pullback_indicators
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    let IA := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
    let IB := MultipleKhintchineCharacteristic.indicatorLp M hM B hB
    @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
        (Lp.compMeasurePreserving Prod.snd
          (relativeJoining_snd_measurePreserving M hM) IB)
        (Lp.compMeasurePreserving Prod.fst
          (relativeJoining_fst_measurePreserving M hM) IA) =
      @inner ℂ (Lp ℂ 2 M.μ) _
        (invariantIndicatorComplexLp M hM B hB)
        (invariantIndicatorComplexLp M hM A hA) := by
  dsimp only
  let IA := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  let IB := MultipleKhintchineCharacteristic.indicatorLp M hM B hB
  let ν := relativeJoiningMeasure M hM
  have hIA :=
    MultipleKhintchineCharacteristic.indicatorLp_coe M hM A hA
  have hIB :=
    MultipleKhintchineCharacteristic.indicatorLp_coe M hM B hB
  have hfst :=
    Lp.coeFn_compMeasurePreserving IA
      (relativeJoining_fst_measurePreserving M hM)
  have hsnd :=
    Lp.coeFn_compMeasurePreserving IB
      (relativeJoining_snd_measurePreserving M hM)
  have hleft :
      @inner ℂ (Lp ℂ 2 ν) _
          (Lp.compMeasurePreserving Prod.snd
            (relativeJoining_snd_measurePreserving M hM) IB)
          (Lp.compMeasurePreserving Prod.fst
            (relativeJoining_fst_measurePreserving M hM) IA) =
        ((ν (A ×ˢ B)).toReal : ℂ) := by
    rw [L2.inner_def]
    calc
      (∫ p,
          (Lp.compMeasurePreserving Prod.fst
            (relativeJoining_fst_measurePreserving M hM) IA) p *
          star
            ((Lp.compMeasurePreserving Prod.snd
              (relativeJoining_snd_measurePreserving M hM) IB) p) ∂ν) =
          ∫ p, (A ×ˢ B).indicator (fun _ ↦ (1 : ℂ)) p ∂ν := by
            apply integral_congr_ae
            filter_upwards [hfst, hsnd,
              (relativeJoining_fst_measurePreserving M hM).quasiMeasurePreserving.ae_eq hIA,
              (relativeJoining_snd_measurePreserving M hM).quasiMeasurePreserving.ae_eq hIB]
              with p hfp hsp hAp hBp
            rw [hfp, hsp, hAp, hBp]
            by_cases hpA : p.1 ∈ A <;> by_cases hpB : p.2 ∈ B <;>
              simp [CorrelationMean.indicatorComplex, Set.indicator,
                hpA, hpB]
      _ = ((ν (A ×ˢ B)).toReal : ℂ) := by
        rw [integral_indicator (hA.prod hB)]
        simp
        rfl
  have hright :
      @inner ℂ (Lp ℂ 2 M.μ) _
          (invariantIndicatorComplexLp M hM B hB)
          (invariantIndicatorComplexLp M hM A hA) =
        ((relativeRectangleMass M hM A B hA hB : ℝ) : ℂ) := by
    rw [L2.inner_def]
    have hAc := invariantIndicatorComplexLp_coe M hM A hA
    have hBc := invariantIndicatorComplexLp_coe M hM B hB
    have hABint : Integrable
        (fun x ↦ invariantIndicatorLp M hM A hA x *
          invariantIndicatorLp M hM B hB x) M.μ :=
      (Lp.memLp (invariantIndicatorLp M hM A hA)).integrable_mul
        (Lp.memLp (invariantIndicatorLp M hM B hB))
    calc
      (∫ x, invariantIndicatorComplexLp M hM A hA x *
          star (invariantIndicatorComplexLp M hM B hB x) ∂M.μ) =
          ∫ x, Complex.ofReal
            (invariantIndicatorLp M hM A hA x *
              invariantIndicatorLp M hM B hB x) ∂M.μ := by
            apply integral_congr_ae
            filter_upwards [hAc, hBc] with x hAx hBx
            rw [hAx, hBx]
            simp
      _ = Complex.ofReal
          (∫ x, invariantIndicatorLp M hM A hA x *
            invariantIndicatorLp M hM B hB x ∂M.μ) := by
            exact Complex.ofRealCLM.integral_comp_comm hABint
      _ = ((relativeRectangleMass M hM A B hA hB : ℝ) : ℂ) := by
        rw [relativeRectangleMass, L2.inner_def]
        apply congrArg Complex.ofReal
        apply integral_congr_ae
        filter_upwards with x
        simp only [RCLike.inner_apply, conj_trivial]
        exact mul_comm _ _
  rw [hleft, hright]
  exact congrArg Complex.ofReal
    (relativeJoiningMeasure_apply_prod_toReal M hM A B hA hB)

/-- Pullback to the first coordinate of the relative joining. -/
def relativeFstCLM
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 (relativeJoiningMeasure M hM) :=
  (Lp.compMeasurePreservingₗᵢ ℂ Prod.fst
    (relativeJoining_fst_measurePreserving M hM)).toContinuousLinearMap

/-- Pullback to the second coordinate of the relative joining. -/
def relativeSndCLM
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 (relativeJoiningMeasure M hM) :=
  (Lp.compMeasurePreservingₗᵢ ℂ Prod.snd
    (relativeJoining_snd_measurePreserving M hM)).toContinuousLinearMap

/-- Orthogonal projection onto the invariant Koopman subspace. -/
def invariantProjectionCLM
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ := by
  let D := MultipleKhintchineCharacteristic.KData M hM
  let S : Submodule ℂ (Lp ℂ 2 M.μ) :=
    LinearMap.eqLocus D.U (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)
  exact S.subtypeL.comp S.orthogonalProjection

lemma invariantProjectionCLM_indicator
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    invariantProjectionCLM M hM
        (MultipleKhintchineCharacteristic.indicatorLp M hM A hA) =
      invariantIndicatorComplexLp M hM A hA := by
  let hf := CorrelationMean.indicatorComplex_memLp M hM A hA 2
  have htoLp :
      hf.toLp (CorrelationMean.indicatorComplex A) =
        MultipleKhintchineCharacteristic.indicatorLp M hM A hA := rfl
  have hproj :=
    HostKraRelativeMean.invariantMeanLp_eq_fixedProjection
      M hM (CorrelationMean.indicatorComplex A) hf
  have hmean := invariantMeanLp_indicatorComplex M hM A hA
  rw [htoLp] at hproj
  exact hproj.symm.trans hmean

lemma simpleIndicatorConst_eq_smul_indicator
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) (hμA : M.μ A ≠ ⊤) (c : ℂ) :
    ((Lp.simpleFunc.indicatorConst
        (2 : ENNReal) hA hμA c :
        Lp.simpleFunc ℂ 2 M.μ) : Lp ℂ 2 M.μ) =
      c • MultipleKhintchineCharacteristic.indicatorLp M hM A hA := by
  letI : IsProbabilityMeasure M.μ := hM.1
  apply Lp.ext
  let ac : Lp.simpleFunc ℂ 2 M.μ :=
    Lp.simpleFunc.indicatorConst (2 : ENNReal) hA hμA c
  have haccoe :
      (fun x ↦ ((ac : Lp ℂ 2 M.μ) : M.X → ℂ) x) =ᵐ[M.μ]
        Lp.simpleFunc.toSimpleFunc ac := by
    filter_upwards [(Lp.simpleFunc.memLp ac).coeFn_toLp] with x hx
    have heq := congrArg
      (fun z : Lp.simpleFunc ℂ 2 M.μ ↦
        (((z : Lp ℂ 2 M.μ) : M.X → ℂ) x))
      (Lp.simpleFunc.toLp_toSimpleFunc ac)
    exact heq.symm.trans hx
  have hacind := Lp.simpleFunc.toSimpleFunc_indicatorConst
    (p := (2 : ENNReal)) hA hμA c
  filter_upwards [
    haccoe, hacind,
    Lp.coeFn_smul c
      (MultipleKhintchineCharacteristic.indicatorLp M hM A hA),
    MultipleKhintchineCharacteristic.indicatorLp_coe M hM A hA]
      with x hc hci hsmul hI
  change ((ac : Lp ℂ 2 M.μ) : M.X → ℂ) x =
    ((c • MultipleKhintchineCharacteristic.indicatorLp M hM A hA :
      Lp ℂ 2 M.μ) : M.X → ℂ) x
  rw [hc, hci, hsmul]
  change
    (SimpleFunc.piecewise A hA
      (SimpleFunc.const M.X c) (SimpleFunc.const M.X 0)) x =
      c * ((MultipleKhintchineCharacteristic.indicatorLp M hM A hA :
        Lp ℂ 2 M.μ) : M.X → ℂ) x
  rw [hI]
  by_cases hx : x ∈ A <;>
    simp [CorrelationMean.indicatorComplex, Set.indicator, hx]

private theorem inner_pullback_simple
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (G F : Lp.simpleFunc ℂ 2 M.μ) :
    @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
        (relativeSndCLM M hM (G : Lp ℂ 2 M.μ))
        (relativeFstCLM M hM (F : Lp ℂ 2 M.μ)) =
      @inner ℂ (Lp ℂ 2 M.μ) _
        (invariantProjectionCLM M hM (G : Lp ℂ 2 M.μ))
        (invariantProjectionCLM M hM (F : Lp ℂ 2 M.μ)) := by
  induction G using Lp.simpleFunc.induction
      (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤) with
  | indicatorConst d hB hμB =>
      rename_i B
      induction F using Lp.simpleFunc.induction
          (by norm_num : (2 : ENNReal) ≠ 0)
          (by norm_num : (2 : ENNReal) ≠ ⊤) with
      | indicatorConst c hA hμA =>
          rename_i A
          rw [simpleIndicatorConst_eq_smul_indicator M hM B hB hμB.ne d,
            simpleIndicatorConst_eq_smul_indicator M hM A hA hμA.ne c,
            map_smul, map_smul, map_smul, map_smul,
            inner_smul_left, inner_smul_right,
            inner_smul_left, inner_smul_right,
            invariantProjectionCLM_indicator M hM B hB,
            invariantProjectionCLM_indicator M hM A hA]
          have hbase := inner_pullback_indicators M hM A B hA hB
          simpa only [relativeSndCLM, relativeFstCLM,
            LinearIsometry.coe_toContinuousLinearMap] using
            congrArg (fun z : ℂ ↦ star d * (c * z)) hbase
      | add hf hg hdis hfEq hgEq =>
          change
            @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
                (relativeSndCLM M hM
                  ((Lp.simpleFunc.indicatorConst
                    (2 : ENNReal) hB hμB.ne d :
                    Lp.simpleFunc ℂ 2 M.μ) : Lp ℂ 2 M.μ))
                (relativeFstCLM M hM
                  ((Lp.simpleFunc.toLp _ hf : Lp ℂ 2 M.μ) +
                    (Lp.simpleFunc.toLp _ hg : Lp ℂ 2 M.μ))) =
              @inner ℂ (Lp ℂ 2 M.μ) _
                (invariantProjectionCLM M hM
                  ((Lp.simpleFunc.indicatorConst
                    (2 : ENNReal) hB hμB.ne d :
                    Lp.simpleFunc ℂ 2 M.μ) : Lp ℂ 2 M.μ))
                (invariantProjectionCLM M hM
                  ((Lp.simpleFunc.toLp _ hf : Lp ℂ 2 M.μ) +
                    (Lp.simpleFunc.toLp _ hg : Lp ℂ 2 M.μ)))
          rw [map_add, map_add, inner_add_right, inner_add_right, hfEq, hgEq]
  | add hf hg hdis hfEq hgEq =>
      change
        @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
            (relativeSndCLM M hM
              ((Lp.simpleFunc.toLp _ hf : Lp ℂ 2 M.μ) +
                (Lp.simpleFunc.toLp _ hg : Lp ℂ 2 M.μ)))
            (relativeFstCLM M hM (F : Lp ℂ 2 M.μ)) =
          @inner ℂ (Lp ℂ 2 M.μ) _
            (invariantProjectionCLM M hM
              ((Lp.simpleFunc.toLp _ hf : Lp ℂ 2 M.μ) +
                (Lp.simpleFunc.toLp _ hg : Lp ℂ 2 M.μ)))
            (invariantProjectionCLM M hM (F : Lp ℂ 2 M.μ))
      rw [map_add, map_add, inner_add_left, inner_add_left, hfEq, hgEq]

/-- Full `L²` relative-independence identity: the pairing of the two
coordinate pullbacks equals the pairing of the two invariant projections. -/
theorem inner_pullback_eq_invariantProjection
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (G F : Lp ℂ 2 M.μ) :
    @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
        (relativeSndCLM M hM G) (relativeFstCLM M hM F) =
      @inner ℂ (Lp ℂ 2 M.μ) _
        (invariantProjectionCLM M hM G)
        (invariantProjectionCLM M hM F) := by
  let e : Lp.simpleFunc ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ :=
    Lp.simpleFunc.coeToLp M.X ℂ ℂ
  have hdense : DenseRange e := by
    simpa [e, Lp.simpleFunc.coeToLp] using
      (Lp.simpleFunc.denseRange
        (E := ℂ) (p := (2 : ENNReal)) (μ := M.μ) (by norm_num))
  have hfirst (Gs : Lp.simpleFunc ℂ 2 M.μ) (F : Lp ℂ 2 M.μ) :
      @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
          (relativeSndCLM M hM (Gs : Lp ℂ 2 M.μ))
          (relativeFstCLM M hM F) =
        @inner ℂ (Lp ℂ 2 M.μ) _
          (invariantProjectionCLM M hM (Gs : Lp ℂ 2 M.μ))
          (invariantProjectionCLM M hM F) := by
    refine hdense.induction_on
      (p := fun F ↦
        @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
            (relativeSndCLM M hM (Gs : Lp ℂ 2 M.μ))
            (relativeFstCLM M hM F) =
          @inner ℂ (Lp ℂ 2 M.μ) _
            (invariantProjectionCLM M hM (Gs : Lp ℂ 2 M.μ))
            (invariantProjectionCLM M hM F))
      F ?_ ?_
    · exact isClosed_eq
        (continuous_const.inner (relativeFstCLM M hM).continuous)
        (continuous_const.inner (invariantProjectionCLM M hM).continuous)
    · intro Fs
      exact inner_pullback_simple M hM Gs Fs
  refine hdense.induction_on
    (p := fun G ↦
      @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
          (relativeSndCLM M hM G) (relativeFstCLM M hM F) =
        @inner ℂ (Lp ℂ 2 M.μ) _
          (invariantProjectionCLM M hM G)
          (invariantProjectionCLM M hM F))
    G ?_ ?_
  · exact isClosed_eq
      ((relativeSndCLM M hM).continuous.inner continuous_const)
      ((invariantProjectionCLM M hM).continuous.inner continuous_const)
  · intro Gs
    exact hfirst Gs F

/-- Diagonal specialization of relative independence: the relative-joining
pairing of the two coordinate copies of an `L²` function is exactly its
invariant-projection energy. -/
theorem inner_pullback_self_eq_invariantEnergy
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
        (relativeSndCLM M hM (hf.toLp f))
        (relativeFstCLM M hM (hf.toLp f)) =
      ((HostKraCubeSeminorm.invariantEnergy M hM f hf : ℝ) : ℂ) := by
  rw [inner_pullback_eq_invariantProjection M hM]
  have hmean :
      invariantProjectionCLM M hM (hf.toLp f) =
        HostKraRelativeMean.invariantMeanLp M hM f hf := by
    simpa only [invariantProjectionCLM, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply] using
      (HostKraRelativeMean.invariantMeanLp_eq_fixedProjection
        M hM f hf).symm
  rw [hmean]
  simpa only [HostKraCubeSeminorm.invariantEnergy,
    Complex.ofReal_pow] using
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
      (HostKraRelativeMean.invariantMeanLp M hM f hf))

/-- The integral of one Host--Kra cube derivative against the relative
joining is the invariant energy of the original function. -/
theorem integral_cubeLift_eq_invariantEnergy
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    ∫ p, HostKraCubeSeminorm.cubeLift f p
        ∂(relativeJoiningMeasure M hM) =
      ((HostKraCubeSeminorm.invariantEnergy M hM f
        (by
          letI : IsProbabilityMeasure M.μ := hM.1
          exact hf.mono_exponent (by simp)) : ℝ) : ℂ) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let hf2 : M.lpMember 2 f := hf.mono_exponent (by simp)
  let F : Lp ℂ 2 M.μ := hf2.toLp f
  let ν := relativeJoiningMeasure M hM
  let PF :=
    Lp.compMeasurePreserving Prod.fst
      (relativeJoining_fst_measurePreserving M hM) F
  let PS :=
    Lp.compMeasurePreserving Prod.snd
      (relativeJoining_snd_measurePreserving M hM) F
  have hfst := Lp.coeFn_compMeasurePreserving F
    (relativeJoining_fst_measurePreserving M hM)
  have hsnd := Lp.coeFn_compMeasurePreserving F
    (relativeJoining_snd_measurePreserving M hM)
  have hfcoe := hf2.coeFn_toLp
  have hfcoeFst :=
    (relativeJoining_fst_measurePreserving M hM).quasiMeasurePreserving.ae_eq
      hfcoe
  have hfcoeSnd :=
    (relativeJoining_snd_measurePreserving M hM).quasiMeasurePreserving.ae_eq
      hfcoe
  calc
    (∫ p, HostKraCubeSeminorm.cubeLift f p ∂ν) =
        ∫ p, PF p * star (PS p) ∂ν := by
          apply integral_congr_ae
          filter_upwards [hfst, hsnd, hfcoeFst, hfcoeSnd]
            with p hpF hpS hpf hps
          rw [hpF, hpS, hpf, hps]
          rfl
    _ = @inner ℂ (Lp ℂ 2 ν) _ PS PF := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards with p
      simp only [RCLike.inner_apply]
      rfl
    _ = ((HostKraCubeSeminorm.invariantEnergy M hM f hf2 : ℝ) : ℂ) := by
      simpa only [ν, PF, PS, F, relativeSndCLM, relativeFstCLM,
        LinearIsometry.coe_toContinuousLinearMap] using
        (inner_pullback_self_eq_invariantEnergy M hM f hf2)

/-- If the invariant projection of an `L²` function vanishes, then its
ordinary integral vanishes.  The key point is that the constant-one vector
belongs to the Koopman fixed subspace. -/
theorem integral_eq_zero_of_invariantMeanLp_eq_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f)
    (hzero : HostKraRelativeMean.invariantMeanLp M hM f hf = 0) :
    ∫ x, f x ∂M.μ = 0 := by
  let D := MultipleKhintchineCharacteristic.KData M hM
  let S : Submodule ℂ (Lp ℂ 2 M.μ) :=
    LinearMap.eqLocus D.U (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)
  let F : Lp ℂ 2 M.μ := hf.toLp f
  have hmean :
      HostKraRelativeMean.invariantMeanLp M hM f hf =
        (S.orthogonalProjection F).val := by
    simpa only [D, S, F] using
      (HostKraRelativeMean.invariantMeanLp_eq_fixedProjection M hM f hf)
  have hprojZero : (S.orthogonalProjection F).val = 0 := by
    rw [← hmean]
    exact hzero
  have horth : F - (S.orthogonalProjection F).val ∈ Sᗮ :=
    S.sub_starProjection_mem_orthogonal F
  have hForth : F ∈ Sᗮ := by
    simpa only [hprojZero, sub_zero] using horth
  have honeFixed :
      D.U (CorrelationMean.oneLp M hM) =
        CorrelationMean.oneLp M hM := by
    apply Lp.ext
    have hiter :=
      MultipleKhintchineKronecker.koopmanData_iter_ae
        M hM 1 (CorrelationMean.oneLp M hM)
    have hcoeShift :=
      hM.2.quasiMeasurePreserving.ae_eq_comp
        (WeakSpectrum.oneLp_coe M hM)
    filter_upwards [hiter, hcoeShift, WeakSpectrum.oneLp_coe M hM]
      with x hx hshift hone
    simp only [Function.iterate_one] at hx
    change
      (show Lp ℂ 2 M.μ from
        D.U (CorrelationMean.oneLp M hM)) x =
        CorrelationMean.oneLp M hM x
    rw [hx]
    exact hshift.trans hone.symm
  have honeMem : CorrelationMean.oneLp M hM ∈ S := by
    change D.U (CorrelationMean.oneLp M hM) =
      (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)
        (CorrelationMean.oneLp M hM)
    simpa only [ContinuousLinearMap.one_apply] using honeFixed
  calc
    (∫ x, f x ∂M.μ) = ∫ x, F x ∂M.μ :=
      (integral_congr_ae hf.coeFn_toLp).symm
    _ = @inner ℂ (Lp ℂ 2 M.μ) _
        (CorrelationMean.oneLp M hM) F :=
      CorrelationMean.integral_eq_inner_oneLp M hM F
    _ = 0 := S.inner_right_of_mem_orthogonal honeMem hForth

/-- One step of zero monotonicity in the Host--Kra recursion. -/
theorem invariantEnergy_eq_zero_of_cubeLiftOne_invariantMean_eq_zero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero :
      HostKraRelativeMean.invariantMeanLp
        (relativeCubeSystemOne M hM)
        (relativeCubeSystemOne_mps M hM)
        (HostKraCubeSeminorm.cubeLiftOne M hM f)
        (HostKraCubeSeminorm.cubeLiftOne_memLp_two M hM f hf) = 0) :
    HostKraCubeSeminorm.invariantEnergy M hM f
      (by
        letI : IsProbabilityMeasure M.μ := hM.1
        exact hf.mono_exponent (by simp)) = 0 := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let hf2 : M.lpMember 2 f := hf.mono_exponent (by simp)
  have hint :
      ∫ p, HostKraCubeSeminorm.cubeLiftOne M hM f p
          ∂(relativeCubeSystemOne M hM).μ = 0 :=
    integral_eq_zero_of_invariantMeanLp_eq_zero
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM)
      (HostKraCubeSeminorm.cubeLiftOne M hM f)
      (HostKraCubeSeminorm.cubeLiftOne_memLp_two M hM f hf)
      hzero
  have hrec :=
    integral_cubeLift_eq_invariantEnergy M hM f hf
  have hcomplex :
      ((HostKraCubeSeminorm.invariantEnergy M hM f hf2 : ℝ) : ℂ) = 0 := by
    exact hrec.symm.trans (by
      simpa only [HostKraCubeSeminorm.cubeLiftOne,
        relativeCubeSystemOne, relativeJoiningSystem] using hint)
  exact_mod_cast hcomplex

/-- Vanishing of the `U³` power forces vanishing of the preceding `U²`
power. -/
theorem hostKraU2Power_eq_zero_of_hasZeroHostKraU3
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : HostKraCubeSeminorm.HasZeroHostKraU3 M hM f hf) :
    HostKraCubeSeminorm.hostKraU2Power M hM f hf = 0 := by
  unfold HostKraCubeSeminorm.hostKraU2Power
  apply invariantEnergy_eq_zero_of_cubeLiftOne_invariantMean_eq_zero
    (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM)
    (HostKraCubeSeminorm.cubeLiftOne M hM f)
    (HostKraCubeSeminorm.cubeLiftOne_memLp_top M hM f hf)
  exact
    (HostKraCubeSeminorm.hasZeroHostKraU3_iff_invariantMean
      M hM f hf).mp hzero

/-- Vanishing of the `U⁴` power forces vanishing of the preceding `U³`
power. -/
theorem hostKraU3Power_eq_zero_of_hasZeroHostKraU4
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : HostKraCubeSeminorm.HasZeroHostKraU4 M hM f hf) :
    HostKraCubeSeminorm.hostKraU3Power M hM f hf = 0 := by
  unfold HostKraCubeSeminorm.hostKraU3Power
  apply invariantEnergy_eq_zero_of_cubeLiftOne_invariantMean_eq_zero
    (relativeCubeSystemTwo M hM)
    (relativeCubeSystemTwo_mps M hM)
    (HostKraCubeSeminorm.cubeLiftTwo M hM f)
    (HostKraCubeSeminorm.cubeLiftTwo_memLp_top M hM f hf)
  exact
    (HostKraCubeSeminorm.hasZeroHostKraU4_iff_invariantMean
      M hM f hf).mp hzero

end Chapter02.HostKraRelativeJoiningComplex
