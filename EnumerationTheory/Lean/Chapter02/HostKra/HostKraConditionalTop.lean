import Chapter02.HostKra.HostKraDualFunction
import Chapter02.Ergodic.LpInterpolation

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraConditionalTop

universe u

open HostKraStandardRelativeJoining
open HostKraRelativeJoiningComplex
open HostKraCubeFactors
open HostKraDualFunction

/-- An essentially bounded complex function has a measurable representative
which is bounded at every point.  This local form keeps the Host--Kra
development independent of the later Chapter 4 `L∞` infrastructure. -/
lemma exists_bounded_measurable_representative
    {X : Type u} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℂ} (hf : MemLp f ⊤ μ) :
    ∃ g : X → ℂ, ∃ C : ℝ,
      0 ≤ C ∧ Measurable g ∧ f =ᵐ[μ] g ∧ (∀ x, ‖g x‖ ≤ C) := by
  have hess : eLpNormEssSup f μ < ⊤ := by
    simpa only [eLpNorm_exponent_top] using hf.2
  obtain ⟨C, hC⟩ :=
    eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hess
  let m : X → ℂ := hf.1.mk f
  have hmmeas : Measurable m := hf.1.measurable_mk
  have hfm : f =ᵐ[μ] m := hf.1.ae_eq_mk
  have hmC : ∀ᵐ x ∂μ, ‖m x‖₊ ≤ C := by
    filter_upwards [hC, hfm] with x hx hxeq
    rw [← hxeq]
    exact hx
  let g : X → ℂ := fun x => if ‖m x‖₊ ≤ C then m x else 0
  have hgmeas : Measurable g :=
    Measurable.ite
      (measurableSet_le hmmeas.nnnorm measurable_const)
      hmmeas measurable_const
  have hfg : f =ᵐ[μ] g := by
    filter_upwards [hfm, hmC] with x hxeq hxC
    simp [g, hxC, hxeq]
  refine ⟨g, C, C.coe_nonneg, hgmeas, hfg, ?_⟩
  intro x
  by_cases hx : ‖m x‖₊ ≤ C
  · simp only [g, hx, if_true]
    exact_mod_cast hx
  · simp [g, hx]

/-- Conditional expectation is an `L∞` contraction at the qualitative
level needed for bounded Host--Kra dual functions. -/
theorem condExp_memLp_top
    {X : Type u} {m m₀ : MeasurableSpace X}
    (μ : Measure X) [IsFiniteMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (f : X → ℂ) (hf : MemLp f ⊤ μ) :
    MemLp (condExp m μ f) ⊤ μ := by
  letI : MeasurableSpace X := m₀
  obtain ⟨g, C, hC, hgmeas, hfg, hgC⟩ :=
    exists_bounded_measurable_representative μ hf
  have hgTop : MemLp g ⊤ μ :=
    memLp_top_of_bound hgmeas.aestronglyMeasurable C
      (Filter.Eventually.of_forall hgC)
  have hgint : Integrable g μ :=
    hgTop.integrable (by simp)
  have hnorm :=
    LpInterpolation.complex_norm_condExp_le μ hm g hgint
  have hmono := condExp_mono
    (m := m) hgint.norm (integrable_const C)
    (Filter.Eventually.of_forall hgC)
  have hconst := condExp_of_stronglyMeasurable hm
    (stronglyMeasurable_const :
      @StronglyMeasurable X ℝ _ m (fun _ => C))
    (integrable_const (μ := μ) C)
  have hbound : ∀ᵐ x ∂μ, ‖condExp m μ f x‖ ≤ C := by
    filter_upwards [condExp_congr_ae (m := m) hfg, hnorm, hmono]
      with x hce hnormx hmonox
    rw [hce]
    exact hnormx.trans (by simpa only [hconst] using hmonox)
  exact memLp_top_of_bound
    (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable C hbound

private lemma relativeFst_comp_ae_eq_mk
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (D : Lp ℂ 2 M.μ) :
    let d : M.X → ℂ := (Lp.memLp D).1.mk (fun x => D x)
    (fun p : M.X × M.X => D p.1) =ᵐ[
      relativeJoiningMeasure M hM] d ∘ Prod.fst := by
  dsimp only
  exact
    (relativeJoining_fst_measurePreserving M hM)
      |>.quasiMeasurePreserving.ae_eq
        (Lp.memLp D).1.ae_eq_mk

/-- Pulling the first-coordinate Hilbert adjoint back to the relative
joining gives conditional expectation onto the first-coordinate
sigma-algebra. -/
theorem relativeFstConditionalCLM_comp_fst_ae_eq_condExp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : Lp ℂ 2 (relativeJoiningMeasure M hM)) :
    let mFst :=
      MeasurableSpace.comap (Prod.fst : M.X × M.X → M.X)
        M.measurableSpace
    (fun p =>
      relativeFstConditionalCLM M hM H p.1) =ᵐ[
        relativeJoiningMeasure M hM]
      condExp mFst (relativeJoiningMeasure M hM) (fun p => H p) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let mProd : MeasurableSpace (M.X × M.X) := inferInstance
  let ν : @Measure (M.X × M.X) mProd :=
    relativeJoiningMeasure M hM
  let mFst :=
    MeasurableSpace.comap (Prod.fst : M.X × M.X → M.X)
      M.measurableSpace
  have hmFst : mFst ≤ mProd := by
    exact Measurable.comap_le measurable_fst
  let D := relativeFstConditionalCLM M hM H
  have hHint : Integrable (fun p => H p) ν :=
    (Lp.memLp H).integrable (by norm_num)
  have hDint : Integrable (fun p : M.X × M.X => D p.1) ν := by
    have hbase : Integrable (fun x => D x) M.μ :=
      (Lp.memLp D).integrable (by norm_num)
    exact (relativeJoining_fst_measurePreserving M hM).integrable_comp
      (Lp.memLp D).1 |>.mpr hbase
  let d : M.X → ℂ := (Lp.memLp D).1.mk (fun x => D x)
  have hDae :
      (fun p : M.X × M.X => D p.1) =ᵐ[ν] d ∘ Prod.fst :=
    relativeFst_comp_ae_eq_mk M hM D
  have hDm :
      @AEStronglyMeasurable (M.X × M.X) ℂ _ mFst mProd
        (fun p => D p.1) ν := by
    have hd :
        @StronglyMeasurable M.X ℂ _ M.measurableSpace d :=
      (Lp.memLp D).1.stronglyMeasurable_mk
    have hfst :
        @Measurable (M.X × M.X) M.X mFst M.measurableSpace Prod.fst := by
      exact measurable_iff_comap_le.mpr le_rfl
    have hdcomp :
        @StronglyMeasurable (M.X × M.X) ℂ _ mFst (d ∘ Prod.fst) :=
      hd.comp_measurable hfst
    exact hdcomp.aestronglyMeasurable.congr hDae.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq
    (m := mFst) (m₀ := mProd)
    (μ := ν) (f := fun p => H p) (g := fun p => D p.1)
    hmFst
    hHint
  · intro s _hs _hfinite
    exact hDint.integrableOn
  · intro s hs _hfinite
    change ∃ t, MeasurableSet t ∧ Prod.fst ⁻¹' t = s at hs
    obtain ⟨A, hA, rfl⟩ := hs
    letI : MeasurableSpace (M.X × M.X) := mProd
    let I := MultipleKhintchineCharacteristic.indicatorLp M hM A hA
    have hinner := inner_relativeFstConditionalCLM M hM I H
    rw [L2.inner_def, L2.inner_def] at hinner
    have hI :=
      MultipleKhintchineCharacteristic.indicatorLp_coe M hM A hA
    have hIpull :=
      (relativeJoining_fst_measurePreserving M hM)
        |>.quasiMeasurePreserving.ae_eq hI
    have hV := relativeFstCLM_coe M hM I
    have hleft :
        ∫ p in Prod.fst ⁻¹' A, D p.1 ∂ν =
          ∫ x in A, D x ∂M.μ := by
      rw [← integral_indicator (hA.preimage measurable_fst),
        ← integral_indicator hA]
      change
        ∫ p, (A.indicator fun x => D x) p.1 ∂ν =
          ∫ x, A.indicator (fun x => D x) x ∂M.μ
      exact HilbertSchmidtInvariant.integral_comp_measurePreserving
        Prod.fst (relativeJoining_fst_measurePreserving M hM)
        (A.indicator fun x => D x)
        ((Lp.memLp D).1.indicator hA)
    have hbase :
        ∫ x in A, D x ∂M.μ =
          ∫ x, @inner ℂ ℂ _ (I x) (D x) ∂M.μ := by
      rw [← integral_indicator hA]
      apply integral_congr_ae
      filter_upwards [hI] with x hx
      simp only [RCLike.inner_apply]
      change I x = CorrelationMean.indicatorComplex A x at hx
      by_cases hxin : x ∈ A
      · rw [hx]
        simp [CorrelationMean.indicatorComplex, Set.indicator, hxin]
      · rw [hx]
        simp [CorrelationMean.indicatorComplex, Set.indicator, hxin]
    have houter :
        (∫ p, @inner ℂ ℂ _
            (relativeFstCLM M hM I p) (H p) ∂ν) =
          ∫ p in Prod.fst ⁻¹' A, H p ∂ν := by
      rw [← integral_indicator (hA.preimage measurable_fst)]
      apply integral_congr_ae
      filter_upwards [hV, hIpull] with p hpull hIp
      simp only [RCLike.inner_apply]
      rw [hpull]
      change I p.1 = CorrelationMean.indicatorComplex A p.1 at hIp
      rw [hIp]
      by_cases hpin : p.1 ∈ A <;>
        simp [CorrelationMean.indicatorComplex, Set.indicator, hpin]
    exact hleft.trans (hbase.trans (hinner.trans houter))
  · exact hDm

/-- Essential boundedness can be read back through an exactly
measure-preserving map. -/
lemma memLp_top_of_comp_measurePreserving
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    (T : X → Y) (hT : MeasurePreserving T μ ν)
    (g : Y → ℂ) (hg : AEStronglyMeasurable g ν)
    (hcomp : MemLp (g ∘ T) ⊤ μ) :
    MemLp g ⊤ ν := by
  refine ⟨hg, ?_⟩
  rw [← eLpNorm_comp_measurePreserving hg hT]
  exact hcomp.2

private lemma memLp_top_of_relativeFst_comp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (g : M.X → ℂ) (hg : AEStronglyMeasurable g M.μ)
    (hcomp : MemLp (g ∘ Prod.fst) ⊤
      (relativeJoiningMeasure M hM)) :
    MemLp g ⊤ M.μ :=
  memLp_top_of_comp_measurePreserving
    Prod.fst (relativeJoining_fst_measurePreserving M hM) g hg hcomp

/- The first-coordinate Hilbert-adjoint conditional map preserves
essential boundedness. -/
set_option maxHeartbeats 800000 in
theorem relativeFstConditionalCLM_memLp_top
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : Lp ℂ 2 (relativeJoiningMeasure M hM))
    (hHtop : MemLp (fun p => H p) ⊤
      (relativeJoiningMeasure M hM)) :
    MemLp
      (fun x => relativeFstConditionalCLM M hM H x)
      ⊤ M.μ := by
  let mProd : MeasurableSpace (M.X × M.X) := inferInstance
  let ν : @Measure (M.X × M.X) mProd :=
    relativeJoiningMeasure M hM
  let mFst :=
    MeasurableSpace.comap (Prod.fst : M.X × M.X → M.X)
      M.measurableSpace
  have hmFst : mFst ≤ mProd :=
    Measurable.comap_le measurable_fst
  have hCEtop :
      MemLp (condExp mFst ν (fun p => H p)) ⊤ ν :=
    condExp_memLp_top ν hmFst (fun p => H p) hHtop
  change
    MemLp
      (condExp mFst (relativeJoiningMeasure M hM) (fun p => H p))
      ⊤ (relativeJoiningMeasure M hM) at hCEtop
  have hcompTop :
      MemLp
        ((fun x => relativeFstConditionalCLM M hM H x) ∘ Prod.fst)
        ⊤ (relativeJoiningMeasure M hM) := by
    change MemLp
      (fun p => relativeFstConditionalCLM M hM H p.1)
      ⊤ (relativeJoiningMeasure M hM)
    rw [memLp_congr_ae
      (relativeFstConditionalCLM_comp_fst_ae_eq_condExp M hM H)]
    exact hCEtop
  exact memLp_top_of_relativeFst_comp M hM
    (fun x => relativeFstConditionalCLM M hM H x)
    (Lp.memLp (relativeFstConditionalCLM M hM H)).1 hcompTop

end Chapter02.HostKraConditionalTop
