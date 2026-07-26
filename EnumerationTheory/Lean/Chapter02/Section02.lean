import Chapter02.Section01
import Chapter02.Ergodic.MeanErgodicL2
import Chapter02.Ergodic.ErgodicAverageLp
import Chapter02.Ergodic.LpInterpolation
import Chapter02.Recurrence.Khintchine
import Chapter02.Recurrence.MultipleKhintchine
import share.Lean.NLFirst_Pfd28c3cf0fb145e58f2b0f19d4e83368_Chapter02
import share.Lean.BHKMultipleKhintchine
import Mathlib.Analysis.InnerProductSpace.MeanErgodic

noncomputable section

open Filter

namespace Chapter02
namespace Section02

universe u

/-- Source: Theorem 2.2.1, Chapter 2, Section 2. -/
theorem vonNeumannErgodicTheoremHilbertForm (D : HilbertOperatorData.{u}) :
    MeanErgodicHilbertStatement D := by
  intro hD
  have hnorm : ‖D.U‖ ≤ 1 := by
    apply D.U.opNorm_le_bound (by norm_num)
    intro x
    simpa using hD x
  let S : Submodule ℂ D.H :=
    LinearMap.eqLocus D.U (1 : D.H →L[ℂ] D.H)
  let P : D.H →L[ℂ] D.H := S.subtypeL.comp S.orthogonalProjection
  refine ⟨P, ?_, ?_, ?_⟩
  · intro x
    change D.U (P x) = P x
    exact (S.orthogonalProjection x).property
  · intro x hx
    have hxS : x ∈ S := hx
    change (S.orthogonalProjection x : D.H) = x
    simpa using congrArg Subtype.val
      (S.orthogonalProjection_mem_subspace_eq_self ⟨x, hxS⟩)
  · intro x
    have hconv := D.U.tendsto_birkhoffAverage_orthogonalProjection hnorm x
    change Tendsto
      (fun n : ℕ => if n = 0 then 0 else
        ((n : ℂ)⁻¹) • ∑ i ∈ Finset.range n, (D.U^[i]) x)
      atTop (nhds (P x))
    convert hconv using 1
    · funext n
      by_cases hn : n = 0
      · simp [hn, birkhoffAverage, birkhoffSum]
      · simp [hn, birkhoffAverage, birkhoffSum]

/-- Source: Remark 2.2.2, Chapter 2, Section 2. -/
theorem isometryFixedSpaceOrthogonalityRemark (D : HilbertOperatorData.{u}) :
    IsometryFixedSpaceOrthogonalityStatement D := by
  intro hU u
  let V : D.H →ₗᵢ[ℂ] D.H :=
    { toLinearMap := D.U.toLinearMap
      norm_map' := hU }
  constructor
  · intro hu v
    rw [inner_sub_right]
    have hv := V.inner_map_map u v
    change @inner ℂ D.H _ (D.U u) (D.U v) = _ at hv
    rw [hu] at hv
    exact sub_eq_zero.mpr hv.symm
  · intro h
    have hu : @inner ℂ D.H _ u (u - D.U u) = 0 := h u
    have hre : Complex.re (@inner ℂ D.H _ u (D.U u)) = ‖u‖ ^ 2 := by
      rw [inner_sub_right, sub_eq_zero] at hu
      rw [← hu]
      simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) u)
    have hnorm : ‖u - D.U u‖ ^ 2 = 0 := by
      rw [norm_sub_sq (𝕜 := ℂ), hU]
      change ‖u‖ ^ 2 - 2 * Complex.re (@inner ℂ D.H _ u (D.U u)) + ‖u‖ ^ 2 = 0
      rw [hre]
      ring
    have hz : ‖u - D.U u‖ = 0 := (sq_eq_zero_iff).mp hnorm
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

/-- Source: Theorem 2.2.3, Chapter 2, Section 2. -/
theorem vonNeumannMeanErgodicTheorem (M : System.{u}) :
    MeanErgodicSystemStatement M 2 := by
  exact MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M

/-- Source: Remark 2.2.4, Chapter 2, Section 2. -/
def meanErgodicLimitAsConditionalExpectation (M : System.{u}) : Prop :=
  ConditionalExpectationInvariant M

/-- Source: Theorem 2.2.5, Chapter 2, Section 2. -/
theorem lpInclusionForFiniteMeasure (P : Chapter01.ProbabilitySpaceData.{u}) :
    LpInclusionFiniteMeasureStatement P := by
  intro hfinite p q hp hpq hq f hf
  letI : MeasureTheory.IsFiniteMeasure P.μ :=
    ⟨hfinite⟩
  have hpqle : p ≤ q := hpq.le
  refine ⟨hf.mono_exponent hpqle, ?_⟩
  simpa [one_div] using
    (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (f := f) (μ := P.μ) hpqle hf.1)

/-- Source: Theorem 2.2.6, Chapter 2, Section 2. -/
theorem lOneMeanErgodicTheorem (M : System.{u}) :
    MeanErgodicSystemStatement M 1 := by
  exact ErgodicAverageLp.meanErgodicSystemStatement_one M

/-- Source: Remark 2.2.7, Chapter 2, Section 2. -/
theorem meanErgodicLimitPreservesLinftyBounds (M : System.{u}) :
    MeanErgodicLimitPreservesLinfty M := by
  intro hM f fstar hf hfstar1 hconv
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let C : ℝ := MeasureTheory.lpNorm f ⊤ M.μ
  have hmeasure : MeasureTheory.TendstoInMeasure M.μ
      (fun n => ergodicAverage M f n) atTop fstar := by
    exact MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun n => (ErgodicAverageLp.ergodicAverage_memLp M hM ⊤ f hf n).1)
      hfstar1.1 hconv
  obtain ⟨ns, hns, hsub⟩ := hmeasure.exists_seq_tendsto_ae
  have havg_bound (n : ℕ) : ∀ᵐ x ∂M.μ,
      ‖ergodicAverage M f n x‖ ≤ C := by
    let hn := ErgodicAverageLp.ergodicAverage_memLp M hM ⊤ f hf n
    have hnorm := ErgodicAverageLp.eLpNorm_ergodicAverage_le
      M hM ⊤ (by simp) f hf n
    have hlp : MeasureTheory.lpNorm (ergodicAverage M f n) ⊤ M.μ ≤ C := by
      dsimp [C]
      rw [← MeasureTheory.toReal_eLpNorm hn.1,
        ← MeasureTheory.toReal_eLpNorm hf.1]
      exact ENNReal.toReal_mono hf.2.ne hnorm
    exact (MeasureTheory.ae_le_lpNorm_exponent_top hn).mono
      (fun _ hx => hx.trans hlp)
  have havg_bound_all : ∀ᵐ x ∂M.μ, ∀ n : ℕ,
      ‖ergodicAverage M f n x‖ ≤ C :=
    MeasureTheory.ae_all_iff.mpr havg_bound
  have hfstar_bound : ∀ᵐ x ∂M.μ, ‖fstar x‖ ≤ C := by
    filter_upwards [havg_bound_all, hsub] with x hx hxs
    have hnorm_tendsto : Tendsto (fun i => ‖ergodicAverage M f (ns i) x‖)
        atTop (nhds ‖fstar x‖) :=
      continuous_norm.continuousAt.tendsto.comp hxs
    exact le_of_tendsto hnorm_tendsto (Eventually.of_forall fun i => hx (ns i))
  have hfstar_top : MeasureTheory.MemLp fstar ⊤ M.μ :=
    MeasureTheory.memLp_top_of_bound hfstar1.1 C hfstar_bound
  refine ⟨hfstar_top, ?_⟩
  calc
    MeasureTheory.eLpNorm fstar ⊤ M.μ ≤ ENNReal.ofReal C := by
      simpa using (MeasureTheory.eLpNorm_le_of_ae_bound
        (p := (⊤ : ENNReal)) hfstar_bound)
    _ = MeasureTheory.eLpNorm f ⊤ M.μ := by
      exact MeasureTheory.ofReal_lpNorm hf

/-- Source: Theorem 2.2.8, Chapter 2, Section 2. -/
theorem lpMeanErgodicTheorem (M : System.{u}) (p : ENNReal)
    (hp : 1 ≤ p) (hp_top : p < ⊤) :
    MeanErgodicSystemStatement M p := by
  intro hM f hf
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  letI : Fact (1 ≤ p) := ⟨hp⟩
  let havg : ∀ n, MeasureTheory.MemLp (ergodicAverage M f n) p M.μ :=
    fun n => ErgodicAverageLp.ergodicAverage_memLp M hM p f hf n
  have hcau : CauchySeq
      (fun n => (havg n).toLp (ergodicAverage M f n)) :=
    LpInterpolation.cauchySeq_ergodicAverage_toLp M hM f p hp hp_top hf
  obtain ⟨Fstar, hFstar⟩ := cauchySeq_tendsto_of_complete hcau
  let fstarP : M.X → ℂ := ⇑Fstar
  have hfstarP : MeasureTheory.MemLp fstarP p M.μ :=
    MeasureTheory.Lp.memLp Fstar
  have hconvpRaw : Tendsto
      (fun n => MeasureTheory.eLpNorm
        ((⇑((havg n).toLp (ergodicAverage M f n))) - fstarP) p M.μ)
      atTop (nhds 0) :=
    (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun n => (havg n).toLp (ergodicAverage M f n)) Fstar).mp hFstar
  have hconvp : Tendsto
      (fun n => MeasureTheory.eLpNorm
        (fun x => ergodicAverage M f n x - fstarP x) p M.μ)
      atTop (nhds 0) := by
    apply hconvpRaw.congr'
    filter_upwards with n
    apply MeasureTheory.eLpNorm_congr_ae
    exact (havg n).coeFn_toLp.sub EventuallyEq.rfl
  have hf1 : MeasureTheory.MemLp f 1 M.μ := hf.mono_exponent hp
  obtain ⟨fstar1, hfstar1, hfinv, hconv1, hfce, hfint, hferg⟩ :=
    ErgodicAverageLp.meanErgodicSystemStatement_one M hM f hf1
  have hmp : MeasureTheory.TendstoInMeasure M.μ
      (fun n => ergodicAverage M f n) atTop fstarP :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (ne_of_gt (zero_lt_one.trans_le hp))
      (fun n => (havg n).aestronglyMeasurable) hfstarP.aestronglyMeasurable hconvp
  have hm1 : MeasureTheory.TendstoInMeasure M.μ
      (fun n => ergodicAverage M f n) atTop fstar1 :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun n => (ErgodicAverageLp.ergodicAverage_memLp M hM 1 f hf1 n).1)
      hfstar1.1 hconv1
  have heq : fstarP =ᵐ[M.μ] fstar1 :=
    MeasureTheory.tendstoInMeasure_ae_unique hmp hm1
  have hfstar : MeasureTheory.MemLp fstar1 p M.μ :=
    MeasureTheory.MemLp.ae_eq heq hfstarP
  have hconv : Tendsto
      (fun n => MeasureTheory.eLpNorm
        (fun x => ergodicAverage M f n x - fstar1 x) p M.μ)
      atTop (nhds 0) := by
    apply hconvp.congr'
    filter_upwards with n
    apply MeasureTheory.eLpNorm_congr_ae
    exact EventuallyEq.rfl.sub heq
  exact ⟨fstar1, hfstar, hfinv, hconv, hfce, hfint, hferg⟩

/-- Source: Theorem 2.2.9, Chapter 2, Section 2. -/
theorem khintchineRecurrenceTheorem (M : System.{u}) :
    KhintchineRecurrenceStatement M := by
  exact Khintchine.khintchineRecurrence M

/-- Source: Remark 2.2.10, Chapter 2, Section 2. -/
theorem bergelsonHostKraMultipleKhintchineRemark (M : System.{u}) :
    MultipleKhintchineStatement M := by
  constructor
  · exact MathCopilotPrior.bergelsonHostKra_multipleKhintchine M
  · exact MultipleKhintchine.exists_system_with_fivefold_upper_bound

end Section02
end Chapter02
