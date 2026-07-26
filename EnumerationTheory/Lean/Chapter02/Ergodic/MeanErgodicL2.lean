import Chapter02.Section01
import Mathlib.Analysis.InnerProductSpace.MeanErgodic

noncomputable section

namespace Chapter02
namespace MeanErgodicL2

universe u

open Filter

lemma fixedSpace_eq_invariantLpMeas (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    let Uiso : MeasureTheory.Lp ℂ 2 M.μ →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
      MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2
    let U : MeasureTheory.Lp ℂ 2 M.μ →L[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
      Uiso.toContinuousLinearMap
    LinearMap.eqLocus U (1 : MeasureTheory.Lp ℂ 2 M.μ →L[ℂ]
      MeasureTheory.Lp ℂ 2 M.μ) =
      MeasureTheory.lpMeas ℂ ℂ
        (MeasurableSpace.generateFrom (invariantSigmaAlgebra M)) 2 M.μ := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  dsimp only
  let mInv : MeasurableSpace M.X :=
    MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  letI : MeasurableSpace M.X := M.measurableSpace
  let Uiso : MeasureTheory.Lp ℂ 2 M.μ →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
    MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2
  let U : MeasureTheory.Lp ℂ 2 M.μ →L[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
    Uiso.toContinuousLinearMap
  apply Submodule.ext
  intro F
  constructor
  · intro hF
    have hfix : U F = F := hF
    have hcoe := MeasureTheory.Lp.coeFn_compMeasurePreserving F hM.2
    have hcomp : (⇑F) ∘ M.T =ᵐ[M.μ] ⇑F := by
      change ⇑(U F) =ᵐ[M.μ] (⇑F) ∘ M.T at hcoe
      exact hcoe.symm.trans (by rw [hfix])
    have hFint : MeasureTheory.Integrable (⇑F) M.μ :=
      (MeasureTheory.Lp.memLp F).integrable (by norm_num)
    obtain ⟨g, hg, hFg⟩ :=
      (Section01.invariantFunctionIffInvariantSigmaMeasurable M (⇑F)
        hFint hM).mp hcomp
    rw [MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable]
    exact hg.aestronglyMeasurable.congr hFg.symm
  · intro hF
    rw [MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable] at hF
    let g : M.X → ℂ := hF.mk (⇑F)
    have hg : @Measurable M.X ℂ mInv inferInstance g :=
      hF.stronglyMeasurable_mk.measurable
    have hFg : (⇑F) =ᵐ[M.μ] g := hF.ae_eq_mk
    have hFint : MeasureTheory.Integrable (⇑F) M.μ :=
      (MeasureTheory.Lp.memLp F).integrable (by norm_num)
    have hcomp : (⇑F) ∘ M.T =ᵐ[M.μ] ⇑F :=
      (Section01.invariantFunctionIffInvariantSigmaMeasurable M (⇑F)
        hFint hM).mpr ⟨g, hg, hFg⟩
    change U F = F
    apply MeasureTheory.Lp.ext
    have hcoe := MeasureTheory.Lp.coeFn_compMeasurePreserving F hM.2
    change ⇑(U F) =ᵐ[M.μ] ⇑F
    exact hcoe.trans hcomp

set_option synthInstance.maxHeartbeats 200000 in
lemma fixedProjection_eq_condExpL2 (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ) :
    let Uiso : MeasureTheory.Lp ℂ 2 M.μ →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
      MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2
    let U : MeasureTheory.Lp ℂ 2 M.μ →L[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
      Uiso.toContinuousLinearMap
    let S : Submodule ℂ (MeasureTheory.Lp ℂ 2 M.μ) :=
      LinearMap.eqLocus U (1 : MeasureTheory.Lp ℂ 2 M.μ →L[ℂ]
        MeasureTheory.Lp ℂ 2 M.μ)
    let mInv : MeasurableSpace M.X :=
      MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
    let hm : mInv ≤ M.measurableSpace := by
      apply MeasurableSpace.generateFrom_le
      intro s hs
      exact hs.1
    (S.orthogonalProjection F : MeasureTheory.Lp ℂ 2 M.μ) =
      ((MeasureTheory.condExpL2 (m := mInv) (m0 := M.measurableSpace)
        (μ := M.μ) ℂ ℂ hm) F :
        MeasureTheory.Lp ℂ 2 M.μ) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  dsimp only
  let mInv : MeasurableSpace M.X :=
    MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  letI : MeasurableSpace M.X := M.measurableSpace
  let hm : mInv ≤ M.measurableSpace := by
    apply MeasurableSpace.generateFrom_le
    intro s hs
    exact hs.1
  letI : Fact (mInv ≤ M.measurableSpace) := ⟨hm⟩
  let Uiso : MeasureTheory.Lp ℂ 2 M.μ →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
    MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2
  let U : MeasureTheory.Lp ℂ 2 M.μ →L[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
    Uiso.toContinuousLinearMap
  let S : Submodule ℂ (MeasureTheory.Lp ℂ 2 M.μ) :=
    LinearMap.eqLocus U (1 : MeasureTheory.Lp ℂ 2 M.μ →L[ℂ]
      MeasureTheory.Lp ℂ 2 M.μ)
  let K : Submodule ℂ (MeasureTheory.Lp ℂ 2 M.μ) :=
    MeasureTheory.lpMeas ℂ ℂ mInv 2 M.μ
  have hSK : S = K :=
    fixedSpace_eq_invariantLpMeas M hM
  rw [MeasureTheory.condExpL2]
  change S.starProjection F = K.starProjection F
  apply S.eq_starProjection_of_mem_orthogonal
  · rw [hSK]
    exact K.starProjection_apply_mem F
  · rw [hSK]
    exact K.sub_starProjection_mem_orthogonal F

lemma koopmanLp_iterate_toLp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MeasureTheory.MemLp f 2 M.μ) (n : ℕ) :
    let Uiso : MeasureTheory.Lp ℂ 2 M.μ →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
      MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2
    let U : MeasureTheory.Lp ℂ 2 M.μ →L[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
      Uiso.toContinuousLinearMap
    (U^[n]) (hf.toLp f) =
      (hf.comp_measurePreserving (hM.2.iterate n)).toLp (f ∘ (M.T^[n])) := by
  dsimp only
  let Uiso : MeasureTheory.Lp ℂ 2 M.μ →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
    MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2
  let U : MeasureTheory.Lp ℂ 2 M.μ →L[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
    Uiso.toContinuousLinearMap
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      change (MeasureTheory.Lp.compMeasurePreserving M.T hM.2)
          ((hf.comp_measurePreserving (hM.2.iterate n)).toLp
            (f ∘ (M.T^[n]))) = _
      rw [MeasureTheory.Lp.toLp_compMeasurePreserving]
      apply MeasureTheory.Lp.ext
      filter_upwards [] with x
      rfl

lemma ergodicAverage_memLp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MeasureTheory.MemLp f 2 M.μ) (n : ℕ) :
    MeasureTheory.MemLp (ergodicAverage M f n) 2 M.μ := by
  classical
  by_cases hn : n = 0
  · unfold ergodicAverage
    simp [hn]
  · have hsum : MeasureTheory.MemLp
        (fun x => ∑ i ∈ Finset.range n, f ((M.T^[i]) x)) 2 M.μ := by
      induction Finset.range n using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          have hterm : MeasureTheory.MemLp (fun x => f ((M.T^[i]) x)) 2 M.μ :=
            hf.comp_measurePreserving (hM.2.iterate i)
          simpa [Finset.sum_insert hi] using hterm.add ih
    unfold ergodicAverage
    simp only [hn, if_false]
    change MeasureTheory.MemLp
      (((n : ℂ)⁻¹) • (fun x => ∑ i ∈ Finset.range n, f ((M.T^[i]) x))) 2 M.μ
    exact hsum.const_smul ((n : ℂ)⁻¹)

lemma birkhoffAverageLp_eq_ergodicAverageToLp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MeasureTheory.MemLp f 2 M.μ) (n : ℕ) :
    let Uiso : MeasureTheory.Lp ℂ 2 M.μ →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
      MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2
    let U : MeasureTheory.Lp ℂ 2 M.μ →L[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
      Uiso.toContinuousLinearMap
    birkhoffAverage ℂ U id n (hf.toLp f) =
      (ergodicAverage_memLp M hM f hf n).toLp (ergodicAverage M f n) := by
  classical
  dsimp only
  let Uiso : MeasureTheory.Lp ℂ 2 M.μ →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
    MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2
  let U : MeasureTheory.Lp ℂ 2 M.μ →L[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
    Uiso.toContinuousLinearMap
  have hcoei (i : ℕ) : ⇑((U^[i]) (hf.toLp f)) =ᵐ[M.μ]
      fun x => f ((M.T^[i]) x) := by
    rw [koopmanLp_iterate_toLp M hM f hf i]
    exact (hf.comp_measurePreserving (hM.2.iterate i)).coeFn_toLp
  have hcoesum : ⇑(∑ i ∈ Finset.range n, (U^[i]) (hf.toLp f)) =ᵐ[M.μ]
      fun x => ∑ i ∈ Finset.range n, f ((M.T^[i]) x) := by
    induction Finset.range n using Finset.induction_on with
    | empty =>
        simpa using (MeasureTheory.Lp.coeFn_zero ℂ 2 M.μ)
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        filter_upwards [MeasureTheory.Lp.coeFn_add
          ((U^[i]) (hf.toLp f)) (∑ j ∈ s, (U^[j]) (hf.toLp f)),
          hcoei i, ih] with x hadd hi' hs'
        exact hadd.trans (by
          simpa only [Pi.add_apply, Finset.sum_insert hi] using
            congrArg₂ (fun a b : ℂ => a + b) hi' hs')
  apply MeasureTheory.Lp.ext
  have hsmul := MeasureTheory.Lp.coeFn_smul ((n : ℂ)⁻¹)
    (∑ i ∈ Finset.range n, (U^[i]) (hf.toLp f))
  have hav := (ergodicAverage_memLp M hM f hf n).coeFn_toLp
  filter_upwards [hsmul, hcoesum, hav] with x hsmulx hsumx havx
  rw [show birkhoffAverage ℂ U id n (hf.toLp f) =
      (n : ℂ)⁻¹ • ∑ i ∈ Finset.range n, (U^[i]) (hf.toLp f) by
    simp [birkhoffAverage, birkhoffSum]]
  rw [hsmulx, Pi.smul_apply, hsumx, havx]
  unfold ergodicAverage
  by_cases hn : n = 0 <;> simp [hn]

set_option synthInstance.maxHeartbeats 400000 in
theorem vonNeumannMeanErgodicTheorem_proof (M : System.{u}) :
    MeanErgodicSystemStatement M 2 := by
  intro hM f hf
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let mInv : MeasurableSpace M.X :=
    MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  letI : MeasurableSpace M.X := M.measurableSpace
  have hm : mInv ≤ M.measurableSpace := by
    apply MeasurableSpace.generateFrom_le
    intro s hs
    exact hs.1
  letI : Fact (mInv ≤ M.measurableSpace) := ⟨hm⟩
  let Uiso : MeasureTheory.Lp ℂ 2 M.μ →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
    MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2
  let U : MeasureTheory.Lp ℂ 2 M.μ →L[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
    Uiso.toContinuousLinearMap
  let S : Submodule ℂ (MeasureTheory.Lp ℂ 2 M.μ) :=
    LinearMap.eqLocus U (1 : MeasureTheory.Lp ℂ 2 M.μ →L[ℂ]
      MeasureTheory.Lp ℂ 2 M.μ)
  let F : MeasureTheory.Lp ℂ 2 M.μ := hf.toLp f
  let Gsub := (MeasureTheory.condExpL2 (m := mInv)
    (m0 := M.measurableSpace) (μ := M.μ) ℂ ℂ hm) F
  let G : MeasureTheory.Lp ℂ 2 M.μ :=
    (Gsub : MeasureTheory.Lp ℂ 2 M.μ)
  have hGmemS : G ∈ S := by
    have hSK : S = MeasureTheory.lpMeas ℂ ℂ mInv 2 M.μ := by
      simpa only [S, U, Uiso] using fixedSpace_eq_invariantLpMeas M hM
    rw [hSK]
    exact Gsub.property
  have hGfix : U G = G := hGmemS
  have hGinv : IsInvariantFunction M (⇑G) := by
    have hcoe := MeasureTheory.Lp.coeFn_compMeasurePreserving G hM.2
    change ⇑(U G) =ᵐ[M.μ] (⇑G) ∘ M.T at hcoe
    rw [hGfix] at hcoe
    exact hcoe.symm
  have hfint : MeasureTheory.Integrable f M.μ := hf.integrable (by norm_num)
  have hce : (⇑G) =ᵐ[M.μ]
      MeasureTheory.condExp mInv M.μ f := by
    exact hf.condExpL2_ae_eq_condExp' hm hfint
  refine ⟨⇑G, MeasureTheory.Lp.memLp G, hGinv, ?_, hce.symm, ?_, ?_⟩
  · have hnorm : ‖U‖ ≤ 1 := by
      apply U.opNorm_le_bound (by norm_num)
      intro H
      rw [one_mul]
      change ‖Uiso H‖ ≤ ‖H‖
      rw [Uiso.norm_map]
    have hhilb := U.tendsto_birkhoffAverage_orthogonalProjection hnorm F
    have hproj : (S.orthogonalProjection F : MeasureTheory.Lp ℂ 2 M.μ) = G := by
      exact fixedProjection_eq_condExpL2 M hM F
    rw [hproj] at hhilb
    have havLp : Tendsto
        (fun n => (ergodicAverage_memLp M hM f hf n).toLp
          (ergodicAverage M f n)) atTop (nhds G) := by
      apply hhilb.congr'
      filter_upwards [] with n
      exact birkhoffAverageLp_eq_ergodicAverageToLp M hM f hf n
    have hnormconv : Tendsto
        (fun n => ‖(ergodicAverage_memLp M hM f hf n).toLp
          (ergodicAverage M f n) - G‖) atTop (nhds 0) := by
      have hconst : Tendsto (fun _ : ℕ => G) atTop (nhds G) :=
        tendsto_const_nhds
      simpa using (havLp.sub hconst).norm
    have heq (n : ℕ) :
        MeasureTheory.eLpNorm
            (fun x => ergodicAverage M f n x - (⇑G) x) 2 M.μ =
          ENNReal.ofReal ‖(ergodicAverage_memLp M hM f hf n).toLp
            (ergodicAverage M f n) - G‖ := by
      let ha := ergodicAverage_memLp M hM f hf n
      let hsub : MeasureTheory.MemLp
          (fun x => ergodicAverage M f n x - (⇑G) x) 2 M.μ :=
        ha.sub (MeasureTheory.Lp.memLp G)
      rw [← ENNReal.ofReal_toReal (ne_of_lt hsub.eLpNorm_lt_top)]
      congr 1
      rw [← MeasureTheory.Lp.norm_toLp _ hsub]
      congr 1
      calc
        hsub.toLp (fun x => ergodicAverage M f n x - (⇑G) x) =
            ha.toLp (ergodicAverage M f n) -
              (MeasureTheory.Lp.memLp G).toLp (⇑G) := by
                simpa only [Pi.sub_apply] using
                  ha.toLp_sub (MeasureTheory.Lp.memLp G)
        _ = ha.toLp (ergodicAverage M f n) - G := by
          congr 1
          apply MeasureTheory.Lp.ext
          exact (MeasureTheory.Lp.memLp G).coeFn_toLp
    rw [show (0 : ENNReal) = ENNReal.ofReal (0 : ℝ) by simp]
    convert ENNReal.tendsto_ofReal hnormconv using 1
    funext n
    exact heq n
  · calc
      ∫ x, (⇑G) x ∂M.μ =
          ∫ x, MeasureTheory.condExp mInv M.μ f x ∂M.μ :=
            MeasureTheory.integral_congr_ae hce
      _ = ∫ x, f x ∂M.μ := MeasureTheory.integral_condExp hm
  · intro hErg
    obtain ⟨c, hc⟩ :=
      (Section01.ergodicityInvariantFunctionCharacterizations M hM).mp hErg
        (⇑G) (MeasureTheory.Lp.memLp G) hGinv
    have hintG : ∫ x, (⇑G) x ∂M.μ = ∫ x, f x ∂M.μ := by
      calc
        ∫ x, (⇑G) x ∂M.μ =
            ∫ x, MeasureTheory.condExp mInv M.μ f x ∂M.μ :=
              MeasureTheory.integral_congr_ae hce
        _ = ∫ x, f x ∂M.μ := MeasureTheory.integral_condExp hm
    have hcval : c = ∫ x, f x ∂M.μ := by
      rw [MeasureTheory.integral_congr_ae hc] at hintG
      simpa using hintG
    simpa [hcval] using hc

end MeanErgodicL2
end Chapter02
