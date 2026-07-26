import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.FactorsThrough

open Classical MeasureTheory

noncomputable section

namespace Chapter02.CompactCodingDensity

universe u v

/-- If a finite-measure factor is coded by a measurable map into a compact
metrizable space, then every `L²` vector measurable with respect to that
code is approximable by pullbacks of continuous functions on the coding
space.

This is the measure-theoretic density component of the finite-coordinate
Host--Kra reduction.  The proof uses the Doob--Dynkin factorization lemma
followed by density of continuous functions in `L²` of the pushforward
measure. -/
theorem exists_continuous_comp_norm_sub_lt
    {α : Type u} {K : Type v}
    [mα : MeasurableSpace α]
    [TopologicalSpace K] [NormalSpace K]
    [CompactSpace K] [SecondCountableTopology K]
    [mK : MeasurableSpace K] [BorelSpace K]
    (μ : Measure α) [IsFiniteMeasure μ]
    (code : α → K) (hcode : Measurable code)
    [Measure.WeaklyRegular (Measure.map code μ)]
    (F : Lp ℂ 2 μ)
    (hF : F ∈
      MeasureTheory.lpMeas ℂ ℂ (MeasurableSpace.comap code mK) 2 μ)
    {η : ℝ} (hη : 0 < η) :
    ∃ φ : C(K, ℂ),
      ‖F -
          MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ code
            ⟨hcode, rfl⟩
            (ContinuousMap.toLp 2 (Measure.map code μ) ℂ φ)‖ < η := by
  let ν : Measure K := Measure.map code μ
  let hmp : MeasurePreserving code μ ν := ⟨hcode, rfl⟩
  have hFae :
      @AEStronglyMeasurable α ℂ _ (MeasurableSpace.comap code mK) mα
        (fun x ↦ F x) μ :=
    MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable.mp hF
  let f : α → ℂ := hFae.mk (fun x ↦ F x)
  have hfstrong :
      @StronglyMeasurable α ℂ _
        (MeasurableSpace.comap code mK) f :=
    hFae.stronglyMeasurable_mk
  obtain ⟨g, hgstrong, hfg⟩ :=
    MeasureTheory.StronglyMeasurable.exists_eq_measurable_comp hfstrong
  have hgf : (g ∘ code) =ᵐ[μ] fun x ↦ F x := by
    filter_upwards [hFae.ae_eq_mk] with x hx
    have hxfg := congrFun hfg x
    exact hxfg.symm.trans hx.symm
  have hgmem : MemLp g 2 ν := by
    rw [MeasureTheory.memLp_map_measure_iff
      hgstrong.aestronglyMeasurable hcode.aemeasurable]
    exact (Lp.memLp F).ae_eq hgf.symm
  let G : Lp ℂ 2 ν := hgmem.toLp g
  have hpull : MeasureTheory.Lp.compMeasurePreserving code hmp G = F := by
    have hGg :
        (fun x ↦ G (code x)) =ᵐ[μ] g ∘ code :=
      hmp.quasiMeasurePreserving.ae_eq_comp hgmem.coeFn_toLp
    apply Lp.ext
    filter_upwards
      [MeasureTheory.Lp.coeFn_compMeasurePreserving G hmp,
        hGg, hgf]
      with x hxG hxGg hxg
    exact hxG.trans (hxGg.trans hxg)
  letI : IsFiniteMeasure ν := Measure.isFiniteMeasure_map μ code
  have hdense :
      DenseRange
        (ContinuousMap.toLp 2 ν ℂ :
          C(K, ℂ) →L[ℂ] Lp ℂ 2 ν) :=
    ContinuousMap.toLp_denseRange ℂ ν ℂ (by norm_num)
  obtain ⟨φ, hφ⟩ := hdense.exists_dist_lt G hη
  refine ⟨φ, ?_⟩
  rw [← hpull]
  change
    ‖(MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ code hmp) G -
        (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ code hmp)
          (ContinuousMap.toLp 2 ν ℂ φ)‖ < η
  rw [← map_sub,
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ code hmp).norm_map]
  simpa only [dist_eq_norm] using hφ

end Chapter02.CompactCodingDensity
