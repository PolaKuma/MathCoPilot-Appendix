import Chapter02.Ergodic.CorrelationMean
import Chapter04.Spectral.LebesgueSpectrumMixing

noncomputable section

open Classical Filter

namespace Chapter04.LebesgueSpectrum

universe u

theorem countableLebesgueSpectrum_strongMixing
    (M : System.{u}) (hSpec : HasCountableLebesgueSpectrum M) :
    Chapter02.IsStrongMixing M := by
  rcases hSpec with ⟨hLeb, _hinv, U, fbase, hbasis⟩
  have hpres : MeasureTheory.MeasurePreserving M.T M.μ M.μ := by
    simpa [U.one_act] using U.measure_preserving 1
  have hM : Chapter01.IsMeasurePreservingSystem M := ⟨hLeb.1, hpres⟩
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  refine ⟨hM, ?_⟩
  intro A B hA hB
  let a : ℂ := Chapter02.realMeasure M A
  let b : ℂ := Chapter02.realMeasure M B
  let f : M.X → ℂ := fun x => Chapter02.CorrelationMean.indicatorComplex B x - b
  let g : M.X → ℂ := fun x => Chapter02.CorrelationMean.indicatorComplex A x - a
  have hB2 := Chapter02.CorrelationMean.indicatorComplex_memLp M hM B hB 2
  have hA2 := Chapter02.CorrelationMean.indicatorComplex_memLp M hM A hA 2
  have hb2 : M.lpMember 2 (fun _ : M.X => b) := MeasureTheory.memLp_const b
  have ha2 : M.lpMember 2 (fun _ : M.X => a) := MeasureTheory.memLp_const a
  have hf : M.lpMember 2 f := hB2.sub hb2
  have hg : M.lpMember 2 g := hA2.sub ha2
  have hf0 : ∫ x, f x ∂M.μ = 0 := by
    rw [show f = fun x => Chapter02.CorrelationMean.indicatorComplex B x - b by rfl]
    rw [MeasureTheory.integral_sub (hB2.integrable (by norm_num))
        (hb2.integrable (by norm_num)),
      Chapter02.CorrelationMean.integral_indicatorComplex M B hB]
    simp [b]
  have hg0 : ∫ x, g x ∂M.μ = 0 := by
    rw [show g = fun x => Chapter02.CorrelationMean.indicatorComplex A x - a by rfl]
    rw [MeasureTheory.integral_sub (hA2.integrable (by norm_num))
        (ha2.integrable (by norm_num)),
      Chapter02.CorrelationMean.integral_indicatorComplex M A hA]
    simp [a]
  have hzero := zeroMean_correlations_tendsto_zero M hM U fbase hbasis
    f g hf hg hf0 hg0
  have hcenter (n : ℕ) :
      Chapter02.functionCorrelation M f g n =
        (Chapter02.correlation M A B n - Chapter02.productMeasureValue M A B : ℂ) := by
    have hBc : M.lpMember 2
        (fun x => Chapter02.CorrelationMean.indicatorComplex B ((M.T^[n]) x)) := by
      simpa [Function.comp_def] using hB2.comp_measurePreserving (hpres.iterate n)
    have hAc : M.lpMember 2
        (fun x => Chapter02.CorrelationMean.indicatorComplex A x) := hA2
    have hIntB : ∫ x, Chapter02.CorrelationMean.indicatorComplex B ((M.T^[n]) x) ∂M.μ = b := by
      have hmap := MeasureTheory.integral_map
        (hpres.iterate n).measurable.aemeasurable (by
          rw [(hpres.iterate n).map_eq]
          exact hB2.1)
      calc
        ∫ x, Chapter02.CorrelationMean.indicatorComplex B ((M.T^[n]) x) ∂M.μ =
            ∫ x, Chapter02.CorrelationMean.indicatorComplex B x
              ∂MeasureTheory.Measure.map (M.T^[n]) M.μ := hmap.symm
        _ = ∫ x, Chapter02.CorrelationMean.indicatorComplex B x ∂M.μ := by
          rw [(hpres.iterate n).map_eq]
        _ = b := by
          rw [Chapter02.CorrelationMean.integral_indicatorComplex M B hB]
    have hIntAstar : ∫ x, star (Chapter02.CorrelationMean.indicatorComplex A x) ∂M.μ = a := by
      have heq : (fun x => star (Chapter02.CorrelationMean.indicatorComplex A x)) =
          Chapter02.CorrelationMean.indicatorComplex A := by
        funext x
        by_cases hx : x ∈ A <;>
          simp [Chapter02.CorrelationMean.indicatorComplex, Set.indicator, hx]
      rw [heq, Chapter02.CorrelationMean.integral_indicatorComplex M A hA]
    have hprod : MeasureTheory.Integrable
        (fun x => Chapter02.CorrelationMean.indicatorComplex B ((M.T^[n]) x) *
          star (Chapter02.CorrelationMean.indicatorComplex A x)) M.μ := hBc.integrable_mul hAc.star
    have htermB : MeasureTheory.Integrable
        (fun x => a * Chapter02.CorrelationMean.indicatorComplex B ((M.T^[n]) x)) M.μ :=
      (hBc.integrable (by norm_num)).const_mul a
    have htermA : MeasureTheory.Integrable
        (fun x => b * star (Chapter02.CorrelationMean.indicatorComplex A x)) M.μ :=
      (hAc.star.integrable (by norm_num)).const_mul b
    have hconst : MeasureTheory.Integrable (fun _ : M.X => b * a) M.μ :=
      MeasureTheory.integrable_const (b * a)
    unfold Chapter02.functionCorrelation f g
    simp only [star_sub]
    rw [show (fun x =>
        (Chapter02.CorrelationMean.indicatorComplex B ((M.T^[n]) x) - b) *
          (star (Chapter02.CorrelationMean.indicatorComplex A x) - star a)) =
        fun x =>
          Chapter02.CorrelationMean.indicatorComplex B ((M.T^[n]) x) *
              star (Chapter02.CorrelationMean.indicatorComplex A x) -
            a * Chapter02.CorrelationMean.indicatorComplex B ((M.T^[n]) x) -
            b * star (Chapter02.CorrelationMean.indicatorComplex A x) + b * a by
      funext x
      simp [a, b]
      ring]
    let p : M.X → ℂ := fun x =>
      Chapter02.CorrelationMean.indicatorComplex B ((M.T^[n]) x) *
        star (Chapter02.CorrelationMean.indicatorComplex A x)
    let q : M.X → ℂ := fun x =>
      a * Chapter02.CorrelationMean.indicatorComplex B ((M.T^[n]) x)
    let r : M.X → ℂ := fun x =>
      b * star (Chapter02.CorrelationMean.indicatorComplex A x)
    let k : M.X → ℂ := fun _ => b * a
    have hp : MeasureTheory.Integrable p M.μ := hprod
    have hq : MeasureTheory.Integrable q M.μ := htermB
    have hr : MeasureTheory.Integrable r M.μ := htermA
    have hk : MeasureTheory.Integrable k M.μ := hconst
    change ∫ x, ((p - q - r) x + k x) ∂M.μ = _
    rw [MeasureTheory.integral_add (hp.sub hq |>.sub hr) hk]
    change (∫ x, (p - q) x - r x ∂M.μ) + (∫ x, k x ∂M.μ) = _
    rw [MeasureTheory.integral_sub (hp.sub hq) hr]
    change ((∫ x, p x - q x ∂M.μ) - ∫ x, r x ∂M.μ) +
      (∫ x, k x ∂M.μ) = _
    rw [MeasureTheory.integral_sub hp hq]
    simp only [p, q, r, k]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      hIntB, hIntAstar]
    change Chapter02.functionCorrelation M
        (Chapter02.CorrelationMean.indicatorComplex B)
        (Chapter02.CorrelationMean.indicatorComplex A) n - a * b - b * a +
          (∫ _x : M.X, b * a ∂M.μ) = _
    rw [Chapter02.CorrelationMean.functionCorrelation_indicator M hM A B hA hB n]
    simp [a, b, Chapter02.productMeasureValue]
  have hshift : Tendsto
      (fun n => (Chapter02.correlation M A B n -
        Chapter02.productMeasureValue M A B : ℂ)) atTop (nhds 0) := by
    simpa only [hcenter] using hzero
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hshift
  have hconst : Tendsto
      (fun _ : ℕ => Chapter02.productMeasureValue M A B) atTop
      (nhds (Chapter02.productMeasureValue M A B)) := tendsto_const_nhds
  unfold Chapter02.seqTendsTo
  convert hconst.add hre using 1
  · funext n
    simp only [Function.comp_apply, Complex.sub_re, Complex.ofReal_re]
    ring
  · simp

end Chapter04.LebesgueSpectrum
