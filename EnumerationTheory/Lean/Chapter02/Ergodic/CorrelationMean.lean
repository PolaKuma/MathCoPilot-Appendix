import Chapter02.Ergodic.ErgodicAverageLp
import Chapter02.Ergodic.DenseExtension

noncomputable section

open Filter
open scoped ComplexConjugate

namespace Chapter02
namespace CorrelationMean

universe u

def indicatorComplex {X : Type u} (A : Set X) : X → ℂ :=
  A.indicator (fun _ => 1)

lemma simpleFunc_eq_sum_indicator {X : Type u} [MeasurableSpace X]
    (s : MeasureTheory.SimpleFunc X ℂ) :
    (s : X → ℂ) = fun x => ∑ c ∈ s.range,
      c * indicatorComplex (s ⁻¹' {c}) x := by
  classical
  funext x
  rw [Finset.sum_eq_single (s x)]
  · simp [indicatorComplex, Set.indicator]
  · intro b hb hne
    simp [indicatorComplex, Set.indicator, hne.symm]
  · simp

lemma tendsto_of_dense_of_uniform_dist {X Y ι : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {l : Filter ι} {S : Set X} (hS : Dense S)
    (F : ι → X → Y) (G : X → Y) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ i x y, dist (F i x) (F i y) ≤ C * dist x y)
    (hG : ∀ x y, dist (G x) (G y) ≤ C * dist x y)
    (hlim : ∀ x ∈ S, Tendsto (fun i => F i x) l (nhds (G x))) :
    ∀ x, Tendsto (fun i => F i x) l (nhds (G x)) :=
  DenseExtension.tendsto_of_dense_of_uniform_dist hS F G C hC hF hG hlim

lemma cesaroTendsTo_finset_sum {I : Type*} (s : Finset I)
    (a : I → ℕ → ℝ)
    (ha : ∀ i ∈ s, cesaroTendsTo (a i) 0) :
    cesaroTendsTo (fun n => ∑ i ∈ s, a i n) 0 := by
  classical
  unfold cesaroTendsTo seqTendsTo cesaroAverage at ha ⊢
  have hsum := tendsto_finset_sum s (fun i hi => ha i hi)
  convert hsum using 1
  · funext N
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  · simp

lemma cesaroTendsTo_zero_of_le {a b : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hab : ∀ n, a n ≤ b n)
    (hb : cesaroTendsTo b 0) : cesaroTendsTo a 0 := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at hb ⊢
  have havg0 (N : ℕ) :
      0 ≤ (((N + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1), a n) := by
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun n hn => ha n)
  have havgle (N : ℕ) :
      (((N + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1), a n) ≤
        (((N + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1), b n) := by
    gcongr with n hn
    exact hab n
  exact squeeze_zero havg0 havgle hb

lemma cesaroTendsTo_const_mul (C : ℝ) {a : ℕ → ℝ} {l : ℝ}
    (ha : cesaroTendsTo a l) :
    cesaroTendsTo (fun n => C * a n) (C * l) := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at ha ⊢
  have h := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => C) atTop (nhds C)).mul ha
  convert h using 1
  funext N
  calc
    (((N + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1), C * a n) =
        ∑ n ∈ Finset.range (N + 1),
          (((N + 1 : ℕ) : ℝ)⁻¹ * C) * a n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = (((N + 1 : ℕ) : ℝ)⁻¹ * C) *
        ∑ n ∈ Finset.range (N + 1), a n := by rw [Finset.mul_sum]
    _ = C * (((N + 1 : ℕ) : ℝ)⁻¹ *
        ∑ n ∈ Finset.range (N + 1), a n) := by ring

lemma cesaroTendsTo_of_dense_of_uniform_dist {X : Type*}
    [PseudoMetricSpace X] {S : Set X} (hS : Dense S)
    (a : X → ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hlip : ∀ x y n, dist (a x n) (a y n) ≤ C * dist x y)
    (hlim : ∀ x ∈ S, cesaroTendsTo (a x) 0) :
    ∀ x, cesaroTendsTo (a x) 0 := by
  unfold cesaroTendsTo seqTendsTo at hlim ⊢
  apply tendsto_of_dense_of_uniform_dist hS
    (fun N x => cesaroAverage (a x) N) (fun _ => 0) C hC
  · intro N x y
    rw [Real.dist_eq]
    unfold cesaroAverage
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul]
    have hinv : 0 ≤ (((N + 1 : ℕ) : ℝ)⁻¹) := inv_nonneg.mpr (by positivity)
    rw [abs_of_nonneg hinv]
    calc
      (((N + 1 : ℕ) : ℝ)⁻¹) *
          |∑ n ∈ Finset.range (N + 1), (a x n - a y n)| ≤
          (((N + 1 : ℕ) : ℝ)⁻¹) *
            ∑ n ∈ Finset.range (N + 1), |a x n - a y n| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (((N + 1 : ℕ) : ℝ)⁻¹) *
          ∑ _n ∈ Finset.range (N + 1), C * dist x y := by
        gcongr with n hn
        simpa [Real.dist_eq] using hlip x y n
      _ = C * dist x y := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
  · intro x y
    simpa using mul_nonneg hC (dist_nonneg : 0 ≤ dist x y)
  · intro x hx
    exact hlim x hx

lemma indicatorComplex_memLp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (A : Set M.X)
    (hA : MeasurableSet A) (p : ENNReal) :
    MeasureTheory.MemLp (indicatorComplex A) p M.μ := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  exact MeasureTheory.memLp_indicator_const p hA 1 (Or.inr (by simp))

lemma integral_indicatorComplex (M : System.{u}) (A : Set M.X)
    (hA : MeasurableSet A) :
    ∫ x, indicatorComplex A x ∂M.μ = (realMeasure M A : ℂ) := by
  rw [show indicatorComplex A = A.indicator (fun _ => (1 : ℂ)) by rfl,
    MeasureTheory.integral_indicator hA]
  simp [realMeasure, MeasureTheory.Measure.real]

lemma correlation_eq_re_functionCorrelation_indicator (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    correlation M A B n =
      (functionCorrelation M (indicatorComplex B) (indicatorComplex A) n).re := by
  let C := A ∩ preimageIter M n B
  have hC : MeasurableSet C := by
    change MeasurableSet (A ∩ (M.T^[n]) ⁻¹' B)
    exact hA.inter (hB.preimage (hM.2.measurable.iterate n))
  have hfun : (fun x => indicatorComplex B ((M.T^[n]) x) *
      star (indicatorComplex A x)) = C.indicator (fun _ => (1 : ℂ)) := by
    funext x
    simp only [indicatorComplex, Set.indicator, C, preimageIter, Chapter01.iterateMap]
    by_cases hxA : x ∈ A <;> by_cases hxB : (M.T^[n]) x ∈ B <;>
      simp [hxA, hxB]
  unfold correlation functionCorrelation realMeasure
  rw [hfun, MeasureTheory.integral_indicator hC]
  simp [MeasureTheory.Measure.real, C]

lemma functionCorrelation_indicator (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    functionCorrelation M (indicatorComplex B) (indicatorComplex A) n =
      (correlation M A B n : ℂ) := by
  let C := A ∩ preimageIter M n B
  have hC : MeasurableSet C := by
    change MeasurableSet (A ∩ (M.T^[n]) ⁻¹' B)
    exact hA.inter (hB.preimage (hM.2.measurable.iterate n))
  have hfun : (fun x => indicatorComplex B ((M.T^[n]) x) *
      star (indicatorComplex A x)) = C.indicator (fun _ => (1 : ℂ)) := by
    funext x
    simp only [indicatorComplex, Set.indicator, C, preimageIter, Chapter01.iterateMap]
    by_cases hxA : x ∈ A <;> by_cases hxB : (M.T^[n]) x ∈ B <;>
      simp [hxA, hxB]
  unfold functionCorrelation correlation realMeasure
  rw [hfun, MeasureTheory.integral_indicator hC]
  simp [MeasureTheory.Measure.real, C]

lemma productOfMeans_indicator (M : System.{u})
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    productOfMeans M (indicatorComplex B) (indicatorComplex A) =
      (productMeasureValue M A B : ℂ) := by
  rw [productOfMeans, integral_indicatorComplex M B hB,
    integral_indicatorComplex M A hA]
  simp [productMeasureValue, mul_comm]

lemma functionCorrelation_eq_innerLp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f g : M.X → ℂ) (hf : M.lpMember 2 f) (hg : M.lpMember 2 g) (n : ℕ) :
    functionCorrelation M f g n =
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (hg.toLp g)
        (((hf.comp_measurePreserving (hM.2.iterate n)).toLp
          (fun x => f ((M.T^[n]) x)))) := by
  rw [MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hg.coeFn_toLp,
      (hf.comp_measurePreserving (hM.2.iterate n)).coeFn_toLp] with x hgx hfx
  simp only [RCLike.inner_apply, starRingEnd_apply]
  have hfx' :
      ((hf.comp_measurePreserving (hM.2.iterate n)).toLp
        (fun x => f ((M.T^[n]) x))) x = f ((M.T^[n]) x) := by
    simpa [Function.comp_apply] using hfx
  rw [hgx, hfx']

noncomputable def oneLp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasureTheory.Lp ℂ 2 M.μ := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  exact (MeasureTheory.memLp_const (p := (2 : ENNReal)) (c := (1 : ℂ))).toLp
    (fun _ : M.X => (1 : ℂ))

noncomputable def koopmanIterLp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (n : ℕ) :
    MeasureTheory.Lp ℂ 2 M.μ →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ (M.T^[n]) (hM.2.iterate n)

lemma koopmanIterLp_apply_toLp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (n : ℕ)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    koopmanIterLp M hM n (hf.toLp f) =
      (hf.comp_measurePreserving (hM.2.iterate n)).toLp
        (fun x => f ((M.T^[n]) x)) := by
  apply MeasureTheory.Lp.ext
  have hleft := MeasureTheory.Lp.coeFn_compMeasurePreserving
    (hf.toLp f) (hM.2.iterate n)
  have hright := (hf.comp_measurePreserving (hM.2.iterate n)).coeFn_toLp
  have hforb := (hM.2.iterate n).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp
  filter_upwards [hleft, hright, hforb] with x hl hr hf0
  change ((koopmanIterLp M hM n (hf.toLp f) :
    MeasureTheory.Lp ℂ 2 M.μ) : M.X → ℂ) x = _
  have hr' : ((hf.comp_measurePreserving (hM.2.iterate n)).toLp
      (fun x => f ((M.T^[n]) x))) x = f ((M.T^[n]) x) := by
    simpa [Function.comp_apply] using hr
  have hf0' : (hf.toLp f : M.X → ℂ) ((M.T^[n]) x) =
      f ((M.T^[n]) x) := by
    simpa [Function.comp_apply] using hf0
  rw [hr']
  calc
    ((koopmanIterLp M hM n (hf.toLp f) :
        MeasureTheory.Lp ℂ 2 M.μ) : M.X → ℂ) x =
        (hf.toLp f : M.X → ℂ) ((M.T^[n]) x) := by
          simpa [koopmanIterLp, Function.comp_apply] using hl
    _ = f ((M.T^[n]) x) := hf0'

lemma integral_eq_inner_oneLp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ) :
    ∫ x, F x ∂M.μ = @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
      (oneLp M hM) F := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  rw [MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  have hone : (oneLp M hM : M.X → ℂ) =ᵐ[M.μ] fun _ => 1 := by
    exact (MeasureTheory.memLp_const (p := (2 : ENNReal))
      (c := (1 : ℂ))).coeFn_toLp
  filter_upwards [hone] with x hx
  rw [RCLike.inner_apply, hx]
  simp

lemma functionCorrelation_simpleFunc (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (s t : MeasureTheory.SimpleFunc M.X ℂ) (n : ℕ) :
    functionCorrelation M s t n =
      ∑ c ∈ s.range, ∑ d ∈ t.range,
        c * star d * (correlation M (t ⁻¹' {d}) (s ⁻¹' {c}) n : ℂ) := by
  classical
  have hs := simpleFunc_eq_sum_indicator s
  have ht := simpleFunc_eq_sum_indicator t
  have hpoint : (fun x => s ((M.T^[n]) x) * star (t x)) =
      fun x => ∑ c ∈ s.range, ∑ d ∈ t.range,
        (c * star d) *
          (indicatorComplex (s ⁻¹' {c}) ((M.T^[n]) x) *
            star (indicatorComplex (t ⁻¹' {d}) x)) := by
    funext x
    rw [show s ((M.T^[n]) x) =
        (∑ c ∈ s.range, c * indicatorComplex (s ⁻¹' {c}) ((M.T^[n]) x)) by
          exact congrFun hs ((M.T^[n]) x)]
    rw [show t x = ∑ d ∈ t.range,
        d * indicatorComplex (t ⁻¹' {d}) x by exact congrFun ht x]
    rw [star_sum]
    simp_rw [star_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    ring
  unfold functionCorrelation
  rw [hpoint]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro c hc
    rw [MeasureTheory.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro d hd
      rw [MeasureTheory.integral_const_mul]
      rw [show (∫ x, indicatorComplex (s ⁻¹' {c}) ((M.T^[n]) x) *
            star (indicatorComplex (t ⁻¹' {d}) x) ∂M.μ) =
          functionCorrelation M (indicatorComplex (s ⁻¹' {c}))
            (indicatorComplex (t ⁻¹' {d})) n by rfl]
      rw [functionCorrelation_indicator M hM (t ⁻¹' {d}) (s ⁻¹' {c})
        (t.measurableSet_fiber d) (s.measurableSet_fiber c) n]
    · intro d hd
      exact ((indicatorComplex_memLp M hM (s ⁻¹' {c})
        (s.measurableSet_fiber c) 2).comp_measurePreserving (hM.2.iterate n)).integrable_mul
          (indicatorComplex_memLp M hM (t ⁻¹' {d})
            (t.measurableSet_fiber d) 2).star |>.const_mul _
  · intro c hc
    induction t.range using Finset.induction with
    | empty => simp
    | @insert d r hd ihr =>
        have hone : MeasureTheory.Integrable
            (fun x => (c * star d) *
              (indicatorComplex (s ⁻¹' {c}) ((M.T^[n]) x) *
                star (indicatorComplex (t ⁻¹' {d}) x))) M.μ :=
          (((indicatorComplex_memLp M hM (s ⁻¹' {c})
            (s.measurableSet_fiber c) 2).comp_measurePreserving
              (hM.2.iterate n)).integrable_mul
                (indicatorComplex_memLp M hM (t ⁻¹' {d})
                  (t.measurableSet_fiber d) 2).star).const_mul (c * star d)
        simpa only [Finset.sum_insert hd] using hone.add ihr

lemma integral_simpleFunc (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (s : MeasureTheory.SimpleFunc M.X ℂ) :
    ∫ x, s x ∂M.μ = ∑ c ∈ s.range,
      c * (realMeasure M (s ⁻¹' {c}) : ℂ) := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  have hs := simpleFunc_eq_sum_indicator s
  rw [show (∫ x, s x ∂M.μ) =
      ∫ x, ∑ c ∈ s.range, c * indicatorComplex (s ⁻¹' {c}) x ∂M.μ by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun x => congrFun hs x]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro c hc
    rw [MeasureTheory.integral_const_mul,
      integral_indicatorComplex M (s ⁻¹' {c}) (s.measurableSet_fiber c)]
  · intro c hc
    exact (indicatorComplex_memLp M hM (s ⁻¹' {c})
      (s.measurableSet_fiber c) 2).integrable (by norm_num) |>.const_mul c

lemma productOfMeans_simpleFunc (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (s t : MeasureTheory.SimpleFunc M.X ℂ) :
    productOfMeans M s t =
      ∑ c ∈ s.range, ∑ d ∈ t.range,
        c * star d *
          ((realMeasure M (t ⁻¹' {d}) * realMeasure M (s ⁻¹' {c}) : ℝ) : ℂ) := by
  classical
  unfold productOfMeans
  rw [integral_simpleFunc M hM s, integral_simpleFunc M hM t, star_sum]
  simp_rw [star_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  push_cast
  rw [show star (realMeasure M (t ⁻¹' {d}) : ℂ) =
    (realMeasure M (t ⁻¹' {d}) : ℂ) by simp]
  ring

lemma strongMixing_simpleFuncCorrelations (M : System.{u})
    (hstrong : IsStrongMixing M)
    (s t : MeasureTheory.SimpleFunc M.X ℂ) :
    Tendsto (fun n => functionCorrelation M s t n) atTop
      (nhds (productOfMeans M s t)) := by
  classical
  have hM := hstrong.1
  have hcd (c d : ℂ) : Tendsto
      (fun n => c * star d *
        (correlation M (t ⁻¹' {d}) (s ⁻¹' {c}) n : ℂ)) atTop
      (nhds (c * star d *
        ((realMeasure M (t ⁻¹' {d}) *
          realMeasure M (s ⁻¹' {c}) : ℝ) : ℂ))) := by
    have hr := hstrong.2 (t ⁻¹' {d}) (s ⁻¹' {c})
      (t.measurableSet_fiber d) (s.measurableSet_fiber c)
    have hcplx := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
    have hconst : Tendsto (fun _ : ℕ => c * star d) atTop
        (nhds (c * star d)) := tendsto_const_nhds
    convert hconst.mul hcplx using 1
  have hsum : Tendsto
      (fun n => ∑ c ∈ s.range, ∑ d ∈ t.range,
        c * star d * (correlation M (t ⁻¹' {d}) (s ⁻¹' {c}) n : ℂ)) atTop
      (nhds (∑ c ∈ s.range, ∑ d ∈ t.range,
        c * star d * ((realMeasure M (t ⁻¹' {d}) *
          realMeasure M (s ⁻¹' {c}) : ℝ) : ℂ))) := by
    apply tendsto_finset_sum
    intro c hc
    apply tendsto_finset_sum
    intro d hd
    exact hcd c d
  convert hsum using 1
  · funext n
    exact functionCorrelation_simpleFunc M hM s t n
  · exact congrArg nhds (productOfMeans_simpleFunc M hM s t)

lemma weakMixing_simpleFuncCorrelations (M : System.{u})
    (hweak : IsWeakMixing M)
    (s t : MeasureTheory.SimpleFunc M.X ℂ) :
    cesaroTendsTo
      (fun n => ‖functionCorrelation M s t n - productOfMeans M s t‖) 0 := by
  classical
  let q : ℂ → ℂ → ℕ → ℂ := fun c d n =>
    c * star d *
      ((correlation M (t ⁻¹' {d}) (s ⁻¹' {c}) n -
        productMeasureValue M (t ⁻¹' {d}) (s ⁻¹' {c}) : ℝ) : ℂ)
  have hq (c d : ℂ) : cesaroTendsTo (fun n => ‖q c d n‖) 0 := by
    have hw := hweak.2 (t ⁻¹' {d}) (s ⁻¹' {c})
      (t.measurableSet_fiber d) (s.measurableSet_fiber c)
    have hm := cesaroTendsTo_const_mul ‖c * star d‖ hw
    change cesaroTendsTo (fun n =>
      ‖c * star d *
        ((correlation M (t ⁻¹' {d}) (s ⁻¹' {c}) n -
          productMeasureValue M (t ⁻¹' {d}) (s ⁻¹' {c}) : ℝ) : ℂ)‖) 0
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_zero] using hm
  have hinner (c : ℂ) :
      cesaroTendsTo (fun n => ∑ d ∈ t.range, ‖q c d n‖) 0 :=
    cesaroTendsTo_finset_sum t.range (fun d n => ‖q c d n‖)
      (fun d hd => hq c d)
  have hsum : cesaroTendsTo
      (fun n => ∑ c ∈ s.range, ∑ d ∈ t.range, ‖q c d n‖) 0 :=
    cesaroTendsTo_finset_sum s.range
      (fun c n => ∑ d ∈ t.range, ‖q c d n‖)
      (fun c hc => hinner c)
  have hdev (n : ℕ) :
      functionCorrelation M s t n - productOfMeans M s t =
        ∑ c ∈ s.range, ∑ d ∈ t.range, q c d n := by
    rw [functionCorrelation_simpleFunc M hweak.1 s t n,
      productOfMeans_simpleFunc M hweak.1 s t]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [q, productMeasureValue]
    push_cast
    ring
  apply cesaroTendsTo_zero_of_le (fun n => norm_nonneg _)
    (fun n => ?_) hsum
  rw [hdev n]
  calc
    ‖∑ c ∈ s.range, ∑ d ∈ t.range, q c d n‖ ≤
        ∑ c ∈ s.range, ‖∑ d ∈ t.range, q c d n‖ := norm_sum_le _ _
    _ ≤ ∑ c ∈ s.range, ∑ d ∈ t.range, ‖q c d n‖ := by
      gcongr with c hc
      exact norm_sum_le _ _

lemma strongMixing_simpleLpCorrelations (M : System.{u})
    (hstrong : IsStrongMixing M)
    (F G : MeasureTheory.Lp.simpleFunc ℂ 2 M.μ) :
    Tendsto (fun n => @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (G : MeasureTheory.Lp ℂ 2 M.μ)
        (koopmanIterLp M hstrong.1 n (F : MeasureTheory.Lp ℂ 2 M.μ)))
      atTop (nhds
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (oneLp M hstrong.1)
          (F : MeasureTheory.Lp ℂ 2 M.μ) *
        star (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (oneLp M hstrong.1)
          (G : MeasureTheory.Lp ℂ 2 M.μ)))) := by
  let s := MeasureTheory.Lp.simpleFunc.toSimpleFunc F
  let t := MeasureTheory.Lp.simpleFunc.toSimpleFunc G
  have hsLp : MeasureTheory.Lp.simpleFunc.toLp s
      (MeasureTheory.Lp.simpleFunc.memLp F) =
      (F : MeasureTheory.Lp ℂ 2 M.μ) :=
    by
      simpa [s] using congrArg
        (fun H : MeasureTheory.Lp.simpleFunc ℂ 2 M.μ =>
          (H : MeasureTheory.Lp ℂ 2 M.μ))
        (MeasureTheory.Lp.simpleFunc.toLp_toSimpleFunc F)
  have htLp : MeasureTheory.Lp.simpleFunc.toLp t
      (MeasureTheory.Lp.simpleFunc.memLp G) =
      (G : MeasureTheory.Lp ℂ 2 M.μ) :=
    by
      simpa [t] using congrArg
        (fun H : MeasureTheory.Lp.simpleFunc ℂ 2 M.μ =>
          (H : MeasureTheory.Lp ℂ 2 M.μ))
        (MeasureTheory.Lp.simpleFunc.toLp_toSimpleFunc G)
  have hsint : (∫ x, (MeasureTheory.Lp.simpleFunc.toLp s
      (MeasureTheory.Lp.simpleFunc.memLp F) :
        MeasureTheory.Lp ℂ 2 M.μ) x ∂M.μ) = ∫ x, s x ∂M.μ := by
    apply MeasureTheory.integral_congr_ae
    exact (MeasureTheory.Lp.simpleFunc.memLp F).coeFn_toLp
  have htint : (∫ x, (MeasureTheory.Lp.simpleFunc.toLp t
      (MeasureTheory.Lp.simpleFunc.memLp G) :
        MeasureTheory.Lp ℂ 2 M.μ) x ∂M.μ) = ∫ x, t x ∂M.μ := by
    apply MeasureTheory.integral_congr_ae
    exact (MeasureTheory.Lp.simpleFunc.memLp G).coeFn_toLp
  have hraw := strongMixing_simpleFuncCorrelations M hstrong s t
  convert hraw using 1
  · funext n
    rw [← hsLp, ← htLp, koopmanIterLp_apply_toLp]
    exact (functionCorrelation_eq_innerLp M hstrong.1 s t
      (MeasureTheory.Lp.simpleFunc.memLp F)
      (MeasureTheory.Lp.simpleFunc.memLp G) n).symm
  · rw [← hsLp, ← htLp, ← integral_eq_inner_oneLp,
      ← integral_eq_inner_oneLp]
    rw [hsint, htint]
    rfl

lemma weakMixing_simpleLpCorrelations (M : System.{u})
    (hweak : IsWeakMixing M)
    (F G : MeasureTheory.Lp.simpleFunc ℂ 2 M.μ) :
    cesaroTendsTo (fun n =>
      ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          (G : MeasureTheory.Lp ℂ 2 M.μ)
          (koopmanIterLp M hweak.1 n (F : MeasureTheory.Lp ℂ 2 M.μ)) -
        @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (oneLp M hweak.1)
            (F : MeasureTheory.Lp ℂ 2 M.μ) *
          star (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (oneLp M hweak.1)
            (G : MeasureTheory.Lp ℂ 2 M.μ))‖) 0 := by
  let s := MeasureTheory.Lp.simpleFunc.toSimpleFunc F
  let t := MeasureTheory.Lp.simpleFunc.toSimpleFunc G
  have hsLp : MeasureTheory.Lp.simpleFunc.toLp s
      (MeasureTheory.Lp.simpleFunc.memLp F) =
      (F : MeasureTheory.Lp ℂ 2 M.μ) := by
    simpa [s] using congrArg
      (fun H : MeasureTheory.Lp.simpleFunc ℂ 2 M.μ =>
        (H : MeasureTheory.Lp ℂ 2 M.μ))
      (MeasureTheory.Lp.simpleFunc.toLp_toSimpleFunc F)
  have htLp : MeasureTheory.Lp.simpleFunc.toLp t
      (MeasureTheory.Lp.simpleFunc.memLp G) =
      (G : MeasureTheory.Lp ℂ 2 M.μ) := by
    simpa [t] using congrArg
      (fun H : MeasureTheory.Lp.simpleFunc ℂ 2 M.μ =>
        (H : MeasureTheory.Lp ℂ 2 M.μ))
      (MeasureTheory.Lp.simpleFunc.toLp_toSimpleFunc G)
  have hsint : (∫ x, (MeasureTheory.Lp.simpleFunc.toLp s
      (MeasureTheory.Lp.simpleFunc.memLp F) :
        MeasureTheory.Lp ℂ 2 M.μ) x ∂M.μ) = ∫ x, s x ∂M.μ := by
    apply MeasureTheory.integral_congr_ae
    exact (MeasureTheory.Lp.simpleFunc.memLp F).coeFn_toLp
  have htint : (∫ x, (MeasureTheory.Lp.simpleFunc.toLp t
      (MeasureTheory.Lp.simpleFunc.memLp G) :
        MeasureTheory.Lp ℂ 2 M.μ) x ∂M.μ) = ∫ x, t x ∂M.μ := by
    apply MeasureTheory.integral_congr_ae
    exact (MeasureTheory.Lp.simpleFunc.memLp G).coeFn_toLp
  have hcorr (n : ℕ) :
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          (G : MeasureTheory.Lp ℂ 2 M.μ)
          (koopmanIterLp M hweak.1 n (F : MeasureTheory.Lp ℂ 2 M.μ)) =
        functionCorrelation M s t n := by
    rw [← hsLp, ← htLp, koopmanIterLp_apply_toLp]
    exact (functionCorrelation_eq_innerLp M hweak.1 s t
      (MeasureTheory.Lp.simpleFunc.memLp F)
      (MeasureTheory.Lp.simpleFunc.memLp G) n).symm
  have hprod :
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (oneLp M hweak.1)
          (F : MeasureTheory.Lp ℂ 2 M.μ) *
        star (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (oneLp M hweak.1)
          (G : MeasureTheory.Lp ℂ 2 M.μ)) = productOfMeans M s t := by
    rw [← hsLp, ← htLp, ← integral_eq_inner_oneLp,
      ← integral_eq_inner_oneLp, hsint, htint]
    rfl
  simpa only [hcorr, hprod] using weakMixing_simpleFuncCorrelations M hweak s t

lemma weakMixing_lpCorrelations (M : System.{u})
    (hweak : IsWeakMixing M) :
    ∀ F G : MeasureTheory.Lp ℂ 2 M.μ,
      cesaroTendsTo (fun n =>
        ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G
            (koopmanIterLp M hweak.1 n F) -
          @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (oneLp M hweak.1) F *
            star (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
              (oneLp M hweak.1) G)‖) 0 := by
  let H := MeasureTheory.Lp ℂ 2 M.μ
  let u : H := oneLp M hweak.1
  have hdense : Dense (MeasureTheory.Lp.simpleFunc ℂ 2 M.μ : Set H) :=
    MeasureTheory.Lp.simpleFunc.dense (by norm_num)
  have hfirst (G : H) (hGs : G ∈ (MeasureTheory.Lp.simpleFunc ℂ 2 M.μ : Set H)) :
      ∀ F : H, cesaroTendsTo (fun n =>
        ‖@inner ℂ H _ G (koopmanIterLp M hweak.1 n F) -
          @inner ℂ H _ u F * star (@inner ℂ H _ u G)‖) 0 := by
    let C : ℝ := ‖G‖ + ‖u‖ ^ 2 * ‖G‖
    apply cesaroTendsTo_of_dense_of_uniform_dist hdense
      (fun F n => ‖@inner ℂ H _ G (koopmanIterLp M hweak.1 n F) -
        @inner ℂ H _ u F * star (@inner ℂ H _ u G)‖) C
    · dsimp [C]
      positivity
    · intro x y n
      rw [Real.dist_eq, dist_eq_norm]
      apply (abs_norm_sub_norm_le _ _).trans
      have hrewrite :
          (@inner ℂ H _ G (koopmanIterLp M hweak.1 n x) -
              @inner ℂ H _ u x * star (@inner ℂ H _ u G)) -
            (@inner ℂ H _ G (koopmanIterLp M hweak.1 n y) -
              @inner ℂ H _ u y * star (@inner ℂ H _ u G)) =
          @inner ℂ H _ G (koopmanIterLp M hweak.1 n (x - y)) -
            @inner ℂ H _ u (x - y) * star (@inner ℂ H _ u G) := by
        rw [map_sub, inner_sub_right, inner_sub_right]
        ring
      rw [hrewrite]
      have h1 : ‖@inner ℂ H _ G (koopmanIterLp M hweak.1 n (x - y))‖ ≤
          ‖G‖ * ‖x - y‖ := by
        calc
          _ ≤ ‖G‖ * ‖koopmanIterLp M hweak.1 n (x - y)‖ := norm_inner_le_norm _ _
          _ = _ := by rw [LinearIsometry.norm_map]
      have hu : ‖@inner ℂ H _ u (x - y)‖ ≤ ‖u‖ * ‖x - y‖ :=
        norm_inner_le_norm _ _
      have hG : ‖@inner ℂ H _ u G‖ ≤ ‖u‖ * ‖G‖ :=
        norm_inner_le_norm _ _
      have h2 : ‖@inner ℂ H _ u (x - y) * star (@inner ℂ H _ u G)‖ ≤
          (‖u‖ * ‖x - y‖) * (‖u‖ * ‖G‖) := by
        rw [norm_mul, norm_star]
        exact mul_le_mul hu hG (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      calc
        ‖@inner ℂ H _ G (koopmanIterLp M hweak.1 n (x - y)) -
            @inner ℂ H _ u (x - y) * star (@inner ℂ H _ u G)‖ ≤
            ‖@inner ℂ H _ G (koopmanIterLp M hweak.1 n (x - y))‖ +
              ‖@inner ℂ H _ u (x - y) * star (@inner ℂ H _ u G)‖ :=
          norm_sub_le _ _
        _ ≤ ‖G‖ * ‖x - y‖ +
            (‖u‖ * ‖x - y‖) * (‖u‖ * ‖G‖) := add_le_add h1 h2
        _ = C * ‖x - y‖ := by dsimp [C]; ring
    · intro F hFs
      let Fs : MeasureTheory.Lp.simpleFunc ℂ 2 M.μ := ⟨F, hFs⟩
      let Gs : MeasureTheory.Lp.simpleFunc ℂ 2 M.μ := ⟨G, hGs⟩
      simpa [H, u, Fs, Gs] using weakMixing_simpleLpCorrelations M hweak Fs Gs
  intro F
  let C : ℝ := ‖F‖ + ‖u‖ ^ 2 * ‖F‖
  apply cesaroTendsTo_of_dense_of_uniform_dist hdense
    (fun G n => ‖@inner ℂ H _ G (koopmanIterLp M hweak.1 n F) -
      @inner ℂ H _ u F * star (@inner ℂ H _ u G)‖) C
  · dsimp [C]
    positivity
  · intro x y n
    rw [Real.dist_eq, dist_eq_norm]
    apply (abs_norm_sub_norm_le _ _).trans
    have hstar : star (@inner ℂ H _ u x) - star (@inner ℂ H _ u y) =
        star (@inner ℂ H _ u (x - y)) := by
      rw [← star_sub, inner_sub_right]
    have hrewrite :
        (@inner ℂ H _ x (koopmanIterLp M hweak.1 n F) -
            @inner ℂ H _ u F * star (@inner ℂ H _ u x)) -
          (@inner ℂ H _ y (koopmanIterLp M hweak.1 n F) -
            @inner ℂ H _ u F * star (@inner ℂ H _ u y)) =
        @inner ℂ H _ (x - y) (koopmanIterLp M hweak.1 n F) -
          @inner ℂ H _ u F * star (@inner ℂ H _ u (x - y)) := by
      rw [inner_sub_left, ← hstar]
      ring
    rw [hrewrite]
    have h1 : ‖@inner ℂ H _ (x - y) (koopmanIterLp M hweak.1 n F)‖ ≤
        ‖x - y‖ * ‖F‖ := by
      calc
        _ ≤ ‖x - y‖ * ‖koopmanIterLp M hweak.1 n F‖ := norm_inner_le_norm _ _
        _ = _ := by rw [LinearIsometry.norm_map]
    have hF : ‖@inner ℂ H _ u F‖ ≤ ‖u‖ * ‖F‖ := norm_inner_le_norm _ _
    have hu : ‖@inner ℂ H _ u (x - y)‖ ≤ ‖u‖ * ‖x - y‖ :=
      norm_inner_le_norm _ _
    have h2 : ‖@inner ℂ H _ u F * star (@inner ℂ H _ u (x - y))‖ ≤
        (‖u‖ * ‖F‖) * (‖u‖ * ‖x - y‖) := by
      rw [norm_mul, norm_star]
      exact mul_le_mul hF hu (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    calc
      ‖@inner ℂ H _ (x - y) (koopmanIterLp M hweak.1 n F) -
          @inner ℂ H _ u F * star (@inner ℂ H _ u (x - y))‖ ≤
          ‖@inner ℂ H _ (x - y) (koopmanIterLp M hweak.1 n F)‖ +
            ‖@inner ℂ H _ u F * star (@inner ℂ H _ u (x - y))‖ :=
        norm_sub_le _ _
      _ ≤ ‖x - y‖ * ‖F‖ +
          (‖u‖ * ‖F‖) * (‖u‖ * ‖x - y‖) := add_le_add h1 h2
      _ = C * ‖x - y‖ := by dsimp [C]; ring
  · intro G hGs
    exact hfirst G hGs F

lemma strongMixing_lpCorrelations (M : System.{u})
    (hstrong : IsStrongMixing M) :
    ∀ F G : MeasureTheory.Lp ℂ 2 M.μ,
      Tendsto (fun n => @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G
          (koopmanIterLp M hstrong.1 n F)) atTop
        (nhds (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          (oneLp M hstrong.1) F *
          star (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
            (oneLp M hstrong.1) G))) := by
  let H := MeasureTheory.Lp ℂ 2 M.μ
  let u : H := oneLp M hstrong.1
  have hdense : Dense (MeasureTheory.Lp.simpleFunc ℂ 2 M.μ : Set H) :=
    MeasureTheory.Lp.simpleFunc.dense (by norm_num)
  have hfirst (G : H) (hGs : G ∈ (MeasureTheory.Lp.simpleFunc ℂ 2 M.μ : Set H)) :
      ∀ F : H, Tendsto (fun n => @inner ℂ H _ G
          (koopmanIterLp M hstrong.1 n F)) atTop
        (nhds (@inner ℂ H _ u F * star (@inner ℂ H _ u G))) := by
    let C : ℝ := ‖G‖ + ‖u‖ ^ 2 * ‖G‖
    apply tendsto_of_dense_of_uniform_dist hdense
      (fun n F => @inner ℂ H _ G (koopmanIterLp M hstrong.1 n F))
      (fun F => @inner ℂ H _ u F * star (@inner ℂ H _ u G)) C
    · dsimp [C]
      positivity
    · intro n x y
      rw [dist_eq_norm, dist_eq_norm]
      have hinner : @inner ℂ H _ G (koopmanIterLp M hstrong.1 n x) -
          @inner ℂ H _ G (koopmanIterLp M hstrong.1 n y) =
          @inner ℂ H _ G (koopmanIterLp M hstrong.1 n (x - y)) := by
        rw [map_sub]
        exact (inner_sub_right G _ _).symm
      rw [hinner]
      calc
        ‖@inner ℂ H _ G (koopmanIterLp M hstrong.1 n (x - y))‖ ≤
            ‖G‖ * ‖koopmanIterLp M hstrong.1 n (x - y)‖ :=
          norm_inner_le_norm _ _
        _ = ‖G‖ * ‖x - y‖ := by
          rw [LinearIsometry.norm_map]
        _ ≤ C * ‖x - y‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          dsimp [C]
          exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (norm_nonneg _))
    · intro x y
      rw [dist_eq_norm, dist_eq_norm]
      have hone : ‖@inner ℂ H _ u (x - y)‖ ≤ ‖u‖ * ‖x - y‖ :=
        norm_inner_le_norm u (x - y)
      have hG : ‖@inner ℂ H _ u G‖ ≤ ‖u‖ * ‖G‖ :=
        norm_inner_le_norm u G
      calc
        ‖@inner ℂ H _ u x * star (@inner ℂ H _ u G) -
            @inner ℂ H _ u y * star (@inner ℂ H _ u G)‖ =
            ‖@inner ℂ H _ u (x - y)‖ * ‖@inner ℂ H _ u G‖ := by
              rw [← sub_mul, inner_sub_right, norm_mul, norm_star]
        _ ≤ (‖u‖ * ‖x - y‖) * (‖u‖ * ‖G‖) :=
          mul_le_mul hone hG (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ C * ‖x - y‖ := by
          dsimp [C]
          nlinarith [norm_nonneg G, norm_nonneg u, norm_nonneg (x - y)]
    · intro F hFs
      let Fs : MeasureTheory.Lp.simpleFunc ℂ 2 M.μ := ⟨F, hFs⟩
      let Gs : MeasureTheory.Lp.simpleFunc ℂ 2 M.μ := ⟨G, hGs⟩
      simpa [H, u, Fs, Gs] using strongMixing_simpleLpCorrelations M hstrong Fs Gs
  intro F
  let C : ℝ := ‖F‖ + ‖u‖ ^ 2 * ‖F‖
  apply tendsto_of_dense_of_uniform_dist hdense
    (fun n G => @inner ℂ H _ G (koopmanIterLp M hstrong.1 n F))
    (fun G => @inner ℂ H _ u F * star (@inner ℂ H _ u G)) C
  · dsimp [C]
    positivity
  · intro n x y
    rw [dist_eq_norm, dist_eq_norm]
    have hinner : @inner ℂ H _ x (koopmanIterLp M hstrong.1 n F) -
        @inner ℂ H _ y (koopmanIterLp M hstrong.1 n F) =
        @inner ℂ H _ (x - y) (koopmanIterLp M hstrong.1 n F) := by
      exact (inner_sub_left x y _).symm
    rw [hinner]
    calc
      ‖@inner ℂ H _ (x - y) (koopmanIterLp M hstrong.1 n F)‖ ≤
          ‖x - y‖ * ‖koopmanIterLp M hstrong.1 n F‖ := norm_inner_le_norm _ _
      _ = ‖x - y‖ * ‖F‖ := by rw [LinearIsometry.norm_map]
      _ ≤ C * ‖x - y‖ := by
        rw [mul_comm]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        dsimp [C]
        exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (norm_nonneg _))
  · intro x y
    rw [dist_eq_norm, dist_eq_norm]
    have hF : ‖@inner ℂ H _ u F‖ ≤ ‖u‖ * ‖F‖ :=
      norm_inner_le_norm u F
    have hone : ‖@inner ℂ H _ u (x - y)‖ ≤ ‖u‖ * ‖x - y‖ :=
      norm_inner_le_norm u (x - y)
    calc
      ‖@inner ℂ H _ u F * star (@inner ℂ H _ u x) -
          @inner ℂ H _ u F * star (@inner ℂ H _ u y)‖ =
          ‖@inner ℂ H _ u F‖ * ‖@inner ℂ H _ u (x - y)‖ := by
            rw [← mul_sub, norm_mul]
            congr 1
            calc
              ‖star (@inner ℂ H _ u x) - star (@inner ℂ H _ u y)‖ =
                  ‖@inner ℂ H _ u x - @inner ℂ H _ u y‖ := by
                rw [← star_sub, norm_star]
              _ = ‖@inner ℂ H _ u (x - y)‖ := by rw [inner_sub_right]
      _ ≤ (‖u‖ * ‖F‖) * (‖u‖ * ‖x - y‖) :=
        mul_le_mul hF hone (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ C * ‖x - y‖ := by
        dsimp [C]
        nlinarith [norm_nonneg F, norm_nonneg u, norm_nonneg (x - y)]
  · intro G hGs
    exact hfirst G hGs F

/-- Strong mixing implies convergence of correlations for arbitrary `L²`
functions, in the raw-function formulation used in Theorem 2.4.8. -/
lemma strongMixing_functionCorrelations (M : System.{u})
    (hstrong : IsStrongMixing M)
    (f g : M.X → ℂ) (hf : M.lpMember 2 f) (hg : M.lpMember 2 g) :
    Tendsto (fun n => functionCorrelation M f g n) atTop
      (nhds (productOfMeans M f g)) := by
  have h := strongMixing_lpCorrelations M hstrong (hf.toLp f) (hg.toLp g)
  have hfint :
      (∫ x, (hf.toLp f : MeasureTheory.Lp ℂ 2 M.μ) x ∂M.μ) =
        ∫ x, f x ∂M.μ :=
    MeasureTheory.integral_congr_ae hf.coeFn_toLp
  have hgint :
      (∫ x, (hg.toLp g : MeasureTheory.Lp ℂ 2 M.μ) x ∂M.μ) =
        ∫ x, g x ∂M.μ :=
    MeasureTheory.integral_congr_ae hg.coeFn_toLp
  convert h using 1
  · funext n
    rw [koopmanIterLp_apply_toLp]
    exact functionCorrelation_eq_innerLp M hstrong.1 f g hf hg n
  · rw [← integral_eq_inner_oneLp, ← integral_eq_inner_oneLp,
      hfint, hgint]
    rfl

lemma weakMixing_functionCorrelations (M : System.{u})
    (hweak : IsWeakMixing M)
    (f g : M.X → ℂ) (hf : M.lpMember 2 f) (hg : M.lpMember 2 g) :
    cesaroTendsTo
      (fun n => ‖functionCorrelation M f g n - productOfMeans M f g‖) 0 := by
  have h := weakMixing_lpCorrelations M hweak (hf.toLp f) (hg.toLp g)
  have hcorr (n : ℕ) :
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (hg.toLp g)
          (koopmanIterLp M hweak.1 n (hf.toLp f)) =
        functionCorrelation M f g n := by
    rw [koopmanIterLp_apply_toLp]
    exact (functionCorrelation_eq_innerLp M hweak.1 f g hf hg n).symm
  have hfint :
      (∫ x, (hf.toLp f : MeasureTheory.Lp ℂ 2 M.μ) x ∂M.μ) =
        ∫ x, f x ∂M.μ := MeasureTheory.integral_congr_ae hf.coeFn_toLp
  have hgint :
      (∫ x, (hg.toLp g : MeasureTheory.Lp ℂ 2 M.μ) x ∂M.μ) =
        ∫ x, g x ∂M.μ := MeasureTheory.integral_congr_ae hg.coeFn_toLp
  have hprod :
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (oneLp M hweak.1) (hf.toLp f) *
          star (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
            (oneLp M hweak.1) (hg.toLp g)) = productOfMeans M f g := by
    rw [← integral_eq_inner_oneLp, ← integral_eq_inner_oneLp, hfint, hgint]
    rfl
  simpa only [hcorr, hprod] using h

lemma weakMixing_iff_functionCorrelations (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    IsWeakMixing M ↔
      ∀ f g : M.X → ℂ, M.lpMember 2 f → M.lpMember 2 g →
        cesaroTendsTo
          (fun n => ‖functionCorrelation M f g n - productOfMeans M f g‖) 0 := by
  constructor
  · intro hweak f g hf hg
    exact weakMixing_functionCorrelations M hweak f g hf hg
  · intro hfun
    refine ⟨hM, ?_⟩
    intro A B hA hB
    have h := hfun (indicatorComplex B) (indicatorComplex A)
      (indicatorComplex_memLp M hM B hB 2)
      (indicatorComplex_memLp M hM A hA 2)
    simp only [functionCorrelation_indicator M hM A B hA hB,
      productOfMeans_indicator M A B hA hB] at h
    rw [show (fun n =>
        ‖(correlation M A B n : ℂ) - (productMeasureValue M A B : ℂ)‖) =
        fun n => |correlation M A B n - productMeasureValue M A B| by
      funext n
      rw [show (correlation M A B n : ℂ) - (productMeasureValue M A B : ℂ) =
          ((correlation M A B n - productMeasureValue M A B : ℝ) : ℂ) by
        push_cast
        rfl]
      rw [Complex.norm_real, Real.norm_eq_abs]] at h
    exact h

lemma strongMixing_iff_functionCorrelations (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    IsStrongMixing M ↔
      ∀ f g : M.X → ℂ, M.lpMember 2 f → M.lpMember 2 g →
        Tendsto (fun n => functionCorrelation M f g n) atTop
          (nhds (productOfMeans M f g)) := by
  constructor
  · intro hstrong f g hf hg
    exact strongMixing_functionCorrelations M hstrong f g hf hg
  · intro hfun
    refine ⟨hM, ?_⟩
    intro A B hA hB
    have h := hfun (indicatorComplex B) (indicatorComplex A)
      (indicatorComplex_memLp M hM B hB 2)
      (indicatorComplex_memLp M hM A hA 2)
    have hre := Complex.continuous_re.continuousAt.tendsto.comp h
    simpa [seqTendsTo, functionCorrelation_indicator M hM A B hA hB,
      productOfMeans_indicator M A B hA hB] using hre

lemma cesaroCorrelation_eq_re_integral_ergodicAverage (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) (N : ℕ) :
    cesaroAverage (fun n => correlation M A B n) N =
      (∫ x, ergodicAverage M (indicatorComplex B) (N + 1) x *
        star (indicatorComplex A x) ∂M.μ).re := by
  classical
  let k := N + 1
  have hk : k ≠ 0 := by omega
  have hA2 := indicatorComplex_memLp M hM A hA 2
  have hB2 := indicatorComplex_memLp M hM B hB 2
  have hcomplex :
      ∫ x, ergodicAverage M (indicatorComplex B) k x *
          star (indicatorComplex A x) ∂M.μ =
        (k : ℂ)⁻¹ * ∑ i ∈ Finset.range k,
          functionCorrelation M (indicatorComplex B) (indicatorComplex A) i := by
    unfold ergodicAverage functionCorrelation
    simp only [hk, if_false]
    simp_rw [mul_assoc, Finset.sum_mul]
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_finset_sum]
    intro i hi
    exact (hB2.comp_measurePreserving (hM.2.iterate i)).integrable_mul hA2.star
  unfold cesaroAverage
  change ((k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, correlation M A B i) = _
  rw [hcomplex]
  simp_rw [correlation_eq_re_functionCorrelation_indicator M hM A B hA hB]
  rw [show (k : ℂ)⁻¹ = (((k : ℝ)⁻¹ : ℝ) : ℂ) by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.re_sum]

lemma tendsto_toLp_of_tendsto_eLpNorm_sub {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X)
    (f : ℕ → X → ℂ) (g : X → ℂ)
    (hf : ∀ n, MeasureTheory.MemLp (f n) 2 μ)
    (hg : MeasureTheory.MemLp g 2 μ)
    (h : Tendsto (fun n => MeasureTheory.eLpNorm (f n - g) 2 μ)
      atTop (nhds 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (nhds (hg.toLp g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp h
  convert hreal using 1
  funext n
  change ‖(hf n).toLp (f n) - hg.toLp g‖ =
    (MeasureTheory.eLpNorm (f n - g) 2 μ).toReal
  rw [← MeasureTheory.Lp.norm_toLp _ ((hf n).sub hg),
    MeasureTheory.MemLp.toLp_sub]

lemma preimageIter_ae_eq_self_of_symmDiff_zero (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (A : Set M.X)
    (hnull : M.μ (Chapter00.symmDiff (M.T ⁻¹' A) A) = 0) (n : ℕ) :
    preimageIter M n A =ᵐ[M.μ] A := by
  have hstep : M.T ⁻¹' A =ᵐ[M.μ] A := by
    rw [← MeasureTheory.measure_symmDiff_eq_zero_iff]
    simpa [Chapter00.symmDiff, Set.symmDiff_def] using hnull
  induction n with
  | zero => simp [preimageIter, Chapter01.iterateMap]
  | succ n ih =>
      have hpre := hM.2.quasiMeasurePreserving.ae_eq_comp ih
      exact (by
        simpa only [preimageIter, Chapter01.iterateMap, Set.preimage_preimage,
          Function.iterate_succ_apply] using hpre.trans hstep)

lemma correlation_self_of_invariant (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (A : Set M.X)
    (hnull : M.μ (Chapter00.symmDiff (M.T ⁻¹' A) A) = 0) (n : ℕ) :
    correlation M A A n = realMeasure M A := by
  unfold correlation
  apply congrArg ENNReal.toReal
  apply MeasureTheory.measure_congr
  filter_upwards [preimageIter_ae_eq_self_of_symmDiff_zero M hM A hnull n] with x hx
  change (x ∈ preimageIter M n A) = (x ∈ A) at hx
  change (x ∈ A ∧ x ∈ preimageIter M n A) = (x ∈ A)
  rw [hx]
  simp

lemma cesaroCorrelation_self_of_invariant (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (A : Set M.X)
    (hnull : M.μ (Chapter00.symmDiff (M.T ⁻¹' A) A) = 0) :
    cesaroTendsTo (fun n => correlation M A A n) (realMeasure M A) := by
  unfold cesaroTendsTo seqTendsTo
  convert tendsto_const_nhds using 1
  funext N
  simp only [cesaroAverage, correlation_self_of_invariant M hM A hnull,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

set_option synthInstance.maxHeartbeats 300000 in
lemma ergodic_cesaroCorrelations (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (hErg : IsErgodic M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    cesaroTendsTo (fun n => correlation M A B n) (productMeasureValue M A B) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let a := indicatorComplex A
  let b := indicatorComplex B
  have ha2 := indicatorComplex_memLp M hM A hA 2
  have hb2 := indicatorComplex_memLp M hM B hB 2
  obtain ⟨bstar, hbstar2, hbstarInv, hconv, hbce, hbint, hbconst⟩ :=
    MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM b hb2
  have hconst := hbconst hErg
  let havg (n : ℕ) := ErgodicAverageLp.ergodicAverage_memLp M hM 2 b hb2 n
  let H (n : ℕ) : MeasureTheory.Lp ℂ 2 M.μ :=
    (havg n).toLp (ergodicAverage M b n)
  let G : MeasureTheory.Lp ℂ 2 M.μ := hbstar2.toLp bstar
  let A₂ : MeasureTheory.Lp ℂ 2 M.μ := ha2.toLp a
  have hHG : Tendsto H atTop (nhds G) := by
    exact tendsto_toLp_of_tendsto_eLpNorm_sub M.μ
      (fun n => ergodicAverage M b n) bstar havg hbstar2 hconv
  have hinner : Tendsto (fun n => @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ A₂ (H n))
      atTop (nhds (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ A₂ G)) :=
    tendsto_const_nhds.inner hHG
  have hre := Complex.continuous_re.continuousAt.tendsto.comp
    (hinner.comp (tendsto_add_atTop_nat 1))
  have hinner_avg (n : ℕ) :
      (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ A₂ (H n)) =
        ∫ x, ergodicAverage M b n x * star (a x) ∂M.μ := by
    rw [MeasureTheory.L2.inner_def]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ha2.coeFn_toLp, (havg n).coeFn_toLp] with x hax hnx
    rw [RCLike.inner_apply]
    rw [hax, hnx]
    simp [a]
  have hinner_lim :
      (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ A₂ G).re =
        productMeasureValue M A B := by
    rw [MeasureTheory.L2.inner_def]
    have hGcoe := hbstar2.coeFn_toLp
    have hconst' : bstar =ᵐ[M.μ] fun _ => (realMeasure M B : ℂ) := by
      convert hconst using 1
      rw [integral_indicatorComplex M B hB]
    have heqint : (fun x => @inner ℂ ℂ _ (⇑A₂ x) (⇑G x)) =ᵐ[M.μ]
        fun x => (realMeasure M B : ℂ) * a x := by
      filter_upwards [ha2.coeFn_toLp, hGcoe, hconst'] with x hax hgx hcx
      rw [RCLike.inner_apply]
      rw [hax, hgx, hcx]
      by_cases hxA : x ∈ A <;> simp [a, indicatorComplex, Set.indicator, hxA]
    rw [MeasureTheory.integral_congr_ae heqint]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_indicatorComplex M A hA]
    simp [productMeasureValue, mul_comm]
  unfold cesaroTendsTo seqTendsTo
  convert hre using 1
  · funext N
    rw [cesaroCorrelation_eq_re_integral_ergodicAverage M hM A B hA hB]
    exact congrArg Complex.re (hinner_avg (N + 1)).symm
  · exact congrArg nhds hinner_lim.symm

/-- In an ergodic probability-preserving system, Cesàro averages of arbitrary
`L²` correlations converge to the product of the two means. -/
lemma ergodic_cesaroFunctionCorrelations (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (hErg : IsErgodic M)
    (f g : M.X → ℂ) (hf : M.lpMember 2 f) (hg : M.lpMember 2 g) :
    Tendsto (fun N : ℕ => if N = 0 then 0 else
      ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N, functionCorrelation M f g n)
      atTop (nhds (productOfMeans M f g)) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  obtain ⟨fstar, hfstar, _hinv, hconv, _hce, _hint, hconst⟩ :=
    MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM f hf
  have hconst' : fstar =ᵐ[M.μ] fun _ => ∫ x, f x ∂M.μ := hconst hErg
  let havg (n : ℕ) := ErgodicAverageLp.ergodicAverage_memLp M hM 2 f hf n
  let H (n : ℕ) : MeasureTheory.Lp ℂ 2 M.μ :=
    (havg n).toLp (ergodicAverage M f n)
  let Fstar : MeasureTheory.Lp ℂ 2 M.μ := hfstar.toLp fstar
  let G : MeasureTheory.Lp ℂ 2 M.μ := hg.toLp g
  have hHF : Tendsto H atTop (nhds Fstar) :=
    tendsto_toLp_of_tendsto_eLpNorm_sub M.μ
      (fun n => ergodicAverage M f n) fstar havg hfstar hconv
  have hinner : Tendsto
      (fun n => @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G (H n)) atTop
      (nhds (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G Fstar)) :=
    tendsto_const_nhds.inner hHF
  have hinner_avg (N : ℕ) :
      (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G (H N)) =
        if N = 0 then 0 else
          ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
            functionCorrelation M f g n := by
    rw [MeasureTheory.L2.inner_def]
    have hcoeG := hg.coeFn_toLp
    have hcoeH := (havg N).coeFn_toLp
    have hfun : (fun x => @inner ℂ ℂ _ (G x) (H N x)) =ᵐ[M.μ]
        fun x => ergodicAverage M f N x * star (g x) := by
      filter_upwards [hcoeG, hcoeH] with x hgx hHx
      simp only [RCLike.inner_apply, starRingEnd_apply]
      rw [hgx, hHx]
    rw [MeasureTheory.integral_congr_ae hfun]
    unfold ergodicAverage functionCorrelation
    by_cases hN : N = 0
    · simp [hN]
    · simp only [hN, if_false]
      simp_rw [mul_assoc, Finset.sum_mul]
      rw [MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_finset_sum]
      intro n hn
      exact (hf.comp_measurePreserving (hM.2.iterate n)).integrable_mul hg.star
  have hinner_lim :
      (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G Fstar) =
        productOfMeans M f g := by
    rw [MeasureTheory.L2.inner_def]
    have hcoeG := hg.coeFn_toLp
    have hcoeF := hfstar.coeFn_toLp
    calc
      ∫ x, @inner ℂ ℂ _ (G x) (Fstar x) ∂M.μ =
          ∫ x, (∫ y, f y ∂M.μ) * star (g x) ∂M.μ := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [hcoeG, hcoeF, hconst'] with x hgx hfx hcx
            simp only [RCLike.inner_apply, starRingEnd_apply]
            rw [hgx, hfx, hcx]
      _ = (∫ y, f y ∂M.μ) * ∫ x, star (g x) ∂M.μ := by
            rw [MeasureTheory.integral_const_mul]
      _ = productOfMeans M f g := by
            change (∫ y, f y ∂M.μ) * (∫ x, conj (g x) ∂M.μ) =
              productOfMeans M f g
            rw [integral_conj]
            rfl
  convert hinner using 1
  · funext N
    exact (hinner_avg N).symm
  · exact congrArg nhds hinner_lim.symm

lemma cesaroCorrelation_eq_re_cesaroFunctionCorrelation (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) (N : ℕ) :
    cesaroAverage (fun n => correlation M A B n) N =
      (((N + 1 : ℕ) : ℂ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
        functionCorrelation M (indicatorComplex B) (indicatorComplex A) n).re := by
  let k := N + 1
  unfold cesaroAverage
  change ((k : ℝ)⁻¹ * ∑ n ∈ Finset.range k, correlation M A B n) =
    (((k : ℕ) : ℂ)⁻¹ * ∑ n ∈ Finset.range k,
      functionCorrelation M (indicatorComplex B) (indicatorComplex A) n).re
  simp_rw [correlation_eq_re_functionCorrelation_indicator M hM A B hA hB]
  rw [show ((k : ℂ)⁻¹ = (((k : ℝ)⁻¹ : ℝ) : ℂ)) by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [Complex.re_sum]

lemma ergodic_iff_cesaroFunctionCorrelations (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    IsErgodic M ↔
      ∀ f g : M.X → ℂ, M.lpMember 2 f → M.lpMember 2 g →
        Tendsto (fun N : ℕ => if N = 0 then 0 else
          ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N, functionCorrelation M f g n)
          atTop (nhds (productOfMeans M f g)) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  constructor
  · intro hErg f g hf hg
    exact ergodic_cesaroFunctionCorrelations M hM hErg f g hf hg
  · intro hcorr
    refine ⟨hM, ?_⟩
    intro A hA hnull
    let f := indicatorComplex A
    let g := indicatorComplex A
    have hf := indicatorComplex_memLp M hM A hA 2
    have hg := indicatorComplex_memLp M hM A hA 2
    have hc := hcorr f g hf hg
    have hc' := hc.comp (tendsto_add_atTop_nat 1)
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hc'
    have hprod : Tendsto (fun N => cesaroAverage
        (fun n => correlation M A A n) N) atTop
        (nhds (productMeasureValue M A A)) := by
      convert hre using 1
      · funext N
        rw [cesaroCorrelation_eq_re_cesaroFunctionCorrelation M hM A A hA hA]
        simp [f, g]
      · dsimp [f, g]
        unfold productOfMeans
        rw [integral_indicatorComplex M A hA]
        simp [productMeasureValue]
    have hself := cesaroCorrelation_self_of_invariant M hM A hnull
    have heq : realMeasure M A = productMeasureValue M A A :=
      tendsto_nhds_unique hself hprod
    have hidem : realMeasure M A * (realMeasure M A - 1) = 0 := by
      unfold productMeasureValue at heq
      nlinarith
    rcases mul_eq_zero.mp hidem with hzero | hone
    · left
      apply (ENNReal.toReal_eq_toReal_iff' (by simp : M.μ A ≠ ⊤)
        (by simp : (0 : ENNReal) ≠ ⊤)).mp
      simpa [realMeasure] using hzero
    · right
      have hrealone : realMeasure M A = 1 := by nlinarith
      apply (ENNReal.toReal_eq_toReal_iff' (by simp : M.μ A ≠ ⊤)
        (by simp : (1 : ENNReal) ≠ ⊤)).mp
      simpa [realMeasure] using hrealone

end CorrelationMean
end Chapter02
