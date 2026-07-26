import Chapter04.MeasureAlgebra.MeasureAlgebraLtwo
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter04.LinfClosure

universe u v

/-- An essentially bounded function has a measurable representative which is
bounded at every point. -/
theorem exists_bounded_measurable_representative
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
      (measurableSet_le hmmeas.nnnorm measurable_const) hmmeas measurable_const
  have hfg : f =ᵐ[μ] g := by
    filter_upwards [hfm, hmC] with x hxeq hxC
    simp [g, hxC, hxeq]
  refine ⟨g, C, C.coe_nonneg, hgmeas, hfg, ?_⟩
  intro x
  by_cases hx : ‖m x‖₊ ≤ C
  · simp only [g, hx, if_true]
    exact_mod_cast hx
  · simp [g, hx]

/-- A uniformly almost-everywhere bounded sequence has an equally bounded
L²-limit. -/
theorem memLp_top_of_uniform_bound_of_tendsto_eLpNorm
    {X : Type u} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ]
    (F : ℕ → X → ℂ) (g : X → ℂ)
    (hF : ∀ n, MemLp (F n) 2 μ) (hg : MemLp g 2 μ)
    (C : ℝ) (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ C)
    (hconv : Tendsto
      (fun n => eLpNorm (fun x => F n x - g x) 2 μ)
      atTop (nhds 0)) :
    MemLp g ⊤ μ := by
  have hmeas : ∀ n, AEStronglyMeasurable (F n) μ :=
    fun n => (hF n).1
  have hinMeasure : TendstoInMeasure μ F atTop g := by
    apply tendstoInMeasure_of_tendsto_eLpNorm
      (p := (2 : ENNReal)) (by norm_num) hmeas hg.1
    simpa only [Pi.sub_apply] using hconv
  obtain ⟨ns, _hns, hsub⟩ := hinMeasure.exists_seq_tendsto_ae
  have hboundAll : ∀ᵐ x ∂μ, ∀ n, ‖F n x‖ ≤ C :=
    ae_all_iff.mpr hbound
  have hgbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C := by
    filter_upwards [hsub, hboundAll] with x hx hbx
    have hnorm :
        Tendsto (fun i => ‖F (ns i) x‖) atTop (nhds ‖g x‖) :=
      continuous_norm.continuousAt.tendsto.comp hx
    exact le_of_tendsto hnorm (Eventually.of_forall fun i => hbx (ns i))
  exact memLp_top_of_bound hg.1 C hgbound

/-- Multiplication by an almost-everywhere bounded scalar function is bounded
on every Lp seminorm. -/
theorem eLpNorm_mul_le_of_ae_bound
    {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (p : ENNReal) (a b : X → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) :
    eLpNorm (fun x => a x * b x) p μ ≤
      ENNReal.ofReal C * eLpNorm b p μ := by
  calc
    eLpNorm (fun x => a x * b x) p μ ≤
        eLpNorm (fun x => (C : ℂ) * b x) p μ := by
      apply eLpNorm_mono_ae
      filter_upwards [ha] with x hx
      simp only [norm_mul]
      simpa [Real.norm_eq_abs, abs_of_nonneg hC] using
        (mul_le_mul_of_nonneg_right hx (norm_nonneg (b x)))
    _ = ENNReal.ofReal C * eLpNorm b p μ := by
      change eLpNorm ((C : ℂ) • b) p μ =
        ENNReal.ofReal C * eLpNorm b p μ
      rw [eLpNorm_const_smul]
      rw [← ofReal_norm_eq_enorm]
      simp [abs_of_nonneg hC]

/-- A uniformly bounded sequence may be multiplied into an Lp-null sequence
without destroying convergence to zero. -/
theorem tendsto_eLpNorm_mul_zero_of_uniform_bound
    {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (p : ENNReal) (a b : ℕ → X → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, ∀ᵐ x ∂μ, ‖a n x‖ ≤ C)
    (hb : Tendsto (fun n => eLpNorm (b n) p μ) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (fun x => a n x * b n x) p μ)
      atTop (nhds 0) := by
  have hCtop : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hupper : Tendsto
      (fun n => ENNReal.ofReal C * eLpNorm (b n) p μ)
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hb (Or.inr hCtop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n => eLpNorm (fun x => a n x * b n x) p μ)
    (g := fun _ => 0)
    (h := fun n => ENNReal.ofReal C * eLpNorm (b n) p μ)
    tendsto_const_nhds hupper
  · exact Eventually.of_forall fun _ => bot_le
  · exact Eventually.of_forall fun n =>
      eLpNorm_mul_le_of_ae_bound μ p (a n) (b n) C hC (ha n)

theorem approx_bound
    {X : Type u} [MeasurableSpace X]
    (g : X → ℂ) (hg : Measurable g) (C : ℝ)
    (hgC : ∀ x, ‖g x‖ ≤ C) (n : ℕ) (x : X) :
    ‖SimpleFunc.approxOn g hg (Set.range g ∪ {0}) 0 (by simp) n x‖ ≤ C := by
  have hzero : (0 : ℂ) ∈ Set.range g ∪ {0} :=
    Set.mem_union_right _ (Set.mem_singleton 0)
  have hx := SimpleFunc.approxOn_mem hg hzero n x
  rcases hx with hxrange | hxzero
  · obtain ⟨y, hy⟩ := hxrange
    calc
      ‖SimpleFunc.approxOn g hg (Set.range g ∪ {0}) 0
          (by simp) n x‖ =
          ‖SimpleFunc.approxOn g hg (Set.range g ∪ {0}) 0
            hzero n x‖ := by rfl
      _ = ‖g y‖ := congrArg norm hy.symm
      _ ≤ C := hgC y
  · have hz : SimpleFunc.approxOn g hg (Set.range g ∪ {0}) 0
        (by simp) n x = 0 := Set.mem_singleton_iff.mp hxzero
    rw [hz, norm_zero]
    exact (norm_nonneg (g x)).trans (hgC x)

/-- On L², the raw map preserves the seminorm of a difference. -/
theorem rawLtwoMap_sub_eLpNorm
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f g : Q.X → ℂ) (hf : MemLp f 2 Q.μ) (hg : MemLp g 2 Q.μ) :
    eLpNorm (fun x =>
        MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ f x -
          MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ g x) 2 P.μ =
      eLpNorm (fun y => f y - g y) 2 Q.μ := by
  let W : (Q.X → ℂ) → P.X → ℂ :=
    MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ
  have hneg : MemLp (fun y => (-1 : ℂ) * g y) 2 Q.μ :=
    hg.const_mul (-1)
  have hdiff : MemLp (fun y => f y - g y) 2 Q.μ := hf.sub hg
  have hadd := MeasureAlgebraLtwo.rawLtwoMap_add
    P Q hP hQ Φ hΦ f (fun y => (-1 : ℂ) * g y) hf hneg
  have hsmul := MeasureAlgebraLtwo.rawLtwoMap_smul
    P Q hP hQ Φ hΦ (-1 : ℂ) g hg
  have hae :
      (fun x => W f x - W g x) =ᵐ[P.μ]
        W (fun y => f y - g y) := by
    filter_upwards [hadd, hsmul] with x ha hs
    change MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ f x -
          MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ g x =
        MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ
          (fun y => f y - g y) x
    calc
      MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ f x -
            MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ g x =
          MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ f x +
            MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ
              (fun y => (-1 : ℂ) * g y) x := by rw [hs]; ring
      _ = MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ
            (fun y => f y + (-1 : ℂ) * g y) x := ha.symm
      _ = MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ
            (fun y => f y - g y) x := by
          congr 2
          funext y
          ring
  calc
    eLpNorm (fun x => W f x - W g x) 2 P.μ =
        eLpNorm (W (fun y => f y - g y)) 2 P.μ :=
      eLpNorm_congr_ae hae
    _ = eLpNorm (fun y => f y - g y) 2 Q.μ :=
      (MeasureAlgebraLtwo.rawLtwoMap_ltwo
        P Q hP hQ Φ hΦ _ hdiff).2

/-- A pointwise bound on a simple function is transported by the raw L² map. -/
theorem rawLtwoMap_simple_bound
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (s : SimpleFunc Q.X ℂ) (hs : MemLp s 2 Q.μ)
    (C : ℝ) (hsC : ∀ y, ‖s y‖ ≤ C) :
    ∀ᵐ x ∂P.μ,
      ‖MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ s x‖ ≤ C := by
  have hall : ∀ᵐ x ∂P.μ, ∀ c ∈ s.range,
      x ∈ MeasureAlgebraLtwo.mappedFiber P Q Φ s c →
        MeasureAlgebraLtwo.mappedSimple P Q Φ s x = c := by
    rw [Filter.eventually_all_finset]
    intro c hc
    exact MeasureAlgebraLtwo.mappedSimple_eq_on_fiber_ae
      P Q hP hQ Φ hΦ s hc
  filter_upwards
    [MeasureAlgebraLtwo.rawLtwoMap_simple P Q hP hQ Φ hΦ s hs,
     MeasureAlgebraLtwo.mapped_fibers_cover_ae P Q hP hQ Φ hΦ s, hall]
    with x hraw hcover hx
  obtain ⟨c, hc, hxc⟩ := hcover
  obtain ⟨y, hy⟩ := SimpleFunc.mem_range.mp hc
  rw [hraw, hx c hc hxc, ← hy]
  exact hsC y

/-- The abstract L² map induced by a probability measure-algebra isomorphism
sends every essentially bounded function to an essentially bounded function. -/
theorem rawLtwoMap_memLp_top
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f : Q.X → ℂ) (hf : MemLp f ⊤ Q.μ) :
    MemLp (MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ f) ⊤ P.μ := by
  letI : IsProbabilityMeasure P.μ := hP
  letI : IsProbabilityMeasure Q.μ := hQ
  obtain ⟨g, C, hC, hgmeas, hfg, hgC⟩ :=
    exists_bounded_measurable_representative Q.μ hf
  have hgTop : MemLp g ⊤ Q.μ := (memLp_congr_ae hfg).mp hf
  have hgTwo : MemLp g 2 Q.μ := hgTop.mono_exponent (by simp)
  let s : ℕ → SimpleFunc Q.X ℂ := fun n =>
    SimpleFunc.approxOn g hgmeas (Set.range g ∪ {0}) 0 (by simp) n
  have hsTwo : ∀ n, MemLp (s n) 2 Q.μ := fun n =>
    SimpleFunc.memLp_approxOn_range hgmeas hgTwo n
  have hsBound : ∀ n x, ‖s n x‖ ≤ C :=
    fun n x => approx_bound g hgmeas C hgC n x
  have hsourceConv : Tendsto
      (fun n => eLpNorm (fun x => s n x - g x) 2 Q.μ)
      atTop (nhds 0) := by
    simpa only [Pi.sub_apply] using
      (SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm
        (p := (2 : ENNReal)) (by norm_num) hgmeas hgTwo.2)
  let W : (Q.X → ℂ) → P.X → ℂ :=
    MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ
  have hWTwo (n : ℕ) : MemLp (W (s n)) 2 P.μ :=
    (MeasureAlgebraLtwo.rawLtwoMap_ltwo
      P Q hP hQ Φ hΦ (s n) (hsTwo n)).1
  have hWgTwo : MemLp (W g) 2 P.μ :=
    (MeasureAlgebraLtwo.rawLtwoMap_ltwo
      P Q hP hQ Φ hΦ g hgTwo).1
  have hWBound : ∀ n, ∀ᵐ x ∂P.μ, ‖W (s n) x‖ ≤ C := by
    intro n
    have hall : ∀ᵐ x ∂P.μ, ∀ c ∈ (s n).range,
        x ∈ MeasureAlgebraLtwo.mappedFiber P Q Φ (s n) c →
          MeasureAlgebraLtwo.mappedSimple P Q Φ (s n) x = c := by
      rw [Filter.eventually_all_finset]
      intro c hc
      exact MeasureAlgebraLtwo.mappedSimple_eq_on_fiber_ae
        P Q hP hQ Φ hΦ (s n) hc
    filter_upwards
      [MeasureAlgebraLtwo.rawLtwoMap_simple
        P Q hP hQ Φ hΦ (s n) (hsTwo n),
       MeasureAlgebraLtwo.mapped_fibers_cover_ae
        P Q hP hQ Φ hΦ (s n), hall]
      with x hraw hcover hx
    obtain ⟨c, hc, hxc⟩ := hcover
    obtain ⟨y, hy⟩ := SimpleFunc.mem_range.mp hc
    change ‖MeasureAlgebraLtwo.rawLtwoMap
      P Q hP hQ Φ hΦ (s n) x‖ ≤ C
    rw [hraw, hx c hc hxc, ← hy]
    exact hsBound n y
  have hWConv : Tendsto
      (fun n => eLpNorm (fun x => W (s n) x - W g x) 2 P.μ)
      atTop (nhds 0) := by
    have heq : ∀ n,
        eLpNorm (fun x => W (s n) x - W g x) 2 P.μ =
          eLpNorm (fun x => s n x - g x) 2 Q.μ := by
      intro n
      have hneg : MemLp (fun y => (-1 : ℂ) * g y) 2 Q.μ :=
        hgTwo.const_mul (-1)
      have hdiff : MemLp (fun y => s n y - g y) 2 Q.μ :=
        (hsTwo n).sub hgTwo
      have hadd := MeasureAlgebraLtwo.rawLtwoMap_add
        P Q hP hQ Φ hΦ (s n) (fun y => (-1 : ℂ) * g y)
        (hsTwo n) hneg
      have hsmul := MeasureAlgebraLtwo.rawLtwoMap_smul
        P Q hP hQ Φ hΦ (-1 : ℂ) g hgTwo
      have hae :
          (fun x => W (s n) x - W g x) =ᵐ[P.μ]
            W (fun y => s n y - g y) := by
        filter_upwards [hadd, hsmul] with x ha hs
        change MeasureAlgebraLtwo.rawLtwoMap
            P Q hP hQ Φ hΦ (s n) x -
              MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ g x =
          MeasureAlgebraLtwo.rawLtwoMap
            P Q hP hQ Φ hΦ (fun y => s n y - g y) x
        calc
          MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ (s n) x -
                MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ g x =
              MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ (s n) x +
                MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ
                  (fun y => (-1 : ℂ) * g y) x := by rw [hs]; ring
          _ = MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ
                (fun y => s n y + (-1 : ℂ) * g y) x := ha.symm
          _ = MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ
                (fun y => s n y - g y) x := by
              congr 2
              funext y
              ring
      calc
        eLpNorm (fun x => W (s n) x - W g x) 2 P.μ =
            eLpNorm (W (fun y => s n y - g y)) 2 P.μ :=
          eLpNorm_congr_ae hae
        _ = eLpNorm (fun y => s n y - g y) 2 Q.μ :=
          (MeasureAlgebraLtwo.rawLtwoMap_ltwo
            P Q hP hQ Φ hΦ _ hdiff).2
    simpa only [heq] using hsourceConv
  have hWgTop : MemLp (W g) ⊤ P.μ :=
    memLp_top_of_uniform_bound_of_tendsto_eLpNorm
      P.μ (fun n => W (s n)) (W g) hWTwo hWgTwo C hWBound hWConv
  have hfTwo : MemLp f 2 Q.μ := hf.mono_exponent (by simp)
  have hraw := MeasureAlgebraLtwo.rawLtwoMap_ae
    P Q hP hQ Φ hΦ f g hfTwo hgTwo hfg
  exact (memLp_congr_ae hraw).mpr hWgTop

end Chapter04.LinfClosure
