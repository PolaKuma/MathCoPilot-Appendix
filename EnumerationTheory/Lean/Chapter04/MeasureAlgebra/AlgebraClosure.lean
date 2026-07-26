import Chapter04.MeasureAlgebra.LinfClosure

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter04.AlgebraClosure

universe u v

open LinfClosure

private theorem tendsto_eLpNorm_of_le_add
    {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (F : ℕ → X → ℂ) (a b : ℕ → ENNReal)
    (hle : ∀ n, eLpNorm (F n) 2 μ ≤ a n + b n)
    (ha : Tendsto a atTop (nhds 0))
    (hb : Tendsto b atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 μ) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n => eLpNorm (F n) 2 μ)
    (g := fun _ => 0) (h := fun n => a n + b n)
    tendsto_const_nhds (by simpa using ha.add hb)
  · exact Eventually.of_forall fun _ => bot_le
  · exact Eventually.of_forall hle

set_option maxHeartbeats 1600000 in
/-- The raw L² map induced by a probability measure-algebra isomorphism
preserves products of essentially bounded functions. -/
theorem rawLtwoMap_mul
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f g : Q.X → ℂ) (hf : MemLp f ⊤ Q.μ) (hg : MemLp g ⊤ Q.μ) :
    MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ
        (fun y => f y * g y) =ᵐ[P.μ]
      fun x =>
        MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ f x *
          MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ g x := by
  letI : IsProbabilityMeasure P.μ := hP
  letI : IsProbabilityMeasure Q.μ := hQ
  let W : (Q.X → ℂ) → P.X → ℂ :=
    MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ
  obtain ⟨f₀, C, hC, hfmeas, hff₀, hfC⟩ :=
    exists_bounded_measurable_representative Q.μ hf
  obtain ⟨g₀, D, hD, hgmeas, hgg₀, hgD⟩ :=
    exists_bounded_measurable_representative Q.μ hg
  have hf₀Top : MemLp f₀ ⊤ Q.μ := (memLp_congr_ae hff₀).mp hf
  have hg₀Top : MemLp g₀ ⊤ Q.μ := (memLp_congr_ae hgg₀).mp hg
  have hf₀Two : MemLp f₀ 2 Q.μ := hf₀Top.mono_exponent (by simp)
  have hg₀Two : MemLp g₀ 2 Q.μ := hg₀Top.mono_exponent (by simp)
  have hprodTop : MemLp (fun y => f₀ y * g₀ y) ⊤ Q.μ :=
    by simpa only [Pi.mul_apply] using hg₀Top.mul hf₀Top
  have hprodTwo : MemLp (fun y => f₀ y * g₀ y) 2 Q.μ :=
    hprodTop.mono_exponent (by simp)
  let s : ℕ → SimpleFunc Q.X ℂ := fun n =>
    SimpleFunc.approxOn f₀ hfmeas (Set.range f₀ ∪ {0}) 0 (by simp) n
  let t : ℕ → SimpleFunc Q.X ℂ := fun n =>
    SimpleFunc.approxOn g₀ hgmeas (Set.range g₀ ∪ {0}) 0 (by simp) n
  have hsTop : ∀ n, MemLp (s n) ⊤ Q.μ :=
    fun n => (s n).memLp_top Q.μ
  have htTop : ∀ n, MemLp (t n) ⊤ Q.μ :=
    fun n => (t n).memLp_top Q.μ
  have hsTwo : ∀ n, MemLp (s n) 2 Q.μ :=
    fun n => (hsTop n).mono_exponent (by simp)
  have htTwo : ∀ n, MemLp (t n) 2 Q.μ :=
    fun n => (htTop n).mono_exponent (by simp)
  have hstTop : ∀ n, MemLp (fun y => s n y * t n y) ⊤ Q.μ :=
    fun n => by
      simpa only [Pi.mul_apply] using (htTop n).mul (hsTop n)
  have hstTwo : ∀ n, MemLp (fun y => s n y * t n y) 2 Q.μ :=
    fun n => (hstTop n).mono_exponent (by simp)
  have hsBound : ∀ n y, ‖s n y‖ ≤ C :=
    fun n y => approx_bound f₀ hfmeas C hfC n y
  have htBound : ∀ n y, ‖t n y‖ ≤ D :=
    fun n y => approx_bound g₀ hgmeas D hgD n y
  have hsConv : Tendsto
      (fun n => eLpNorm (fun y => s n y - f₀ y) 2 Q.μ)
      atTop (nhds 0) := by
    simpa only [Pi.sub_apply] using
      (SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm
        (p := (2 : ENNReal)) (by norm_num) hfmeas hf₀Two.2)
  have htConv : Tendsto
      (fun n => eLpNorm (fun y => t n y - g₀ y) 2 Q.μ)
      atTop (nhds 0) := by
    simpa only [Pi.sub_apply] using
      (SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm
        (p := (2 : ENNReal)) (by norm_num) hgmeas hg₀Two.2)
  have hsourceProdConv : Tendsto
      (fun n => eLpNorm
        (fun y => s n y * t n y - f₀ y * g₀ y) 2 Q.μ)
      atTop (nhds 0) := by
    have hleft := tendsto_eLpNorm_mul_zero_of_uniform_bound
      Q.μ 2 (fun n y => s n y) (fun n y => t n y - g₀ y)
      C hC (fun n => Eventually.of_forall (hsBound n)) htConv
    have hright := tendsto_eLpNorm_mul_zero_of_uniform_bound
      Q.μ 2 (fun _ y => g₀ y) (fun n y => s n y - f₀ y)
      D hD (fun _ => Eventually.of_forall hgD) hsConv
    apply tendsto_eLpNorm_of_le_add Q.μ
      (fun n y => s n y * t n y - f₀ y * g₀ y)
      (fun n => eLpNorm (fun y => s n y * (t n y - g₀ y)) 2 Q.μ)
      (fun n => eLpNorm (fun y => g₀ y * (s n y - f₀ y)) 2 Q.μ)
      _ hleft hright
    intro n
    change eLpNorm (fun y => s n y * t n y - f₀ y * g₀ y) 2 Q.μ ≤
      eLpNorm (fun y => s n y * (t n y - g₀ y)) 2 Q.μ +
        eLpNorm (fun y => g₀ y * (s n y - f₀ y)) 2 Q.μ
    rw [show (fun y => s n y * t n y - f₀ y * g₀ y) =
        fun y => s n y * (t n y - g₀ y) +
          g₀ y * (s n y - f₀ y) by
      funext y
      ring]
    exact eLpNorm_add_le
      ((hsTop n).1.mul ((htTop n).sub hg₀Top).1)
      (hg₀Top.1.mul ((hsTop n).sub hf₀Top).1) (by norm_num)
  have hWsBound : ∀ n, ∀ᵐ x ∂P.μ, ‖W (s n) x‖ ≤ C :=
    fun n => rawLtwoMap_simple_bound P Q hP hQ Φ hΦ
      (s n) (hsTwo n) C (hsBound n)
  have hWgTop : MemLp (W g₀) ⊤ P.μ :=
    rawLtwoMap_memLp_top P Q hP hQ Φ hΦ g₀ hg₀Top
  have hWfTop : MemLp (W f₀) ⊤ P.μ :=
    rawLtwoMap_memLp_top P Q hP hQ Φ hΦ f₀ hf₀Top
  obtain ⟨wg, E, hE, _hwgmeas, hWgwg, hwgE⟩ :=
    exists_bounded_measurable_representative P.μ hWgTop
  have hWgBound : ∀ᵐ x ∂P.μ, ‖W g₀ x‖ ≤ E := by
    filter_upwards [hWgwg] with x hx
    rw [hx]
    exact hwgE x
  have hWsConv : Tendsto
      (fun n => eLpNorm (fun x => W (s n) x - W f₀ x) 2 P.μ)
      atTop (nhds 0) := by
    apply hsConv.congr'
    exact Eventually.of_forall fun n =>
      (rawLtwoMap_sub_eLpNorm
        P Q hP hQ Φ hΦ (s n) f₀ (hsTwo n) hf₀Two).symm
  have hWtConv : Tendsto
      (fun n => eLpNorm (fun x => W (t n) x - W g₀ x) 2 P.μ)
      atTop (nhds 0) := by
    apply htConv.congr'
    exact Eventually.of_forall fun n =>
      (rawLtwoMap_sub_eLpNorm
        P Q hP hQ Φ hΦ (t n) g₀ (htTwo n) hg₀Two).symm
  have htargetProdConv : Tendsto
      (fun n => eLpNorm
        (fun x => W (s n) x * W (t n) x - W f₀ x * W g₀ x)
        2 P.μ) atTop (nhds 0) := by
    have hleft := tendsto_eLpNorm_mul_zero_of_uniform_bound
      P.μ 2 (fun n x => W (s n) x)
      (fun n x => W (t n) x - W g₀ x)
      C hC hWsBound hWtConv
    have hright := tendsto_eLpNorm_mul_zero_of_uniform_bound
      P.μ 2 (fun _ x => W g₀ x)
      (fun n x => W (s n) x - W f₀ x)
      E hE (fun _ => hWgBound) hWsConv
    apply tendsto_eLpNorm_of_le_add P.μ
      (fun n x => W (s n) x * W (t n) x - W f₀ x * W g₀ x)
      (fun n => eLpNorm
        (fun x => W (s n) x * (W (t n) x - W g₀ x)) 2 P.μ)
      (fun n => eLpNorm
        (fun x => W g₀ x * (W (s n) x - W f₀ x)) 2 P.μ)
      _ hleft hright
    intro n
    change eLpNorm
        (fun x => W (s n) x * W (t n) x - W f₀ x * W g₀ x)
        2 P.μ ≤
      eLpNorm (fun x => W (s n) x * (W (t n) x - W g₀ x))
          2 P.μ +
        eLpNorm (fun x => W g₀ x * (W (s n) x - W f₀ x))
          2 P.μ
    rw [show
        (fun x => W (s n) x * W (t n) x - W f₀ x * W g₀ x) =
          fun x => W (s n) x * (W (t n) x - W g₀ x) +
            W g₀ x * (W (s n) x - W f₀ x) by
      funext x
      ring]
    exact eLpNorm_add_le
      ((MeasureAlgebraLtwo.rawLtwoMap_ltwo
          P Q hP hQ Φ hΦ (s n) (hsTwo n)).1.1.mul
        (((MeasureAlgebraLtwo.rawLtwoMap_ltwo
          P Q hP hQ Φ hΦ (t n) (htTwo n)).1.sub
        (MeasureAlgebraLtwo.rawLtwoMap_ltwo
          P Q hP hQ Φ hΦ g₀ hg₀Two).1).1))
      (hWgTop.1.mul
        (((MeasureAlgebraLtwo.rawLtwoMap_ltwo
          P Q hP hQ Φ hΦ (s n) (hsTwo n)).1.sub
        (MeasureAlgebraLtwo.rawLtwoMap_ltwo
          P Q hP hQ Φ hΦ f₀ hf₀Two).1).1)) (by norm_num)
  have hWstConv : Tendsto
      (fun n => eLpNorm
        (fun x => W (fun y => s n y * t n y) x -
          W (fun y => f₀ y * g₀ y) x) 2 P.μ)
      atTop (nhds 0) := by
    apply hsourceProdConv.congr'
    exact Eventually.of_forall fun n =>
      (rawLtwoMap_sub_eLpNorm
        P Q hP hQ Φ hΦ
          (fun y => s n y * t n y) (fun y => f₀ y * g₀ y)
          (hstTwo n) hprodTwo).symm
  have hmiddle (n : ℕ) :
      W (fun y => s n y * t n y) =ᵐ[P.μ]
        fun x => W (s n) x * W (t n) x :=
    MeasureAlgebraLtwo.rawLtwoMap_simple_mul
      P Q hP hQ Φ hΦ (s n) (t n) (hsTwo n) (htTwo n) (hstTwo n)
  have hreverse (n : ℕ) :
      eLpNorm (fun x =>
          W (fun y => f₀ y * g₀ y) x -
            W (fun y => s n y * t n y) x) 2 P.μ =
        eLpNorm (fun x =>
          W (fun y => s n y * t n y) x -
            W (fun y => f₀ y * g₀ y) x) 2 P.μ := by
    calc
      eLpNorm (fun x =>
          W (fun y => f₀ y * g₀ y) x -
            W (fun y => s n y * t n y) x) 2 P.μ =
          eLpNorm (-(fun x =>
            W (fun y => s n y * t n y) x -
              W (fun y => f₀ y * g₀ y) x)) 2 P.μ := by
            congr 2
            funext x
            simp
      _ = eLpNorm (fun x =>
          W (fun y => s n y * t n y) x -
            W (fun y => f₀ y * g₀ y) x) 2 P.μ :=
        eLpNorm_neg _ _ _
  have hzero :
      eLpNorm (fun x =>
        W (fun y => f₀ y * g₀ y) x - W f₀ x * W g₀ x) 2 P.μ = 0 := by
    have hupper : Tendsto
        (fun n =>
          eLpNorm (fun x =>
            W (fun y => s n y * t n y) x -
              W (fun y => f₀ y * g₀ y) x) 2 P.μ +
          eLpNorm (fun x =>
            W (s n) x * W (t n) x - W f₀ x * W g₀ x) 2 P.μ)
        atTop (nhds 0) := by
          simpa using hWstConv.add htargetProdConv
    apply le_antisymm ?_ bot_le
    exact ge_of_tendsto hupper (Eventually.of_forall fun n => by
        have hmeasFirst : AEStronglyMeasurable
            (fun x =>
              W (fun y => f₀ y * g₀ y) x -
                W (fun y => s n y * t n y) x) P.μ :=
          ((MeasureAlgebraLtwo.rawLtwoMap_ltwo
            P Q hP hQ Φ hΦ _ hprodTwo).1.sub
           (MeasureAlgebraLtwo.rawLtwoMap_ltwo
            P Q hP hQ Φ hΦ _ (hstTwo n)).1).1
        have hWsTop : MemLp (W (s n)) ⊤ P.μ :=
          rawLtwoMap_memLp_top P Q hP hQ Φ hΦ (s n) (hsTop n)
        have hWtTop : MemLp (W (t n)) ⊤ P.μ :=
          rawLtwoMap_memLp_top P Q hP hQ Φ hΦ (t n) (htTop n)
        have hmeasSecond : AEStronglyMeasurable
            (fun x =>
              W (s n) x * W (t n) x - W f₀ x * W g₀ x) P.μ := by
          have h1 : MemLp (fun x => W (s n) x * W (t n) x) ⊤ P.μ := by
            simpa only [Pi.mul_apply] using hWtTop.mul hWsTop
          have h2 : MemLp (fun x => W f₀ x * W g₀ x) ⊤ P.μ := by
            simpa only [Pi.mul_apply] using hWgTop.mul hWfTop
          exact (h1.sub h2).1
        calc
          eLpNorm (fun x =>
              W (fun y => f₀ y * g₀ y) x - W f₀ x * W g₀ x) 2 P.μ =
              eLpNorm (fun x =>
                (W (fun y => f₀ y * g₀ y) x -
                  W (fun y => s n y * t n y) x) +
                (W (s n) x * W (t n) x - W f₀ x * W g₀ x))
                2 P.μ := by
                  apply eLpNorm_congr_ae
                  filter_upwards [hmiddle n] with x hx
                  rw [hx]
                  ring
          _ ≤ eLpNorm (fun x =>
                W (fun y => f₀ y * g₀ y) x -
                  W (fun y => s n y * t n y) x) 2 P.μ +
              eLpNorm (fun x =>
                W (s n) x * W (t n) x - W f₀ x * W g₀ x) 2 P.μ := by
                exact eLpNorm_add_le hmeasFirst hmeasSecond (by norm_num)
          _ = eLpNorm (fun x =>
                W (fun y => s n y * t n y) x -
                  W (fun y => f₀ y * g₀ y) x) 2 P.μ +
              eLpNorm (fun x =>
                W (s n) x * W (t n) x - W f₀ x * W g₀ x) 2 P.μ := by
                rw [hreverse n])
  have hcore :
      W (fun y => f₀ y * g₀ y) =ᵐ[P.μ]
        fun x => W f₀ x * W g₀ x := by
    have hWprodTop : MemLp (fun x => W f₀ x * W g₀ x) ⊤ P.μ := by
      simpa only [Pi.mul_apply] using hWgTop.mul hWfTop
    have hdiffTwo : MemLp (fun x =>
        W (fun y => f₀ y * g₀ y) x - W f₀ x * W g₀ x) 2 P.μ :=
      (MeasureAlgebraLtwo.rawLtwoMap_ltwo
        P Q hP hQ Φ hΦ _ hprodTwo).1.sub
          (hWprodTop.mono_exponent (by simp))
    have hz := (eLpNorm_eq_zero_iff hdiffTwo.1 (by norm_num)).1 hzero
    filter_upwards [hz] with x hx
    simpa only [Pi.zero_apply, sub_eq_zero] using hx
  have hfTwo : MemLp f 2 Q.μ := hf.mono_exponent (by simp)
  have hgTwo : MemLp g 2 Q.μ := hg.mono_exponent (by simp)
  have hprodAe :
      (fun y => f y * g y) =ᵐ[Q.μ] fun y => f₀ y * g₀ y := by
    filter_upwards [hff₀, hgg₀] with y hfy hgy
    rw [hfy, hgy]
  have hfgTwo : MemLp (fun y => f y * g y) 2 Q.μ :=
    (memLp_congr_ae hprodAe).mpr hprodTwo
  filter_upwards
    [MeasureAlgebraLtwo.rawLtwoMap_ae
      P Q hP hQ Φ hΦ _ _ hfgTwo hprodTwo hprodAe,
     MeasureAlgebraLtwo.rawLtwoMap_ae
      P Q hP hQ Φ hΦ f f₀ hfTwo hf₀Two hff₀,
     MeasureAlgebraLtwo.rawLtwoMap_ae
      P Q hP hQ Φ hΦ g g₀ hgTwo hg₀Two hgg₀,
     hcore]
    with x hp hfa hga hc
  rw [hp, hfa, hga]
  simpa only [W] using hc

end Chapter04.AlgebraClosure
