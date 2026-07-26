import Chapter04.MeasureAlgebra.InverseLtwo

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter04.MeasureAlgebraDynamics

universe u v

open MeasureAlgebraLtwo

/-- On measurable simple functions, the L² map induced by a conjugacy
intertwines the two transformations. -/
theorem mappedSimple_comp
    (M : System.{u}) (N : System.{v})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (Φ : MeasureAlgebraHomData
      (inducedMeasureAlgebra N.toProbabilitySpace)
      (inducedMeasureAlgebra M.toProbabilitySpace))
    (hΦ : IsMeasureAlgebraIsomorphism Φ)
    (hcomm : ∀ B : (inducedMeasureAlgebraSystem N).carrier,
      (inducedMeasureAlgebraSystem M).equiv
        (Φ.map ((inducedMeasureAlgebraSystem N).transform B))
        ((inducedMeasureAlgebraSystem M).transform (Φ.map B)))
    (s : SimpleFunc N.X ℂ) :
    mappedSimple M.toProbabilitySpace N.toProbabilitySpace Φ
        (s.comp N.T hN.2.measurable) =ᵐ[M.μ]
      fun x => mappedSimple M.toProbabilitySpace N.toProbabilitySpace Φ s
        (M.T x) := by
  let t : SimpleFunc N.X ℂ := s.comp N.T hN.2.measurable
  have hfiber (c : ℂ) :
      (fun x => x ∈ mappedFiber M.toProbabilitySpace
          N.toProbabilitySpace Φ t c) =ᵐ[M.μ]
        fun x => M.T x ∈ mappedFiber M.toProbabilitySpace
          N.toProbabilitySpace Φ s c := by
    let B : (inducedMeasureAlgebra N.toProbabilitySpace).carrier :=
      ⟨s ⁻¹' {c}, s.measurableSet_preimage {c}⟩
    have hc := hcomm B
    have hTN :
        (inducedMeasureAlgebraSystem N).transform B =
          ⟨N.T ⁻¹' B.1, B.2.preimage hN.2.measurable⟩ := by
      simp [inducedMeasureAlgebraSystem, hN.2.measurable]
    have hTM :
        (inducedMeasureAlgebraSystem M).transform (Φ.map B) =
          ⟨M.T ⁻¹' (Φ.map B).1,
            (Φ.map B).2.preimage hM.2.measurable⟩ := by
      simp [inducedMeasureAlgebraSystem, hM.2.measurable]
    rw [hTN, hTM] at hc
    have hae := ae_eq_set_of_equiv M.toProbabilitySpace hc
    simpa [t, mappedFiber, SimpleFunc.coe_comp] using hae
  have hallFiber :
      ∀ᵐ x ∂M.μ, ∀ c ∈ t.range,
        (x ∈ mappedFiber M.toProbabilitySpace N.toProbabilitySpace Φ t c ↔
          M.T x ∈ mappedFiber M.toProbabilitySpace
            N.toProbabilitySpace Φ s c) := by
    rw [Filter.eventually_all_finset]
    intro c hc
    filter_upwards [hfiber c] with x hx
    rw [hx]
  have hallLeft :
      ∀ᵐ x ∂M.μ, ∀ c ∈ t.range,
        x ∈ mappedFiber M.toProbabilitySpace N.toProbabilitySpace Φ t c →
          mappedSimple M.toProbabilitySpace N.toProbabilitySpace Φ t x = c := by
    rw [Filter.eventually_all_finset]
    intro c hc
    exact mappedSimple_eq_on_fiber_ae
      M.toProbabilitySpace N.toProbabilitySpace hM.1 hN.1 Φ hΦ.1 t hc
  have hallRight :
      ∀ᵐ x ∂M.μ, ∀ c ∈ t.range,
        M.T x ∈ mappedFiber M.toProbabilitySpace N.toProbabilitySpace Φ s c →
          mappedSimple M.toProbabilitySpace N.toProbabilitySpace Φ s
            (M.T x) = c := by
    rw [Filter.eventually_all_finset]
    intro c hc
    have hcRange : c ∈ s.range := by
      exact SimpleFunc.range_comp_subset_range s hN.2.measurable hc
    exact hM.2.quasiMeasurePreserving.ae
      (mappedSimple_eq_on_fiber_ae
        M.toProbabilitySpace N.toProbabilitySpace hM.1 hN.1
        Φ hΦ.1 s hcRange)
  filter_upwards
    [mapped_fibers_cover_ae M.toProbabilitySpace N.toProbabilitySpace
      hM.1 hN.1 Φ hΦ.1 t, hallFiber, hallLeft, hallRight]
    with x hcover hfiber' hleft hright
  obtain ⟨c, hc, hxc⟩ := hcover
  rw [hleft c hc hxc, hright c hc ((hfiber' c hc).mp hxc)]

/-- The raw L² map intertwines the two transformations on simple functions. -/
theorem rawLtwoMap_simple_comp
    (M : System.{u}) (N : System.{v})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (Φ : MeasureAlgebraHomData
      (inducedMeasureAlgebra N.toProbabilitySpace)
      (inducedMeasureAlgebra M.toProbabilitySpace))
    (hΦ : IsMeasureAlgebraIsomorphism Φ)
    (hcomm : ∀ B : (inducedMeasureAlgebraSystem N).carrier,
      (inducedMeasureAlgebraSystem M).equiv
        (Φ.map ((inducedMeasureAlgebraSystem N).transform B))
        ((inducedMeasureAlgebraSystem M).transform (Φ.map B)))
    (s : SimpleFunc N.X ℂ) :
    rawLtwoMap M.toProbabilitySpace N.toProbabilitySpace
        hM.1 hN.1 Φ hΦ.1 (fun y => s (N.T y)) =ᵐ[M.μ]
      fun x => rawLtwoMap M.toProbabilitySpace N.toProbabilitySpace
        hM.1 hN.1 Φ hΦ.1 s (M.T x) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : IsProbabilityMeasure N.μ := hN.1
  let t : SimpleFunc N.X ℂ := s.comp N.T hN.2.measurable
  have hsTwo : MemLp s 2 N.μ :=
    (s.memLp_top N.μ).mono_exponent (by simp)
  have htTwo : MemLp t 2 N.μ :=
    (t.memLp_top N.μ).mono_exponent (by simp)
  have hleft := rawLtwoMap_simple
    M.toProbabilitySpace N.toProbabilitySpace hM.1 hN.1
    Φ hΦ.1 t htTwo
  have hright := hM.2.quasiMeasurePreserving.ae
    (rawLtwoMap_simple M.toProbabilitySpace N.toProbabilitySpace
      hM.1 hN.1 Φ hΦ.1 s hsTwo)
  have hmiddle := mappedSimple_comp M N hM hN Φ hΦ hcomm s
  filter_upwards [hleft, hmiddle, hright] with x hx hm hr
  simpa [t, SimpleFunc.coe_comp] using hx.trans (hm.trans hr.symm)

set_option maxHeartbeats 1800000 in
/-- The Koopman-intertwining error is controlled by either side of a
simple-function approximation. -/
theorem rawLtwoMap_comp_eLpNorm_le
    (M : System.{u}) (N : System.{v})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (Φ : MeasureAlgebraHomData
      (inducedMeasureAlgebra N.toProbabilitySpace)
      (inducedMeasureAlgebra M.toProbabilitySpace))
    (hΦ : IsMeasureAlgebraIsomorphism Φ)
    (hcomm : ∀ B : (inducedMeasureAlgebraSystem N).carrier,
      (inducedMeasureAlgebraSystem M).equiv
        (Φ.map ((inducedMeasureAlgebraSystem N).transform B))
        ((inducedMeasureAlgebraSystem M).transform (Φ.map B)))
    (f : N.X → ℂ) (hf : MemLp f 2 N.μ)
    (s : SimpleFunc N.X ℂ) (hs : MemLp s 2 N.μ) :
    eLpNorm
        (fun x =>
          rawLtwoMap M.toProbabilitySpace N.toProbabilitySpace
              hM.1 hN.1 Φ hΦ.1 (fun y => f (N.T y)) x -
            rawLtwoMap M.toProbabilitySpace N.toProbabilitySpace
              hM.1 hN.1 Φ hΦ.1 f (M.T x))
        2 M.μ ≤
      eLpNorm (fun y => f y - s y) 2 N.μ +
        eLpNorm (fun y => s y - f y) 2 N.μ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : IsProbabilityMeasure N.μ := hN.1
  let W : (N.X → ℂ) → M.X → ℂ :=
    rawLtwoMap M.toProbabilitySpace N.toProbabilitySpace
      hM.1 hN.1 Φ hΦ.1
  let sT : N.X → ℂ := fun y => s (N.T y)
  have hsTTwo : MemLp sT 2 N.μ := hs.comp_measurePreserving hN.2
  have hleftTwo : MemLp (W (fun y => f (N.T y))) 2 M.μ := by
    apply (rawLtwoMap_ltwo M.toProbabilitySpace N.toProbabilitySpace
      hM.1 hN.1 Φ hΦ.1 _ ?_).1
    exact hf.comp_measurePreserving hN.2
  have hrightTwo : MemLp (fun x => W f (M.T x)) 2 M.μ := by
    exact ((rawLtwoMap_ltwo M.toProbabilitySpace N.toProbabilitySpace
      hM.1 hN.1 Φ hΦ.1 f hf).1).comp_measurePreserving hM.2
  have hmid := rawLtwoMap_simple_comp M N hM hN Φ hΦ hcomm s
  have hfirstMeas : AEStronglyMeasurable
      (fun x => W (fun y => f (N.T y)) x - W sT x) M.μ :=
    (hleftTwo.sub
      (rawLtwoMap_ltwo M.toProbabilitySpace N.toProbabilitySpace
        hM.1 hN.1 Φ hΦ.1 sT hsTTwo).1).1
  have hsecondMeas : AEStronglyMeasurable
      (fun x => W s (M.T x) - W f (M.T x)) M.μ := by
    exact ((((rawLtwoMap_ltwo M.toProbabilitySpace N.toProbabilitySpace
      hM.1 hN.1 Φ hΦ.1 s hs).1).sub
      (rawLtwoMap_ltwo M.toProbabilitySpace N.toProbabilitySpace
        hM.1 hN.1 Φ hΦ.1 f hf).1).comp_measurePreserving hM.2).1
  have hfirstNorm :
      eLpNorm (fun x => W (fun y => f (N.T y)) x - W sT x) 2 M.μ =
        eLpNorm (fun y => f y - s y) 2 N.μ := by
    calc
      eLpNorm (fun x => W (fun y => f (N.T y)) x - W sT x)
          2 M.μ =
          eLpNorm (fun y => f (N.T y) - sT y) 2 N.μ :=
        LinfClosure.rawLtwoMap_sub_eLpNorm
          M.toProbabilitySpace N.toProbabilitySpace
          hM.1 hN.1 Φ hΦ.1 _ _
          (hf.comp_measurePreserving hN.2) hsTTwo
      _ = eLpNorm (fun y => f y - s y) 2 N.μ := by
        simpa only [sT] using
          (eLpNorm_comp_measurePreserving ((hf.sub hs).1) hN.2)
  have hsecondNorm :
      eLpNorm (fun x => W s (M.T x) - W f (M.T x)) 2 M.μ =
        eLpNorm (fun y => s y - f y) 2 N.μ := by
    calc
      eLpNorm (fun x => W s (M.T x) - W f (M.T x)) 2 M.μ =
          eLpNorm (fun x => W s x - W f x) 2 M.μ := by
        simpa only using
          (eLpNorm_comp_measurePreserving
            (((rawLtwoMap_ltwo M.toProbabilitySpace
              N.toProbabilitySpace hM.1 hN.1 Φ hΦ.1 s hs).1.sub
              (rawLtwoMap_ltwo M.toProbabilitySpace
                N.toProbabilitySpace hM.1 hN.1 Φ hΦ.1 f hf).1).1) hM.2)
      _ = eLpNorm (fun y => s y - f y) 2 N.μ :=
        LinfClosure.rawLtwoMap_sub_eLpNorm
          M.toProbabilitySpace N.toProbabilitySpace
          hM.1 hN.1 Φ hΦ.1 _ _ hs hf
  calc
    eLpNorm (fun x => W (fun y => f (N.T y)) x - W f (M.T x))
        2 M.μ =
        eLpNorm (fun x =>
          (W (fun y => f (N.T y)) x - W sT x) +
          (W s (M.T x) - W f (M.T x))) 2 M.μ := by
      apply eLpNorm_congr_ae
      filter_upwards [hmid] with x hx
      change W sT x = W s (M.T x) at hx
      rw [hx]
      ring
    _ ≤ eLpNorm (fun x => W (fun y => f (N.T y)) x - W sT x)
          2 M.μ +
        eLpNorm (fun x => W s (M.T x) - W f (M.T x)) 2 M.μ :=
      eLpNorm_add_le hfirstMeas hsecondMeas (by norm_num)
    _ = eLpNorm (fun y => f y - s y) 2 N.μ +
        eLpNorm (fun y => s y - f y) 2 N.μ := by
      rw [hfirstNorm, hsecondNorm]

set_option maxHeartbeats 1800000 in
/-- The raw L² map induced by an abstract measure-algebra conjugacy
intertwines the two Koopman operators on every L² function. -/
theorem rawLtwoMap_comp
    (M : System.{u}) (N : System.{v})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (Φ : MeasureAlgebraHomData
      (inducedMeasureAlgebra N.toProbabilitySpace)
      (inducedMeasureAlgebra M.toProbabilitySpace))
    (hΦ : IsMeasureAlgebraIsomorphism Φ)
    (hcomm : ∀ B : (inducedMeasureAlgebraSystem N).carrier,
      (inducedMeasureAlgebraSystem M).equiv
        (Φ.map ((inducedMeasureAlgebraSystem N).transform B))
        ((inducedMeasureAlgebraSystem M).transform (Φ.map B)))
    (f : N.X → ℂ) (hf : MemLp f 2 N.μ) :
    rawLtwoMap M.toProbabilitySpace N.toProbabilitySpace
        hM.1 hN.1 Φ hΦ.1 (Chapter01.koopman N.T f) =ᵐ[M.μ]
      Chapter01.koopman M.T
        (rawLtwoMap M.toProbabilitySpace N.toProbabilitySpace
          hM.1 hN.1 Φ hΦ.1 f) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : IsProbabilityMeasure N.μ := hN.1
  let W : (N.X → ℂ) → M.X → ℂ :=
    rawLtwoMap M.toProbabilitySpace N.toProbabilitySpace
      hM.1 hN.1 Φ hΦ.1
  let f₀ : N.X → ℂ := hf.1.mk f
  have hfmeas : Measurable f₀ := hf.1.measurable_mk
  have hff₀ : f =ᵐ[N.μ] f₀ := hf.1.ae_eq_mk
  have hf₀Two : MemLp f₀ 2 N.μ := (memLp_congr_ae hff₀).mp hf
  let s : ℕ → SimpleFunc N.X ℂ := fun n =>
    SimpleFunc.approxOn f₀ hfmeas (Set.range f₀ ∪ {0}) 0 (by simp) n
  have hsTwo : ∀ n, MemLp (s n) 2 N.μ :=
    fun n => SimpleFunc.memLp_approxOn_range hfmeas hf₀Two n
  have hconv : Tendsto
      (fun n => eLpNorm (fun y => s n y - f₀ y) 2 N.μ)
      atTop (nhds 0) := by
    simpa only [Pi.sub_apply] using
      (SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm
        (p := (2 : ENNReal)) (by norm_num) hfmeas hf₀Two.2)
  have hconvRev : Tendsto
      (fun n => eLpNorm (fun y => f₀ y - s n y) 2 N.μ)
      atTop (nhds 0) := by
    apply hconv.congr'
    exact Eventually.of_forall fun n => by
      symm
      calc
        eLpNorm (fun y => f₀ y - s n y) 2 N.μ =
            eLpNorm (-(fun y => s n y - f₀ y)) 2 N.μ := by
              congr 2
              funext y
              simp
        _ = eLpNorm (fun y => s n y - f₀ y) 2 N.μ :=
          eLpNorm_neg _ _ _
  have hleftTwo : MemLp (W (fun y => f₀ (N.T y))) 2 M.μ := by
    apply (rawLtwoMap_ltwo M.toProbabilitySpace N.toProbabilitySpace
      hM.1 hN.1 Φ hΦ.1 _ ?_).1
    exact hf₀Two.comp_measurePreserving hN.2
  have hrightTwo : MemLp (fun x => W f₀ (M.T x)) 2 M.μ := by
    exact ((rawLtwoMap_ltwo M.toProbabilitySpace N.toProbabilitySpace
      hM.1 hN.1 Φ hΦ.1 f₀ hf₀Two).1).comp_measurePreserving hM.2
  have hdiffTwo : MemLp
      (fun x => W (fun y => f₀ (N.T y)) x - W f₀ (M.T x)) 2 M.μ :=
    hleftTwo.sub hrightTwo
  have hupper : Tendsto
      (fun n =>
        eLpNorm (fun y => f₀ y - s n y) 2 N.μ +
        eLpNorm (fun y => s n y - f₀ y) 2 N.μ)
      atTop (nhds 0) := by
    simpa using hconvRev.add hconv
  have hzero :
      eLpNorm (fun x => W (fun y => f₀ (N.T y)) x - W f₀ (M.T x))
        2 M.μ = 0 := by
    apply le_antisymm ?_ bot_le
    exact ge_of_tendsto hupper (Eventually.of_forall fun n =>
      rawLtwoMap_comp_eLpNorm_le
        M N hM hN Φ hΦ hcomm f₀ hf₀Two (s n) (hsTwo n))
  have hcore :
      W (fun y => f₀ (N.T y)) =ᵐ[M.μ] fun x => W f₀ (M.T x) := by
    have hz := (eLpNorm_eq_zero_iff hdiffTwo.1 (by norm_num)).1 hzero
    filter_upwards [hz] with x hx
    simpa only [Pi.zero_apply, sub_eq_zero] using hx
  have hfCompTwo : MemLp (fun y => f (N.T y)) 2 N.μ :=
    hf.comp_measurePreserving hN.2
  have hf₀CompTwo : MemLp (fun y => f₀ (N.T y)) 2 N.μ :=
    hf₀Two.comp_measurePreserving hN.2
  have hcompAe :
      (fun y => f (N.T y)) =ᵐ[N.μ] fun y => f₀ (N.T y) :=
    hN.2.quasiMeasurePreserving.ae_eq_comp hff₀
  have hWff₀ := rawLtwoMap_ae
    M.toProbabilitySpace N.toProbabilitySpace hM.1 hN.1 Φ hΦ.1
    f f₀ hf hf₀Two hff₀
  have hWff₀Comp := hM.2.quasiMeasurePreserving.ae_eq_comp hWff₀
  filter_upwards
    [rawLtwoMap_ae M.toProbabilitySpace N.toProbabilitySpace
      hM.1 hN.1 Φ hΦ.1 _ _ hfCompTwo hf₀CompTwo hcompAe,
     hcore, hWff₀Comp]
    with x hleft hmid hright
  exact hleft.trans (hmid.trans hright.symm)

end Chapter04.MeasureAlgebraDynamics
