import Chapter04.MeasureAlgebra.AlgebraClosure

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter04.InverseLtwo

universe u v

open MeasureAlgebraLtwo LinfClosure

attribute [local instance]
  Lp.simpleFunc.smul
  Lp.simpleFunc.module
  Lp.simpleFunc.isBoundedSMul
  Lp.simpleFunc.normedSpace

set_option maxHeartbeats 1200000 in
/-- The L² map attached to the chosen inverse measure-algebra homomorphism is
a right inverse to the original L² map. -/
theorem ltwoMap_inverseHom_rightInverse
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraIsomorphism Φ)
    (F : Lp ℂ 2 P.μ) :
    ltwoMap P Q hP hQ Φ hΦ.1
        (ltwoMap Q P hQ hP (inverseHom P Q Φ hΦ)
          (inverseHom_isMeasureAlgebraHom P Q hP hQ Φ hΦ) F) = F := by
  letI : IsProbabilityMeasure P.μ := hP
  letI : IsProbabilityMeasure Q.μ := hQ
  let Ψ := inverseHom P Q Φ hΦ
  let hΨ : IsMeasureAlgebraHom Ψ :=
    inverseHom_isMeasureAlgebraHom P Q hP hQ Φ hΦ
  let L := ltwoMap P Q hP hQ Φ hΦ.1
  let K := ltwoMap Q P hQ hP Ψ hΨ
  have hclosed : IsClosed {G : Lp ℂ 2 P.μ | L (K G) = G} :=
    isClosed_eq (L.continuous.comp K.continuous) continuous_id
  have hsimple (s : Lp.simpleFunc ℂ 2 P.μ) :
      L (K (s : Lp ℂ 2 P.μ)) = (s : Lp ℂ 2 P.μ) := by
    induction s using Lp.simpleFunc.induction
        (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤) with
    | indicatorConst c hA hμA =>
        rename_i A
        let A' : (inducedMeasureAlgebra P).carrier := ⟨A, hA⟩
        let B : (inducedMeasureAlgebra Q).carrier := Ψ.map A'
        let a : Lp.simpleFunc ℂ 2 P.μ :=
          Lp.simpleFunc.indicatorConst
            (2 : ENNReal) hA hμA.ne (1 : ℂ)
        let b : Lp.simpleFunc ℂ 2 Q.μ :=
          Lp.simpleFunc.indicatorConst
            (2 : ENNReal) B.2 (measure_ne_top Q.μ B.1) (1 : ℂ)
        have hK :
            K (a : Lp ℂ 2 P.μ) = (b : Lp ℂ 2 Q.μ) := by
          rw [show K (a : Lp ℂ 2 P.μ) =
              (mappedIndicator_memLp Q P hQ Ψ A' 2).toLp
                (mappedIndicator Q P Ψ A') by
            exact ltwoMap_indicator_one Q P hQ hP Ψ hΨ A']
          apply Lp.ext
          have hbcoe :
              (fun y => ((b : Lp ℂ 2 Q.μ) : Q.X → ℂ) y) =ᵐ[Q.μ]
                Lp.simpleFunc.toSimpleFunc b := by
            filter_upwards [(Lp.simpleFunc.memLp b).coeFn_toLp] with y hy
            have heq := congrArg
              (fun z : Lp.simpleFunc ℂ 2 Q.μ =>
                (((z : Lp ℂ 2 Q.μ) : Q.X → ℂ) y))
              (Lp.simpleFunc.toLp_toSimpleFunc b)
            exact heq.symm.trans hy
          have hbind := Lp.simpleFunc.toSimpleFunc_indicatorConst
            (p := (2 : ENNReal)) B.2 (measure_ne_top Q.μ B.1) (1 : ℂ)
          exact (mappedIndicator_memLp Q P hQ Ψ A' 2).coeFn_toLp
            |>.trans (by
              simpa [b, B, mappedIndicator, LtwoProjection.indicatorOne,
                indicatorSimpleFunc] using (hbcoe.trans hbind).symm)
        have hL :
            L (b : Lp ℂ 2 Q.μ) = (a : Lp ℂ 2 P.μ) := by
          rw [show L (b : Lp ℂ 2 Q.μ) =
              (mappedIndicator_memLp P Q hP Φ B 2).toLp
                (mappedIndicator P Q Φ B) by
            exact ltwoMap_indicator_one P Q hP hQ Φ hΦ.1 B]
          apply Lp.ext
          have hset := ae_eq_set_of_equiv P
            (inverseHom_spec P Q Φ hΦ A')
          have hacoe :
              (fun x => ((a : Lp ℂ 2 P.μ) : P.X → ℂ) x) =ᵐ[P.μ]
                Lp.simpleFunc.toSimpleFunc a := by
            filter_upwards [(Lp.simpleFunc.memLp a).coeFn_toLp] with x hx
            have heq := congrArg
              (fun z : Lp.simpleFunc ℂ 2 P.μ =>
                (((z : Lp ℂ 2 P.μ) : P.X → ℂ) x))
              (Lp.simpleFunc.toLp_toSimpleFunc a)
            exact heq.symm.trans hx
          have haind := Lp.simpleFunc.toSimpleFunc_indicatorConst
            (p := (2 : ENNReal)) hA hμA.ne (1 : ℂ)
          filter_upwards
            [(mappedIndicator_memLp P Q hP Φ B 2).coeFn_toLp,
             hacoe, haind, hset]
            with x hx ha hai hs
          rw [hx, ha, hai]
          change LtwoProjection.indicatorOne (Φ.map B).1 x =
            A.indicator (fun _ => (1 : ℂ)) x
          change (Φ.map B).1.indicator (fun _ => (1 : ℂ)) x =
            A.indicator (fun _ => (1 : ℂ)) x
          by_cases hxA : x ∈ A
          · have hxB : x ∈ (Φ.map B).1 := hs.mpr hxA
            simp [hxA, hxB]
          · have hxB : x ∉ (Φ.map B).1 := fun h => hxA (hs.mp h)
            simp [hxA, hxB]
        have haScalar :
            ((Lp.simpleFunc.indicatorConst
              (2 : ENNReal) hA hμA.ne c :
              Lp.simpleFunc ℂ 2 P.μ) : Lp ℂ 2 P.μ) =
              c • (a : Lp ℂ 2 P.μ) := by
          apply Lp.ext
          let ac : Lp.simpleFunc ℂ 2 P.μ :=
            Lp.simpleFunc.indicatorConst
              (2 : ENNReal) hA hμA.ne c
          have haccoe :
              (fun x => ((ac : Lp ℂ 2 P.μ) : P.X → ℂ) x) =ᵐ[P.μ]
                Lp.simpleFunc.toSimpleFunc ac := by
            filter_upwards [(Lp.simpleFunc.memLp ac).coeFn_toLp] with x hx
            have heq := congrArg
              (fun z : Lp.simpleFunc ℂ 2 P.μ =>
                (((z : Lp ℂ 2 P.μ) : P.X → ℂ) x))
              (Lp.simpleFunc.toLp_toSimpleFunc ac)
            exact heq.symm.trans hx
          have hacind := Lp.simpleFunc.toSimpleFunc_indicatorConst
            (p := (2 : ENNReal)) hA hμA.ne c
          have hacoe :
              (fun x => ((a : Lp ℂ 2 P.μ) : P.X → ℂ) x) =ᵐ[P.μ]
                Lp.simpleFunc.toSimpleFunc a := by
            filter_upwards [(Lp.simpleFunc.memLp a).coeFn_toLp] with x hx
            have heq := congrArg
              (fun z : Lp.simpleFunc ℂ 2 P.μ =>
                (((z : Lp ℂ 2 P.μ) : P.X → ℂ) x))
              (Lp.simpleFunc.toLp_toSimpleFunc a)
            exact heq.symm.trans hx
          have haind := Lp.simpleFunc.toSimpleFunc_indicatorConst
            (p := (2 : ENNReal)) hA hμA.ne (1 : ℂ)
          filter_upwards
            [haccoe, hacind, hacoe, haind,
             Lp.coeFn_smul c (a : Lp ℂ 2 P.μ)]
            with x hc hci h1 h1i hs
          have hleft :
              ((((Lp.simpleFunc.indicatorConst
                  (2 : ENNReal) hA hμA.ne c :
                  Lp.simpleFunc ℂ 2 P.μ) : Lp ℂ 2 P.μ) :
                  P.X → ℂ) x) = A.indicator (fun _ => c) x := by
            simpa only [ac] using hc.trans hci
          have hright :
              (((c • (a : Lp ℂ 2 P.μ)) : Lp ℂ 2 P.μ) : P.X → ℂ) x =
                c * A.indicator (fun _ => (1 : ℂ)) x := by
            calc
              (((c • (a : Lp ℂ 2 P.μ)) : Lp ℂ 2 P.μ) :
                  P.X → ℂ) x =
                  (c • ((a : Lp ℂ 2 P.μ) : P.X → ℂ)) x := hs
              _ = c * ((a : Lp ℂ 2 P.μ) : P.X → ℂ) x := rfl
              _ = c * (SimpleFunc.piecewise A hA
                  (SimpleFunc.const P.X 1) (SimpleFunc.const P.X 0)) x := by
                    rw [h1, h1i]
              _ = c * A.indicator (fun _ => (1 : ℂ)) x := by
                    by_cases hx : x ∈ A <;> simp [hx]
          rw [hleft, hright]
          by_cases hx : x ∈ A <;> simp [hx]
        rw [haScalar, map_smul, map_smul, hK, hL]
    | add hfmem hgmem hdis hfirst hsecond =>
        rename_i sf sg
        change L (K ((Lp.simpleFunc.coeToLp P.X ℂ ℂ)
          (Lp.simpleFunc.toLp sf hfmem + Lp.simpleFunc.toLp sg hgmem))) =
            (Lp.simpleFunc.coeToLp P.X ℂ ℂ)
              (Lp.simpleFunc.toLp sf hfmem + Lp.simpleFunc.toLp sg hgmem)
        rw [map_add, map_add, map_add]
        change L (K (Lp.simpleFunc.toLp sf hfmem : Lp ℂ 2 P.μ)) +
            L (K (Lp.simpleFunc.toLp sg hgmem : Lp ℂ 2 P.μ)) =
          (Lp.simpleFunc.toLp sf hfmem : Lp ℂ 2 P.μ) +
            (Lp.simpleFunc.toLp sg hgmem : Lp ℂ 2 P.μ)
        rw [hfirst, hsecond]
  have hdense :
      DenseRange (Lp.simpleFunc.coeToLp P.X ℂ ℂ :
        Lp.simpleFunc ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ) := by
    simpa [Lp.simpleFunc.coeToLp] using
      (Lp.simpleFunc.denseRange
        (E := ℂ) (p := (2 : ENNReal)) (μ := P.μ) (by norm_num))
  exact hdense.induction_on F hclosed hsimple

/-- The raw forward map sends the raw inverse image back to the original L²
function, almost everywhere. -/
theorem rawLtwoMap_inverseHom_rightInverse
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraIsomorphism Φ)
    (h : P.X → ℂ) (hh : MemLp h 2 P.μ) :
    let Ψ := inverseHom P Q Φ hΦ
    let hΨ := inverseHom_isMeasureAlgebraHom P Q hP hQ Φ hΦ
    rawLtwoMap P Q hP hQ Φ hΦ.1
        (rawLtwoMap Q P hQ hP Ψ hΨ h) =ᵐ[P.μ] h := by
  let Ψ := inverseHom P Q Φ hΦ
  let hΨ := inverseHom_isMeasureAlgebraHom P Q hP hQ Φ hΦ
  dsimp only
  have hKh : MemLp (rawLtwoMap Q P hQ hP Ψ hΨ h) 2 Q.μ :=
    (rawLtwoMap_ltwo Q P hQ hP Ψ hΨ h hh).1
  rw [rawLtwoMap_apply P Q hP hQ Φ hΦ.1 _ hKh]
  have hinner :
      hKh.toLp (rawLtwoMap Q P hQ hP Ψ hΨ h) =
        ltwoMap Q P hQ hP Ψ hΨ (hh.toLp h) := by
    let G := ltwoMap Q P hQ hP Ψ hΨ (hh.toLp h)
    have hrawEq := rawLtwoMap_apply Q P hQ hP Ψ hΨ h hh
    have hrawAe :
        rawLtwoMap Q P hQ hP Ψ hΨ h =ᵐ[Q.μ] (G : Q.X → ℂ) :=
      Eventually.of_forall fun y => congrFun hrawEq y
    have hcongr := MemLp.toLp_congr hKh (Lp.memLp G) hrawAe
    exact hcongr.trans (Lp.toLp_coeFn G (Lp.memLp G))
  rw [hinner]
  have hcomp := ltwoMap_inverseHom_rightInverse P Q hP hQ Φ hΦ
    (hh.toLp h)
  rw [hcomp]
  exact hh.coeFn_toLp

/-- The raw L² map attached to a measure-algebra isomorphism is surjective on
essentially bounded functions. -/
theorem rawLtwoMap_memLp_top_surjective
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraIsomorphism Φ)
    (h : P.X → ℂ) (hh : MemLp h ⊤ P.μ) :
    ∃ f : Q.X → ℂ, MemLp f ⊤ Q.μ ∧
      rawLtwoMap P Q hP hQ Φ hΦ.1 f =ᵐ[P.μ] h := by
  letI : IsProbabilityMeasure P.μ := hP
  letI : IsProbabilityMeasure Q.μ := hQ
  let Ψ := inverseHom P Q Φ hΦ
  let hΨ := inverseHom_isMeasureAlgebraHom P Q hP hQ Φ hΦ
  let f := rawLtwoMap Q P hQ hP Ψ hΨ h
  have hfTop : MemLp f ⊤ Q.μ :=
    rawLtwoMap_memLp_top Q P hQ hP Ψ hΨ h hh
  refine ⟨f, hfTop, ?_⟩
  exact rawLtwoMap_inverseHom_rightInverse P Q hP hQ Φ hΦ h
    (hh.mono_exponent (by simp))

end Chapter04.InverseLtwo
