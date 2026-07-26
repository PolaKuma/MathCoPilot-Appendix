import Chapter04.MeasureAlgebra.LtwoProjection
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter04.MeasureAlgebraLtwo

universe u v

attribute [local instance]
  MeasureTheory.Lp.simpleFunc.smul
  MeasureTheory.Lp.simpleFunc.module
  MeasureTheory.Lp.simpleFunc.isBoundedSMul
  MeasureTheory.Lp.simpleFunc.normedSpace

/-- The indicator assigned to a measurable set by a measure-algebra
homomorphism.  This is the generating prescription in the proof of 4.1.23. -/
def mappedIndicator
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (B : (inducedMeasureAlgebra Q).carrier) : P.X → ℂ :=
  LtwoProjection.indicatorOne (Φ.map B).1

theorem map_measure
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (B : (inducedMeasureAlgebra Q).carrier) :
    P.μ (Φ.map B).1 = Q.μ B.1 := by
  letI : IsProbabilityMeasure P.μ := hP
  letI : IsProbabilityMeasure Q.μ := hQ
  have hr : (P.μ (Φ.map B).1).toReal = (Q.μ B.1).toReal := hΦ.2.2.2.2 B
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top P.μ _) (measure_ne_top Q.μ _)).mp hr

theorem mappedIndicator_memLp
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (B : (inducedMeasureAlgebra Q).carrier) (p : ENNReal) :
    MemLp (mappedIndicator P Q Φ B) p P.μ := by
  exact LtwoProjection.indicatorOne_memLp P hP (Φ.map B).2 p

theorem mappedIndicator_eLpNorm
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (B : (inducedMeasureAlgebra Q).carrier) :
    eLpNorm (mappedIndicator P Q Φ B) 2 P.μ =
      eLpNorm (LtwoProjection.indicatorOne B.1) 2 Q.μ := by
  change eLpNorm ((Φ.map B).1.indicator fun _ => (1 : ℂ)) 2 P.μ =
    eLpNorm (B.1.indicator fun _ => (1 : ℂ)) 2 Q.μ
  rw [eLpNorm_indicator_const (Φ.map B).2 (by norm_num) (by norm_num),
    eLpNorm_indicator_const B.2 (by norm_num) (by norm_num),
    map_measure P Q hP hQ Φ hΦ B]

/-- Concrete form of equivalence in an induced measure algebra. -/
theorem ae_eq_set_of_equiv
    (P : ProbabilitySpace.{u})
    {A B : (inducedMeasureAlgebra P).carrier}
    (hAB : (inducedMeasureAlgebra P).equiv A B) :
    (fun x => x ∈ A.1) =ᵐ[P.μ] fun x => x ∈ B.1 := by
  rw [MeasureTheory.ae_eq_set]
  change P.μ ((A.1 \ B.1) ∪ (B.1 \ A.1)) = 0 at hAB
  exact ⟨MeasureTheory.measure_mono_null Set.subset_union_left hAB,
    MeasureTheory.measure_mono_null Set.subset_union_right hAB⟩

/-- A homomorphism of induced measure algebras preserves intersections.  The
chapter's primitive homomorphism interface only lists unions and complements,
so this derived fact is recorded once for all later simple-function proofs. -/
theorem map_inter_ae
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (B C : (inducedMeasureAlgebra Q).carrier) :
    (fun x => x ∈ (Φ.map ((inducedMeasureAlgebra Q).inter B C)).1) =ᵐ[P.μ]
      fun x => x ∈ ((Φ.map B).1 ∩ (Φ.map C).1 : Set P.X) := by
  let D := (inducedMeasureAlgebra Q).union
    ((inducedMeasureAlgebra Q).compl B)
    ((inducedMeasureAlgebra Q).compl C)
  have hsource :
      (inducedMeasureAlgebra Q).inter B C =
        (inducedMeasureAlgebra Q).compl D := by
    apply Subtype.ext
    ext x
    simp [D, inducedMeasureAlgebra]
  have houter := ae_eq_set_of_equiv P (hΦ.2.2.1 D)
  have hunion := ae_eq_set_of_equiv P
    (hΦ.2.1 ((inducedMeasureAlgebra Q).compl B)
      ((inducedMeasureAlgebra Q).compl C))
  have hB := ae_eq_set_of_equiv P (hΦ.2.2.1 B)
  have hC := ae_eq_set_of_equiv P (hΦ.2.2.1 C)
  rw [hsource]
  filter_upwards [houter, hunion, hB, hC] with x hx hu hb hc
  simp only [D, inducedMeasureAlgebra, Set.mem_compl_iff, Set.mem_union,
    Set.mem_inter_iff] at hx hu hb hc ⊢
  rw [hx, hu, hb, hc]
  apply propext
  tauto

theorem map_mono_ae
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (B C : (inducedMeasureAlgebra Q).carrier) (hBC : B.1 ⊆ C.1) :
    ∀ᵐ x ∂P.μ, x ∈ (Φ.map B).1 → x ∈ (Φ.map C).1 := by
  have hsource :
      (inducedMeasureAlgebra Q).union B C = C := by
    apply Subtype.ext
    exact Set.union_eq_right.mpr hBC
  have hu := ae_eq_set_of_equiv P (hΦ.2.1 B C)
  rw [hsource] at hu
  filter_upwards [hu] with x hx hxb
  have : x ∈
      ((inducedMeasureAlgebra P).union (Φ.map B) (Φ.map C)).1 :=
    Or.inl hxb
  rw [← hx] at this
  exact this

def mappedFiber
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (f : MeasureTheory.SimpleFunc Q.X ℂ) (c : ℂ) : Set P.X :=
  (Φ.map ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩).1

/-- The image of a scalar-valued simple function, obtained by mapping each of
its measurable level sets.  Distinct image level sets can overlap only on a
null set; this is why the expression is naturally used modulo almost-everywhere
equality. -/
def mappedSimple
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (f : MeasureTheory.SimpleFunc Q.X ℂ) : P.X → ℂ :=
  fun x => ∑ c ∈ f.range,
    c * mappedIndicator P Q Φ
      ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩ x

theorem mappedSimple_memLp
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (f : MeasureTheory.SimpleFunc Q.X ℂ) (p : ENNReal) :
    MemLp (mappedSimple P Q Φ f) p P.μ := by
  classical
  change MemLp (fun x => ∑ c ∈ f.range,
    c * mappedIndicator P Q Φ
      ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩ x) p P.μ
  let term : ℂ → P.X → ℂ := fun c x =>
    c * mappedIndicator P Q Φ
      ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩ x
  have hterm (c : ℂ) : MemLp (term c) p P.μ :=
    (mappedIndicator_memLp P Q hP Φ
      ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩ p).const_mul c
  change MemLp (fun x => ∑ c ∈ f.range, term c x) p P.μ
  induction f.range using Finset.induction_on with
  | empty => simpa using (MemLp.zero : MemLp (fun _ : P.X => (0 : ℂ)) p P.μ)
  | @insert c s hc ih =>
      simpa [Finset.sum_insert hc] using (hterm c).add ih

/-- Images of two distinct level sets of a simple function are disjoint modulo
null sets. -/
theorem mapped_fibers_ae_disjoint
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f : MeasureTheory.SimpleFunc Q.X ℂ) {c d : ℂ} (hcd : c ≠ d) :
    ∀ᵐ x ∂P.μ,
      ¬ (x ∈ mappedFiber P Q Φ f c ∧ x ∈ mappedFiber P Q Φ f d) := by
  let B : (inducedMeasureAlgebra Q).carrier :=
    ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩
  let C : (inducedMeasureAlgebra Q).carrier :=
    ⟨f ⁻¹' {d}, f.measurableSet_preimage {d}⟩
  let E := (inducedMeasureAlgebra Q).inter B C
  have hEempty : E.1 = ∅ := by
    ext y
    change (f y = c ∧ f y = d) ↔ y ∈ (∅ : Set Q.X)
    constructor
    · rintro ⟨hyc, hyd⟩
      exact (hcd (hyc.symm.trans hyd)).elim
    · exact fun hy => hy.elim
  have hEzero : P.μ (Φ.map E).1 = 0 := by
    rw [map_measure P Q hP hQ Φ hΦ E, hEempty, MeasureTheory.measure_empty]
  have hnot : ∀ᵐ x ∂P.μ, x ∉ (Φ.map E).1 :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hEzero
  have hinter := map_inter_ae P Q Φ hΦ B C
  filter_upwards [hnot, hinter] with x hx hxi
  change ¬ (x ∈ mappedFiber P Q Φ f c ∧
    x ∈ mappedFiber P Q Φ f d)
  change ¬ (x ∈ (Φ.map B).1 ∧ x ∈ (Φ.map C).1)
  intro hboth
  have hxE : x ∈ (Φ.map E).1 := by
    rw [hxi]
    exact hboth
  exact hx hxE

theorem mapped_fibers_pairwise_ae
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f : MeasureTheory.SimpleFunc Q.X ℂ) :
    ∀ᵐ x ∂P.μ, ∀ c ∈ f.range, ∀ d ∈ f.range, c ≠ d →
      ¬ (x ∈ mappedFiber P Q Φ f c ∧ x ∈ mappedFiber P Q Φ f d) := by
  rw [Filter.eventually_all_finset]
  intro c hc
  rw [Filter.eventually_all_finset]
  intro d hd
  by_cases hcd : c = d
  · exact Filter.Eventually.of_forall fun _ hne => (hne hcd).elim
  · exact (mapped_fibers_ae_disjoint P Q hP hQ Φ hΦ f hcd).mono
      (fun _ hx _ => hx)

theorem mapped_fibers_cover_ae
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f : MeasureTheory.SimpleFunc Q.X ℂ) :
    ∀ᵐ x ∂P.μ, ∃ c ∈ f.range, x ∈ mappedFiber P Q Φ f c := by
  let U : Set P.X := ⋃ c ∈ (f.range : Set ℂ), mappedFiber P Q Φ f c
  have hm (c : ℂ) : MeasurableSet (mappedFiber P Q Φ f c) :=
    (Φ.map ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩).2
  have hmeas_union (s : Finset ℂ) :
      MeasurableSet (⋃ c ∈ (s : Set ℂ), mappedFiber P Q Φ f c) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert c s hc ih =>
        simpa [Finset.coe_insert, Set.biUnion_insert] using (hm c).union ih
  have hUmeas : MeasurableSet U := by
    exact hmeas_union f.range
  have hd : Set.Pairwise (↑f.range : Set ℂ)
      (fun c d => MeasureTheory.AEDisjoint P.μ
        (mappedFiber P Q Φ f c) (mappedFiber P Q Φ f d)) := by
    intro c hc d hd hcd
    change P.μ (mappedFiber P Q Φ f c ∩ mappedFiber P Q Φ f d) = 0
    apply MeasureTheory.measure_eq_zero_iff_ae_notMem.mpr
    exact (mapped_fibers_ae_disjoint P Q hP hQ Φ hΦ f hcd).mono
      (fun x hx hmem => hx hmem)
  have hUmeasure : P.μ U = 1 := by
    calc
      P.μ U = ∑ c ∈ f.range, P.μ (mappedFiber P Q Φ f c) := by
        exact MeasureTheory.measure_biUnion_finset₀ hd
          (fun c hc => (hm c).nullMeasurableSet)
      _ = ∑ c ∈ f.range, Q.μ (f ⁻¹' {c}) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact map_measure P Q hP hQ Φ hΦ
          ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩
      _ = Q.μ Set.univ :=
        MeasureTheory.SimpleFunc.sum_range_measure_preimage_singleton f Q.μ
      _ = 1 := hQ.measure_univ
  have hUc0 : P.μ Uᶜ = 0 := by
    rw [MeasureTheory.measure_compl hUmeas (by rw [hUmeasure]; norm_num)]
    rw [hP.measure_univ, hUmeasure]
    simp
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hUc0] with x hx
  have hxU : x ∈ U := by simpa using hx
  simpa [U] using hxU

theorem mappedSimple_eq_on_fiber_ae
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f : MeasureTheory.SimpleFunc Q.X ℂ) {c : ℂ} (hc : c ∈ f.range) :
    ∀ᵐ x ∂P.μ, x ∈ mappedFiber P Q Φ f c →
      mappedSimple P Q Φ f x = c := by
  filter_upwards [mapped_fibers_pairwise_ae P Q hP hQ Φ hΦ f] with x hx hxc
  rw [mappedSimple, Finset.sum_eq_single c]
  · have hxc' :
      x ∈ (Φ.map ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩).1 := hxc
    rw [mappedIndicator, LtwoProjection.indicatorOne,
      Set.indicator_of_mem hxc']
    simp
  · intro d hd hdc
    have hxd : x ∉ mappedFiber P Q Φ f d := by
      intro hxd
      exact hx d hd c hc hdc ⟨hxd, hxc⟩
    have hxd' :
        x ∉ (Φ.map ⟨f ⁻¹' {d}, f.measurableSet_preimage {d}⟩).1 := hxd
    rw [mappedIndicator, LtwoProjection.indicatorOne,
      Set.indicator_of_notMem hxd']
    simp
  · exact fun hcnot => (hcnot hc).elim

theorem mappedSimple_eq_on_fiber_ae_any
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f : MeasureTheory.SimpleFunc Q.X ℂ) (c : ℂ) :
    ∀ᵐ x ∂P.μ, x ∈ mappedFiber P Q Φ f c →
      mappedSimple P Q Φ f x = c := by
  by_cases hc : c ∈ f.range
  · exact mappedSimple_eq_on_fiber_ae P Q hP hQ Φ hΦ f hc
  · have hfempty : f ⁻¹' {c} = ∅ := by
      ext y
      constructor
      · intro hy
        have hyc : f y = c := hy
        exact (hc (hyc ▸ f.mem_range_self y)).elim
      · exact fun hy => hy.elim
    have hzero : P.μ (mappedFiber P Q Φ f c) = 0 := by
      change P.μ (Φ.map
        ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩).1 = 0
      rw [map_measure P Q hP hQ Φ hΦ
        ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩]
      change Q.μ (f ⁻¹' {c}) = 0
      rw [hfempty, MeasureTheory.measure_empty]
    exact (MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hzero).mono
      (fun _ hx hmem => (hx hmem).elim)

theorem mappedFiber_add_ae
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f g : MeasureTheory.SimpleFunc Q.X ℂ) (c d : ℂ) :
    ∀ᵐ x ∂P.μ, x ∈ mappedFiber P Q Φ f c →
      x ∈ mappedFiber P Q Φ g d →
      x ∈ mappedFiber P Q Φ (f + g) (c + d) := by
  let B : (inducedMeasureAlgebra Q).carrier :=
    ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩
  let C : (inducedMeasureAlgebra Q).carrier :=
    ⟨g ⁻¹' {d}, g.measurableSet_preimage {d}⟩
  let E := (inducedMeasureAlgebra Q).inter B C
  let H : (inducedMeasureAlgebra Q).carrier :=
    ⟨(f + g) ⁻¹' {c + d}, (f + g).measurableSet_preimage {c + d}⟩
  have hEH : E.1 ⊆ H.1 := by
    intro y hy
    change f y = c ∧ g y = d at hy
    change (f + g) y = c + d
    simpa [hy.1, hy.2]
  have hinter := map_inter_ae P Q Φ hΦ B C
  have hmono := map_mono_ae P Q Φ hΦ E H hEH
  filter_upwards [hinter, hmono] with x hxi hxm hxf hxg
  have hxE : x ∈ (Φ.map E).1 := by
    rw [hxi]
    exact ⟨hxf, hxg⟩
  exact hxm hxE

theorem mappedSimple_add_ae
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f g : MeasureTheory.SimpleFunc Q.X ℂ) :
    mappedSimple P Q Φ (f + g) =ᵐ[P.μ]
      fun x => mappedSimple P Q Φ f x + mappedSimple P Q Φ g x := by
  have hef : ∀ᵐ x ∂P.μ, ∀ c ∈ f.range,
      x ∈ mappedFiber P Q Φ f c → mappedSimple P Q Φ f x = c := by
    rw [Filter.eventually_all_finset]
    intro c hc
    exact mappedSimple_eq_on_fiber_ae P Q hP hQ Φ hΦ f hc
  have heg : ∀ᵐ x ∂P.μ, ∀ d ∈ g.range,
      x ∈ mappedFiber P Q Φ g d → mappedSimple P Q Φ g x = d := by
    rw [Filter.eventually_all_finset]
    intro d hd
    exact mappedSimple_eq_on_fiber_ae P Q hP hQ Φ hΦ g hd
  have hj : ∀ᵐ x ∂P.μ, ∀ c ∈ f.range, ∀ d ∈ g.range,
      x ∈ mappedFiber P Q Φ f c →
      x ∈ mappedFiber P Q Φ g d →
      mappedSimple P Q Φ (f + g) x = c + d := by
    rw [Filter.eventually_all_finset]
    intro c hc
    rw [Filter.eventually_all_finset]
    intro d hd
    filter_upwards [mappedFiber_add_ae P Q Φ hΦ f g c d,
      mappedSimple_eq_on_fiber_ae_any P Q hP hQ Φ hΦ (f + g) (c + d)]
      with x hadd heq hxf hxg
    exact heq (hadd hxf hxg)
  filter_upwards [mapped_fibers_cover_ae P Q hP hQ Φ hΦ f,
    mapped_fibers_cover_ae P Q hP hQ Φ hΦ g, hef, heg, hj]
    with x hcf hcg hfe hge hje
  obtain ⟨c, hc, hxc⟩ := hcf
  obtain ⟨d, hd, hxd⟩ := hcg
  rw [hfe c hc hxc, hge d hd hxd, hje c hc d hd hxc hxd]

theorem mappedFiber_mul_ae
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f g : MeasureTheory.SimpleFunc Q.X ℂ) (c d : ℂ) :
    ∀ᵐ x ∂P.μ, x ∈ mappedFiber P Q Φ f c →
      x ∈ mappedFiber P Q Φ g d →
      x ∈ mappedFiber P Q Φ (f * g) (c * d) := by
  let B : (inducedMeasureAlgebra Q).carrier :=
    ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩
  let C : (inducedMeasureAlgebra Q).carrier :=
    ⟨g ⁻¹' {d}, g.measurableSet_preimage {d}⟩
  let E := (inducedMeasureAlgebra Q).inter B C
  let H : (inducedMeasureAlgebra Q).carrier :=
    ⟨(f * g) ⁻¹' {c * d}, (f * g).measurableSet_preimage {c * d}⟩
  have hEH : E.1 ⊆ H.1 := by
    intro y hy
    change f y = c ∧ g y = d at hy
    change (f * g) y = c * d
    simpa [hy.1, hy.2]
  have hinter := map_inter_ae P Q Φ hΦ B C
  have hmono := map_mono_ae P Q Φ hΦ E H hEH
  filter_upwards [hinter, hmono] with x hxi hxm hxf hxg
  have hxE : x ∈ (Φ.map E).1 := by
    rw [hxi]
    exact ⟨hxf, hxg⟩
  exact hxm hxE

theorem mappedSimple_mul_ae
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f g : MeasureTheory.SimpleFunc Q.X ℂ) :
    mappedSimple P Q Φ (f * g) =ᵐ[P.μ]
      fun x => mappedSimple P Q Φ f x * mappedSimple P Q Φ g x := by
  have hef : ∀ᵐ x ∂P.μ, ∀ c ∈ f.range,
      x ∈ mappedFiber P Q Φ f c → mappedSimple P Q Φ f x = c := by
    rw [Filter.eventually_all_finset]
    intro c hc
    exact mappedSimple_eq_on_fiber_ae P Q hP hQ Φ hΦ f hc
  have heg : ∀ᵐ x ∂P.μ, ∀ d ∈ g.range,
      x ∈ mappedFiber P Q Φ g d → mappedSimple P Q Φ g x = d := by
    rw [Filter.eventually_all_finset]
    intro d hd
    exact mappedSimple_eq_on_fiber_ae P Q hP hQ Φ hΦ g hd
  have hj : ∀ᵐ x ∂P.μ, ∀ c ∈ f.range, ∀ d ∈ g.range,
      x ∈ mappedFiber P Q Φ f c →
      x ∈ mappedFiber P Q Φ g d →
      mappedSimple P Q Φ (f * g) x = c * d := by
    rw [Filter.eventually_all_finset]
    intro c hc
    rw [Filter.eventually_all_finset]
    intro d hd
    filter_upwards [mappedFiber_mul_ae P Q Φ hΦ f g c d,
      mappedSimple_eq_on_fiber_ae_any P Q hP hQ Φ hΦ (f * g) (c * d)]
      with x hmul heq hxf hxg
    exact heq (hmul hxf hxg)
  filter_upwards [mapped_fibers_cover_ae P Q hP hQ Φ hΦ f,
    mapped_fibers_cover_ae P Q hP hQ Φ hΦ g, hef, heg, hj]
    with x hcf hcg hfe hge hje
  obtain ⟨c, hc, hxc⟩ := hcf
  obtain ⟨d, hd, hxd⟩ := hcg
  rw [hfe c hc hxc, hge d hd hxd, hje c hc d hd hxc hxd]

theorem mappedFiber_smul_ae
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (k : ℂ) (f : MeasureTheory.SimpleFunc Q.X ℂ) (c : ℂ) :
    ∀ᵐ x ∂P.μ, x ∈ mappedFiber P Q Φ f c →
      x ∈ mappedFiber P Q Φ (k • f) (k * c) := by
  let B : (inducedMeasureAlgebra Q).carrier :=
    ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩
  let C : (inducedMeasureAlgebra Q).carrier :=
    ⟨(k • f) ⁻¹' {k * c}, (k • f).measurableSet_preimage {k * c}⟩
  have hBC : B.1 ⊆ C.1 := by
    intro y hy
    change f y = c at hy
    change (k • f) y = k * c
    simpa [hy]
  exact map_mono_ae P Q Φ hΦ B C hBC

theorem mappedSimple_smul_ae
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (k : ℂ) (f : MeasureTheory.SimpleFunc Q.X ℂ) :
    mappedSimple P Q Φ (k • f) =ᵐ[P.μ]
      fun x => k * mappedSimple P Q Φ f x := by
  have hef : ∀ᵐ x ∂P.μ, ∀ c ∈ f.range,
      x ∈ mappedFiber P Q Φ f c → mappedSimple P Q Φ f x = c := by
    rw [Filter.eventually_all_finset]
    intro c hc
    exact mappedSimple_eq_on_fiber_ae P Q hP hQ Φ hΦ f hc
  have hj : ∀ᵐ x ∂P.μ, ∀ c ∈ f.range,
      x ∈ mappedFiber P Q Φ f c →
      mappedSimple P Q Φ (k • f) x = k * c := by
    rw [Filter.eventually_all_finset]
    intro c hc
    filter_upwards [mappedFiber_smul_ae P Q Φ hΦ k f c,
      mappedSimple_eq_on_fiber_ae_any P Q hP hQ Φ hΦ (k • f) (k * c)]
      with x hmap heq hxc
    exact heq (hmap hxc)
  filter_upwards [mapped_fibers_cover_ae P Q hP hQ Φ hΦ f, hef, hj]
    with x hcover hfe hje
  obtain ⟨c, hc, hxc⟩ := hcover
  rw [hfe c hc hxc, hje c hc hxc]

theorem mappedFiber_congr_ae
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f g : MeasureTheory.SimpleFunc Q.X ℂ) (hfg : f =ᵐ[Q.μ] g)
    (c : ℂ) :
    (fun x => x ∈ mappedFiber P Q Φ f c) =ᵐ[P.μ]
      fun x => x ∈ mappedFiber P Q Φ g c := by
  let B : (inducedMeasureAlgebra Q).carrier :=
    ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩
  let C : (inducedMeasureAlgebra Q).carrier :=
    ⟨g ⁻¹' {c}, g.measurableSet_preimage {c}⟩
  have hsets : (fun y => y ∈ B.1) =ᵐ[Q.μ] fun y => y ∈ C.1 := by
    filter_upwards [hfg] with y hy
    simp [B, C, hy]
  have heq : (inducedMeasureAlgebra Q).equiv B C := by
    rcases MeasureTheory.ae_eq_set.mp hsets with ⟨h₁, h₂⟩
    change Q.μ ((B.1 \ C.1) ∪ (C.1 \ B.1)) = 0
    exact MeasureTheory.measure_union_null h₁ h₂
  exact ae_eq_set_of_equiv P (hΦ.1 B C heq)

theorem mappedSimple_congr_ae
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f g : MeasureTheory.SimpleFunc Q.X ℂ) (hfg : f =ᵐ[Q.μ] g) :
    mappedSimple P Q Φ f =ᵐ[P.μ] mappedSimple P Q Φ g := by
  have hall : ∀ᵐ x ∂P.μ, ∀ c ∈ f.range,
      x ∈ mappedFiber P Q Φ f c →
      mappedSimple P Q Φ f x = c ∧ mappedSimple P Q Φ g x = c := by
    rw [Filter.eventually_all_finset]
    intro c hc
    filter_upwards [mappedFiber_congr_ae P Q Φ hΦ f g hfg c,
      mappedSimple_eq_on_fiber_ae P Q hP hQ Φ hΦ f hc,
      mappedSimple_eq_on_fiber_ae_any P Q hP hQ Φ hΦ g c]
      with x hfib hfe hge hxc
    exact ⟨hfe hxc, hge (hfib ▸ hxc)⟩
  filter_upwards [mapped_fibers_cover_ae P Q hP hQ Φ hΦ f, hall]
    with x hcover hx
  obtain ⟨c, hc, hxc⟩ := hcover
  exact (hx c hc hxc).1.trans (hx c hc hxc).2.symm

theorem mappedSimple_enorm_sq_ae
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f : MeasureTheory.SimpleFunc Q.X ℂ) :
    (fun x => ‖mappedSimple P Q Φ f x‖ₑ ^ (2 : ℝ)) =ᵐ[P.μ]
      fun x => ∑ c ∈ f.range,
        if x ∈ mappedFiber P Q Φ f c then ‖c‖ₑ ^ (2 : ℝ) else 0 := by
  filter_upwards [mapped_fibers_pairwise_ae P Q hP hQ Φ hΦ f] with x hx
  by_cases hex : ∃ c ∈ f.range, x ∈ mappedFiber P Q Φ f c
  · obtain ⟨c, hc, hxc⟩ := hex
    have hother (d : ℂ) (hd : d ∈ f.range) (hdc : d ≠ c) :
        x ∉ mappedFiber P Q Φ f d := by
      intro hxd
      exact hx d hd c hc hdc ⟨hxd, hxc⟩
    have hvalue : mappedSimple P Q Φ f x = c := by
      rw [mappedSimple, Finset.sum_eq_single c]
      · have hxc' :
          x ∈ (Φ.map ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩).1 := hxc
        rw [mappedIndicator, LtwoProjection.indicatorOne,
          Set.indicator_of_mem hxc']
        simp
      · intro d hd hdc
        have hxd' :
            x ∉ (Φ.map ⟨f ⁻¹' {d}, f.measurableSet_preimage {d}⟩).1 :=
          hother d hd hdc
        rw [mappedIndicator, LtwoProjection.indicatorOne,
          Set.indicator_of_notMem hxd']
        simp
      · exact fun hcnot => (hcnot hc).elim
    rw [hvalue, Finset.sum_eq_single c]
    · simp [hxc]
    · intro d hd hdc
      simp [hother d hd hdc]
    · exact fun hcnot => (hcnot hc).elim
  · have hnone (c : ℂ) (hc : c ∈ f.range) :
        x ∉ mappedFiber P Q Φ f c :=
      fun hxc => hex ⟨c, hc, hxc⟩
    have hzero : mappedSimple P Q Φ f x = 0 := by
      rw [mappedSimple]
      apply Finset.sum_eq_zero
      intro c hc
      have hxc' :
          x ∉ (Φ.map ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩).1 :=
        hnone c hc
      rw [mappedIndicator, LtwoProjection.indicatorOne,
        Set.indicator_of_notMem hxc']
      simp
    rw [hzero]
    simp only [enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    symm
    apply Finset.sum_eq_zero
    intro c hc
    simp [hnone c hc]

theorem mappedSimple_lintegral_enorm_sq
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f : MeasureTheory.SimpleFunc Q.X ℂ) :
    (∫⁻ x, ‖mappedSimple P Q Φ f x‖ₑ ^ (2 : ℝ) ∂P.μ) =
      ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂Q.μ := by
  rw [MeasureTheory.lintegral_congr_ae
    (mappedSimple_enorm_sq_ae P Q hP hQ Φ hΦ f)]
  let F : ℂ → P.X → ENNReal := fun c x =>
    if x ∈ mappedFiber P Q Φ f c then ‖c‖ₑ ^ (2 : ℝ) else 0
  have hFm (c : ℂ) : Measurable (F c) :=
    measurable_const.piecewise
      (Φ.map ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩).2 measurable_const
  have hsum (s : Finset ℂ) :
      (∫⁻ x, ∑ c ∈ s, F c x ∂P.μ) =
        ∑ c ∈ s, ∫⁻ x, F c x ∂P.μ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert c s hc ih =>
        simp only [Finset.sum_insert hc]
        rw [MeasureTheory.lintegral_add_left (hFm c), ih]
  change (∫⁻ x, ∑ c ∈ f.range, F c x ∂P.μ) =
    ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂Q.μ
  rw [hsum f.range]
  have hFint (c : ℂ) :
      (∫⁻ x, F c x ∂P.μ) =
        ‖c‖ₑ ^ (2 : ℝ) * P.μ (mappedFiber P Q Φ f c) := by
    have hFindicator :
        F c = (mappedFiber P Q Φ f c).indicator
          (fun _ => ‖c‖ₑ ^ (2 : ℝ)) := by
      funext x
      by_cases hx : x ∈ mappedFiber P Q Φ f c <;> simp [F, hx]
    rw [hFindicator]
    exact MeasureTheory.lintegral_indicator_const
      (Φ.map ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩).2 _
  simp_rw [hFint]
  simp_rw [show ∀ c, P.μ (mappedFiber P Q Φ f c) =
      Q.μ (f ⁻¹' {c}) by
    intro c
    exact map_measure P Q hP hQ Φ hΦ
      ⟨f ⁻¹' {c}, f.measurableSet_preimage {c}⟩]
  let nf : MeasureTheory.SimpleFunc Q.X ENNReal :=
    f.map (fun c => ‖c‖ₑ ^ (2 : ℝ))
  calc
    (∑ c ∈ f.range, ‖c‖ₑ ^ (2 : ℝ) * Q.μ (f ⁻¹' {c})) =
        nf.lintegral Q.μ := (MeasureTheory.SimpleFunc.map_lintegral
          (fun c : ℂ => ‖c‖ₑ ^ (2 : ℝ)) f).symm
    _ = ∫⁻ y, nf y ∂Q.μ :=
      (MeasureTheory.SimpleFunc.lintegral_eq_lintegral nf Q.μ).symm
    _ = ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂Q.μ := by
      rfl

theorem mappedSimple_eLpNorm_two
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f : MeasureTheory.SimpleFunc Q.X ℂ) :
    eLpNorm (mappedSimple P Q Φ f) 2 P.μ = eLpNorm f 2 Q.μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num
  congr 1
  simpa only [ENNReal.rpow_two] using
    mappedSimple_lintegral_enorm_sq P Q hP hQ Φ hΦ f

def simpleToLp
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (f : MeasureTheory.Lp.simpleFunc ℂ 2 Q.μ) :
    MeasureTheory.Lp ℂ 2 P.μ :=
  let sf := MeasureTheory.Lp.simpleFunc.toSimpleFunc f
  let hf := mappedSimple_memLp P Q hP Φ sf 2
  hf.toLp (mappedSimple P Q Φ sf)

def simpleLinearMap
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ) :
    MeasureTheory.Lp.simpleFunc ℂ 2 Q.μ →ₗ[ℂ]
      MeasureTheory.Lp ℂ 2 P.μ where
  toFun := simpleToLp P Q hP Φ
  map_add' f g := by
    let sf := MeasureTheory.Lp.simpleFunc.toSimpleFunc f
    let sg := MeasureTheory.Lp.simpleFunc.toSimpleFunc g
    let sfg := MeasureTheory.Lp.simpleFunc.toSimpleFunc (f + g)
    let hmf := mappedSimple_memLp P Q hP Φ sf 2
    let hmg := mappedSimple_memLp P Q hP Φ sg 2
    let hmfg := mappedSimple_memLp P Q hP Φ sfg 2
    apply MeasureTheory.Lp.ext
    have hsource : sfg =ᵐ[Q.μ] sf + sg :=
      MeasureTheory.Lp.simpleFunc.add_toSimpleFunc f g
    exact hmfg.coeFn_toLp
      |>.trans (mappedSimple_congr_ae P Q hP hQ Φ hΦ sfg (sf + sg) hsource)
      |>.trans (mappedSimple_add_ae P Q hP hQ Φ hΦ sf sg)
      |>.trans ((hmf.coeFn_toLp.add hmg.coeFn_toLp).symm)
      |>.trans (MeasureTheory.Lp.coeFn_add
        (simpleToLp P Q hP Φ f) (simpleToLp P Q hP Φ g)).symm
  map_smul' k f := by
    let sf := MeasureTheory.Lp.simpleFunc.toSimpleFunc f
    let skf := MeasureTheory.Lp.simpleFunc.toSimpleFunc (k • f)
    let hmf := mappedSimple_memLp P Q hP Φ sf 2
    let hmkf := mappedSimple_memLp P Q hP Φ skf 2
    apply MeasureTheory.Lp.ext
    have hsource : skf =ᵐ[Q.μ] k • sf :=
      MeasureTheory.Lp.simpleFunc.smul_toSimpleFunc k f
    exact hmkf.coeFn_toLp
      |>.trans (mappedSimple_congr_ae P Q hP hQ Φ hΦ skf (k • sf) hsource)
      |>.trans (mappedSimple_smul_ae P Q hP hQ Φ hΦ k sf)
      |>.trans ((hmf.coeFn_toLp.const_smul k).symm)
      |>.trans (MeasureTheory.Lp.coeFn_smul k (simpleToLp P Q hP Φ f)).symm

theorem norm_simpleLinearMap
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f : MeasureTheory.Lp.simpleFunc ℂ 2 Q.μ) :
    ‖simpleLinearMap P Q hP hQ Φ hΦ f‖ = ‖f‖ := by
  rw [show simpleLinearMap P Q hP hQ Φ hΦ f =
      simpleToLp P Q hP Φ f from rfl]
  rw [simpleToLp, MeasureTheory.Lp.norm_toLp]
  rw [mappedSimple_eLpNorm_two P Q hP hQ Φ hΦ
    (MeasureTheory.Lp.simpleFunc.toSimpleFunc f)]
  exact (MeasureTheory.Lp.simpleFunc.norm_toSimpleFunc f).symm

def simpleContinuousLinearMap
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ) :
    MeasureTheory.Lp.simpleFunc ℂ 2 Q.μ →L[ℂ]
      MeasureTheory.Lp ℂ 2 P.μ :=
  (simpleLinearMap P Q hP hQ Φ hΦ).mkContinuous 1 fun f => by
    rw [norm_simpleLinearMap P Q hP hQ Φ hΦ f, one_mul]

def ltwoMap
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ) :
    MeasureTheory.Lp ℂ 2 Q.μ →L[ℂ] MeasureTheory.Lp ℂ 2 P.μ :=
  ContinuousLinearMap.extend (simpleContinuousLinearMap P Q hP hQ Φ hΦ)
    (MeasureTheory.Lp.simpleFunc.coeToLp Q.X ℂ ℂ)

theorem ltwoMap_apply_simple
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f : MeasureTheory.Lp.simpleFunc ℂ 2 Q.μ) :
    ltwoMap P Q hP hQ Φ hΦ
        ((MeasureTheory.Lp.simpleFunc.coeToLp Q.X ℂ ℂ) f) =
      simpleContinuousLinearMap P Q hP hQ Φ hΦ f := by
  apply ContinuousLinearMap.extend_eq
  · simpa [MeasureTheory.Lp.simpleFunc.coeToLp] using
      (MeasureTheory.Lp.simpleFunc.denseRange
        (E := ℂ) (p := (2 : ENNReal)) (μ := Q.μ) (by norm_num))
  · simpa [MeasureTheory.Lp.simpleFunc.coeToLp] using
      (MeasureTheory.Lp.simpleFunc.isUniformInducing
        (E := ℂ) (p := (2 : ENNReal)) (μ := Q.μ))

theorem norm_ltwoMap
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f : MeasureTheory.Lp ℂ 2 Q.μ) :
    ‖ltwoMap P Q hP hQ Φ hΦ f‖ = ‖f‖ := by
  let e : MeasureTheory.Lp.simpleFunc ℂ 2 Q.μ →L[ℂ]
      MeasureTheory.Lp ℂ 2 Q.μ :=
    MeasureTheory.Lp.simpleFunc.coeToLp Q.X ℂ ℂ
  have hdense : DenseRange e := by
    simpa [e, MeasureTheory.Lp.simpleFunc.coeToLp] using
      (MeasureTheory.Lp.simpleFunc.denseRange
        (E := ℂ) (p := (2 : ENNReal)) (μ := Q.μ) (by norm_num))
  refine hdense.induction_on
    (p := fun g => ‖ltwoMap P Q hP hQ Φ hΦ g‖ = ‖g‖) f ?_ ?_
  · exact isClosed_eq
      (continuous_norm.comp (ltwoMap P Q hP hQ Φ hΦ).continuous)
      continuous_norm
  · intro g
    rw [ltwoMap_apply_simple P Q hP hQ Φ hΦ g]
    change ‖simpleLinearMap P Q hP hQ Φ hΦ g‖ =
      ‖(g : MeasureTheory.Lp ℂ 2 Q.μ)‖
    exact norm_simpleLinearMap P Q hP hQ Φ hΦ g

noncomputable def inverseHom
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraIsomorphism Φ) :
    MeasureAlgebraHomData (inducedMeasureAlgebra P)
      (inducedMeasureAlgebra Q) where
  map := fun A => Classical.choose (hΦ.2.2 A)

theorem inverseHom_spec
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraIsomorphism Φ)
    (A : (inducedMeasureAlgebra P).carrier) :
    (inducedMeasureAlgebra P).equiv
      (Φ.map ((inverseHom P Q Φ hΦ).map A)) A :=
  Classical.choose_spec (hΦ.2.2 A)

theorem inverseHom_isMeasureAlgebraHom
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraIsomorphism Φ) :
    IsMeasureAlgebraHom (inverseHom P Q Φ hΦ) := by
  let AP := inducedMeasureAlgebra P
  let AQ := inducedMeasureAlgebra Q
  have hAP : IsMeasureAlgebra AP :=
    isMeasureAlgebra_inducedMeasureAlgebra P hP
  have hAQ : IsMeasureAlgebra AQ :=
    isMeasureAlgebra_inducedMeasureAlgebra Q hQ
  let Ψ := inverseHom P Q Φ hΦ
  have hspec (A : AP.carrier) : AP.equiv (Φ.map (Ψ.map A)) A :=
    inverseHom_spec P Q Φ hΦ A
  have hinj {B C : AQ.carrier} (h : AP.equiv (Φ.map B) (Φ.map C)) :
      AQ.equiv B C :=
    hΦ.2.1 B C h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A B hAB
    apply hinj
    exact hAP.1.trans (hspec A)
      (hAP.1.trans hAB (hAP.1.symm (hspec B)))
  · intro A B
    apply hinj
    have hmap := hΦ.1.2.1 (Ψ.map A) (Ψ.map B)
    have hcongr := (hAP.2.1 _ _ _ _
      (hspec A) (hspec B)).1
    exact hAP.1.trans (hspec (AP.union A B))
      (hAP.1.trans (hAP.1.symm hcongr) (hAP.1.symm hmap))
  · intro A
    apply hinj
    have hmap := hΦ.1.2.2.1 (Ψ.map A)
    have hcongr := hAP.2.2.1 _ _ (hspec A)
    exact hAP.1.trans (hspec (AP.compl A))
      (hAP.1.trans (hAP.1.symm hcongr) (hAP.1.symm hmap))
  · intro f
    apply hinj
    have hmap := hΦ.1.2.2.2.1 (fun n => Ψ.map (f n))
    have hcongr : AP.equiv
        (AP.iUnion (fun n => Φ.map (Ψ.map (f n)))) (AP.iUnion f) := by
      change P.μ (Chapter00.symmDiff
        (⋃ n, (Φ.map (Ψ.map (f n))).1) (⋃ n, (f n).1)) = 0
      apply MeasureTheory.measure_mono_null
        (t := ⋃ n, Chapter00.symmDiff
          (Φ.map (Ψ.map (f n))).1 (f n).1)
      · intro x hx
        simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff,
          Set.mem_iUnion] at hx ⊢
        rcases hx with ⟨⟨n, hn⟩, hall⟩ | ⟨⟨n, hn⟩, hall⟩
        · exact ⟨n, Or.inl ⟨hn, fun h => hall ⟨n, h⟩⟩⟩
        · exact ⟨n, Or.inr ⟨hn, fun h => hall ⟨n, h⟩⟩⟩
      · apply MeasureTheory.measure_iUnion_null
        intro n
        exact hspec (f n)
    exact hAP.1.trans (hspec (AP.iUnion f))
      (hAP.1.trans (hAP.1.symm hcongr) (hAP.1.symm hmap))
  · intro A
    calc
      AQ.measure (Ψ.map A) = AP.measure (Φ.map (Ψ.map A)) := by
        symm
        exact hΦ.1.2.2.2.2 (Ψ.map A)
      _ = AP.measure A := hAP.2.2.2.1 _ _ (hspec A)

def indicatorSimpleFunc {X : Type*} [MeasurableSpace X]
    (A : Set X) (hA : MeasurableSet A) :
    MeasureTheory.SimpleFunc X ℂ :=
  (MeasureTheory.SimpleFunc.const X 1).piecewise A hA
    (MeasureTheory.SimpleFunc.const X 0)

@[simp] theorem indicatorSimpleFunc_apply {X : Type*} [MeasurableSpace X]
    (A : Set X) (hA : MeasurableSet A) (x : X) :
    indicatorSimpleFunc A hA x = LtwoProjection.indicatorOne A x := by
  by_cases hx : x ∈ A <;>
    simp [indicatorSimpleFunc, LtwoProjection.indicatorOne, hx]

theorem mappedSimple_indicator_ae
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (B : (inducedMeasureAlgebra Q).carrier) :
    mappedSimple P Q Φ (indicatorSimpleFunc B.1 B.2) =ᵐ[P.μ]
      mappedIndicator P Q Φ B := by
  let f := indicatorSimpleFunc B.1 B.2
  have hall : ∀ᵐ x ∂P.μ, ∀ c ∈ f.range,
      x ∈ mappedFiber P Q Φ f c →
        mappedSimple P Q Φ f x = c := by
    rw [Filter.eventually_all_finset]
    intro c hc
    exact mappedSimple_eq_on_fiber_ae P Q hP hQ Φ hΦ f hc
  have hpre : (⟨f ⁻¹' ({1} : Set ℂ),
      f.measurableSet_preimage {1}⟩ :
      (inducedMeasureAlgebra Q).carrier) = B := by
    apply Subtype.ext
    ext y
    by_cases hy : y ∈ B.1 <;>
      simp [f, indicatorSimpleFunc, hy]
  have hfiberOne :
      mappedFiber P Q Φ f 1 = (Φ.map B).1 := by
    simp only [mappedFiber]
    rw [hpre]
  filter_upwards
    [mapped_fibers_cover_ae P Q hP hQ Φ hΦ f, hall,
      mapped_fibers_ae_disjoint P Q hP hQ Φ hΦ f
        (by norm_num : (0 : ℂ) ≠ 1)]
    with x hcover hx hdis
  obtain ⟨c, hc, hxc⟩ := hcover
  rw [hx c hc hxc]
  have hc01 : c = 0 ∨ c = 1 := by
    rcases MeasureTheory.SimpleFunc.mem_range.mp hc with ⟨y, rfl⟩
    by_cases hy : y ∈ B.1 <;>
      simp [f, indicatorSimpleFunc, hy]
  rcases hc01 with rfl | rfl
  · have hxnot : x ∉ (Φ.map B).1 := by
      intro hxB
      have hxone : x ∈ mappedFiber P Q Φ f 1 := by
        rwa [hfiberOne]
      exact hdis ⟨hxc, hxone⟩
    simp [mappedIndicator, LtwoProjection.indicatorOne, hxnot]
  · have hxB : x ∈ (Φ.map B).1 := by
      rwa [← hfiberOne]
    simp [mappedIndicator, LtwoProjection.indicatorOne, hxB]

theorem ltwoMap_indicator_one
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (B : (inducedMeasureAlgebra Q).carrier) :
    ltwoMap P Q hP hQ Φ hΦ
        ((MeasureTheory.Lp.simpleFunc.indicatorConst
          (2 : ENNReal) B.2
            (by
              letI : IsProbabilityMeasure Q.μ := hQ
              exact MeasureTheory.measure_ne_top Q.μ B.1)
            (1 : ℂ) :
          MeasureTheory.Lp.simpleFunc ℂ 2 Q.μ) :
          MeasureTheory.Lp ℂ 2 Q.μ) =
      (mappedIndicator_memLp P Q hP Φ B 2).toLp
        (mappedIndicator P Q Φ B) := by
  letI : IsProbabilityMeasure Q.μ := hQ
  let s : MeasureTheory.Lp.simpleFunc ℂ 2 Q.μ :=
    MeasureTheory.Lp.simpleFunc.indicatorConst
      (2 : ENNReal) B.2 (MeasureTheory.measure_ne_top Q.μ B.1) (1 : ℂ)
  change ltwoMap P Q hP hQ Φ hΦ
      (s : MeasureTheory.Lp ℂ 2 Q.μ) =
    (mappedIndicator_memLp P Q hP Φ B 2).toLp
      (mappedIndicator P Q Φ B)
  rw [show (s : MeasureTheory.Lp ℂ 2 Q.μ) =
      (MeasureTheory.Lp.simpleFunc.coeToLp Q.X ℂ ℂ) s by rfl]
  rw [ltwoMap_apply_simple P Q hP hQ Φ hΦ s]
  change simpleToLp P Q hP Φ s =
    (mappedIndicator_memLp P Q hP Φ B 2).toLp
      (mappedIndicator P Q Φ B)
  let sf := MeasureTheory.Lp.simpleFunc.toSimpleFunc s
  let hmf := mappedSimple_memLp P Q hP Φ sf 2
  apply MeasureTheory.Lp.ext
  have hsource : sf =ᵐ[Q.μ] indicatorSimpleFunc B.1 B.2 := by
    simpa [s, indicatorSimpleFunc] using
      (MeasureTheory.Lp.simpleFunc.toSimpleFunc_indicatorConst
        (p := (2 : ENNReal)) B.2
        (MeasureTheory.measure_ne_top Q.μ B.1) (1 : ℂ))
  exact hmf.coeFn_toLp
    |>.trans (mappedSimple_congr_ae P Q hP hQ Φ hΦ sf
      (indicatorSimpleFunc B.1 B.2) hsource)
    |>.trans (mappedSimple_indicator_ae P Q hP hQ Φ hΦ B)
    |>.trans ((mappedIndicator_memLp P Q hP Φ B 2).coeFn_toLp.symm)

theorem ltwoMap_surjective
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraIsomorphism Φ) :
    Function.Surjective (ltwoMap P Q hP hQ Φ hΦ.1) := by
  letI : IsProbabilityMeasure P.μ := hP
  letI : IsProbabilityMeasure Q.μ := hQ
  let L := ltwoMap P Q hP hQ Φ hΦ.1
  have hLiso : Isometry L :=
    AddMonoidHomClass.isometry_of_norm L
      (norm_ltwoMap P Q hP hQ Φ hΦ.1)
  have hclosed : IsClosed (Set.range L) :=
    hLiso.isClosedEmbedding.isClosed_range
  have hsimple (g : MeasureTheory.Lp.simpleFunc ℂ 2 P.μ) :
      (g : MeasureTheory.Lp ℂ 2 P.μ) ∈ Set.range L := by
    induction g using MeasureTheory.Lp.simpleFunc.induction
        (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤) with
    | indicatorConst c hA hμA =>
        rename_i A
        let A' : (inducedMeasureAlgebra P).carrier := ⟨A, hA⟩
        obtain ⟨B, hBA⟩ := hΦ.2.2 A'
        let b : MeasureTheory.Lp.simpleFunc ℂ 2 Q.μ :=
          MeasureTheory.Lp.simpleFunc.indicatorConst
            (2 : ENNReal) B.2 (MeasureTheory.measure_ne_top Q.μ B.1) (1 : ℂ)
        refine ⟨c • (b : MeasureTheory.Lp ℂ 2 Q.μ), ?_⟩
        change L (c • (b : MeasureTheory.Lp ℂ 2 Q.μ)) =
          ((MeasureTheory.Lp.simpleFunc.indicatorConst
            (2 : ENNReal) hA hμA.ne c :
            MeasureTheory.Lp.simpleFunc ℂ 2 P.μ) :
            MeasureTheory.Lp ℂ 2 P.μ)
        rw [map_smul]
        change c • ltwoMap P Q hP hQ Φ hΦ.1
            (b : MeasureTheory.Lp ℂ 2 Q.μ) = _
        rw [show ltwoMap P Q hP hQ Φ hΦ.1
            (b : MeasureTheory.Lp ℂ 2 Q.μ) =
          (mappedIndicator_memLp P Q hP Φ B 2).toLp
            (mappedIndicator P Q Φ B) by
          exact ltwoMap_indicator_one P Q hP hQ Φ hΦ.1 B]
        change c • (mappedIndicator_memLp P Q hP Φ B 2).toLp
            (mappedIndicator P Q Φ B) =
          MeasureTheory.indicatorConstLp (2 : ENNReal) hA hμA.ne c
        apply MeasureTheory.Lp.ext
        filter_upwards
          [MeasureTheory.Lp.coeFn_smul c
            ((mappedIndicator_memLp P Q hP Φ B 2).toLp
              (mappedIndicator P Q Φ B)),
            (mappedIndicator_memLp P Q hP Φ B 2).coeFn_toLp,
            ae_eq_set_of_equiv P hBA,
            MeasureTheory.indicatorConstLp_coeFn
              (p := (2 : ENNReal)) (s := A) (hs := hA)
              (hμs := hμA.ne) (c := c)]
          with x hxsmul hxmap hxset hxtarget
        rw [hxsmul, hxtarget]
        change c * ((mappedIndicator_memLp P Q hP Φ B 2).toLp
          (mappedIndicator P Q Φ B) : P.X → ℂ) x =
            A.indicator (fun _ => c) x
        rw [hxmap]
        by_cases hxA : x ∈ A
        · have hxΦ : x ∈ (Φ.map B).1 := hxset.mpr hxA
          simp [mappedIndicator, LtwoProjection.indicatorOne, hxA, hxΦ]
        · have hxΦ : x ∉ (Φ.map B).1 := fun h => hxA (hxset.mp h)
          simp [mappedIndicator, LtwoProjection.indicatorOne, hxA, hxΦ]
    | add hf hg hdis hfRange hgRange =>
        obtain ⟨x, hx⟩ := hfRange
        obtain ⟨y, hy⟩ := hgRange
        refine ⟨x + y, ?_⟩
        rw [map_add, hx, hy]
        rfl
  have hdense :
      DenseRange (MeasureTheory.Lp.simpleFunc.coeToLp P.X ℂ ℂ :
        MeasureTheory.Lp.simpleFunc ℂ 2 P.μ →L[ℂ]
          MeasureTheory.Lp ℂ 2 P.μ) := by
    simpa [MeasureTheory.Lp.simpleFunc.coeToLp] using
      (MeasureTheory.Lp.simpleFunc.denseRange
        (E := ℂ) (p := (2 : ENNReal)) (μ := P.μ) (by norm_num))
  intro f
  exact hdense.induction_on f hclosed hsimple

noncomputable def rawLtwoMap
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f : Q.X → ℂ) : P.X → ℂ :=
  if hf : MemLp f 2 Q.μ then
    (ltwoMap P Q hP hQ Φ hΦ (hf.toLp f) :
      P.X → ℂ)
  else 0

theorem rawLtwoMap_apply
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f : Q.X → ℂ) (hf : MemLp f 2 Q.μ) :
    rawLtwoMap P Q hP hQ Φ hΦ f =
      (ltwoMap P Q hP hQ Φ hΦ (hf.toLp f) :
        P.X → ℂ) := by
  simp [rawLtwoMap, hf]

theorem rawLtwoMap_simple
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f : MeasureTheory.SimpleFunc Q.X ℂ)
    (hf : MemLp f 2 Q.μ) :
    rawLtwoMap P Q hP hQ Φ hΦ f =ᵐ[P.μ]
      mappedSimple P Q Φ f := by
  let s : MeasureTheory.Lp.simpleFunc ℂ 2 Q.μ :=
    MeasureTheory.Lp.simpleFunc.toLp f hf
  rw [rawLtwoMap_apply P Q hP hQ Φ hΦ f hf]
  change (ltwoMap P Q hP hQ Φ hΦ
      (s : MeasureTheory.Lp ℂ 2 Q.μ) : P.X → ℂ) =ᵐ[P.μ] _
  rw [show (s : MeasureTheory.Lp ℂ 2 Q.μ) =
      (MeasureTheory.Lp.simpleFunc.coeToLp Q.X ℂ ℂ) s by rfl]
  rw [ltwoMap_apply_simple P Q hP hQ Φ hΦ s]
  let sf := MeasureTheory.Lp.simpleFunc.toSimpleFunc s
  let hmf := mappedSimple_memLp P Q hP Φ sf 2
  exact hmf.coeFn_toLp.trans
    (mappedSimple_congr_ae P Q hP hQ Φ hΦ sf f
      (MeasureTheory.Lp.simpleFunc.toSimpleFunc_toLp f hf))

theorem rawLtwoMap_simple_mul
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f g : MeasureTheory.SimpleFunc Q.X ℂ)
    (hf : MemLp f 2 Q.μ) (hg : MemLp g 2 Q.μ)
    (hfg : MemLp (fun y => f y * g y) 2 Q.μ) :
    rawLtwoMap P Q hP hQ Φ hΦ (fun y => f y * g y) =ᵐ[P.μ]
      fun x => rawLtwoMap P Q hP hQ Φ hΦ f x *
        rawLtwoMap P Q hP hQ Φ hΦ g x := by
  have hfg' : MemLp (f * g) 2 Q.μ := by
    simpa only [MeasureTheory.SimpleFunc.coe_mul] using hfg
  have hcoemul :
      (fun y => f y * g y) = (fun y => (f * g) y) := by
    funext y
    rfl
  rw [hcoemul]
  filter_upwards [rawLtwoMap_simple P Q hP hQ Φ hΦ (f * g) hfg',
    mappedSimple_mul_ae P Q hP hQ Φ hΦ f g,
    rawLtwoMap_simple P Q hP hQ Φ hΦ f hf,
    rawLtwoMap_simple P Q hP hQ Φ hΦ g hg]
    with x hprod hmul hf' hg'
  rw [hprod, hmul, hf', hg']

theorem rawLtwoMap_one
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ) :
    rawLtwoMap P Q hP hQ Φ hΦ (fun _ => (1 : ℂ)) =ᵐ[P.μ]
      fun _ => (1 : ℂ) := by
  let f : MeasureTheory.SimpleFunc Q.X ℂ :=
    MeasureTheory.SimpleFunc.const Q.X 1
  have hf : MemLp f 2 Q.μ := by
    have h :=
      LtwoProjection.indicatorOne_memLp Q hQ MeasurableSet.univ 2
    simpa [f, LtwoProjection.indicatorOne] using h
  have hone : (fun _ : Q.X => (1 : ℂ)) = fun y => f y := by
    funext y
    rfl
  rw [hone]
  have hall : ∀ᵐ x ∂P.μ, ∀ c ∈ f.range,
      x ∈ mappedFiber P Q Φ f c →
        mappedSimple P Q Φ f x = c := by
    rw [Filter.eventually_all_finset]
    intro c hc
    exact mappedSimple_eq_on_fiber_ae P Q hP hQ Φ hΦ f hc
  filter_upwards [rawLtwoMap_simple P Q hP hQ Φ hΦ f hf,
    mapped_fibers_cover_ae P Q hP hQ Φ hΦ f, hall]
    with x hraw hcover hx
  obtain ⟨c, hc, hxc⟩ := hcover
  have hcOne : c = 1 := by
    rcases MeasureTheory.SimpleFunc.mem_range.mp hc with ⟨y, rfl⟩
    rfl
  rw [hraw, hx c hc hxc, hcOne]

theorem rawLtwoMap_ae
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f g : Q.X → ℂ) (hf : MemLp f 2 Q.μ) (hg : MemLp g 2 Q.μ)
    (hfg : f =ᵐ[Q.μ] g) :
    rawLtwoMap P Q hP hQ Φ hΦ f =ᵐ[P.μ]
      rawLtwoMap P Q hP hQ Φ hΦ g := by
  have hto : hf.toLp f = hg.toLp g :=
    MeasureTheory.MemLp.toLp_congr hf hg hfg
  rw [rawLtwoMap_apply P Q hP hQ Φ hΦ f hf,
    rawLtwoMap_apply P Q hP hQ Φ hΦ g hg, hto]

theorem rawLtwoMap_add
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f g : Q.X → ℂ) (hf : MemLp f 2 Q.μ) (hg : MemLp g 2 Q.μ) :
    rawLtwoMap P Q hP hQ Φ hΦ (fun y => f y + g y) =ᵐ[P.μ]
      fun x => rawLtwoMap P Q hP hQ Φ hΦ f x +
        rawLtwoMap P Q hP hQ Φ hΦ g x := by
  have hfg : MemLp (fun y => f y + g y) 2 Q.μ := hf.add hg
  have hto :
      hfg.toLp (fun y => f y + g y) = hf.toLp f + hg.toLp g := by
    exact hf.toLp_add hg
  rw [rawLtwoMap_apply P Q hP hQ Φ hΦ _ hfg,
    rawLtwoMap_apply P Q hP hQ Φ hΦ f hf,
    rawLtwoMap_apply P Q hP hQ Φ hΦ g hg,
    hto, map_add]
  exact MeasureTheory.Lp.coeFn_add _ _

theorem rawLtwoMap_smul
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (c : ℂ) (f : Q.X → ℂ) (hf : MemLp f 2 Q.μ) :
    rawLtwoMap P Q hP hQ Φ hΦ (fun y => c * f y) =ᵐ[P.μ]
      fun x => c * rawLtwoMap P Q hP hQ Φ hΦ f x := by
  have hcf : MemLp (fun y => c * f y) 2 Q.μ := hf.const_mul c
  have hto :
      hcf.toLp (fun y => c * f y) = c • hf.toLp f := by
    exact hf.toLp_const_smul c
  rw [rawLtwoMap_apply P Q hP hQ Φ hΦ _ hcf,
    rawLtwoMap_apply P Q hP hQ Φ hΦ f hf,
    hto, map_smul]
  exact MeasureTheory.Lp.coeFn_smul c _

theorem rawLtwoMap_ltwo
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraHom Φ)
    (f : Q.X → ℂ) (hf : MemLp f 2 Q.μ) :
    MemLp (rawLtwoMap P Q hP hQ Φ hΦ f) 2 P.μ ∧
      eLpNorm (rawLtwoMap P Q hP hQ Φ hΦ f) 2 P.μ =
        eLpNorm f 2 Q.μ := by
  rw [rawLtwoMap_apply P Q hP hQ Φ hΦ f hf]
  let F := ltwoMap P Q hP hQ Φ hΦ (hf.toLp f)
  have hF : MemLp (F : P.X → ℂ) 2 P.μ := MeasureTheory.Lp.memLp F
  refine ⟨hF, ?_⟩
  have hnorm : ‖F‖ = ‖hf.toLp f‖ :=
    norm_ltwoMap P Q hP hQ Φ hΦ (hf.toLp f)
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def] at hnorm
  have he :
      eLpNorm (F : P.X → ℂ) 2 P.μ =
        eLpNorm (hf.toLp f : Q.X → ℂ) 2 Q.μ :=
    (ENNReal.toReal_eq_toReal_iff'
      (MeasureTheory.Lp.memLp F).2.ne
      (MeasureTheory.Lp.memLp (hf.toLp f)).2.ne).mp hnorm
  exact he.trans (eLpNorm_congr_ae hf.coeFn_toLp)

theorem rawLtwoMap_dense
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q)
      (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraIsomorphism Φ)
    (h : P.X → ℂ) (hh : MemLp h 2 P.μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : Q.X → ℂ, MemLp f 2 Q.μ ∧
      eLpNorm (fun x => h x -
        rawLtwoMap P Q hP hQ Φ hΦ.1 f x) 2 P.μ <
        ENNReal.ofReal ε := by
  obtain ⟨F, hF⟩ :=
    ltwoMap_surjective P Q hP hQ Φ hΦ (hh.toLp h)
  let f : Q.X → ℂ := fun y => F y
  have hf : MemLp f 2 Q.μ := MeasureTheory.Lp.memLp F
  refine ⟨f, hf, ?_⟩
  have hraw :
      rawLtwoMap P Q hP hQ Φ hΦ.1 f =ᵐ[P.μ] h := by
    rw [rawLtwoMap_apply P Q hP hQ Φ hΦ.1 f hf,
      MeasureTheory.Lp.toLp_coeFn F hf, hF]
    exact hh.coeFn_toLp
  have hz : (fun x => h x -
      rawLtwoMap P Q hP hQ Φ hΦ.1 f x) =ᵐ[P.μ]
      fun _ => (0 : ℂ) := by
    filter_upwards [hraw] with x hx
    rw [hx, sub_self]
  rw [eLpNorm_congr_ae hz]
  simpa using ENNReal.ofReal_pos.mpr hε

end Chapter04.MeasureAlgebraLtwo
