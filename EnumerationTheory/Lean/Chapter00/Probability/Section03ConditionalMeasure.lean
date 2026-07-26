import Chapter00.Probability.Section03Representation
import Mathlib.Probability.Kernel.Condexp

noncomputable section

open Classical Filter MeasureTheory ProbabilityTheory

namespace Chapter00.Section03

private def conditionalFamilyMS {X : Type*} (A : SetFamily X)
    (hA : IsSigmaAlgebraFamily A) : MeasurableSpace X where
  MeasurableSet' := A
  measurableSet_empty := by simpa using hA.2.1 Set.univ hA.1
  measurableSet_compl := hA.2.1
  measurableSet_iUnion := hA.2.2

private theorem sigmaUnion {X : Type*} {A : SetFamily X}
    (hA : IsSigmaAlgebraFamily A) {s t : Set X} (hs : s ∈ A) (ht : t ∈ A) :
    s ∪ t ∈ A := by
  let U : ℕ → Set X := fun n => if n = 0 then s else t
  have hU : ∀ n, U n ∈ A := fun n => by by_cases hn : n = 0 <;> simp [U, hn, hs, ht]
  have heq : ⋃ n, U n = s ∪ t := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hmem⟩
      by_cases hn : n = 0
      · left; simpa [U, hn] using hmem
      · right; simpa [U, hn] using hmem
    · intro hx
      rcases hx with hx | hx
      · exact Set.mem_iUnion.mpr ⟨0, by simpa [U] using hx⟩
      · exact Set.mem_iUnion.mpr ⟨1, by simpa [U] using hx⟩
  rw [← heq]
  exact hA.2.2 U hU

private theorem sigmaInter {X : Type*} {A : SetFamily X}
    (hA : IsSigmaAlgebraFamily A) {s t : Set X} (hs : s ∈ A) (ht : t ∈ A) :
    s ∩ t ∈ A := by
  have hc := hA.2.1 _ (sigmaUnion hA (hA.2.1 s hs) (hA.2.1 t ht))
  convert hc using 1 <;> ext x <;> simp

theorem conditionalMeasureFamilyAux
    (P : BasicProbabilitySpaceData) [StandardBorelSpace P.X]
    (A : SetFamily P.X) :
    IsSigmaAlgebraFamily A -> A ⊆ P.𝓧 ->
      ∃ E : ConditionalExpectationData P A,
        ∃ D : ConditionalMeasureFamily P A,
          IsConditionalExpectation P A E ∧ IsConditionalMeasureFamily P A E D ∧
          (CountablyGeneratedFamily A ->
            (∀ x ∈ D.fullSet,
              D.measureAt x (⋂₀ {B : Set P.X | B ∈ A ∧ x ∈ B}) = 1) ∧
            ∀ x ∈ D.fullSet, ∀ y ∈ D.fullSet,
              (⋂₀ {B : Set P.X | B ∈ A ∧ x ∈ B}) =
                (⋂₀ {B : Set P.X | B ∈ A ∧ y ∈ B}) ->
              D.measureAt x = D.measureAt y) ∧
          ∀ C : SetFamily P.X, IsSigmaAlgebraFamily C -> C ⊆ P.𝓧 ->
            ∀ EC : ConditionalExpectationData P C,
            ∀ DC : ConditionalMeasureFamily P C,
              IsConditionalExpectation P C EC ->
              IsConditionalMeasureFamily P C EC DC ->
              Section01.completedSigmaAlgebraFamily A P.μ =
                Section01.completedSigmaAlgebraFamily C P.μ ->
              ∀ᵐ x ∂P.μ, D.measureAt x = DC.measureAt x := by
  intro hA hsub
  let mA : MeasurableSpace P.X := conditionalFamilyMS A hA
  have hm : mA ≤ P.measurableSpace := fun _ hs => hsub hs
  letI : SigmaFinite (P.μ.trim hm) := inferInstance
  let E : ConditionalExpectationData P A :=
    ⟨fun f => condExp mA P.μ f⟩
  let CK : @Kernel P.X P.X mA P.measurableSpace :=
    @condExpKernel P.X P.measurableSpace inferInstance P.μ inferInstance mA
  let K : P.X → @Measure P.X P.measurableSpace := fun x => CK x
  let G : ℕ → Set P.X := if h : CountablyGeneratedFamily A then Classical.choose h else fun _ => ∅
  let good : Set P.X := ⋂ n, {x | K x (G n) = if x ∈ G n then 1 else 0}
  let D : ConditionalMeasureFamily P A := ⟨good, K⟩
  refine ⟨E, D, ?_, ?_, ?_, ?_⟩
  · intro f hf
    refine ⟨?_, integrable_condExp, ?_⟩
    · intro C hC
      change (condExp mA P.μ f) ⁻¹' C ∈ A
      change @MeasurableSet P.X mA ((condExp mA P.μ f) ⁻¹' C)
      exact stronglyMeasurable_condExp.measurable hC.measurableSet
    · intro B hBA
      exact setIntegral_condExp hm hf (show @MeasurableSet P.X mA B from hBA)
  · have hGmem : ∀ n, G n ∈ A := by
      intro n
      by_cases hcg : CountablyGeneratedFamily A
      · have hgen := Classical.choose_spec hcg
        have hGeq : G = Classical.choose hcg := by simp [G, hcg]
        rw [hGeq]
        have hn : Classical.choose hcg n ∈
            generatedSigmaAlgebra (Set.range (Classical.choose hcg)) :=
          MeasurableSpace.measurableSet_generateFrom ⟨n, rfl⟩
        rw [hgen] at hn
        exact hn
      · simp [G, hcg]
        simpa using hA.2.1 Set.univ hA.1
    have hgoodA : good ∈ A := by
      have hone : ∀ n, {x | K x (G n) = 1} ∈ A := by
        intro n
        change @MeasurableSet P.X mA {x | CK x (G n) = 1}
        exact (@measurable_condExpKernel P.X mA P.measurableSpace inferInstance
          P.μ inferInstance (G n) (hsub (hGmem n)))
          (measurableSet_singleton 1)
      have hzero : ∀ n, {x | K x (G n) = 0} ∈ A := by
        intro n
        change @MeasurableSet P.X mA {x | CK x (G n) = 0}
        exact (@measurable_condExpKernel P.X mA P.measurableSpace inferInstance
          P.μ inferInstance (G n) (hsub (hGmem n)))
          (measurableSet_singleton 0)
      change (⋂ n, {x | K x (G n) = if x ∈ G n then 1 else 0}) ∈ A
      rw [Set.iInter_eq_compl_iUnion_compl]
      apply hA.2.1
      apply hA.2.2
      intro n
      have hGn := hGmem n
      have hGc := hA.2.1 (G n) hGn
      have hu : {x | K x (G n) = if x ∈ G n then 1 else 0} =
          ({x | K x (G n) = 1} ∩ G n) ∪ ({x | K x (G n) = 0} ∩ (G n)ᶜ) := by
        ext x
        by_cases hx : x ∈ G n <;> simp [hx]
      rw [hu]
      exact hA.2.1 _ (sigmaUnion hA (sigmaInter hA (hone n) hGn)
        (sigmaInter hA (hzero n) hGc))
    refine ⟨hgoodA, ?_, ?_, ?_, ?_⟩
    · have hcoord : ∀ n, ∀ᵐ x ∂P.μ,
          K x (G n) = if x ∈ G n then 1 else 0 := by
        intro n
        have hGambient : @MeasurableSet P.X P.measurableSpace (G n) := hsub (hGmem n)
        have hGsub : @MeasurableSet P.X mA (G n) := hGmem n
        have hk := @condExpKernel_ae_eq_condExp P.X mA P.measurableSpace
          inferInstance P.μ inferInstance hm (G n) hGambient
        have hce : condExp mA P.μ ((G n).indicator fun _ => (1 : ℝ)) =
            (G n).indicator fun _ => (1 : ℝ) :=
          condExp_of_stronglyMeasurable hm
            (stronglyMeasurable_const.indicator hGsub)
            ((integrable_const (1 : ℝ)).indicator hGambient)
        filter_upwards [hk] with x hx
        rw [hce] at hx
        by_cases hxn : x ∈ G n
        · rw [if_pos hxn]
          apply (ENNReal.toReal_eq_one_iff _).mp
          simpa [K, CK, Measure.real_def, Set.indicator, hxn] using hx
        · rw [if_neg hxn]
          have hz : (K x (G n)).toReal = 0 := by
            simpa [K, CK, Measure.real_def, Set.indicator, hxn] using hx
          rcases (ENNReal.toReal_eq_zero_iff _).mp hz with hz | htop
          · exact hz
          · exact (measure_ne_top (K x) (G n) htop).elim
      have hae : ∀ᵐ x ∂P.μ, x ∈ good := by
        have hall : ∀ᵐ x ∂P.μ, ∀ n, K x (G n) = if x ∈ G n then 1 else 0 :=
          ae_all_iff.mpr hcoord
        filter_upwards [hall] with x hx
        exact Set.mem_iInter.mpr hx
      calc
        P.μ good = P.μ Set.univ := measure_congr (by
          filter_upwards [hae] with x hx
          exact propext ⟨fun _ => Set.mem_univ x, fun _ => hx⟩)
        _ = 1 := measure_univ
    · intro x _
      simpa [D, K] using (inferInstance : IsProbabilityMeasure (CK x))
    · intro B hB C hC
      change (fun x => D.measureAt x B) ⁻¹' C ∈ A
      change @MeasurableSet P.X mA ((fun x => D.measureAt x B) ⁻¹' C)
      simp only [D, K]
      exact (@measurable_condExpKernel P.X mA P.measurableSpace inferInstance
        P.μ inferInstance B hB) hC.measurableSet
    · intro f hf
      simpa [E, D, K, CK] using
        (@condExp_ae_eq_integral_condExpKernel P.X ℂ mA P.measurableSpace
          inferInstance P.μ inferInstance inferInstance f inferInstance inferInstance hm hf)
  · intro hcg
    have hGeq : G = Classical.choose hcg := by simp [G, hcg]
    have hgen0 := Classical.choose_spec hcg
    have hgen : A = generatedSigmaAlgebra (Set.range G) := by
      rw [hGeq]
      exact hgen0.symm
    have hAtom : ∀ x : P.X,
        ⋂₀ {B : Set P.X | B ∈ A ∧ x ∈ B} =
          ⋂ n, if x ∈ G n then G n else (G n)ᶜ := by
      intro x
      ext y
      constructor
      · intro hy
        rw [Set.mem_iInter]
        intro n
        by_cases hxn : x ∈ G n
        · simp only [hxn, if_pos]
          exact Set.mem_sInter.mp hy (G n) ⟨by rw [hgen]; exact
            MeasurableSpace.measurableSet_generateFrom ⟨n, rfl⟩, hxn⟩
        · simp only [hxn, if_false]
          exact Set.mem_sInter.mp hy (G n)ᶜ ⟨by rw [hgen]; exact
            (MeasurableSpace.measurableSet_generateFrom
              (show G n ∈ Set.range G from ⟨n, rfl⟩)).compl, by simpa using hxn⟩
      · intro hy
        apply Set.mem_sInter.mpr
        rintro B ⟨hBA, hxB⟩
        have hBm : @MeasurableSet P.X
            (MeasurableSpace.generateFrom (Set.range G)) B := by
          rw [hgen] at hBA
          exact hBA
        have hpat : ∀ n, x ∈ G n ↔ y ∈ G n := by
          intro n
          have hyn := Set.mem_iInter.mp hy n
          by_cases hxn : x ∈ G n
          · simp only [hxn, if_pos] at hyn
            exact ⟨fun _ => hyn, fun _ => hxn⟩
          · simp only [hxn, if_false, Set.mem_compl_iff] at hyn
            exact ⟨fun hx => (hxn hx).elim, fun hyG => (hyn hyG).elim⟩
        have hiff : x ∈ B ↔ y ∈ B := by
          apply MeasurableSpace.generateFrom_induction (Set.range G)
              (fun C _ => x ∈ C ↔ y ∈ C)
          · rintro _ ⟨n, rfl⟩ _; exact hpat n
          · simp
          · intro C _ h; simpa only [Set.mem_compl_iff, not_iff_not] using h
          · intro C _ h
            simp only [Set.mem_iUnion]
            exact exists_congr fun n => h n
          · exact hBm
        exact hiff.mp hxB
    constructor
    · intro x hxgood
      change x ∈ good at hxgood
      rw [hAtom]
      let S : ℕ → Set P.X := fun n => if x ∈ G n then G n else (G n)ᶜ
      have hSmeas : ∀ n, @MeasurableSet P.X P.measurableSpace (S n) := by
        intro n
        by_cases hxn : x ∈ G n
        · rw [show S n = G n by simp [S, hxn]]
          exact hsub (by rw [hgen]; exact
            MeasurableSpace.measurableSet_generateFrom ⟨n, rfl⟩)
        · rw [show S n = (G n)ᶜ by simp [S, hxn]]
          exact (hsub (by rw [hgen]; exact
            MeasurableSpace.measurableSet_generateFrom ⟨n, rfl⟩)).compl
      have hSone : ∀ n, K x (S n) = 1 := by
        intro n
        have hgoodn := Set.mem_iInter.mp hxgood n
        by_cases hxn : x ∈ G n
        · simpa [S, hxn] using hgoodn
        · have hzero : K x (G n) = 0 := by simpa [hxn] using hgoodn
          have hc := measure_compl (hsub (by rw [hgen]; exact
            MeasurableSpace.measurableSet_generateFrom ⟨n, rfl⟩))
            (measure_ne_top (K x) (G n))
          have huniv : K x Set.univ = 1 := measure_univ
          simpa [S, hxn, hzero, huniv] using hc
      have hSae : ∀ n, ∀ᵐ z ∂K x, z ∈ S n := by
        intro n
        rw [ae_iff]
        change K x (S n)ᶜ = 0
        rw [measure_compl (μ := K x) (hSmeas n) (measure_ne_top (K x) (S n)), hSone n]
        simp
      have hall : ∀ᵐ z ∂K x, ∀ n, z ∈ S n := ae_all_iff.mpr hSae
      calc
        K x (⋂ n, S n) = K x Set.univ := measure_congr (by
          filter_upwards [hall] with z hz
          exact propext ⟨fun h => Set.mem_univ z, fun _ => Set.mem_iInter.mpr hz⟩)
        _ = 1 := measure_univ
    · intro x hx y hy hatom
      change K x = K y
      apply @Measure.ext P.X P.measurableSpace
      intro B hB
      let H : Set P.X := {z | K z B = K x B}
      have hHA : H ∈ A := by
        change @MeasurableSet P.X mA {z | CK z B = CK x B}
        exact (@measurable_condExpKernel P.X mA P.measurableSpace inferInstance
          P.μ inferInstance B hB) (measurableSet_singleton (CK x B))
      have hxH : x ∈ H := rfl
      have hyatom : y ∈ ⋂₀ {C : Set P.X | C ∈ A ∧ x ∈ C} := by
        rw [hatom]
        exact Set.mem_sInter.mpr fun C hC => hC.2
      exact (Set.mem_sInter.mp hyatom H ⟨hHA, hxH⟩).symm
  · intro C hC hCsub EC DC hEC hDC hcomp
    let mC : MeasurableSpace P.X := conditionalFamilyMS C hC
    have hmC : mC ≤ P.measurableSpace := fun _ hs => hCsub hs
    letI : SigmaFinite (P.μ.trim hmC) := inferInstance
    have baseCompleted (F : SetFamily P.X) (hF : IsSigmaAlgebraFamily F)
        {s : Set P.X} (hs : s ∈ F) :
        s ∈ Section01.completedSigmaAlgebraFamily F P.μ := by
      refine ⟨s, hs, ∅, ∅, ?_, measure_empty, Set.Subset.rfl, ?_⟩
      · simpa using hF.2.1 Set.univ hF.1
      · ext x
        simp [symmDiff]
    have completedApprox (F : SetFamily P.X) (hF : IsSigmaAlgebraFamily F)
        {s : Set P.X} (hs : s ∈ Section01.completedSigmaAlgebraFamily F P.μ) :
        ∃ t ∈ F, s =ᵐ[P.μ] t := by
      rcases hs with ⟨t, ht, N, Z, hZF, hZ0, hNZ, rfl⟩
      refine ⟨t, ht, ?_⟩
      have hnotZ : ∀ᵐ x ∂P.μ, x ∉ Z := by
        rw [ae_iff]
        simpa only [not_not] using hZ0
      filter_upwards [hnotZ] with x hx
      apply propext
      have hn : x ∉ N := fun hN => hx (hNZ hN)
      constructor
      · rintro (⟨htx, -⟩ | ⟨hNx, -⟩)
        · exact htx
        · exact (hn hNx).elim
      · intro htx
        exact Or.inl ⟨htx, hn⟩
    have completedNull (F : SetFamily P.X) (hF : IsSigmaAlgebraFamily F)
        (mF : MeasurableSpace P.X)
        (hmF : ∀ s, s ∈ F ↔ @MeasurableSet P.X mF s)
        (hleF : mF ≤ P.measurableSpace)
        {s : Set P.X} (hs : s ∈ Section01.completedSigmaAlgebraFamily F P.μ) :
        @NullMeasurableSet P.X mF s (P.μ.trim hleF) := by
      rcases hs with ⟨t, ht, N, Z, hZF, hZ0, hNZ, rfl⟩
      have htF : @MeasurableSet P.X mF t := (hmF t).mp ht
      have hZF' : @MeasurableSet P.X mF Z := (hmF Z).mp hZF
      have hZtrim : (P.μ.trim hleF) Z = 0 := by
        rw [trim_measurableSet_eq hleF hZF']
        exact hZ0
      have hNtrim : (P.μ.trim hleF) N = 0 :=
        measure_mono_null hNZ hZtrim
      have hNnull : @NullMeasurableSet P.X mF N (P.μ.trim hleF) :=
        (@MeasurableSet.nullMeasurableSet P.X mF (P.μ.trim hleF) ∅
          MeasurableSet.empty).congr (ae_eq_empty.mpr hNtrim).symm
      exact htF.nullMeasurableSet.symmDiff hNnull
    have hCEeq : ∀ f : P.X → ℂ, Integrable f P.μ →
        E.op f =ᵐ[P.μ] EC.op f := by
      intro f hf
      obtain ⟨hECmeas, hECint, hECset⟩ := hEC f hf
      have hECmeasC : @Measurable P.X ℂ mC (borel ℂ) (EC.op f) :=
        measurable_of_isClosed fun s hs => hECmeas s hs
      have hnull : @NullMeasurable P.X ℂ mA (borel ℂ) (EC.op f)
          (P.μ.trim hm) := by
        intro s hs
        have hsC : (EC.op f) ⁻¹' s ∈ C := hECmeasC hs
        have hsCompC := baseCompleted C hC hsC
        have hsCompA : (EC.op f) ⁻¹' s ∈
            Section01.completedSigmaAlgebraFamily A P.μ := by
          rw [hcomp]
          exact hsCompC
        exact completedNull A hA mA (fun _ => Iff.rfl) hm hsCompA
      have haeC : AEMeasurable (EC.op f) (P.μ.trim hm) := hnull.aemeasurable
      let v : P.X → ℂ := haeC.mk (EC.op f)
      have hvmeas : @Measurable P.X ℂ mA (borel ℂ) v := haeC.measurable_mk
      have huvTrim : EC.op f =ᵐ[P.μ.trim hm] v := haeC.ae_eq_mk
      have huv : EC.op f =ᵐ[P.μ] v :=
        MeasureTheory.ae_eq_of_ae_eq_trim huvTrim
      have hvint : Integrable v P.μ := hECint.congr huv
      have hvsets : ∀ s, @MeasurableSet P.X mA s →
          ∫ x in s, v x ∂P.μ = ∫ x in s, f x ∂P.μ := by
        intro s hs
        have hsA : s ∈ A := hs
        have hsCompA := baseCompleted A hA hsA
        have hsCompC : s ∈ Section01.completedSigmaAlgebraFamily C P.μ := by
          rw [← hcomp]
          exact hsCompA
        obtain ⟨t, htC, hst⟩ := completedApprox C hC hsCompC
        calc
          ∫ x in s, v x ∂P.μ = ∫ x in s, EC.op f x ∂P.μ :=
            integral_congr_ae (ae_restrict_of_ae huv.symm)
          _ = ∫ x in t, EC.op f x ∂P.μ := by rw [Measure.restrict_congr_set hst]
          _ = ∫ x in t, f x ∂P.μ := hECset t htC
          _ = ∫ x in s, f x ∂P.μ := by rw [Measure.restrict_congr_set hst]
      have hvce : v =ᵐ[P.μ] condExp mA P.μ f :=
        ae_eq_condExp_of_forall_setIntegral_eq hm hf
          (fun _ _ _ => hvint.integrableOn) (fun s hs _ => hvsets s hs)
          hvmeas.aestronglyMeasurable
      exact hvce.symm.trans (huv.symm)
    letI : MeasurableSpace P.X := P.measurableSpace
    have hDCfull : ∀ᵐ x ∂P.μ, x ∈ DC.fullSet := by
      rw [ae_iff]
      change P.μ DC.fullSetᶜ = 0
      rw [measure_compl (hCsub hDC.1) (measure_ne_top _ _), hDC.2.1]
      simp
    have hseteq (s : Set P.X) (hs : MeasurableSet s) :
        ∀ᵐ x ∂P.μ, K x s = DC.measureAt x s := by
      let f : P.X → ℂ := s.indicator fun _ => 1
      have hf : Integrable f P.μ :=
        (integrable_const (1 : ℂ)).indicator hs
      have hKrep : E.op f =ᵐ[P.μ] fun x => ∫ y, f y ∂K x := by
        simpa [E, K, CK] using
          (@condExp_ae_eq_integral_condExpKernel P.X ℂ mA P.measurableSpace
            inferInstance P.μ inferInstance inferInstance f inferInstance inferInstance hm hf)
      have hDCrep : EC.op f =ᵐ[P.μ] fun x => ∫ y, f y ∂DC.measureAt x :=
        hDC.2.2.2.2 f hf
      filter_upwards [hKrep, hCEeq f hf, hDCrep, hDCfull] with x hxK hxE hxD hxfull
      have hint : ∫ y, f y ∂K x = ∫ y, f y ∂DC.measureAt x :=
        hxK.symm.trans (hxE.trans hxD)
      have hreal : (K x s).toReal = (DC.measureAt x s).toReal := by
        simpa [f, integral_indicator_const, hs, Measure.real_def] using
          hint
      have hKtop : K x s ≠ ⊤ := measure_ne_top _ _
      letI : IsProbabilityMeasure (DC.measureAt x) := hDC.2.2.1 x hxfull
      have hDtop : DC.measureAt x s ≠ ⊤ := measure_ne_top _ _
      exact (ENNReal.toReal_eq_toReal hKtop hDtop).mp hreal
    let B : Set (Set P.X) := MeasurableSpace.countableGeneratingSet P.X
    let S : Set (Set P.X) := generatePiSystem B
    have hBcount : B.Countable := MeasurableSpace.countable_countableGeneratingSet
    have hScount : S.Countable := by
      letI : Countable B := hBcount.to_subtype
      let interList : List B → Set P.X := fun l =>
        l.foldr (fun s t => s.1 ∩ t) Set.univ
      have interList_append (l r : List B) :
          interList (l ++ r) = interList l ∩ interList r := by
        induction l with
        | nil => simp [interList]
        | cons a l ih =>
            rw [List.cons_append]
            simp only [interList, List.foldr_cons]
            change a.1 ∩ interList (l ++ r) =
              (a.1 ∩ interList l) ∩ interList r
            rw [ih]
            exact (Set.inter_assoc _ _ _).symm
      have hrepr : ∀ {s : Set P.X}, s ∈ S → ∃ l : List B, interList l = s := by
        intro s hs
        induction hs with
        | base hmem =>
            exact ⟨[⟨_, hmem⟩], by simp [interList]⟩
        | inter hs ht hne ihs iht =>
            rcases ihs with ⟨l, rfl⟩
            rcases iht with ⟨r, rfl⟩
            refine ⟨l ++ r, ?_⟩
            exact interList_append l r
      apply (Set.countable_range interList).mono
      intro s hs
      rcases hrepr hs with ⟨l, rfl⟩
      exact ⟨l, rfl⟩
    have hbasic : ∀ᵐ x ∂P.μ, ∀ s ∈ S, K x s = DC.measureAt x s := by
      letI : Countable S := hScount.to_subtype
      have hsubtype : ∀ t : S, ∀ᵐ x ∂P.μ, K x t.1 = DC.measureAt x t.1 :=
        fun t => hseteq t.1
          (generatePiSystem_measurableSet
            (fun u hu => MeasurableSpace.measurableSet_countableGeneratingSet hu) t.1 t.2)
      have hall : ∀ᵐ x ∂P.μ, ∀ t : S, K x t.1 = DC.measureAt x t.1 :=
        ae_all_iff.mpr hsubtype
      filter_upwards [hall] with x hx
      intro s hs
      exact hx ⟨s, hs⟩
    have hgen : P.measurableSpace = MeasurableSpace.generateFrom S := by
      simp [S, B, generateFrom_generatePiSystem_eq,
        MeasurableSpace.generateFrom_countableGeneratingSet]
      rfl
    have hallsets : ∀ᵐ x ∂P.μ, ∀ {s : Set P.X}, MeasurableSet s →
        K x s = DC.measureAt x s := by
      apply MeasurableSpace.ae_induction_on_inter hgen
        (isPiSystem_generatePiSystem B)
      · simp
      · exact hbasic
      · filter_upwards [hDCfull] with x hxfull
        intro s hs heq
        letI : IsProbabilityMeasure (DC.measureAt x) := hDC.2.2.1 x hxfull
        letI : IsProbabilityMeasure (K x) := inferInstance
        rw [measure_compl hs (measure_ne_top _ _),
          measure_compl hs (measure_ne_top _ _), heq, measure_univ, measure_univ]
      · filter_upwards [hDCfull] with x hxfull
        intro f hdisj hfmeas heq
        letI : IsProbabilityMeasure (DC.measureAt x) := hDC.2.2.1 x hxfull
        rw [measure_iUnion hdisj hfmeas, measure_iUnion hdisj hfmeas]
        congr 1
        funext n
        exact heq n
    filter_upwards [hallsets] with x hx
    change K x = DC.measureAt x
    apply Measure.ext
    intro s hs
    exact hx hs

end Chapter00.Section03
