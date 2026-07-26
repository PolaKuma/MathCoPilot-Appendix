import Chapter04.Common
import Chapter04.MeasureAlgebra.InducedMeasureAlgebra
import Chapter04.MeasureAlgebra.MeasureAlgebraStone
import Chapter04.Descriptive.StandardBorel
import Chapter04.Descriptive.AnalyticUniformization
import Chapter04.Descriptive.AnalyticUniversal
import Chapter04.Descriptive.ProbabilityRepresentation
import Chapter04.MeasureAlgebra.QuotientBoolean
import Chapter04.Descriptive.ProbabilitySpatial
import Chapter04.MeasureAlgebra.InverseLtwo
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter04

universe u v

namespace Section01

/--
Source: Theorem 4.1.1, Chapter 4, Section 1.
For a measurable space, being isomorphic to the Borel sigma algebra of a
separable metric space, being isomorphic to a Borel subset of Cantor space, and
having a countably generated point-separating sigma algebra are equivalent.
-/
theorem borelSpaceCharacterizations (M : MeasurableSpaceData.{u}) :
    (HasSeparableMetricBorelModel M ∧ HasCantorSubsetBorelModel M) ↔
      HasCountableGeneratingFamily M.sets ∧ SeparatesPoints M.sets := by
  constructor
  · rintro ⟨⟨Y, tY, mY, metrizableY, sepY, borelY, f, g,
        hleft, hright, hf, hg⟩, -⟩
    letI : TopologicalSpace Y := tY
    letI : MeasurableSpace Y := mY
    letI : TopologicalSpace.MetrizableSpace Y := metrizableY
    letI : TopologicalSpace.SeparableSpace Y := sepY
    letI : BorelSpace Y := borelY
    letI : MetricSpace Y := TopologicalSpace.metrizableSpaceMetric Y
    letI : MeasurableSpace.CountablyGenerated Y := inferInstance
    let E : ℕ → Set Y := MeasurableSpace.natGeneratingSequence Y
    let A : ℕ → Set M.X := fun n => f ⁻¹' E n
    have hgenY : MeasurableSpace.generateFrom (Set.range E) = mY := by
      exact MeasurableSpace.generateFrom_natGeneratingSequence Y
    let mA : MeasurableSpace M.X := MeasurableSpace.generateFrom (Set.range A)
    have hpull : ∀ S : Set Y, MeasurableSet S → @MeasurableSet M.X mA (f ⁻¹' S) := by
      intro S hS
      have hS' : @MeasurableSet Y
          (MeasurableSpace.generateFrom (Set.range E)) S := by
        rw [hgenY]
        exact hS
      exact MeasurableSpace.generateFrom_induction (Set.range E)
        (fun T _ => @MeasurableSet M.X mA (f ⁻¹' T))
        (by
          rintro _ ⟨n, rfl⟩ _
          exact MeasurableSpace.measurableSet_generateFrom ⟨n, rfl⟩)
        MeasurableSet.empty
        (fun _ _ ih => ih.compl)
        (fun _ _ ih => by
          simpa only [Set.preimage_iUnion] using MeasurableSet.iUnion ih)
        S hS'
    have hmA : mA = M.measurableSpace := by
      apply le_antisymm
      · apply MeasurableSpace.generateFrom_le
        rintro _ ⟨n, rfl⟩
        exact hf (E n) (MeasurableSpace.measurableSet_natGeneratingSequence n)
      · intro S hS
        have hgS : MeasurableSet (g ⁻¹' S) := hg S hS
        have hp := hpull (g ⁻¹' S) hgS
        rw [show f ⁻¹' (g ⁻¹' S) = S by
          ext x
          simp only [Set.mem_preimage]
          rw [hleft x]] at hp
        exact hp
    refine ⟨?_, ?_⟩
    · refine ⟨A, ?_⟩
      change {S | @MeasurableSet M.X mA S} =
        {S | @MeasurableSet M.X M.measurableSpace S}
      rw [hmA]
    · intro x y hxy
      have hfxy : f x ≠ f y := fun h =>
        hxy (Function.LeftInverse.injective hleft h)
      let B : Set Y := Metric.ball (f x) (dist (f x) (f y))
      refine ⟨f ⁻¹' B, hf B Metric.isOpen_ball.measurableSet, ?_, ?_⟩
      · change f x ∈ B
        simp [B, dist_pos.mpr hfxy]
      · change f y ∉ B
        simp [B, Metric.mem_ball, dist_comm]
  · rintro ⟨⟨a, ha⟩, hsep⟩
    have hm : M.measurableSpace = MeasurableSpace.generateFrom (Set.range a) := by
      apply MeasurableSpace.ext
      intro S
      exact (Set.ext_iff.mp ha S).symm
    letI : MeasurableSpace.CountablyGenerated M.X :=
      ⟨Set.range a, Set.countable_range a, hm⟩
    letI : MeasurableSpace.SeparatesPoints M.X := ⟨by
      intro x y h
      by_contra hxy
      obtain ⟨S, hS, hxS, hyS⟩ := hsep x y hxy
      exact hyS (h S hS hxS)⟩
    constructor
    · obtain ⟨tM, secondM, t4M, borelM⟩ :=
        exists_borelSpace_of_countablyGenerated_of_separatesPoints M.X
      letI : TopologicalSpace M.X := tM
      letI : SecondCountableTopology M.X := secondM
      letI : T4Space M.X := t4M
      letI : BorelSpace M.X := borelM
      letI : TopologicalSpace.MetrizableSpace M.X := inferInstance
      letI : TopologicalSpace.SeparableSpace M.X := inferInstance
      refine ⟨M.X, inferInstance, M.measurableSpace, inferInstance,
        inferInstance, inferInstance, id, id, ?_, ?_, ?_, ?_⟩
      · exact fun _ => rfl
      · exact fun _ => rfl
      · exact fun _ hS => hS
      · exact fun _ hS => hS
    · obtain ⟨C, ⟨e⟩⟩ :=
        MeasurableSpace.measurableEquiv_nat_bool_of_countablyGenerated (α := M.X)
      refine ⟨C, inferInstance, ?_, e, e.symm, ?_, ?_, ?_, ?_⟩
      · have hpi : MeasurableSpace.pi = borel (ℕ → Bool) :=
          BorelSpace.measurable_eq
        change MeasurableSpace.comap Subtype.val MeasurableSpace.pi =
          MeasurableSpace.comap Subtype.val (borel (ℕ → Bool))
        rw [hpi]
      · exact e.symm_apply_apply
      · exact e.apply_symm_apply
      · exact e.measurable
      · exact e.symm.measurable

/--
Source: Remark 4.1.2, Chapter 4, Section 1.
A measurable-space isomorphism is a bijection whose two directions are
measurable; the Cantor-space model in Theorem 4.1.1 is obtained by coding points
using a countable separating family.
-/
def measurableIsomorphismCantorCodingRemark : Prop :=
  ∀ M : MeasurableSpaceData.{u},
    HasCountableGeneratingFamily M.sets -> SeparatesPoints M.sets ->
      HasCantorSubsetBorelModel M

/--
Source: Definition 4.1.3, Chapter 4, Section 1.
A standard Borel space is a measurable space isomorphic to the Borel sigma
algebra of a Polish space.
-/
def standardBorelSpace (M : MeasurableSpaceData.{u}) : Prop :=
  IsStandardBorelSpaceData M

/--
Source: Theorem 4.1.4, Chapter 4, Section 1.
Kuratowski's theorem: two standard Borel spaces are measurably isomorphic
exactly when their underlying sets have the same cardinality.
-/
theorem kuratowskiStandardBorelIsomorphism
    (M N : MeasurableSpaceData.{u}) :
    IsStandardBorelSpaceData M -> IsStandardBorelSpaceData N ->
      (IsMeasurableIsomorphism M N ↔ Cardinal.mk M.X = Cardinal.mk N.X) := by
  rintro ⟨Y, mY, sY, hMY⟩ ⟨Z, mZ, sZ, hNZ⟩
  constructor
  · rintro ⟨f, g, hleft, hright, -, -⟩
    exact Cardinal.mk_congr
      { toFun := f, invFun := g, left_inv := hleft, right_inv := hright }
  · intro hcard
    rcases hMY with ⟨fM, gM, hMleft, hMright, hfM, hgM⟩
    rcases hNZ with ⟨fN, gN, hNleft, hNright, hfN, hgN⟩
    let eM : M.X ≃ Y :=
      { toFun := fM, invFun := gM, left_inv := hMleft, right_inv := hMright }
    let eN : N.X ≃ Z :=
      { toFun := fN, invFun := gN, left_inv := hNleft, right_inv := hNright }
    have hYZ : Cardinal.mk Y = Cardinal.mk Z := by
      calc
        Cardinal.mk Y = Cardinal.mk M.X := (Cardinal.mk_congr eM).symm
        _ = Cardinal.mk N.X := hcard
        _ = Cardinal.mk Z := Cardinal.mk_congr eN
    let eYZ : Y ≃ Z := Classical.choice (Cardinal.eq.mp hYZ)
    let bYZ : Y ≃ᵐ Z := PolishSpace.Equiv.measurableEquiv eYZ
    let φ : M.X → N.X := fun x => gN (bYZ (fM x))
    let ψ : N.X → M.X := fun y => gM (bYZ.symm (fN y))
    have hfM' : Measurable fM := hfM
    have hgM' : Measurable gM := hgM
    have hfN' : Measurable fN := hfN
    have hgN' : Measurable gN := hgN
    refine ⟨φ, ψ, ?_, ?_, ?_, ?_⟩
    · intro x
      dsimp [φ, ψ]
      rw [hNright, bYZ.symm_apply_apply, hMleft]
    · intro y
      dsimp [φ, ψ]
      rw [hMright, bYZ.apply_symm_apply, hNleft]
    · exact hgN'.comp (bYZ.measurable.comp hfM')
    · exact hgM'.comp (bYZ.symm.measurable.comp hfN')

/--
Source: Proposition 4.1.5(a), Chapter 4, Section 1.
A Borel subspace of a standard Borel space is again standard Borel.
-/
theorem standardBorelSubspace (M : MeasurableSpaceData.{u}) (A : Set M.X) :
    IsStandardBorelSpaceData M -> A ∈ M.sets ->
      IsStandardBorelSpaceData (subspaceMeasurableSpace M A) := by
  rintro ⟨Y, mY, sY, f, g, hleft, hright, hf, hg⟩ hA
  have hf' : Measurable f := hf
  have hg' : Measurable g := hg
  have hA' : MeasurableSet A := hA
  have himage : MeasurableSet (f '' A) := by
    rw [show f '' A = g ⁻¹' A by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [hleft x] using hx
      · intro hy
        exact ⟨g y, hy, hright y⟩]
    exact hg' hA'
  letI : StandardBorelSpace (f '' A) := himage.standardBorel
  refine ⟨f '' A, inferInstance, inferInstance, ?_⟩
  let fA : A → (f '' A) := fun x => ⟨f x, x, x.2, rfl⟩
  let gA : (f '' A) → A := fun y => ⟨g y, by
    rcases y.2 with ⟨x, hx, hxy⟩
    have hgy : g y = x := by
      rw [← hxy]
      exact hleft x
    simpa [hgy] using hx⟩
  refine ⟨fA, gA, ?_, ?_, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    change g (f x.val) = x.val
    exact hleft x.val
  · intro y
    apply Subtype.ext
    change f (g y.val) = y.val
    exact hright y.val
  · exact hf'.comp measurable_subtype_coe |>.subtype_mk
  · exact hg'.comp measurable_subtype_coe |>.subtype_mk

/--
Source: Proposition 4.1.5(b), Chapter 4, Section 1.
The image of a Borel set under an injective measurable map between standard
Borel spaces is Borel.
-/
theorem injectiveMeasurableImageIsBorel
    (M : MeasurableSpaceData.{u}) (N : MeasurableSpaceData.{v})
    (f : M.X -> N.X) (A : Set M.X) :
    IsStandardBorelSpaceData M -> IsStandardBorelSpaceData N ->
      IsMeasurableMap M N f -> A ∈ M.sets -> Set.InjOn f A -> f '' A ∈ N.sets := by
  intro hM hN hf hA hinj
  rcases standardBorelSubspace M A hM hA with
    ⟨Y, mY, sY, p, q, hpq, hqp, hp, hq⟩
  rcases hN with ⟨Z, mZ, sZ, r, s, hsr, hrs, hr, hs⟩
  have hf' : Measurable f := hf
  have hp' : Measurable p := hp
  have hq' : Measurable q := hq
  have hr' : Measurable r := hr
  let F : Y → Z := fun y => r (f (q y).val)
  have hF : Measurable F :=
    hr'.comp (hf'.comp (measurable_subtype_coe.comp hq'))
  have hFinj : Function.Injective F := by
    intro y₁ y₂ heq
    have hfq : f (q y₁).val = f (q y₂).val :=
      (Function.LeftInverse.injective hsr) heq
    have hqeq : q y₁ = q y₂ := by
      apply Subtype.ext
      exact hinj (q y₁).2 (q y₂).2 hfq
    calc
      y₁ = p (q y₁) := (hqp y₁).symm
      _ = p (q y₂) := congrArg p hqeq
      _ = y₂ := hqp y₂
  have hFembed : MeasurableEmbedding F := hF.measurableEmbedding hFinj
  have hFrange : MeasurableSet (F '' Set.univ) :=
    hFembed.measurableSet_image' MeasurableSet.univ
  have hrange : F '' Set.univ = r '' (f '' A) := by
    ext z
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨f (q y).val, ⟨(q y).val, (q y).2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨p ⟨x, hx⟩, Set.mem_univ _, ?_⟩
      change r (f (q (p ⟨x, hx⟩)).val) = r (f x)
      rw [hpq]
  have himage : f '' A = r ⁻¹' (F '' Set.univ) := by
    rw [hrange]
    ext y
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y', hy', hry⟩
      have : y' = y := Function.LeftInverse.injective hsr hry
      simpa [this] using hy'
  rw [himage]
  exact hr' hFrange

/-- The second conclusion of Source 4.1.5(2): the restricted injection is a
measurable-space isomorphism onto its Borel image. -/
theorem injectiveMeasurableRestrictionIsomorphism
    (M : MeasurableSpaceData.{u}) (N : MeasurableSpaceData.{v})
    (f : M.X -> N.X) (A : Set M.X) :
    IsStandardBorelSpaceData M -> IsStandardBorelSpaceData N ->
    IsMeasurableMap M N f -> A ∈ M.sets -> Set.InjOn f A ->
      ∃ g : (f '' A) -> A,
        Function.LeftInverse g (fun x : A => ⟨f x, ⟨x, x.2, rfl⟩⟩) ∧
        Function.RightInverse g (fun x : A => ⟨f x, ⟨x, x.2, rfl⟩⟩) ∧
        @Measurable A (f '' A)
          (MeasurableSpace.comap Subtype.val M.measurableSpace)
          (MeasurableSpace.comap Subtype.val N.measurableSpace)
          (fun x : A => ⟨f x, ⟨x, x.2, rfl⟩⟩) ∧
        @Measurable (f '' A) A
          (MeasurableSpace.comap Subtype.val N.measurableSpace)
          (MeasurableSpace.comap Subtype.val M.measurableSpace) g := by
  intro hM hN hf hA hinj
  have hf' : Measurable f := hf
  have hA' : MeasurableSet A := hA
  let fA : A → (f '' A) := fun x => ⟨f x.val, x.val, x.2, rfl⟩
  have hfA : Measurable fA :=
    hf'.comp measurable_subtype_coe |>.subtype_mk
  have hinjA : Function.Injective fA := by
    intro x y hxy
    apply Subtype.ext
    exact hinj x.2 y.2 (congrArg Subtype.val hxy)
  have himageA : ∀ ⦃S : Set A⦄, MeasurableSet S → MeasurableSet (fA '' S) := by
    intro S hS
    have hSambient : MeasurableSet (Subtype.val '' S) := hA'.subtype_image hS
    have hfinjS : Set.InjOn f (Subtype.val '' S) := by
      intro x hx y hy hxy
      rcases hx with ⟨xA, hxA, rfl⟩
      rcases hy with ⟨yA, hyA, rfl⟩
      exact hinj xA.2 yA.2 hxy
    have hImageAmbient : MeasurableSet (f '' (Subtype.val '' S)) :=
      injectiveMeasurableImageIsBorel M N f (Subtype.val '' S)
        hM hN hf hSambient hfinjS
    have hpre : MeasurableSet
        (Subtype.val ⁻¹' (f '' (Subtype.val '' S)) : Set (f '' A)) :=
      hImageAmbient.preimage measurable_subtype_coe
    rw [show fA '' S =
        (Subtype.val ⁻¹' (f '' (Subtype.val '' S)) : Set (f '' A)) by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.val, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨xA, hxA, rfl⟩, hfx⟩
        refine ⟨xA, hxA, ?_⟩
        apply Subtype.ext
        exact hfx]
    exact hpre
  have hembed : MeasurableEmbedding fA :=
    MeasurableEmbedding.mk hinjA hfA himageA
  have hsurjA : Function.Surjective fA := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let e : A ≃ (f '' A) := Equiv.ofBijective fA ⟨hinjA, hsurjA⟩
  let g : (f '' A) → A := e.symm
  have he_apply (x : A) : e x = fA x := Equiv.ofBijective_apply _ _ x
  have hleft : Function.LeftInverse g fA := by
    intro x
    rw [← he_apply]
    exact e.symm_apply_apply x
  have hright : Function.RightInverse g fA := by
    intro y
    rw [← he_apply]
    exact e.apply_symm_apply y
  have hg : Measurable g := by
    rw [← hembed.measurable_comp_iff]
    have : fA ∘ g = id := funext hright
    rw [this]
    exact measurable_id
  exact ⟨g, hleft, hright, hfA, hg⟩

/--
Source: Proposition 4.1.5(c), Chapter 4, Section 1.
A countably generated point-separating sub-sigma-algebra of a standard Borel
space is the whole Borel sigma algebra.
-/
theorem countablyGeneratedSeparatingSubsigmaAlgebraUnique
    (M : MeasurableSpaceData.{u}) (A : SetFamily M.X) :
    IsStandardBorelSpaceData M -> A ⊆ M.sets ->
      HasCountableGeneratingFamily A -> SeparatesPoints A -> A = M.sets := by
  rintro hM hsub ⟨a, ha⟩ hsep
  let MA : MeasurableSpaceData.{u} :=
    { X := M.X, measurableSpace := MeasurableSpace.generateFrom (Set.range a) }
  have hMAsets : MA.sets = A := ha
  have hMAgen : HasCountableGeneratingFamily MA.sets := by
    exact ⟨a, rfl⟩
  have hMAsep : SeparatesPoints MA.sets := by
    simpa [hMAsets] using hsep
  obtain ⟨-, hCantor⟩ :=
    (borelSpaceCharacterizations MA).2 ⟨hMAgen, hMAsep⟩
  rcases hCantor with ⟨C, mC, rfl, f, g, hleft, hright, hf, hg⟩
  let K : MeasurableSpaceData.{0} :=
    { X := ℕ → Bool, measurableSpace := borel (ℕ → Bool) }
  have sK : @StandardBorelSpace (ℕ → Bool) K.measurableSpace := by
    have hpi : MeasurableSpace.pi = borel (ℕ → Bool) := BorelSpace.measurable_eq
    change @StandardBorelSpace (ℕ → Bool) (borel (ℕ → Bool))
    rw [← hpi]
    infer_instance
  have hKstd : IsStandardBorelSpaceData K := by
    refine ⟨ℕ → Bool, K.measurableSpace, sK, id, id, ?_, ?_, ?_, ?_⟩
    · exact fun _ => rfl
    · exact fun _ => rfl
    · exact fun _ hB => hB
    · exact fun _ hB => hB
  letI : MeasurableSpace (ℕ → Bool) := borel (ℕ → Bool)
  let F : M.X → K.X := fun x => (f x).val
  have hFMA : IsMeasurableMap MA K F := by
    exact measurable_subtype_coe.comp (show Measurable f from hf)
  have hFM : IsMeasurableMap M K F := by
    intro B hB
    apply hsub
    rw [← hMAsets]
    exact hFMA B hB
  have hFinj : Function.Injective F := by
    intro x y hxy
    apply Function.LeftInverse.injective hleft
    apply Subtype.ext
    exact hxy
  apply Set.Subset.antisymm hsub
  intro B hB
  have hImage : F '' B ∈ K.sets :=
    injectiveMeasurableImageIsBorel M K F B hM hKstd hFM hB hFinj.injOn
  let S : Set C := Subtype.val ⁻¹' (F '' B)
  have hImage' : @MeasurableSet (ℕ → Bool) (borel (ℕ → Bool)) (F '' B) := hImage
  have hS : @MeasurableSet C
      (MeasurableSpace.comap Subtype.val (borel (ℕ → Bool))) S :=
    hImage'.preimage measurable_subtype_coe
  have hpre : f ⁻¹' S ∈ MA.sets := hf S hS
  have heq : f ⁻¹' S = B := by
    ext x
    constructor
    · rintro ⟨y, hy, hFy⟩
      have : y = x := hFinj hFy
      simpa [← this] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [← hMAsets]
  simpa [heq] using hpre

/--
Source: Definition 4.1.6, Chapter 4, Section 1.
An analytic set in a standard Borel space is the measurable image of a Borel set
from another standard Borel space.
-/
def analyticSet (M : MeasurableSpaceData.{u}) (A : Set M.X) : Prop :=
  IsAnalyticSet M A

/--
Source: Remark 4.1.7, Chapter 4, Section 1.
Borel sets are exactly the sets whose set and complement are analytic; analytic
sets generate the analytic sigma algebra and are measured through completions by
null sets.
-/
def analyticSetAndCompletionRemark (M : MeasurableSpaceData.{u}) : Prop :=
  IsStandardBorelSpaceData M ->
    (¬ Set.Countable (Set.univ : Set M.X) ->
      ∃ A : Set M.X, IsAnalyticSet M A ∧ A ∉ M.sets) ∧
    (∀ A : Set M.X, A ∈ M.sets ↔ IsAnalyticSet M A ∧ IsAnalyticSet M Aᶜ) ∧
    analyticSigmaAlgebra M =
      Chapter00.generatedSigmaAlgebra {A : Set M.X | IsAnalyticSet M A}

/--
Source: Theorem 4.1.8, Chapter 4, Section 1.
Lusin's theorem: analytic subsets of a standard Borel space are universally
measurable.
-/
theorem lusinAnalyticSetUniversallyMeasurable
    (M : MeasurableSpaceData.{u}) (A : Set M.X) :
    IsStandardBorelSpaceData M -> IsAnalyticSet M A -> IsUniversallyMeasurable M A := by
  intro hM hA
  exact AnalyticUniversal.universallyMeasurable_of_data M hM A hA

/--
Source: Theorem 4.1.9, Chapter 4, Section 1.
Jankov-von Neumann selection: a surjective measurable map between standard
Borel spaces admits a measurable right inverse on its range.
-/
theorem jankovVonNeumannSelection
    (M N : MeasurableSpaceData.{u}) (f : M.X -> N.X) :
    IsStandardBorelSpaceData M -> IsStandardBorelSpaceData N ->
      IsMeasurableMap M N f ->
        ∃ g : Set.range f -> M.X,
          (∀ A : Set M.X, A ∈ M.sets ->
            g ⁻¹' A ∈ analyticSigmaAlgebra
              (subspaceMeasurableSpace N (Set.range f))) ∧
          ∀ y : Set.range f, f (g y) = y.1 := by
  intro hM hN hf
  exact AnalyticUniformization.jankovVonNeumannSelection_of_data
    M N f hM hN hf

/--
Source: Theorem 4.1.10, Chapter 4, Section 1.
Every continuous probability measure on a standard Borel space is isomorphic to
Lebesgue measure on the unit interval.
-/
theorem continuousStandardBorelProbabilityIsLebesgueInterval
    (P : ProbabilitySpace.{u}) :
    IsLebesgueProbabilitySpace P -> IsContinuousProbabilityMeasure P ->
      IsLebesgueUnitIntervalModel P := by
  intro hP hC
  exact ProbabilityRepresentation.atomless_standardBorel_unitInterval_model P hP hC

/--
Source: Definition 4.1.11, Chapter 4, Section 1.
A Lebesgue space is a standard Borel probability space in the measure-theoretic
sense used for isomorphism modulo null sets.
-/
def lebesgueProbabilitySpace (P : ProbabilitySpace.{u}) : Prop :=
  IsLebesgueProbabilitySpace P

/--
Source: Remark 4.1.12 contained after Definition 4.1.11, Chapter 4, Section 1.
Lebesgue probability spaces have a canonical form consisting of an interval part
and at most countably many atoms.
-/
def lebesgueSpaceCanonicalFormRemark : Prop :=
  ∀ P : ProbabilitySpace.{u}, IsLebesgueProbabilitySpace P ->
    HasLebesgueCanonicalDecomposition P

/--
Source: Definition 4.1.13, Chapter 4, Section 1.
An ideal and a sigma ideal of subsets of a measurable space.
-/
def ideal (𝓘 : Set (Set α)) : Prop :=
  IsIdeal 𝓘

/--
Source: Definition 4.1.13, Chapter 4, Section 1.
The quotient Boolean sigma algebra modulo an ideal identifies sets whose
symmetric difference lies in the ideal.
-/
def quotientBooleanSigmaAlgebraByIdeal {X : Type u}
    (𝓘 : Set (Set X)) (A B : Set X) : Prop :=
  quotientEquivalentByIdeal 𝓘 A B

/--
Source: Proposition 4.1.14, Chapter 4, Section 1.
A homomorphism from a nonempty standard Borel sigma algebra into a quotient
sigma algebra is represented by a measurable map, unique modulo the source ideal.
-/
theorem booleanSigmaHomomorphismRealizedByMeasurableMap
    (M N : MeasurableSpaceData.{u}) (I : Set (Set M.X)) (J : Set (Set N.X))
    (Φ : QuotientBooleanHomData M N I J) :
    IsStandardBorelSpaceData N -> Nonempty N.X ->
    IsSigmaIdeal I -> IsSigmaIdeal J -> IsQuotientBooleanHom Φ ->
      ∃ φ : M.X -> N.X, IsMeasurableMap M N φ ∧
        (∀ A ∈ N.sets, quotientEquivalentByIdeal I (φ ⁻¹' A) (Φ.map A)) ∧
        ∀ ψ : M.X -> N.X, IsMeasurableMap M N ψ ->
          (∀ A ∈ N.sets, quotientEquivalentByIdeal I (ψ ⁻¹' A) (Φ.map A)) ->
          {x : M.X | φ x ≠ ψ x} ∈ I := by
  intro hN hN0 hI _hJ hΦ
  exact QuotientBoolean.realized_by_measurable_map M N I J Φ hN0 hN hI hΦ

/--
Source: Theorem 4.1.15, Chapter 4, Section 1.
For standard Borel spaces, a given quotient Boolean-algebra map is an
isomorphism exactly when it is represented off ideal-small sets by a Borel
isomorphism.
-/
theorem quotientBooleanAlgebraIsomorphismRealizedByBorelIsomorphism
    (M N : MeasurableSpaceData.{u}) (I : Set (Set M.X)) (J : Set (Set N.X))
    (Φ : QuotientBooleanHomData M N I J) :
    IsStandardBorelSpaceData M -> IsStandardBorelSpaceData N ->
    IsSigmaIdeal I -> IsSigmaIdeal J -> IsQuotientBooleanHom Φ ->
    (IsQuotientBooleanIso Φ ↔
      ∃ X₀ : Set M.X, ∃ Y₀ : Set N.X,
        MeasurableSet X₀ ∧ MeasurableSet Y₀ ∧ X₀ᶜ ∈ I ∧ Y₀ᶜ ∈ J ∧
        ∃ φ : X₀ -> Y₀, ∃ ψ : Y₀ -> X₀,
          Function.LeftInverse ψ φ ∧ Function.RightInverse ψ φ ∧
          @Measurable X₀ Y₀
            (MeasurableSpace.comap Subtype.val M.measurableSpace)
            (MeasurableSpace.comap Subtype.val N.measurableSpace) φ ∧
          @Measurable Y₀ X₀
            (MeasurableSpace.comap Subtype.val N.measurableSpace)
            (MeasurableSpace.comap Subtype.val M.measurableSpace) ψ ∧
          (∀ A : Set N.X, A ∈ N.sets ->
            (A ∈ J ↔
              Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' (A ∩ Y₀))) ∈ I)) ∧
          ∀ A : Set N.X, A ∈ N.sets ->
            quotientEquivalentByIdeal I (Φ.map A)
              (Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' (A ∩ Y₀))))) := by
  intro hM hN hI hJ hΦ
  constructor
  · intro hiso
    by_cases hM0 : Nonempty M.X
    · by_cases hN0 : Nonempty N.X
      · exact QuotientBoolean.iso_has_borel_core M N I J Φ hM0 hN0 hM hN hI hJ hiso
      · letI : IsEmpty N.X := ⟨fun x => hN0 ⟨x⟩⟩
        have hJuniv : (Set.univ : Set N.X) ∈ J := by
          have hu : (Set.univ : Set N.X) = ∅ := by
            ext x
            exact False.elim (isEmptyElim x)
          rw [hu]
          exact hJ.1.1
        have hIuniv : (Set.univ : Set M.X) ∈ I := by
          obtain ⟨A, hA, hFA⟩ := hiso.2.2 Set.univ MeasurableSet.univ
          have hAe : A = ∅ := Subsingleton.elim _ _
          subst A
          have hz := QuotientBoolean.equiv_trans hI
            (QuotientBoolean.equiv_symm hFA) (QuotientBoolean.map_empty hI hiso.1)
          simpa [quotientEquivalentByIdeal, Chapter00.symmDiff] using hz
        let φ : (∅ : Set M.X) → (∅ : Set N.X) := fun x => False.elim x.2
        let ψ : (∅ : Set N.X) → (∅ : Set M.X) := fun y => False.elim y.2
        have hXemptyc : (∅ : Set M.X)ᶜ ∈ I := by simpa using hIuniv
        have hYemptyc : (∅ : Set N.X)ᶜ ∈ J := by simpa using hJuniv
        refine ⟨∅, ∅, MeasurableSet.empty, MeasurableSet.empty,
          hXemptyc, hYemptyc, φ, ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x
          exact False.elim x.2
        · intro y
          exact False.elim y.2
        · apply measurable_of_countable
        · apply measurable_of_countable
        · intro A hA
          constructor
          · intro _
            exact QuotientBoolean.ideal_mono hI (Set.subset_univ _) hIuniv
          · intro _
            exact QuotientBoolean.ideal_mono hJ (Set.subset_univ A) hJuniv
        · intro A hA
          apply QuotientBoolean.ideal_mono hI (B := Set.univ)
          · exact Set.subset_univ _
          · exact hIuniv
    · letI : IsEmpty M.X := ⟨fun x => hM0 ⟨x⟩⟩
      have hIuniv : (Set.univ : Set M.X) ∈ I := by
        have hu : (Set.univ : Set M.X) = ∅ := by
          ext x
          exact False.elim (isEmptyElim x)
        rw [hu]
        exact hI.1.1
      have hJuniv : (Set.univ : Set N.X) ∈ J := by
        have heq : Φ.map (Set.univ : Set N.X) = Φ.map ∅ := Subsingleton.elim _ _
        have hsame : quotientEquivalentByIdeal I
            (Φ.map (Set.univ : Set N.X)) (Φ.map ∅) := by
          rw [heq]
          exact QuotientBoolean.equiv_refl hI _
        have hz := hiso.2.1 Set.univ ∅ MeasurableSet.univ MeasurableSet.empty hsame
        simpa [quotientEquivalentByIdeal, Chapter00.symmDiff] using hz
      let φ : (∅ : Set M.X) → (∅ : Set N.X) := fun x => False.elim x.2
      let ψ : (∅ : Set N.X) → (∅ : Set M.X) := fun y => False.elim y.2
      have hXemptyc : (∅ : Set M.X)ᶜ ∈ I := by simpa using hIuniv
      have hYemptyc : (∅ : Set N.X)ᶜ ∈ J := by simpa using hJuniv
      refine ⟨∅, ∅, MeasurableSet.empty, MeasurableSet.empty,
        hXemptyc, hYemptyc, φ, ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x
        exact False.elim x.2
      · intro y
        exact False.elim y.2
      · apply measurable_of_countable
      · apply measurable_of_countable
      · intro A hA
        constructor
        · intro _
          exact QuotientBoolean.ideal_mono hI (Set.subset_univ _) hIuniv
        · intro _
          exact QuotientBoolean.ideal_mono hJ (Set.subset_univ A) hJuniv
      · intro A hA
        apply QuotientBoolean.ideal_mono hI (B := Set.univ)
        · exact Set.subset_univ _
        · exact hIuniv
  · rintro ⟨X₀, Y₀, hX₀, hY₀, hXc, hYc, φ, ψ,
      hleft, hright, hφm, hψm, hideal, hrep⟩
    exact QuotientBoolean.borel_core_gives_iso M N I J Φ hI hJ hΦ
      hX₀ hY₀ hXc hYc φ ψ hleft hright hφm hψm hideal hrep

/--
Source: Definition 4.1.16, Chapter 4, Section 1.
A measure algebra is a Boolean sigma algebra with a faithful finite,
countably-additive measure.
-/
def measureAlgebra (A : MeasureAlgebraData.{u}) : Prop :=
  IsMeasureAlgebra A

/--
Source: Definition 4.1.17, Chapter 4, Section 1.
A measure-algebra homomorphism preserves Boolean operations and the measure;
isomorphisms and automorphisms are the corresponding bijective self cases.
-/
def measureAlgebraHomomorphism {B : MeasureAlgebraData.{u}} {A : MeasureAlgebraData.{v}}
    (Φ : MeasureAlgebraHomData B A) : Prop :=
  IsMeasureAlgebraHom Φ

/--
Source: Remark 4.1.18, Chapter 4, Section 1.
Measure-algebra isomorphisms can be read either as measure-preserving Boolean
algebra isomorphisms or as spatial isomorphisms modulo null sets in the
Lebesgue setting.
-/
def measureAlgebraIsomorphismRemark : Prop :=
  ∀ B : MeasureAlgebraData.{u}, ∀ A : MeasureAlgebraData.{u},
    ∀ Φ : MeasureAlgebraHomData B A,
      IsMeasureAlgebraIsomorphism Φ ->
        IsMeasureAlgebraHom Φ ∧
        (∀ b c, A.equiv (Φ.map b) (Φ.map c) -> B.equiv b c) ∧
        ∀ b c,
          measureAlgebraDistance A (Φ.map b) (Φ.map c) =
            measureAlgebraDistance B b c

/--
Source: Theorem 4.1.19, Chapter 4, Section 1.
Every separable probability measure algebra is represented by the measure
algebra of some probability space.
-/
theorem separableMeasureAlgebraRepresentation
    (A : MeasureAlgebraData.{u}) :
    IsMeasureAlgebra A -> A.measure A.top = 1 -> IsSeparableMeasureAlgebra A ->
      ∃ P : ProbabilitySpace.{u}, ∃ Φ : MeasureAlgebraHomData A (inducedMeasureAlgebra P),
        Chapter01.IsProbabilitySpace P ∧ IsMeasureAlgebra (inducedMeasureAlgebra P) ∧
        IsMeasureAlgebraIsomorphism Φ := by
  intro hA hTop _
  let P := MeasureAlgebraStone.stoneProbabilitySpace hA
  let Φ := MeasureAlgebraStone.representationHom hA
  have hP : Chapter01.IsProbabilitySpace P :=
    MeasureAlgebraStone.isProbabilitySpace_stoneProbabilitySpace hA hTop
  exact ⟨P, Φ, hP, isMeasureAlgebra_inducedMeasureAlgebra P hP,
    MeasureAlgebraStone.isMeasureAlgebraIsomorphism_representationHom hA⟩

/--
Source: Definition 4.1.20, Chapter 4, Section 1.
An isomorphism of probability spaces is an isomorphism after discarding null
sets.
-/
def probabilitySpaceIsomorphism (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v}) : Prop :=
  IsIsomorphicProbabilitySpaces P Q

/--
Source: Definition 4.1.21, Chapter 4, Section 1.
Two probability spaces are conjugate when their measure algebras are
isomorphic.
-/
def probabilitySpaceConjugacy (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v}) : Prop :=
  AreConjugateProbabilitySpaces P Q

/--
Source: Definition 4.1.21, Chapter 4, Section 1.
Probability-space isomorphism implies conjugacy of measure algebras, and
conjugacy is the measure-algebra form of equivalence.
-/
theorem probabilitySpaceIsomorphismImpliesConjugacy
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{u}) :
    Chapter01.IsProbabilitySpace P -> Chapter01.IsProbabilitySpace Q ->
    IsIsomorphicProbabilitySpaces P Q -> AreConjugateProbabilitySpaces P Q := by
  intro hP hQ hIso
  letI : MeasureTheory.IsProbabilityMeasure P.μ := hP
  letI : MeasureTheory.IsProbabilityMeasure Q.μ := hQ
  rcases hIso with
    ⟨X₀, Y₀, hXm, hYm, hPX, hQY, φ, ψ, hleft, hright, hφm, hψm, hφμ⟩
  have hXc : P.μ X₀ᶜ = 0 := by
    rw [MeasureTheory.measure_compl hXm (by rw [hPX]; simp)]
    simp [hPX]
  have hYc : Q.μ Y₀ᶜ = 0 := by
    rw [MeasureTheory.measure_compl hYm (by rw [hQY]; simp)]
    simp [hQY]
  let pull : (inducedMeasureAlgebra Q).carrier → Set P.X := fun B =>
    Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' B.1))
  have hpull_meas (B : (inducedMeasureAlgebra Q).carrier) : MeasurableSet (pull B) := by
    apply hXm.subtype_image
    exact (B.2.preimage measurable_subtype_coe).preimage hφm
  have hpull_measure (B : (inducedMeasureAlgebra Q).carrier) : P.μ (pull B) = Q.μ B.1 := by
    have hm := hφμ (Subtype.val ⁻¹' B.1) (B.2.preimage measurable_subtype_coe)
    change P.μ (pull B) = Q.μ B.1
    rw [hm]
    rw [show Subtype.val '' (Subtype.val ⁻¹' B.1 : Set Y₀) = B.1 ∩ Y₀ by
      ext y
      simp [and_comm]]
    rw [show B.1 ∩ Y₀ = B.1 \ Y₀ᶜ by ext y; simp]
    exact MeasureTheory.measure_diff_null hYc
  let Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q) (inducedMeasureAlgebra P) :=
    { map := fun B => ⟨pull B, hpull_meas B⟩ }
  refine ⟨Φ, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro B C hBC
      change P.μ (Chapter00.symmDiff (pull B) (pull C)) = 0
      rw [show Chapter00.symmDiff (pull B) (pull C) =
          pull ⟨Chapter00.symmDiff B.1 C.1,
            B.2.diff C.2 |>.union (C.2.diff B.2)⟩ by
        ext x
        simp [pull, Chapter00.symmDiff]]
      rw [hpull_measure]
      exact hBC
    · intro B C
      change P.μ (Chapter00.symmDiff (pull ⟨B.1 ∪ C.1, B.2.union C.2⟩)
        (pull B ∪ pull C)) = 0
      have heq : pull ⟨B.1 ∪ C.1, B.2.union C.2⟩ = pull B ∪ pull C := by
        ext x
        simp [pull]
      simp [heq, Chapter00.symmDiff]
    · intro B
      change P.μ (Chapter00.symmDiff (pull ⟨B.1ᶜ, B.2.compl⟩) (pull B)ᶜ) = 0
      apply MeasureTheory.measure_mono_null (t := X₀ᶜ) ?_ hXc
      intro x hx
      simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff, Set.mem_compl_iff] at hx ⊢
      have hpart : x ∈ X₀ →
          (x ∈ pull ⟨B.1ᶜ, B.2.compl⟩ ↔ x ∉ pull B) := by
        intro hxX
        constructor
        · rintro ⟨x₁, hx₁, hx₁x⟩ ⟨x₂, hx₂, hx₂x⟩
          have hx12 : x₁ = x₂ := Subtype.ext (hx₁x.trans hx₂x.symm)
          subst x₂
          exact hx₁ hx₂
        · intro hxnot
          refine ⟨⟨x, hxX⟩, ?_, rfl⟩
          intro hφB
          exact hxnot ⟨⟨x, hxX⟩, hφB, rfl⟩
      rcases hx with hx | hx
      · exact fun hxX => hx.2 ((hpart hxX).mp hx.1)
      · exact fun hxX => hx.2 ((hpart hxX).mpr hx.1)
    · intro f
      change P.μ (Chapter00.symmDiff
        (pull ⟨⋃ n, (f n).1, MeasurableSet.iUnion fun n => (f n).2⟩)
        (⋃ n, pull (f n))) = 0
      have heq : pull ⟨⋃ n, (f n).1, MeasurableSet.iUnion fun n => (f n).2⟩ =
          ⋃ n, pull (f n) := by
        ext x
        simp [pull]
      simp [heq, Chapter00.symmDiff]
    · intro B
      change (P.μ (pull B)).toReal = (Q.μ B.1).toReal
      rw [hpull_measure]
  · intro B C hBC
    change Q.μ (Chapter00.symmDiff B.1 C.1) = 0
    rw [← hpull_measure
      ⟨Chapter00.symmDiff B.1 C.1, B.2.diff C.2 |>.union (C.2.diff B.2)⟩]
    rw [show pull ⟨Chapter00.symmDiff B.1 C.1,
          B.2.diff C.2 |>.union (C.2.diff B.2)⟩ =
        Chapter00.symmDiff (pull B) (pull C) by
      ext x
      simp [pull, Chapter00.symmDiff]]
    exact hBC
  · intro A
    let S : Set Y₀ := ψ ⁻¹' (Subtype.val ⁻¹' A.1)
    have hSm : MeasurableSet S := (A.2.preimage measurable_subtype_coe).preimage hψm
    let Bset : Set Q.X := Subtype.val '' S
    have hBm : MeasurableSet Bset := hYm.subtype_image hSm
    refine ⟨⟨Bset, hBm⟩, ?_⟩
    change P.μ (Chapter00.symmDiff (pull ⟨Bset, hBm⟩) A.1) = 0
    apply MeasureTheory.measure_mono_null (t := X₀ᶜ) ?_ hXc
    intro x hx
    simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff, Set.mem_compl_iff] at hx ⊢
    have hcore : x ∈ X₀ → (x ∈ pull ⟨Bset, hBm⟩ ↔ x ∈ A.1) := by
      intro hxX
      constructor
      · rintro ⟨x', hx', rfl⟩
        rcases hx' with ⟨y, hyS, hφxy⟩
        have hxy : y = φ x' := Subtype.ext hφxy
        subst y
        have hyA := hyS
        change (ψ (φ x')).val ∈ A.1 at hyA
        rw [hleft x'] at hyA
        exact hyA
      · intro hxA
        refine ⟨⟨x, hxX⟩, ?_, rfl⟩
        change (φ ⟨x, hxX⟩).val ∈ Bset
        refine ⟨φ ⟨x, hxX⟩, ?_, rfl⟩
        change (ψ (φ ⟨x, hxX⟩)).val ∈ A.1
        rw [hleft ⟨x, hxX⟩]
        exact hxA
    rcases hx with hx | hx
    · exact fun hxX => hx.2 ((hcore hxX).mp hx.1)
    · exact fun hxX => hx.2 ((hcore hxX).mpr hx.1)

/--
Source: Example 4.1.22, Chapter 4, Section 1.
There exist conjugate probability spaces that are not isomorphic as probability
spaces.
-/
theorem conjugateButNotIsomorphicProbabilitySpacesExample :
    ∃ P Q : ProbabilitySpace.{0},
      AreConjugateProbabilitySpaces P Q ∧ ¬ IsIsomorphicProbabilitySpaces P Q := by
  let mP : MeasurableSpace Unit := ⊥
  let mQ : MeasurableSpace Bool := ⊥
  let P : ProbabilitySpace.{0} :=
    { X := Unit, measurableSpace := mP,
      μ := @MeasureTheory.Measure.dirac Unit mP () }
  let Q : ProbabilitySpace.{0} :=
    { X := Bool, measurableSpace := mQ,
      μ := @MeasureTheory.Measure.dirac Bool mQ false }
  let Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q) (inducedMeasureAlgebra P) :=
    { map := fun B => ⟨(fun _ : Unit => false) ⁻¹' B.1, by
        change @MeasurableSet Unit mP ((fun _ : Unit => false) ⁻¹' B.1)
        have hB : B.1 = ∅ ∨ B.1 = Set.univ := by
          have hBm : @MeasurableSet Bool mQ B.1 := B.property
          have hBm' : @MeasurableSet Bool (⊥) B.1 := by simpa [mQ] using hBm
          exact MeasurableSpace.measurableSet_bot_iff.mp hBm'
        rcases hB with hB | hB <;> rw [hB] <;> simp ⟩ }
  refine ⟨P, Q, ?_, ?_⟩
  · refine ⟨Φ, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro B C hBC
        have hB : B.1 = ∅ ∨ B.1 = Set.univ := by
          have hBm : @MeasurableSet Bool mQ B.1 := B.property
          have hBm' : @MeasurableSet Bool (⊥) B.1 := by simpa [mQ] using hBm
          exact MeasurableSpace.measurableSet_bot_iff.mp hBm'
        have hC : C.1 = ∅ ∨ C.1 = Set.univ := by
          have hCm : @MeasurableSet Bool mQ C.1 := C.property
          have hCm' : @MeasurableSet Bool (⊥) C.1 := by simpa [mQ] using hCm
          exact MeasurableSpace.measurableSet_bot_iff.mp hCm'
        rcases hB with hB | hB <;> rcases hC with hC | hC <;>
          simp [Φ, inducedMeasureAlgebra, Q, Chapter00.symmDiff, hB, hC] at hBC ⊢
      · intro B C
        simp [Φ, inducedMeasureAlgebra, Chapter00.symmDiff]
      · intro B
        simp [Φ, inducedMeasureAlgebra, Chapter00.symmDiff]
      · intro B
        simp [Φ, inducedMeasureAlgebra, Chapter00.symmDiff]
      · intro B
        have hB : B.1 = ∅ ∨ B.1 = Set.univ := by
          have hBm : @MeasurableSet Bool mQ B.1 := B.property
          have hBm' : @MeasurableSet Bool (⊥) B.1 := by simpa [mQ] using hBm
          exact MeasurableSpace.measurableSet_bot_iff.mp hBm'
        rcases hB with hB | hB <;>
          simp [Φ, inducedMeasureAlgebra, P, Q, hB]
    · intro B C hBC
      have hB : B.1 = ∅ ∨ B.1 = Set.univ := by
        have hBm : @MeasurableSet Bool mQ B.1 := B.property
        have hBm' : @MeasurableSet Bool (⊥) B.1 := by simpa [mQ] using hBm
        exact MeasurableSpace.measurableSet_bot_iff.mp hBm'
      have hC : C.1 = ∅ ∨ C.1 = Set.univ := by
        have hCm : @MeasurableSet Bool mQ C.1 := C.property
        have hCm' : @MeasurableSet Bool (⊥) C.1 := by simpa [mQ] using hCm
        exact MeasurableSpace.measurableSet_bot_iff.mp hCm'
      rcases hB with hB | hB <;> rcases hC with hC | hC <;>
        simp [Φ, inducedMeasureAlgebra, P, Q, Chapter00.symmDiff, hB, hC] at hBC ⊢
    · intro A
      have hA : A.1 = ∅ ∨ A.1 = Set.univ := by
        have hAm : @MeasurableSet Unit mP A.1 := A.property
        simpa [mP] using MeasurableSpace.measurableSet_bot_iff.mp hAm
      rcases hA with hA | hA
      · refine ⟨⟨∅, MeasurableSet.empty⟩, ?_⟩
        simp [Φ, inducedMeasureAlgebra, P, Chapter00.symmDiff, hA]
      · refine ⟨⟨Set.univ, MeasurableSet.univ⟩, ?_⟩
        simp [Φ, inducedMeasureAlgebra, P, Chapter00.symmDiff, hA]
  · rintro ⟨X₀, Y₀, hXm, hYm, hPX, hQY, φ, ψ, hleft, hright, -⟩
    have hX₀ : X₀ = Set.univ := by
      rcases (MeasurableSpace.measurableSet_bot_iff.mp hXm) with rfl | h
      · simp [P] at hPX
      · exact h
    have hY₀ : Y₀ = Set.univ := by
      rcases (MeasurableSpace.measurableSet_bot_iff.mp hYm) with rfl | h
      · simp [Q] at hQY
      · exact h
    subst X₀
    subst Y₀
    let x : (Set.univ : Set Unit) := ⟨(), Set.mem_univ _⟩
    let y₀ : (Set.univ : Set Bool) := ⟨false, Set.mem_univ _⟩
    let y₁ : (Set.univ : Set Bool) := ⟨true, Set.mem_univ _⟩
    have hψ : ψ y₀ = ψ y₁ := Subsingleton.elim _ _
    have := congrArg φ hψ
    rw [hright y₀, hright y₁] at this
    exact Bool.false_ne_true (congrArg Subtype.val this)

/--
Source: Example 4.1.22, Chapter 4, Section 1.
For Lebesgue spaces, isomorphism and conjugacy coincide; the same distinction is
visible from the associated L² spaces.
-/
theorem lebesgueProbabilitySpacesIsomorphicIffConjugate
    (P Q : ProbabilitySpace.{u}) :
    IsLebesgueProbabilitySpace P -> IsLebesgueProbabilitySpace Q ->
      (IsIsomorphicProbabilitySpaces P Q ↔ AreConjugateProbabilitySpaces P Q) := by
  intro hP hQ
  constructor
  · exact probabilitySpaceIsomorphismImpliesConjugacy P Q hP.1 hQ.1
  · rintro ⟨Φ, hΦ⟩
    exact MeasureAlgebraSpatial.probability_iso_of_measureAlgebra_iso P Q hP hQ Φ hΦ

/--
Source: Theorem 4.1.23, Chapter 4, Section 1.
Two probability spaces are conjugate exactly when there is an L² operator that
is unitary on L², preserves multiplication on bounded functions, and sends the
constant one function to itself.
-/
theorem probabilitySpaceConjugacyIffLtwoAlgebraUnitary
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{u})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q) :
    AreConjugateProbabilitySpaces P Q ↔ HasLtwoAlgebraUnitary P Q := by
  constructor
  · rintro ⟨Φ, hΦ⟩
    let W : (Q.X → ℂ) → P.X → ℂ :=
      MeasureAlgebraLtwo.rawLtwoMap P Q hP hQ Φ hΦ.1
    refine ⟨W, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro f g hf hg hfg
      exact MeasureAlgebraLtwo.rawLtwoMap_ae
        P Q hP hQ Φ hΦ.1 f g hf hg hfg
    · intro f g hf hg
      exact MeasureAlgebraLtwo.rawLtwoMap_add
        P Q hP hQ Φ hΦ.1 f g hf hg
    · intro c f hf
      exact MeasureAlgebraLtwo.rawLtwoMap_smul
        P Q hP hQ Φ hΦ.1 c f hf
    · intro f hf
      exact MeasureAlgebraLtwo.rawLtwoMap_ltwo
        P Q hP hQ Φ hΦ.1 f hf
    · intro h hh ε hε
      exact MeasureAlgebraLtwo.rawLtwoMap_dense
        P Q hP hQ Φ hΦ h hh ε hε
    · intro f hf
      exact LinfClosure.rawLtwoMap_memLp_top
        P Q hP hQ Φ hΦ.1 f hf
    · intro h hh
      exact InverseLtwo.rawLtwoMap_memLp_top_surjective
        P Q hP hQ Φ hΦ h hh
    · exact MeasureAlgebraLtwo.rawLtwoMap_one
        P Q hP hQ Φ hΦ.1
    · intro f g hf hg
      exact AlgebraClosure.rawLtwoMap_mul
        P Q hP hQ Φ hΦ.1 f g hf hg
  · rintro ⟨W, hW⟩
    let Φ := LtwoProjection.indicatorHom P Q hQ W hW
    exact ⟨Φ,
      LtwoProjection.indicatorHom_isMeasureAlgebraIsomorphism
        P Q hP hQ W hW⟩

/--
Source: Proposition 4.1.24, Chapter 4, Section 1.
A measure-algebra isomorphism gives the associated L² operator by sending
indicator functions to the indicators of their image classes.
-/
theorem indicatorOperatorFromMeasureAlgebraIsomorphism
    (P Q : ProbabilitySpace.{u})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q) :
    AreConjugateProbabilitySpaces P Q -> HasLtwoAlgebraUnitary P Q := by
  exact (probabilitySpaceConjugacyIffLtwoAlgebraUnitary P Q hP hQ).mp

end Section01
end Chapter04
