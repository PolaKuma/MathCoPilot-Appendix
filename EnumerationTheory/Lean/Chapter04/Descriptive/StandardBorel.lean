import Chapter04.Common
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

noncomputable section

open Classical

namespace Chapter04.StandardBorel

universe u

/-- An explicit standard-Borel model in the chapter's data language gives the
corresponding Mathlib typeclass on the original carrier.  This lets later
descriptive-set proofs use Mathlib's Polish model without changing the
measurable space carried by the textbook data. -/
def instanceOfData (M : MeasurableSpaceData.{u})
    (hM : IsStandardBorelSpaceData M) : StandardBorelSpace M.X := by
  rcases hM with ⟨Y, mY, sY, f, g, hleft, hright, hf, hg⟩
  letI : MeasurableSpace Y := mY
  letI : StandardBorelSpace Y := sY
  let e : M.X ≃ᵐ Y :=
    { toFun := f
      invFun := g
      left_inv := hleft
      right_inv := hright
      measurable_toFun := hf
      measurable_invFun := hg }
  let tY : TopologicalSpace Y := (upgradeStandardBorel Y).toTopologicalSpace
  let tX : TopologicalSpace M.X := tY.induced e
  have hpolish : @PolishSpace M.X tX := e.toEquiv.polishSpace_induced
  have hborel : @borel M.X tX = M.measurableSpace := by
    calc
      @borel M.X tX = MeasurableSpace.comap e (@borel Y tY) := borel_comap
      _ = MeasurableSpace.comap e mY := by
        change MeasurableSpace.comap f (@borel Y tY) =
          MeasurableSpace.comap f mY
        exact congrArg (MeasurableSpace.comap f)
          (eq_borel_upgradeStandardBorel Y).symm
      _ = M.measurableSpace := e.measurableEmbedding.comap_eq
  exact ⟨⟨tX, ⟨hborel.symm⟩, hpolish⟩⟩

/-- The chapter's image-based definition of an analytic set agrees with
Mathlib's analytic-set predicate after installing a compatible Polish topology
on the target standard Borel space. -/
theorem analyticSet_of_data (M : MeasurableSpaceData.{u})
    (hM : IsStandardBorelSpaceData M) (A : Set M.X)
    (hA : IsAnalyticSet M A) :
    @MeasureTheory.AnalyticSet M.X
      (upgradeStandardBorel M.X (h := instanceOfData M hM)).toTopologicalSpace A := by
  letI : StandardBorelSpace M.X := instanceOfData M hM
  letI : UpgradedStandardBorel M.X := upgradeStandardBorel M.X
  rcases hA with ⟨Y, hY, B, hB, f, hf, rfl⟩
  letI : StandardBorelSpace Y.X := instanceOfData Y hY
  exact hB.analyticSet_image hf

/-- Lusin separation, expressed directly in the chapter's standard-Borel and
analytic-set language. -/
theorem measurablySeparable_of_data (M : MeasurableSpaceData.{u})
    (hM : IsStandardBorelSpaceData M) {A B : Set M.X}
    (hA : IsAnalyticSet M A) (hB : IsAnalyticSet M B)
    (hdis : Disjoint A B) :
    ∃ C : Set M.X, A ⊆ C ∧ Disjoint B C ∧ MeasurableSet C := by
  letI : StandardBorelSpace M.X := instanceOfData M hM
  letI : UpgradedStandardBorel M.X := upgradeStandardBorel M.X
  exact (analyticSet_of_data M hM A hA).measurablySeparable
    (analyticSet_of_data M hM B hB) hdis

/-- A one-to-one measurable map between the chapter's standard Borel spaces is
a measurable embedding.  This is the Lusin--Souslin theorem in the form used
by the selection and local-inversion arguments. -/
theorem measurableEmbedding_of_data
    (M N : MeasurableSpaceData.{u}) (hM : IsStandardBorelSpaceData M)
    (hN : IsStandardBorelSpaceData N) (f : M.X → N.X)
    (hf : IsMeasurableMap M N f) (hinj : Function.Injective f) :
    @MeasurableEmbedding M.X N.X M.measurableSpace N.measurableSpace f := by
  letI : StandardBorelSpace M.X := instanceOfData M hM
  letI : StandardBorelSpace N.X := instanceOfData N hN
  have hf' : Measurable f := hf
  exact hf'.measurableEmbedding hinj

theorem measurableSet_image_of_injective
    (M N : MeasurableSpaceData.{u}) (hM : IsStandardBorelSpaceData M)
    (hN : IsStandardBorelSpaceData N) (f : M.X → N.X)
    (hf : IsMeasurableMap M N f) (hinj : Function.Injective f)
    {A : Set M.X} (hA : A ∈ M.sets) : f '' A ∈ N.sets := by
  exact (measurableEmbedding_of_data M N hM hN f hf hinj).measurableSet_image.2 hA

/-- The chapter's explicit completion formulation is exactly null
measurability for every finite measure. -/
theorem universallyMeasurable_iff_nullMeasurable
    (M : MeasurableSpaceData.{u}) (A : Set M.X) :
    IsUniversallyMeasurable M A ↔
      ∀ μ : MeasureTheory.Measure M.X, μ Set.univ < ⊤ →
        MeasureTheory.NullMeasurableSet A μ := by
  constructor
  · intro h μ hμ
    rcases h μ hμ with ⟨B, N, hB, hN, hN0, hdiff⟩
    refine ⟨B, hB, ?_⟩
    apply Filter.EventuallyEq.symm
    rw [MeasureTheory.ae_eq_set]
    constructor
    · exact MeasureTheory.measure_mono_null
        (fun x hx => hdiff (Or.inr hx)) hN0
    · exact MeasureTheory.measure_mono_null
        (fun x hx => hdiff (Or.inl hx)) hN0
  · intro h μ hμ
    rcases h μ hμ with ⟨B, hB, hBA⟩
    let D : Set M.X := Chapter00.symmDiff A B
    have hAB : A =ᵐ[μ] B := hBA
    have hD0 : μ D = 0 := by
      have hparts := MeasureTheory.ae_eq_set.mp hAB
      simp [D, Chapter00.symmDiff, hparts.1, hparts.2]
    refine ⟨B, MeasureTheory.toMeasurable μ D, hB,
      MeasureTheory.measurableSet_toMeasurable μ D, ?_, ?_⟩
    · simpa [D] using (MeasureTheory.measure_toMeasurable D).trans hD0
    · exact MeasureTheory.subset_toMeasurable μ D

/-- Every measurable set is universally measurable in the chapter's explicit
completion formulation. -/
theorem universallyMeasurable_of_measurableSet
    (M : MeasurableSpaceData.{u}) {A : Set M.X}
    (hA : MeasurableSet A) :
    IsUniversallyMeasurable M A := by
  rw [universallyMeasurable_iff_nullMeasurable]
  intro μ hμ
  exact hA.nullMeasurableSet

/-- Suslin's theorem in the chapter's data language: an analytic set with
analytic complement is Borel measurable. -/
theorem measurableSet_of_analytic_compl
    (M : MeasurableSpaceData.{u}) (hM : IsStandardBorelSpaceData M)
    {A : Set M.X} (hA : IsAnalyticSet M A)
    (hAc : IsAnalyticSet M Aᶜ) :
    MeasurableSet A := by
  letI : StandardBorelSpace M.X := instanceOfData M hM
  letI : UpgradedStandardBorel M.X := upgradeStandardBorel M.X
  exact (analyticSet_of_data M hM A hA).measurableSet_of_compl
    (analyticSet_of_data M hM Aᶜ hAc)

/-- The universally measurable conclusion of Lusin's theorem follows
immediately in the special case where the complement is also analytic. -/
theorem universallyMeasurable_of_analytic_compl
    (M : MeasurableSpaceData.{u}) (hM : IsStandardBorelSpaceData M)
    {A : Set M.X} (hA : IsAnalyticSet M A)
    (hAc : IsAnalyticSet M Aᶜ) :
    IsUniversallyMeasurable M A :=
  universallyMeasurable_of_measurableSet M
    (measurableSet_of_analytic_compl M hM hA hAc)

/-- The injective case of Jankov--von Neumann selection.  Here the canonical
inverse on the range is already measurable, and its measurable preimages are
themselves analytic generators. -/
theorem injectiveSelection_of_data
    (M N : MeasurableSpaceData.{u}) (f : M.X → N.X)
    (hM : IsStandardBorelSpaceData M)
    (hN : IsStandardBorelSpaceData N)
    (hf : IsMeasurableMap M N f) (hinj : Function.Injective f) :
    ∃ g : Set.range f → M.X,
      (∀ A : Set M.X, A ∈ M.sets →
        g ⁻¹' A ∈ analyticSigmaAlgebra
          (subspaceMeasurableSpace N (Set.range f))) ∧
      ∀ y : Set.range f, f (g y) = y.1 := by
  have hf' : Measurable f := hf
  have hemb := measurableEmbedding_of_data M N hM hN f hf hinj
  let g : Set.range f → M.X := Set.rangeSplitting f
  have hg : Measurable g := hemb.measurable_rangeSplitting
  refine ⟨g, ?_, ?_⟩
  · intro A hA
    apply MeasurableSpace.measurableSet_generateFrom
    change IsAnalyticSet (subspaceMeasurableSpace N (Set.range f))
      (g ⁻¹' A)
    refine ⟨M, hM, A, hA, Set.rangeFactorization f, ?_, ?_⟩
    · exact hf'.subtype_mk
    · ext y
      constructor
      · intro hy
        exact ⟨g y, hy, by
          simpa only [g] using Set.leftInverse_rangeSplitting f y⟩
      · rintro ⟨x, hx, rfl⟩
        change Set.rangeSplitting f (Set.rangeFactorization f x) ∈ A
        rw [Set.rightInverse_rangeSplitting hinj x]
        exact hx
  · intro y
    exact congrArg Subtype.val (Set.leftInverse_rangeSplitting f y)

end Chapter04.StandardBorel
