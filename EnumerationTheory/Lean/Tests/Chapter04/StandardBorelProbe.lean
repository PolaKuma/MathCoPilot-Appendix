import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

noncomputable section

open Classical

universe u

structure MSD where
  X : Type u
  measurableSpace : MeasurableSpace X

attribute [instance] MSD.measurableSpace

def IsMeasurableIso (M N : MSD.{u}) : Prop :=
  ∃ f : M.X → N.X, ∃ g : N.X → M.X,
    Function.LeftInverse g f ∧ Function.RightInverse g f ∧
      Measurable f ∧ Measurable g

def IsStandardData (M : MSD.{u}) : Prop :=
  ∃ Y : Type u, ∃ mY : MeasurableSpace Y, ∃ sY : @StandardBorelSpace Y mY,
    IsMeasurableIso M ⟨Y, mY⟩

def instanceOfData (M : MSD.{u}) (hM : IsStandardData M) :
    StandardBorelSpace M.X := by
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

def IsAnalyticData (M : MSD.{u}) (A : Set M.X) : Prop :=
  ∃ Y : MSD.{u}, IsStandardData Y ∧
    ∃ B : Set Y.X, MeasurableSet B ∧
    ∃ f : Y.X → M.X, Measurable f ∧ A = f '' B

theorem analyticSet_of_data (M : MSD.{u}) (hM : IsStandardData M)
    (A : Set M.X) (hA : IsAnalyticData M A) :
    @MeasureTheory.AnalyticSet M.X
      (upgradeStandardBorel M.X (h := instanceOfData M hM)).toTopologicalSpace A := by
  letI : StandardBorelSpace M.X := instanceOfData M hM
  letI : UpgradedStandardBorel M.X := upgradeStandardBorel M.X
  rcases hA with ⟨Y, hY, B, hB, f, hf, rfl⟩
  letI : StandardBorelSpace Y.X := instanceOfData Y hY
  exact hB.analyticSet_image hf

theorem measurablySeparable_of_data (M : MSD.{u}) (hM : IsStandardData M)
    {A B : Set M.X} (hA : IsAnalyticData M A) (hB : IsAnalyticData M B)
    (hdis : Disjoint A B) :
    ∃ C : Set M.X, A ⊆ C ∧ Disjoint B C ∧ MeasurableSet C := by
  letI : StandardBorelSpace M.X := instanceOfData M hM
  letI : UpgradedStandardBorel M.X := upgradeStandardBorel M.X
  exact (analyticSet_of_data M hM A hA).measurablySeparable
    (analyticSet_of_data M hM B hB) hdis

theorem measurableEmbedding_of_data
    (M N : MSD.{u}) (hM : IsStandardData M) (hN : IsStandardData N)
    (f : M.X → N.X)
    (hf : @Measurable M.X N.X M.measurableSpace N.measurableSpace f)
    (hinj : Function.Injective f) :
    @MeasurableEmbedding M.X N.X M.measurableSpace N.measurableSpace f := by
  letI : StandardBorelSpace M.X := instanceOfData M hM
  letI : StandardBorelSpace N.X := instanceOfData N hN
  exact hf.measurableEmbedding hinj

theorem measurableSet_image_of_injective
    (M N : MSD.{u}) (hM : IsStandardData M) (hN : IsStandardData N)
    (f : M.X → N.X)
    (hf : @Measurable M.X N.X M.measurableSpace N.measurableSpace f)
    (hinj : Function.Injective f) {A : Set M.X}
    (hA : @MeasurableSet M.X M.measurableSpace A) :
    @MeasurableSet N.X N.measurableSpace (f '' A) := by
  exact (measurableEmbedding_of_data M N hM hN f hf hinj).measurableSet_image.2 hA

def IsUniversalData (M : MSD.{u}) (A : Set M.X) : Prop :=
  ∀ μ : MeasureTheory.Measure M.X, μ Set.univ < ⊤ →
    ∃ B N : Set M.X, MeasurableSet B ∧ MeasurableSet N ∧ μ N = 0 ∧
      ((A \ B) ∪ (B \ A)) ⊆ N

theorem universallyMeasurable_iff_nullMeasurable (M : MSD.{u}) (A : Set M.X) :
    IsUniversalData M A ↔
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
    let D : Set M.X := (A \ B) ∪ (B \ A)
    have hAB : A =ᵐ[μ] B := hBA
    have hD0 : μ D = 0 := by
      have hparts := MeasureTheory.ae_eq_set.mp hAB
      simp [D, hparts.1, hparts.2]
    refine ⟨B, MeasureTheory.toMeasurable μ D, hB,
      MeasureTheory.measurableSet_toMeasurable μ D, ?_, ?_⟩
    · simpa [D] using (MeasureTheory.measure_toMeasurable D).trans hD0
    · exact MeasureTheory.subset_toMeasurable μ D
