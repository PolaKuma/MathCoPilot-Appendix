import Chapter02.Common
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

noncomputable section

open Classical MeasureTheory

namespace Chapter02.CompactAbelianPeterWeyl

universe u

variable {G : Type u} [CommGroup G] [MetricSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

abbrev Character :=
  Chapter02.ContinuousMultiplicativeCircleCharacter G

def characterContinuousMap (χ : Character (G := G)) : C(G, ℂ) where
  toFun := χ.toFun
  continuous_toFun := χ.continuous

def oneCharacter : Character (G := G) where
  toFun _ := 1
  map_one := rfl
  map_mul _ _ := by simp
  continuous := continuous_const
  unit_norm _ := by simp

def mulCharacter (χ ψ : Character (G := G)) : Character (G := G) where
  toFun x := χ.toFun x * ψ.toFun x
  map_one := by simp [χ.map_one, ψ.map_one]
  map_mul x y := by rw [χ.map_mul, ψ.map_mul]; ring
  continuous := χ.continuous.mul ψ.continuous
  unit_norm x := by simp [χ.unit_norm x, ψ.unit_norm x]

def starCharacter (χ : Character (G := G)) : Character (G := G) where
  toFun x := star (χ.toFun x)
  map_one := by simp [χ.map_one]
  map_mul x y := by simp [χ.map_mul]
  continuous := χ.continuous.star
  unit_norm x := by simp [χ.unit_norm x]

omit [CompactSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] in
@[simp]
lemma characterContinuousMap_mul (χ ψ : Character (G := G)) :
    characterContinuousMap (mulCharacter χ ψ) =
      characterContinuousMap χ * characterContinuousMap ψ :=
  rfl

omit [CompactSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] in
@[simp]
lemma characterContinuousMap_star (χ : Character (G := G)) :
    characterContinuousMap (starCharacter χ) =
      star (characterContinuousMap χ) :=
  rfl

def continuousCharacterSpan : Submodule ℂ C(G, ℂ) :=
  Submodule.span ℂ (Set.range (characterContinuousMap (G := G)))

omit [CompactSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] in
lemma continuousCharacterSpan_one :
    (1 : C(G, ℂ)) ∈ continuousCharacterSpan (G := G) := by
  apply Submodule.subset_span
  exact ⟨oneCharacter, rfl⟩

omit [CompactSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] in
lemma continuousCharacterSpan_mul
    {f g : C(G, ℂ)}
    (hf : f ∈ continuousCharacterSpan (G := G))
    (hg : g ∈ continuousCharacterSpan (G := G)) :
    f * g ∈ continuousCharacterSpan (G := G) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨χ, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨ψ, rfl⟩ := hg
          rw [← characterContinuousMap_mul]
          exact Submodule.subset_span ⟨mulCharacter χ ψ, rfl⟩
      | zero => simp [continuousCharacterSpan]
      | add x y _ _ hx hy =>
          simpa [mul_add] using
            (continuousCharacterSpan (G := G)).add_mem hx hy
      | smul c x _ hx =>
          simpa [mul_smul_comm] using
            (continuousCharacterSpan (G := G)).smul_mem c hx
  | zero => simp [continuousCharacterSpan]
  | add x y _ _ hx hy =>
      simpa [add_mul] using
        (continuousCharacterSpan (G := G)).add_mem hx hy
  | smul c x _ hx =>
      simpa [smul_mul_assoc] using
        (continuousCharacterSpan (G := G)).smul_mem c hx

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
lemma continuousCharacterSpan_star
    {f : C(G, ℂ)} (hf : f ∈ continuousCharacterSpan (G := G)) :
    star f ∈ continuousCharacterSpan (G := G) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨χ, rfl⟩ := hf
      rw [← characterContinuousMap_star]
      exact Submodule.subset_span ⟨starCharacter χ, rfl⟩
  | zero => simp [continuousCharacterSpan]
  | add x y _ _ hx hy =>
      rw [star_add]
      exact (continuousCharacterSpan (G := G)).add_mem hx hy
  | smul c x _ hx =>
      simpa only [star_smul] using
        (continuousCharacterSpan (G := G)).smul_mem (star c) hx

def characterStarSubalgebra : StarSubalgebra ℂ C(G, ℂ) where
  carrier := continuousCharacterSpan (G := G)
  zero_mem' := (continuousCharacterSpan (G := G)).zero_mem
  add_mem' := (continuousCharacterSpan (G := G)).add_mem
  one_mem' := continuousCharacterSpan_one
  mul_mem' := continuousCharacterSpan_mul
  algebraMap_mem' c := by
    simpa [Algebra.smul_def] using
      (continuousCharacterSpan (G := G)).smul_mem c
        continuousCharacterSpan_one
  star_mem' := continuousCharacterSpan_star

def characterLp
    (m : Measure G) [IsProbabilityMeasure m]
    (χ : Character (G := G)) :
    Lp ℂ 2 m := by
  have hχ : MemLp χ.toFun 2 m := by
    apply (memLp_top_of_bound χ.continuous.aestronglyMeasurable 1 ?_).mono_exponent
      (by simp)
    exact .of_forall fun x => le_of_eq (χ.unit_norm x)
  exact hχ.toLp χ.toFun

omit [IsTopologicalGroup G] in
lemma characterLp_eq_toLp
    (m : Measure G) [IsProbabilityMeasure m]
    (χ : Character (G := G)) :
    characterLp m χ =
      ContinuousMap.toLp 2 m ℂ (characterContinuousMap χ) := by
  have hχ : MemLp χ.toFun 2 m := by
    apply (memLp_top_of_bound χ.continuous.aestronglyMeasurable 1 ?_).mono_exponent
      (by simp)
    exact .of_forall fun x => le_of_eq (χ.unit_norm x)
  apply Lp.ext
  filter_upwards
      [hχ.coeFn_toLp,
        ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) m
          (characterContinuousMap χ)] with x hx hy
  exact hx.trans hy.symm

def lpCharacterSpan
    (m : Measure G) [IsProbabilityMeasure m] :
    Submodule ℂ (Lp ℂ 2 m) :=
  Submodule.span ℂ (Set.range (characterLp m))

omit [IsTopologicalGroup G] in
lemma toLp_mem_lpCharacterSpan
    (m : Measure G) [IsProbabilityMeasure m]
    {f : C(G, ℂ)} (hf : f ∈ continuousCharacterSpan (G := G)) :
    ContinuousMap.toLp 2 m ℂ f ∈ lpCharacterSpan m := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨χ, rfl⟩ := hf
      rw [← characterLp_eq_toLp]
      exact Submodule.subset_span ⟨χ, rfl⟩
  | zero => simp [lpCharacterSpan]
  | add x y _ _ hx hy =>
      simpa using (lpCharacterSpan m).add_mem hx hy
  | smul c x _ hx =>
      simpa using (lpCharacterSpan m).smul_mem c hx

omit [IsTopologicalGroup G] in
theorem character_span_dense_of_separates
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hsep : ∀ x y : G, x ≠ y →
      ∃ χ : Character (G := G), χ.toFun x ≠ χ.toFun y) :
    Dense (lpCharacterSpan m : Set (Lp ℂ 2 m)) := by
  have hsepA :
      (characterStarSubalgebra (G := G)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨χ, hχ⟩ := hsep x y hxy
    refine ⟨χ.toFun, ⟨characterContinuousMap χ, ?_, rfl⟩, hχ⟩
    change characterContinuousMap χ ∈ continuousCharacterSpan (G := G)
    exact Submodule.subset_span ⟨χ, rfl⟩
  have hcontinuous :
      Dense (continuousCharacterSpan (G := G) : Set C(G, ℂ)) := by
    apply dense_iff_closure_eq.mpr
    simpa [StarSubalgebra.topologicalClosure_coe,
      characterStarSubalgebra] using congrArg
        (fun A : StarSubalgebra ℂ C(G, ℂ) => (A : Set C(G, ℂ)))
        (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
          (characterStarSubalgebra (G := G)) hsepA)
  have hsubtype :
      DenseRange (continuousCharacterSpan (G := G)).subtypeL := by
    exact denseRange_subtype_val.mpr hcontinuous
  have htoLp :
      DenseRange (ContinuousMap.toLp 2 m ℂ :
        C(G, ℂ) →L[ℂ] Lp ℂ 2 m) :=
    ContinuousMap.toLp_denseRange
      (p := 2) (α := G) (E := ℂ) (μ := m) (𝕜 := ℂ) (by simp)
  have hcomp :
      DenseRange ((ContinuousMap.toLp 2 m ℂ).comp
        (continuousCharacterSpan (G := G)).subtypeL) :=
    by
      simpa [Function.comp_def] using
        htoLp.comp hsubtype (ContinuousMap.toLp 2 m ℂ).continuous
  apply hcomp.mono
  rintro _ ⟨f, rfl⟩
  exact toLp_mem_lpCharacterSpan m f.property

end Chapter02.CompactAbelianPeterWeyl
