import Chapter02.Spectral.CircleFourier
import Mathlib.MeasureTheory.Function.ContinuousMapDense

open Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace Chapter02.CircleLaurent

/-- The Laurent character `z ↦ z ^ n` on the unit circle. -/
def character (n : ℤ) : C(Circle, ℂ) where
  toFun z := (z : ℂ) ^ n
  continuous_toFun := continuous_subtype_val.zpow₀ n
    (fun z => Or.inl (Circle.coe_ne_zero z))

@[simp] theorem character_apply (n : ℤ) (z : Circle) :
    character n z = (z : ℂ) ^ n := rfl

@[simp] theorem character_zero : character 0 = 1 := by
  ext z
  simp

theorem character_add (m n : ℤ) : character (m + n) = character m * character n := by
  ext z
  exact zpow_add₀ z.coe_ne_zero m n

theorem star_character (n : ℤ) : star (character n) = character (-n) := by
  ext z
  simp only [ContinuousMap.star_apply, character_apply]
  rw [Complex.star_def, map_zpow₀]
  rw [show (starRingEnd ℂ) (z : ℂ) = (z : ℂ)⁻¹ by
    apply Complex.ext <;> simp [Complex.inv_def, Circle.norm_coe]]
  simp

/-- The complex linear span of the Laurent characters. -/
def span : Submodule ℂ C(Circle, ℂ) :=
  Submodule.span ℂ (Set.range character)

theorem character_mem_span (n : ℤ) : character n ∈ span :=
  Submodule.subset_span (Set.mem_range_self n)

theorem character_mul_mem_span (m : ℤ) {g : C(Circle, ℂ)} (hg : g ∈ span) :
    character m * g ∈ span := by
  refine Submodule.span_induction (p := fun g _ => character m * g ∈ span) ?_ ?_ ?_ ?_ hg
  · intro x hx
    obtain ⟨n, rfl⟩ := hx
    rw [← character_add]
    exact character_mem_span (m + n)
  · simpa using span.zero_mem
  · intro x y _ _ hx hy
    simpa [mul_add] using span.add_mem hx hy
  · intro a x _ hx
    simpa [mul_smul_comm] using span.smul_mem a hx

theorem mul_mem_span {f g : C(Circle, ℂ)} (hf : f ∈ span) (hg : g ∈ span) :
    f * g ∈ span := by
  refine Submodule.span_induction (p := fun f _ => f * g ∈ span) ?_ ?_ ?_ ?_ hf
  · intro x hx
    obtain ⟨m, rfl⟩ := hx
    exact character_mul_mem_span m hg
  · simpa using span.zero_mem
  · intro x y _ _ hx hy
    simpa [add_mul] using span.add_mem hx hy
  · intro a x _ hx
    simpa [smul_mul_assoc] using span.smul_mem a hx

theorem star_mem_span {f : C(Circle, ℂ)} (hf : f ∈ span) : star f ∈ span := by
  refine Submodule.span_induction (p := fun f _ => star f ∈ span) ?_ ?_ ?_ ?_ hf
  · intro x hx
    obtain ⟨n, rfl⟩ := hx
    rw [star_character]
    exact character_mem_span (-n)
  · simpa using span.zero_mem
  · intro x y _ _ hx hy
    rw [show star (x + y) = star x + star y by ext z; simp]
    exact span.add_mem hx hy
  · intro a x _ hx
    simpa only [star_smul] using span.smul_mem (star a) hx

/-- Laurent polynomials, regarded as a self-adjoint algebra of continuous functions. -/
def algebra : StarSubalgebra ℂ C(Circle, ℂ) where
  carrier := span
  zero_mem' := span.zero_mem
  one_mem' := by simpa [← character_zero] using character_mem_span 0
  add_mem' := span.add_mem
  mul_mem' := mul_mem_span
  algebraMap_mem' := fun a => by
    have h := span.smul_mem a (character_mem_span 0)
    convert h using 1 <;> ext z <;> simp
  star_mem' := star_mem_span

theorem algebra_separatesPoints : algebra.SeparatesPoints := by
  intro x y hxy
  refine ⟨⇑(character 1), ?_, ?_⟩
  · exact ⟨character 1, character_mem_span 1, rfl⟩
  · simpa using hxy

/-- Laurent polynomials are uniformly dense in continuous functions on the circle. -/
theorem dense_continuous : Dense (algebra : Set C(Circle, ℂ)) := by
  have htop :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      algebra algebra_separatesPoints
  intro f
  change f ∈ algebra.topologicalClosure
  rw [htop]
  trivial

/-- Laurent polynomials are dense in `Lᵖ` for every finite Borel circle measure
and every finite exponent `p ≥ 1`. -/
theorem dense_toLp (μ : CircleMeasureData) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense ((ContinuousMap.toLp p μ.μ ℂ) '' (algebra : Set C(Circle, ℂ))) := by
  exact (ContinuousMap.toLp_denseRange ℂ μ.μ ℂ hp).dense_image
    (ContinuousMap.toLp p μ.μ ℂ).continuous dense_continuous

theorem dense_toL2 (μ : CircleMeasureData) :
    Dense ((ContinuousMap.toLp 2 μ.μ ℂ) '' (algebra : Set C(Circle, ℂ))) :=
  dense_toLp μ 2 (by norm_num)

end Chapter02.CircleLaurent
