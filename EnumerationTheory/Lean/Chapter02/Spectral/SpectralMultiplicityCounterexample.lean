import Chapter02.Section05

noncomputable section

open Classical Filter

namespace Chapter02
namespace SpectralMultiplicityCounterexample

universe u

abbrev TwoHilbert : Type u := ULift.{u} (EuclideanSpace ℂ (Fin 2))

noncomputable local instance : Inner ℂ TwoHilbert :=
  ⟨fun x y => @inner ℂ (EuclideanSpace ℂ (Fin 2)) _ x.down y.down⟩

noncomputable local instance : InnerProductSpace ℂ TwoHilbert :=
  @InnerProductSpace.mk ℂ TwoHilbert _ _ _ _
    (by intro x; exact InnerProductSpace.norm_sq_eq_re_inner x.down)
    (by intro x y; exact inner_conj_symm x.down y.down)
    (by intro x y z; exact inner_add_left x.down y.down z.down)
    (by intro x y r; exact inner_smul_left x.down y.down r)

noncomputable def identityOperator : HilbertOperatorData.{u} where
  H := TwoHilbert
  normedAddCommGroup := inferInstance
  innerProductSpace := inferInstance
  completeSpace := inferInstance
  U := ContinuousLinearMap.id ℂ _

noncomputable def firstBasis : TwoHilbert :=
  ULift.up (EuclideanSpace.single 0 1)

noncomputable def secondBasis : TwoHilbert :=
  ULift.up (EuclideanSpace.single 1 1)

lemma identityOperator_unitary :
    IsUnitary (identityOperator : HilbertOperatorData.{u}) := by
  constructor
  · exact Function.surjective_id
  · intro x
    rfl

lemma hyperplane_reducing (w : TwoHilbert) :
    IsClosedReducingSubspace (identityOperator : HilbertOperatorData.{u})
      {v | @inner ℂ TwoHilbert _ w v = 0} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · intro x hx y hy a b
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [inner_add_right, inner_smul_right, inner_smul_right, hx, hy]
    simp
  · intro xseq hx x hlim
    simp only [Set.mem_setOf_eq] at hx ⊢
    have ht : Tendsto (fun n => @inner ℂ TwoHilbert _ w (xseq n)) atTop
        (nhds (@inner ℂ TwoHilbert _ w x)) :=
      tendsto_const_nhds.inner (𝕜 := ℂ) hlim
    have hz : Tendsto (fun n => @inner ℂ TwoHilbert _ w (xseq n)) atTop
        (nhds 0) := by
      simp [hx]
    exact tendsto_nhds_unique ht hz
  · intro x
    rfl

lemma basis_cyclic_subspaces_orthogonal :
    OrthogonalCyclicSubspaces (identityOperator : HilbertOperatorData.{u})
      (firstBasis : (identityOperator : HilbertOperatorData.{u}).H)
      (secondBasis : (identityOperator : HilbertOperatorData.{u}).H) := by
  intro a b ha hb
  have hxy : @inner ℂ (identityOperator : HilbertOperatorData.{u}).H _
      (secondBasis : (identityOperator : HilbertOperatorData.{u}).H)
      (firstBasis : (identityOperator : HilbertOperatorData.{u}).H) = 0 := by
    change @inner ℂ (EuclideanSpace ℂ (Fin 2)) _
      (EuclideanSpace.single 1 1) (EuclideanSpace.single 0 1) = 0
    rw [EuclideanSpace.inner_single_left]
    simp
  have hya : @inner ℂ TwoHilbert _ secondBasis a = 0 :=
    ha _ (hyperplane_reducing secondBasis) hxy
  have hay : @inner ℂ TwoHilbert _ a secondBasis = 0 := by
    rw [← inner_conj_symm]
    simp [hya]
  exact hb _ (hyperplane_reducing a) hay

noncomputable def pointMeasure : CircleMeasureData where
  μ := MeasureTheory.Measure.dirac 1
  isFinite := inferInstance

private lemma basis_spectral (i : Fin 2) :
    HasSpectralMeasure (identityOperator : HilbertOperatorData.{u})
      (ULift.up (EuclideanSpace.single i 1) :
        (identityOperator : HilbertOperatorData.{u}).H) pointMeasure := by
  intro n
  rw [circleFourierCoefficient, pointMeasure, MeasureTheory.integral_dirac]
  change (1 : ℂ) ^ (n : ℤ) = @inner ℂ TwoHilbert _
      (ULift.up (EuclideanSpace.single i 1))
    (((identityOperator : HilbertOperatorData.{u}).U^[n])
      (ULift.up (EuclideanSpace.single i 1)))
  rw [one_zpow]
  change 1 = @inner ℂ TwoHilbert _
      (ULift.up (EuclideanSpace.single i 1))
    (((fun x : TwoHilbert => x)^[n])
      (ULift.up (EuclideanSpace.single i 1)))
  have hid : ((fun x : TwoHilbert => x)^[n])
      (ULift.up (EuclideanSpace.single i 1)) =
        ULift.up (EuclideanSpace.single i 1) := by
    induction n with
    | zero => rfl
    | succ n ih => simpa [Function.iterate_succ_apply] using ih
  rw [hid]
  change 1 = @inner ℂ (EuclideanSpace ℂ (Fin 2)) _
    (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
  rw [EuclideanSpace.inner_single_left]
  simp

lemma firstBasis_spectral :
    HasSpectralMeasure (identityOperator : HilbertOperatorData.{u})
      (firstBasis : (identityOperator : HilbertOperatorData.{u}).H) pointMeasure := by
  exact basis_spectral 0

lemma secondBasis_spectral :
    HasSpectralMeasure (identityOperator : HilbertOperatorData.{u})
      (secondBasis : (identityOperator : HilbertOperatorData.{u}).H) pointMeasure := by
  exact basis_spectral 1

lemma pointMeasure_not_singular_self :
    ¬ MeasureTheory.Measure.MutuallySingular pointMeasure.μ pointMeasure.μ := by
  rintro ⟨s, hs, hzero, hcomp⟩
  have hnot : (1 : Circle) ∉ s := by
    intro hmem
    have : pointMeasure.μ s = 1 := by
      simp [pointMeasure, hs, hmem]
    simp [this] at hzero
  have hmem : (1 : Circle) ∈ s := by
    by_contra h
    have hc : (1 : Circle) ∈ sᶜ := h
    have : pointMeasure.μ sᶜ = 1 := by
      simp [pointMeasure, hs.compl, hc]
    simp [this] at hcomp
  exact hnot hmem

theorem counterexample : OrthogonalCyclicSubspacesCounterexample.{u} := by
  exact ⟨identityOperator, firstBasis, secondBasis, identityOperator_unitary,
    basis_cyclic_subspaces_orthogonal, pointMeasure, pointMeasure,
    firstBasis_spectral, secondBasis_spectral, pointMeasure_not_singular_self⟩

end SpectralMultiplicityCounterexample
end Chapter02
