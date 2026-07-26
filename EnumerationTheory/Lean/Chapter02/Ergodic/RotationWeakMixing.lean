import Chapter02.Spectral.WeakSpectrum

noncomputable section

open Classical MeasureTheory Filter

namespace Chapter02.RotationWeakMixing

universe u

lemma projectMap_of_measurePreserving {X : Type u} [MeasurableSpace X]
    (m : Measure X) (T : X → X) (hT : MeasurePreserving T m m) :
    Chapter01.IsMeasurePreservingMap
      {A : Set X | MeasurableSet A} m {A : Set X | MeasurableSet A} m T := by
  refine ⟨fun B hB => hT.measurable hB, ?_⟩
  intro B hB
  calc
    m (T ⁻¹' B) = (Measure.map T m) B :=
      (Measure.map_apply hT.measurable hB).symm
    _ = m B := by rw [hT.map_eq]

set_option maxHeartbeats 800000 in
theorem rotationNotWeakMixing : RotationNotWeakMixingStatement.{u} := by
  intro G _instGroup _instMetric _instCompact _instMeas _instBorel
    _instTopGroup _instNontrivial m hm htrans a hex hweak
  let M := compactGroupRotationSystem m a
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hm
  have hM : Chapter01.IsMeasurePreservingSystem M := ⟨hm, htrans a⟩
  have hinv : Chapter01.IsInvertibleMeasurePreservingMap
      M.𝓧 M.μ M.𝓧 M.μ M.T := by
    let S : G → G := fun x => a⁻¹ * x
    refine ⟨S, projectMap_of_measurePreserving m _ (htrans a),
      projectMap_of_measurePreserving m _ (htrans a⁻¹), ?_, ?_⟩
    · intro x
      simp [M, S, compactGroupRotationSystem]
    · intro x
      simp [M, S, compactGroupRotationSystem]
  have hcont : HasContinuousSpectrum M :=
    (WeakSpectrum.weakMixing_iff_continuousSpectrum M hM hinv).mp hweak
  obtain ⟨χ, hχnonconst⟩ := hex
  have hχLp : M.lpMember 2 χ.toFun := by
    apply (MeasureTheory.memLp_top_of_bound
      χ.continuous.aestronglyMeasurable 1 ?_).mono_exponent (by simp)
    exact Filter.Eventually.of_forall fun x => le_of_eq (χ.unit_norm x)
  have hχne : ¬ χ.toFun =ᵐ[M.μ] 0 := by
    intro hz
    apply hχnonconst
    exact ⟨0, hz⟩
  have heig : Eigenfunction M (χ.toFun a) χ.toFun := by
    refine ⟨hχLp, hχne, Filter.Eventually.of_forall ?_⟩
    intro x
    exact χ.map_mul a x
  have hone : χ.toFun a = 1 := hcont.1 (χ.toFun a) ⟨χ.toFun, heig⟩
  apply hχnonconst
  exact hcont.2 χ.toFun (by simpa [hone] using heig)

end Chapter02.RotationWeakMixing
