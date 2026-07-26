import Chapter02.HostKra.HostKraStandardRelativeJoining

open Classical Set MeasureTheory

noncomputable section

namespace Chapter02.HostKraCubeFactors

universe u

open HostKraRelativeJoining HostKraStandardRelativeJoining

/-- The first marginal of the relative independent square is the original
measure. -/
theorem relativeJoiningMeasure_preimage_fst
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    relativeJoiningMeasure M hM (Prod.fst ⁻¹' A) = M.μ A := by
  letI : IsProbabilityMeasure M.μ := hM.1
  rw [show Prod.fst ⁻¹' A = A ×ˢ Set.univ by ext p; simp]
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top (relativeJoiningMeasure M hM) (A ×ˢ Set.univ))
    (measure_ne_top M.μ A)).mp
  rw [relativeJoiningMeasure_apply_prod_toReal M hM A Set.univ hA
      MeasurableSet.univ,
    relativeRectangleMass_univ_right]
  rfl

/-- The second marginal of the relative independent square is the original
measure. -/
theorem relativeJoiningMeasure_preimage_snd
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    relativeJoiningMeasure M hM (Prod.snd ⁻¹' A) = M.μ A := by
  letI : IsProbabilityMeasure M.μ := hM.1
  rw [show Prod.snd ⁻¹' A = Set.univ ×ˢ A by ext p; simp]
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top (relativeJoiningMeasure M hM) (Set.univ ×ˢ A))
    (measure_ne_top M.μ A)).mp
  rw [relativeJoiningMeasure_apply_prod_toReal M hM Set.univ A
      MeasurableSet.univ hA,
    relativeRectangleMass_univ_left]
  rfl

theorem relativeJoining_fst_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasurePreserving Prod.fst
      (relativeJoiningMeasure M hM) M.μ := by
  refine ⟨measurable_fst, ?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_fst hA]
  exact relativeJoiningMeasure_preimage_fst M hM A hA

theorem relativeJoining_snd_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasurePreserving Prod.snd
      (relativeJoiningMeasure M hM) M.μ := by
  refine ⟨measurable_snd, ?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_snd hA]
  exact relativeJoiningMeasure_preimage_snd M hM A hA

theorem relativeJoining_fst_intertwines (M : System.{u}) :
    Prod.fst ∘ relativeJoiningTransform M = M.T ∘ Prod.fst :=
  rfl

theorem relativeJoining_snd_intertwines (M : System.{u}) :
    Prod.snd ∘ relativeJoiningTransform M = M.T ∘ Prod.snd :=
  rfl

private theorem factorMap_of_measurePreserving_intertwine
    {E F : System.{u}}
    (hE : Chapter01.IsMeasurePreservingSystem E)
    (hF : Chapter01.IsMeasurePreservingSystem F)
    (π : E.X → F.X)
    (hπ : MeasurePreserving π E.μ F.μ)
    (hinter : π ∘ E.T = F.T ∘ π) :
    Chapter01.IsFactorMap E F π := by
  refine ⟨hE, hF, Set.univ, Set.univ, hE.1.measure_univ,
    hF.1.measure_univ, (fun x _ ↦ Set.mem_univ (E.T x)),
    (fun y _ ↦ Set.mem_univ (F.T y)), ?_, ?_⟩
  · refine ⟨MeasurableSet.univ, MeasurableSet.univ, hE.1.measure_univ,
      hF.1.measure_univ, (fun x _ ↦ Set.mem_univ (π x)), ?_⟩
    intro B hB
    have hBm : MeasurableSet B := hB
    constructor
    · change MeasurableSet (Set.univ ∩ π ⁻¹' (B ∩ Set.univ))
      simpa using hBm.preimage hπ.measurable
    · change E.μ (Set.univ ∩ π ⁻¹' (B ∩ Set.univ)) =
        F.μ (B ∩ Set.univ)
      simpa only [Set.inter_univ, Set.univ_inter] using
        hπ.measure_preimage hBm.nullMeasurableSet
  · intro x _
    exact congrFun hinter x

/-- Either coordinate projection is a factor map from the relative joining
system back to its predecessor. -/
theorem relativeJoining_fst_factorMap
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter01.IsFactorMap (relativeJoiningSystem M hM) M Prod.fst :=
  factorMap_of_measurePreserving_intertwine
    (relativeJoiningSystem_mps M hM) hM Prod.fst
    (relativeJoining_fst_measurePreserving M hM)
    (relativeJoining_fst_intertwines M)

theorem relativeJoining_snd_factorMap
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter01.IsFactorMap (relativeJoiningSystem M hM) M Prod.snd :=
  factorMap_of_measurePreserving_intertwine
    (relativeJoiningSystem_mps M hM) hM Prod.snd
    (relativeJoining_snd_measurePreserving M hM)
    (relativeJoining_snd_intertwines M)

/-- The two faces of `X^[2]` project as factors onto `X^[1]`. -/
theorem relativeCubeSystemTwo_fst_factorMap
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter01.IsFactorMap
      (relativeCubeSystemTwo M hM) (relativeCubeSystemOne M hM) Prod.fst :=
  relativeJoining_fst_factorMap
    (relativeCubeSystemOne M hM) (relativeCubeSystemOne_mps M hM)

theorem relativeCubeSystemTwo_snd_factorMap
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter01.IsFactorMap
      (relativeCubeSystemTwo M hM) (relativeCubeSystemOne M hM) Prod.snd :=
  relativeJoining_snd_factorMap
    (relativeCubeSystemOne M hM) (relativeCubeSystemOne_mps M hM)

/-- The two faces of `X^[3]` project as factors onto `X^[2]`. -/
theorem relativeCubeSystemThree_fst_factorMap
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter01.IsFactorMap
      (relativeCubeSystemThree M hM) (relativeCubeSystemTwo M hM) Prod.fst :=
  relativeJoining_fst_factorMap
    (relativeCubeSystemTwo M hM) (relativeCubeSystemTwo_mps M hM)

theorem relativeCubeSystemThree_snd_factorMap
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter01.IsFactorMap
      (relativeCubeSystemThree M hM) (relativeCubeSystemTwo M hM) Prod.snd :=
  relativeJoining_snd_factorMap
    (relativeCubeSystemTwo M hM) (relativeCubeSystemTwo_mps M hM)

end Chapter02.HostKraCubeFactors
