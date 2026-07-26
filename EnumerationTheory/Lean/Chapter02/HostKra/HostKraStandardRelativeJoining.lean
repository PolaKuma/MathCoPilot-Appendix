import Chapter02.HostKra.HostKraRelativeJoining
import Mathlib.Probability.Kernel.Condexp

open Classical Set MeasureTheory ProbabilityTheory

noncomputable section

namespace Chapter02.HostKraStandardRelativeJoining

universe u

open Chapter02.HostKraRelativeJoining

/-- The regular conditional-probability kernel over the invariant
sigma-algebra.  Standard Borelness is needed only at this stage. -/
def invariantCondExpKernel
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    @Kernel M.X M.X (invariantMeasurableSpace M) M.measurableSpace := by
  letI : IsProbabilityMeasure M.μ := hM.1
  exact @condExpKernel M.X M.measurableSpace inferInstance M.μ inferInstance
    (invariantMeasurableSpace M)

/-- The relative independent square over the invariant sigma-algebra:
integrate the fiberwise products `κₓ × κₓ` against the invariant trim of
the original probability measure. -/
def relativeJoiningMeasure
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Measure (M.X × M.X) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let κ := invariantCondExpKernel M hM
  let mI := invariantMeasurableSpace M
  let hm : mI ≤ M.measurableSpace := invariantMeasurableSpace_le M
  exact @Measure.bind M.X (M.X × M.X) mI
    (@Prod.instMeasurableSpace M.X M.X M.measurableSpace M.measurableSpace)
    (M.μ.trim hm) (fun x => (Kernel.prod κ κ) x)

theorem relativeJoiningMeasure_apply
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (s : Set (M.X × M.X)) (hs : MeasurableSet s) :
    relativeJoiningMeasure M hM s =
      ∫⁻ x, ((Kernel.prod (invariantCondExpKernel M hM)
        (invariantCondExpKernel M hM)) x) s
        ∂(M.μ.trim (invariantMeasurableSpace_le M)) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  simp only [relativeJoiningMeasure]
  change (@Measure.bind M.X (M.X × M.X)
      (invariantMeasurableSpace M)
      (@Prod.instMeasurableSpace M.X M.X M.measurableSpace M.measurableSpace)
      (M.μ.trim (invariantMeasurableSpace_le M))
      (fun x => (Kernel.prod (invariantCondExpKernel M hM)
        (invariantCondExpKernel M hM)) x)) s = _
  apply Measure.bind_apply hs
  exact (Kernel.measurable
    (Kernel.prod (invariantCondExpKernel M hM)
      (invariantCondExpKernel M hM))).aemeasurable

theorem relativeJoiningMeasure_apply_prod
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    relativeJoiningMeasure M hM (A ×ˢ B) =
      ∫⁻ x, (invariantCondExpKernel M hM x) A *
        (invariantCondExpKernel M hM x) B
        ∂(M.μ.trim (invariantMeasurableSpace_le M)) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : IsMarkovKernel (invariantCondExpKernel M hM) := by
    unfold invariantCondExpKernel
    infer_instance
  rw [relativeJoiningMeasure_apply M hM (A ×ˢ B) (hA.prod hB)]
  apply lintegral_congr
  intro x
  exact Kernel.prod_apply_prod

/-- On measurable rectangles, the kernel construction is exactly the
previously constructed real `L²` rectangle functional. -/
theorem relativeJoiningMeasure_apply_prod_toReal
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (relativeJoiningMeasure M hM (A ×ˢ B)).toReal =
      relativeRectangleMass M hM A B hA hB := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : IsMarkovKernel (invariantCondExpKernel M hM) := by
    unfold invariantCondExpKernel
    infer_instance
  let κ := invariantCondExpKernel M hM
  let mI := invariantMeasurableSpace M
  let hm : mI ≤ M.measurableSpace := invariantMeasurableSpace_le M
  have hκA : @Measurable M.X ENNReal mI inferInstance
      (fun x => κ x A) :=
    Kernel.measurable_coe κ hA
  have hκB : @Measurable M.X ENNReal mI inferInstance
      (fun x => κ x B) :=
    Kernel.measurable_coe κ hB
  have hκmul : @Measurable M.X ENNReal mI inferInstance
      (fun x => κ x A * κ x B) :=
    hκA.mul hκB
  have hκmul0 : @Measurable M.X ENNReal M.measurableSpace inferInstance
      (fun x => κ x A * κ x B) :=
    hκmul.mono hm le_rfl
  have hfinite : ∀ᵐ x ∂M.μ, κ x A * κ x B < (⊤ : ENNReal) := by
    filter_upwards with x
    exact ENNReal.mul_lt_top (measure_lt_top (κ x) A)
      (measure_lt_top (κ x) B)
  have hcondA :
      (fun x => (κ x).real A) =ᵐ[M.μ]
        condExp mI M.μ (indicatorReal A) := by
    simpa only [κ, mI, hm, indicatorReal, Measure.real_def] using
      (@condExpKernel_ae_eq_condExp M.X mI M.measurableSpace inferInstance
        M.μ inferInstance hm A hA)
  have hcondB :
      (fun x => (κ x).real B) =ᵐ[M.μ]
        condExp mI M.μ (indicatorReal B) := by
    simpa only [κ, mI, hm, indicatorReal, Measure.real_def] using
      (@condExpKernel_ae_eq_condExp M.X mI M.measurableSpace inferInstance
        M.μ inferInstance hm B hB)
  rw [relativeJoiningMeasure_apply_prod M hM A B hA hB]
  rw [lintegral_trim hm hκmul]
  rw [relativeRectangleMass_eq_integral_condExp]
  calc
    (∫⁻ x, κ x A * κ x B ∂M.μ).toReal =
        ∫ x, (κ x A * κ x B).toReal ∂M.μ :=
      (integral_toReal (μ := M.μ) hκmul0.aemeasurable hfinite).symm
    _ = ∫ x,
        condExp mI M.μ (indicatorReal A) x *
        condExp mI M.μ (indicatorReal B) x ∂M.μ := by
      apply integral_congr_ae
      filter_upwards [hcondA, hcondB] with x hxA hxB
      rw [ENNReal.toReal_mul, show (κ x A).toReal = (κ x).real A by rfl,
        show (κ x B).toReal = (κ x).real B by rfl, hxA, hxB]

theorem relativeJoiningMeasure_univ
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    relativeJoiningMeasure M hM Set.univ = 1 := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : IsMarkovKernel (invariantCondExpKernel M hM) := by
    unfold invariantCondExpKernel
    infer_instance
  rw [show (Set.univ : Set (M.X × M.X)) =
      (Set.univ : Set M.X) ×ˢ Set.univ by ext x; simp]
  rw [relativeJoiningMeasure_apply_prod M hM Set.univ Set.univ
    MeasurableSet.univ MeasurableSet.univ]
  simp only [measure_univ, one_mul, lintegral_one]
  exact trim_measurableSet_eq (invariantMeasurableSpace_le M)
    MeasurableSet.univ |>.trans hM.1.measure_univ

instance relativeJoiningMeasure_isProbabilityMeasure
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    IsProbabilityMeasure (relativeJoiningMeasure M hM) :=
  ⟨relativeJoiningMeasure_univ M hM⟩

/-- Exchangeability of the two copies in a relatively independent
joining.  This is the first cube-symmetry generator. -/
theorem relativeJoining_swap_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasurePreserving
      (fun p : M.X × M.X ↦ (p.2, p.1))
      (relativeJoiningMeasure M hM)
      (relativeJoiningMeasure M hM) := by
  let σ : M.X × M.X → M.X × M.X := fun p ↦ (p.2, p.1)
  have hσ : Measurable σ := Measurable.prod measurable_snd measurable_fst
  refine ⟨hσ, ?_⟩
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply hσ (hA.prod hB)]
  have hpre : σ ⁻¹' (A ×ˢ B) = B ×ˢ A := by
    ext p
    simp only [σ, Set.mem_preimage, Set.mem_prod]
    constructor <;> intro hp <;> exact ⟨hp.2, hp.1⟩
  rw [hpre]
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top (relativeJoiningMeasure M hM) (B ×ˢ A))
    (measure_ne_top (relativeJoiningMeasure M hM) (A ×ˢ B))).mp
  rw [relativeJoiningMeasure_apply_prod_toReal M hM B A hB hA,
    relativeJoiningMeasure_apply_prod_toReal M hM A B hA hB]
  exact relativeRectangleMass_symm M hM B A hB hA

/-- The diagonal action on the relative independent square. -/
def relativeJoiningTransform (M : System.{u}) : M.X × M.X → M.X × M.X :=
  fun p ↦ (M.T p.1, M.T p.2)

theorem relativeJoiningTransform_measurable
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    Measurable (relativeJoiningTransform M) :=
  Measurable.prod (hM.2.measurable.comp measurable_fst)
    (hM.2.measurable.comp measurable_snd)

theorem relativeJoiningTransform_preimage_prod
    (M : System.{u}) (A B : Set M.X) :
    relativeJoiningTransform M ⁻¹' (A ×ˢ B) =
      (M.T ⁻¹' A) ×ˢ (M.T ⁻¹' B) := by
  ext p
  rfl

/-- The diagonal action preserves the relative independent square on
measurable rectangles. -/
theorem relativeJoiningMeasure_preimage_prod
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    relativeJoiningMeasure M hM
        (relativeJoiningTransform M ⁻¹' (A ×ˢ B)) =
      relativeJoiningMeasure M hM (A ×ˢ B) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  rw [relativeJoiningTransform_preimage_prod]
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top (relativeJoiningMeasure M hM)
      ((M.T ⁻¹' A) ×ˢ (M.T ⁻¹' B)))
    (measure_ne_top (relativeJoiningMeasure M hM) (A ×ˢ B))).mp
  rw [relativeJoiningMeasure_apply_prod_toReal M hM
      (M.T ⁻¹' A) (M.T ⁻¹' B)
      (hA.preimage hM.2.measurable) (hB.preimage hM.2.measurable),
    relativeJoiningMeasure_apply_prod_toReal M hM A B hA hB]
  exact relativeRectangleMass_preimage M hM A B hA hB

/-- The diagonal action preserves the full relative-joining measure. -/
theorem relativeJoiningTransform_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasurePreserving (relativeJoiningTransform M)
      (relativeJoiningMeasure M hM) (relativeJoiningMeasure M hM) := by
  refine ⟨relativeJoiningTransform_measurable M hM, ?_⟩
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply (relativeJoiningTransform_measurable M hM)
    (hA.prod hB)]
  exact relativeJoiningMeasure_preimage_prod M hM A B hA hB

/-- The first genuine Host--Kra relative square, packaged as a system so
that the relative-joining construction can be iterated. -/
def relativeJoiningSystem
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) : System.{u} where
  X := M.X × M.X
  measurableSpace := inferInstance
  μ := relativeJoiningMeasure M hM
  T := relativeJoiningTransform M

theorem relativeJoiningSystem_mps
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter01.IsMeasurePreservingSystem (relativeJoiningSystem M hM) := by
  constructor
  · exact relativeJoiningMeasure_isProbabilityMeasure M hM
  · exact relativeJoiningTransform_measurePreserving M hM

instance relativeJoiningSystem_standardBorel
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    StandardBorelSpace (relativeJoiningSystem M hM).X := by
  change StandardBorelSpace (M.X × M.X)
  infer_instance

/-- The one-dimensional Host--Kra cube system `X^[1]`. -/
abbrev relativeCubeSystemOne
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) : System.{u} :=
  relativeJoiningSystem M hM

theorem relativeCubeSystemOne_mps
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter01.IsMeasurePreservingSystem (relativeCubeSystemOne M hM) :=
  relativeJoiningSystem_mps M hM

/-- The twice-iterated relative joining `X^[2]`, whose underlying points
have four coordinates. -/
abbrev relativeCubeSystemTwo
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) : System.{u} :=
  relativeJoiningSystem (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM)

theorem relativeCubeSystemTwo_mps
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter01.IsMeasurePreservingSystem (relativeCubeSystemTwo M hM) :=
  relativeJoiningSystem_mps (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM)

/-- The three-dimensional Host--Kra cube system `X^[3]`, obtained by
relative independent joining of `X^[2]` over its invariant sigma-algebra.
Its underlying points have eight coordinates. -/
abbrev relativeCubeSystemThree
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) : System.{u} :=
  relativeJoiningSystem (relativeCubeSystemTwo M hM)
    (relativeCubeSystemTwo_mps M hM)

theorem relativeCubeSystemThree_mps
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter01.IsMeasurePreservingSystem (relativeCubeSystemThree M hM) :=
  relativeJoiningSystem_mps (relativeCubeSystemTwo M hM)
    (relativeCubeSystemTwo_mps M hM)

end Chapter02.HostKraStandardRelativeJoining
