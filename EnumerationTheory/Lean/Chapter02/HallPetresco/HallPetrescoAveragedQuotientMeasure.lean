import Chapter02.HallPetresco.HallPetrescoReducedHausdorff
import Chapter02.HallPetresco.HallPetrescoQuotientCentralLift

open Classical MeasureTheory
open scoped ENNReal

noncomputable section

namespace Chapter02.HallPetrescoAveragedQuotientMeasure

open Chapter02.HallPetrescoTwoStepGroup
open Chapter02.HallPetrescoNormalForm
open Chapter02.HallPetrescoLattice
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoAveragingSubgroup
open Chapter02.HallPetrescoReducedHausdorff
open Chapter02.HallPetrescoQuotientCentralLift

universe u v

/-- A measurable skew product whose fiber maps are pointwise left
translations preserves a product measure.  No measurable choice of the
translation parameter is needed: Tonelli reduces the statement to the
Haar invariance of each individual fiber. -/
theorem lintegral_prod_skew_mul
    {A G : Type*}
    [MeasurableSpace A] [MeasurableSpace G]
    [Group G] [MeasurableMul G]
    (μ : Measure A) (m : Measure G)
    [SFinite μ] [SFinite m] [m.IsMulLeftInvariant]
    (R : A → A) (hR : MeasurePreserving R μ μ)
    (f f' : A × G → ℝ≥0∞)
    (hf : Measurable f) (hf' : Measurable f')
    (hskew : ∀ x : A, ∃ t : G, ∀ z : G,
      f' (x, z) = f (R x, t * z)) :
    (∫⁻ p, f' p ∂(μ.prod m)) = ∫⁻ p, f p ∂(μ.prod m) := by
  have hinner (x : A) :
      (∫⁻ z, f' (x, z) ∂m) = ∫⁻ z, f (R x, z) ∂m := by
    obtain ⟨t, ht⟩ := hskew x
    calc
      (∫⁻ z, f' (x, z) ∂m) = ∫⁻ z, f (R x, t * z) ∂m := by
        apply lintegral_congr
        exact ht
      _ = ∫⁻ z, f (R x, z) ∂m := by
        let T : G → G := fun z ↦ t * z
        let q : G → ℝ≥0∞ := fun z ↦ f (R x, z)
        have hT : MeasurePreserving T m m :=
          measurePreserving_mul_left m t
        have hq : Measurable q :=
          hf.comp (measurable_const.prodMk measurable_id)
        calc
          (∫⁻ z, f (R x, t * z) ∂m) = ∫⁻ z, q (T z) ∂m := rfl
          _ = ∫⁻ z, q z ∂Measure.map T m :=
            (lintegral_map hq hT.measurable).symm
          _ = ∫⁻ z, q z ∂m := by rw [hT.map_eq]
  let q : A → ℝ≥0∞ := fun x ↦ ∫⁻ z, f (x, z) ∂m
  have hq : Measurable q := hf.lintegral_prod_right'
  calc
    (∫⁻ p, f' p ∂(μ.prod m)) = ∫⁻ x, ∫⁻ z, f' (x, z) ∂m ∂μ :=
      lintegral_prod _ hf'.aemeasurable
    _ = ∫⁻ x, ∫⁻ z, f (R x, z) ∂m ∂μ := by
      apply lintegral_congr
      exact hinner
    _ = ∫⁻ x, q (R x) ∂μ := rfl
    _ = ∫⁻ x, q x ∂Measure.map R μ :=
      (lintegral_map hq hR.measurable).symm
    _ = ∫⁻ x, q x ∂μ := by rw [hR.map_eq]
    _ = ∫⁻ p, f p ∂(μ.prod m) :=
      (lintegral_prod _ hf.aemeasurable).symm

/-- Translate the compact `Ḡ`-orbit of the identity coset by a
Hall--Petresco group element. -/
def averagedQuotientPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (s : subgroup N)
    (p : X × (Fin N.torusDim → Circle)) :
    Quotient N P.lattice :=
  s • averagingOrbitPoint N P p

theorem continuous_averagedQuotientPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Continuous (fun z : subgroup N ×
        (X × (Fin N.torusDim → Circle)) ↦
      averagedQuotientPoint N P z.1 z.2) := by
  exact continuous_smul.comp
    (continuous_fst.prodMk
      ((continuous_averagingOrbitPoint N P).comp continuous_snd))

theorem continuous_averagedQuotientPoint_fixed
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (s : subgroup N) :
    Continuous (averagedQuotientPoint N P s) := by
  exact (continuous_averagedQuotientPoint N P).comp
    (continuous_const.prodMk continuous_id)

/-- The compact parameterization is equivariant for the explicit averaging
group law. -/
theorem averagingElement_smul_averagingOrbitPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (h : H) (z : Fin N.torusDim → Circle)
    (p : X × (Fin N.torusDim → Circle)) :
    averagingElement N (h, z) • averagingOrbitPoint N P p =
      averagingOrbitPoint N P
        (N.ambientAction.toMulAction.smul h p.1, z * p.2) := by
  letI := configurationAction N
  apply injective_quotientConfiguration N P
  rw [quotientConfiguration_smul]
  change
    (averagingElement N (h, z)) •
        quotientConfiguration N P (averagingOrbitPoint N P p) =
      quotientConfiguration N P
        (averagingOrbitPoint N P
          (N.ambientAction.toMulAction.smul h p.1, z * p.2))
  unfold averagingOrbitPoint
  rw [quotientConfiguration_smul, quotientConfiguration_smul,
    quotientConfiguration_quotientDiagonalPoint,
    quotientConfiguration_quotientDiagonalPoint]
  funext j
  change
    N.ambientAction.toMulAction.smul
        (h * N.centralHom z ^ j.val)
        (N.ambientAction.toMulAction.smul
          (N.centralHom p.2 ^ j.val) p.1) =
      N.ambientAction.toMulAction.smul
        (N.centralHom (z * p.2) ^ j.val)
        (N.ambientAction.toMulAction.smul h p.1)
  have hcomm :
      Commute (N.centralHom z) (N.centralHom p.2) :=
    (Subgroup.mem_center_iff.mp
      (N.centralHom_mem_center z) (N.centralHom p.2)).symm
  have hcenter :
      N.centralHom z ^ j.val * N.centralHom p.2 ^ j.val ∈
        Subgroup.center H :=
    (Subgroup.center H).mul_mem
      ((Subgroup.center H).pow_mem (N.centralHom_mem_center z) _)
      ((Subgroup.center H).pow_mem (N.centralHom_mem_center p.2) _)
  calc
    N.ambientAction.toMulAction.smul
        (h * N.centralHom z ^ j.val)
        (N.ambientAction.toMulAction.smul
          (N.centralHom p.2 ^ j.val) p.1) =
      N.ambientAction.toMulAction.smul
        ((h * N.centralHom z ^ j.val) *
          N.centralHom p.2 ^ j.val) p.1 := by
            symm
            exact N.ambientAction.toMulAction.mul_smul _ _ _
    _ = N.ambientAction.toMulAction.smul
        ((N.centralHom z ^ j.val *
          N.centralHom p.2 ^ j.val) * h) p.1 := by
      congr 1
      rw [(Subgroup.mem_center_iff.mp hcenter h).symm]
      group
    _ = N.ambientAction.toMulAction.smul
        (N.centralHom (z * p.2) ^ j.val * h) p.1 := by
      rw [map_mul, hcomm.mul_pow]
    _ = N.ambientAction.toMulAction.smul
        (N.centralHom (z * p.2) ^ j.val)
        (N.ambientAction.toMulAction.smul h p.1) :=
      N.ambientAction.toMulAction.mul_smul _ _ _

/-- Average a translated `Ḡ`-fiber using the invariant probability
measure `μ × Haar`. -/
def averagedQuotientMeasure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m]
    (s : subgroup N) :
    ProbabilityMeasure (Quotient N P.lattice) :=
  ProbabilityMeasure.map
    (⟨μ.prod m, inferInstance⟩ :
      ProbabilityMeasure (X × (Fin N.torusDim → Circle)))
    (continuous_averagedQuotientPoint_fixed N P s).measurable.aemeasurable

/-- Averaged fiber measures vary continuously with the Hall--Petresco group
representative. -/
theorem continuous_averagedQuotientMeasure
    {H : Type u} {X : Type v}
    [Group H] [MetricSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [CompactSpace (Quotient N P.lattice)]
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] :
    Continuous (averagedQuotientMeasure N P m) := by
  letI : LocallyCompactSpace (subgroup N) :=
    (show IsClosed (subgroup N : Set (Vertex → H)) from
      inferInstance).locallyCompactSpace
  letI : T2Space (Quotient N P.lattice) :=
    quotientT2Space N P
  rw [continuous_iff_continuousAt]
  intro s
  change Filter.Tendsto (averagedQuotientMeasure N P m)
    (nhds s) (nhds (averagedQuotientMeasure N P m s))
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro F
  have hjoint :
      Continuous (fun z : subgroup N ×
          (X × (Fin N.torusDim → Circle)) ↦
        F (averagedQuotientPoint N P z.1 z.2)) :=
    F.continuous.comp (continuous_averagedQuotientPoint N P)
  have hint :
      Continuous (fun s : subgroup N ↦
        ∫ p, F (averagedQuotientPoint N P s p) ∂(μ.prod m)) := by
    have h :=
      continuous_parametric_integral_of_continuous
        (μ := μ.prod m)
        (f := fun s : subgroup N ↦
          fun p : X × (Fin N.torusDim → Circle) ↦
            F (averagedQuotientPoint N P s p))
        hjoint isCompact_univ
    simpa only [Measure.restrict_univ] using h
  have hmap (t : subgroup N) :
      (∫ q, F q ∂(averagedQuotientMeasure N P m t :
          ProbabilityMeasure (Quotient N P.lattice))) =
        ∫ p, F (averagedQuotientPoint N P t p) ∂(μ.prod m) := by
    rw [averagedQuotientMeasure, ProbabilityMeasure.toMeasure_map]
    exact integral_map
      (continuous_averagedQuotientPoint_fixed N P t).measurable.aemeasurable
      F.continuous.aestronglyMeasurable
  simpa only [hmap] using hint.continuousAt

/-- Left translation of a Hall representative becomes pushforward of its
averaged fiber measure. -/
theorem averagedQuotientMeasure_mul
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m]
    (t s : subgroup N) :
    averagedQuotientMeasure N P m (t * s) =
      (averagedQuotientMeasure N P m s).map
        (continuous_const_smul t).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [averagedQuotientMeasure, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map
    (continuous_const_smul t).measurable
    (continuous_averagedQuotientPoint_fixed N P s).measurable]
  congr 1
  funext p
  simpa [averagedQuotientPoint, Function.comp_apply] using
    (mul_smul t s (averagingOrbitPoint N P p))

/-- Right multiplication of a representative by `Ḡ` does not change its
averaged fiber measure. -/
theorem averagedQuotientMeasure_mul_averagingElement
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (s : subgroup N) (h : H) (z : Fin N.torusDim → Circle) :
    averagedQuotientMeasure N P m
        (s * averagingElement N (h, z)) =
      averagedQuotientMeasure N P m s := by
  let R : X × (Fin N.torusDim → Circle) →
      X × (Fin N.torusDim → Circle) :=
    fun p ↦
      (N.ambientAction.toMulAction.smul h p.1, z * p.2)
  have hR : MeasurePreserving R (μ.prod m) (μ.prod m) := by
    simpa [R, Prod.map] using
      MeasurePreserving.prod
        (N.ambientAction.measurePreserving_smul h)
        (measurePreserving_mul_left m z)
  apply ProbabilityMeasure.toMeasure_injective
  simp only [averagedQuotientMeasure, ProbabilityMeasure.toMeasure_map]
  calc
    Measure.map
        (averagedQuotientPoint N P
          (s * averagingElement N (h, z))) (μ.prod m) =
      Measure.map (averagedQuotientPoint N P s ∘ R) (μ.prod m) := by
        apply Measure.map_congr
        exact Filter.Eventually.of_forall fun p ↦ by
          simp only [averagedQuotientPoint, Function.comp_apply]
          rw [mul_smul,
            averagingElement_smul_averagingOrbitPoint N P h z p]
    _ = Measure.map (averagedQuotientPoint N P s)
          (Measure.map R (μ.prod m)) := by
      rw [Measure.map_map
        (continuous_averagedQuotientPoint_fixed N P s).measurable
        hR.measurable]
    _ = Measure.map (averagedQuotientPoint N P s) (μ.prod m) := by
      rw [hR.map_eq]

/-- The preceding invariance holds for every element of the actual closed
averaging subgroup. -/
theorem averagedQuotientMeasure_mul_mem_averagingNormalSubgroup
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (s b : subgroup N) (hb : b ∈ averagingNormalSubgroup N) :
    averagedQuotientMeasure N P m (s * b) =
      averagedQuotientMeasure N P m s := by
  rw [← explicitAveragingSubgroup_eq_averagingNormalSubgroup N] at hb
  change b ∈ (averagingHom N).range at hb
  rcases hb with ⟨⟨h, z⟩, rfl⟩
  exact averagedQuotientMeasure_mul_averagingElement N P m s h z

/-- A lattice element conjugates the compact averaging orbit by a
measure-preserving skew translation of its `X × 𝕋ᵈ` parameters.  The torus
translation may depend on `x`, but is uniform in the Haar variable. -/
theorem exists_lattice_smul_averagingOrbitPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (l : subgroup N) (hl : l ∈ subgroupLattice N P.lattice) :
    ∃ k : H, k ∈ P.lattice ∧
      ∀ x : X, ∃ t : Fin N.torusDim → Circle,
          ∀ z : Fin N.torusDim → Circle,
            l • averagingOrbitPoint N P (x, z) =
              averagingOrbitPoint N P
                (N.ambientAction.toMulAction.smul k x, t * z) := by
  have hlNormalForm :
      ((l : subgroup N) : Vertex → H) ∈ normalFormSubgroup N := by
    rw [← subgroup_eq_normalFormSubgroup N]
    exact l.property
  rcases hlNormalForm with ⟨⟨⟨k, a⟩, w⟩, hlNormal'⟩
  have hlNormal :
      ((l : subgroup N) : Vertex → H) =
        hallTuple N ((k, a), w) :=
    hlNormal'.symm
  have hk : k ∈ P.lattice := by
    have hl0 := hl (0 : Vertex)
    change (((l : subgroup N) : Vertex → H) 0) ∈ P.lattice at hl0
    rw [hlNormal, hallTuple_apply] at hl0
    simpa using hl0
  refine ⟨k, hk, ?_⟩
  intro x
  obtain ⟨g, hg⟩ :=
    N.transitive_ambientAction (quotientBasePoint N P) x
  have hx :
      x = P.toQuotient.symm
        (QuotientGroup.mk g : H ⧸ P.lattice) := by
    apply P.toQuotient.injective
    rw [Homeomorph.apply_symm_apply, ← hg, P.equivariant]
    simp [quotientBasePoint]
  obtain ⟨k', a', w', t, hlNormal', ht, hconj⟩ :=
    exists_conjugate_averagingElement N l g
  have hkk : k' = k := by
    have heq : hallTuple N ((k', a'), w') =
        hallTuple N ((k, a), w) := by
      rw [← hlNormal', ← hlNormal]
    have := congrArg extractedBase heq
    simpa using this
  subst k'
  refine ⟨t, ?_⟩
  intro z
  have hkx :
      N.ambientAction.toMulAction.smul k x =
        P.toQuotient.symm
          (QuotientGroup.mk (k * g * k⁻¹) : H ⧸ P.lattice) := by
    apply P.toQuotient.injective
    rw [Homeomorph.apply_symm_apply, P.equivariant, hx,
      Homeomorph.apply_symm_apply]
    change
      QuotientGroup.mk (k * g) =
        QuotientGroup.mk (k * g * k⁻¹)
    apply QuotientGroup.eq.mpr
    have heq :
        (k * g)⁻¹ * (k * g * k⁻¹) = k⁻¹ := by
      group
    rw [heq]
    exact P.lattice.inv_mem hk
  rw [hkx, hx, averagingOrbitPoint_representative,
    averagingOrbitPoint_representative]
  change
    l • (QuotientGroup.mk (averagingElement N (g, z)) :
      Quotient N P.lattice) =
      (QuotientGroup.mk
        (averagingElement N (k * g * k⁻¹, t * z)) :
          Quotient N P.lattice)
  change
    QuotientGroup.mk (l * averagingElement N (g, z)) =
      QuotientGroup.mk
        (averagingElement N (k * g * k⁻¹, t * z))
  have hmul :
      l * averagingElement N (g, z) =
        averagingElement N (k * g * k⁻¹, t * z) * l := by
    have hz := hconj z
    calc
      l * averagingElement N (g, z) =
          (l * averagingElement N (g, z) * l⁻¹) * l := by
            group
      _ = averagingElement N (k * g * k⁻¹, t * z) * l := by
        rw [hz]
  rw [hmul]
  apply QuotientGroup.eq.mpr
  simpa using (subgroupLattice N P.lattice).inv_mem hl

/-- Averaging over the compact `Ḡ`-fiber removes the ambiguity coming
from a Hall--Petresco lattice representative.  This is the Fubini--Haar
step in the construction of the BHK configuration-measure factor. -/
theorem averagedQuotientMeasure_lattice
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (l : subgroup N) (hl : l ∈ subgroupLattice N P.lattice) :
    averagedQuotientMeasure N P m l =
      averagedQuotientMeasure N P m 1 := by
  obtain ⟨k, _, hskew⟩ :=
    exists_lattice_smul_averagingOrbitPoint N P l hl
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro S hS
  let F : Quotient N P.lattice → ℝ≥0∞ :=
    S.indicator fun _ ↦ 1
  have hF : Measurable F :=
    measurable_const.indicator hS
  let R : X → X :=
    fun x ↦ N.ambientAction.toMulAction.smul k x
  let f : X × (Fin N.torusDim → Circle) → ℝ≥0∞ :=
    fun p ↦ F (averagingOrbitPoint N P p)
  let f' : X × (Fin N.torusDim → Circle) → ℝ≥0∞ :=
    fun p ↦ F (l • averagingOrbitPoint N P p)
  have hf : Measurable f :=
    hF.comp (continuous_averagingOrbitPoint N P).measurable
  have hf' : Measurable f' := by
    exact hF.comp
      ((continuous_const_smul l).comp
        (continuous_averagingOrbitPoint N P)).measurable
  have hprod :
      (∫⁻ p, f' p ∂(μ.prod m)) = ∫⁻ p, f p ∂(μ.prod m) := by
    apply lintegral_prod_skew_mul μ m R
      (N.ambientAction.measurePreserving_smul k) f f' hf hf'
    intro x
    obtain ⟨t, ht⟩ := hskew x
    refine ⟨t, fun z ↦ ?_⟩
    exact congrArg F (ht z)
  simp only [averagedQuotientMeasure,
    ProbabilityMeasure.toMeasure_map]
  rw [← lintegral_indicator_one hS,
    ← lintegral_indicator_one hS]
  change
    (∫⁻ q, F q ∂Measure.map
      (averagedQuotientPoint N P l) (μ.prod m)) =
      ∫⁻ q, F q ∂Measure.map
        (averagedQuotientPoint N P 1) (μ.prod m)
  rw [lintegral_map hF
      (continuous_averagedQuotientPoint_fixed N P l).measurable,
    lintegral_map hF
      (continuous_averagedQuotientPoint_fixed N P 1).measurable]
  change (∫⁻ p, f' p ∂(μ.prod m)) =
    ∫⁻ p, F (averagedQuotientPoint N P 1 p) ∂(μ.prod m)
  calc
    (∫⁻ p, f' p ∂(μ.prod m)) = ∫⁻ p, f p ∂(μ.prod m) := hprod
    _ = ∫⁻ p, F (averagedQuotientPoint N P 1 p) ∂(μ.prod m) := by
      apply lintegral_congr
      intro p
      simp [f, averagedQuotientPoint]

/-- Right multiplication by an arbitrary Hall--Petresco lattice element
does not change the averaged fiber measure. -/
theorem averagedQuotientMeasure_mul_lattice
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (s l : subgroup N) (hl : l ∈ subgroupLattice N P.lattice) :
    averagedQuotientMeasure N P m (s * l) =
      averagedQuotientMeasure N P m s := by
  calc
    averagedQuotientMeasure N P m (s * l) =
        (averagedQuotientMeasure N P m l).map
          (continuous_const_smul s).measurable.aemeasurable :=
      averagedQuotientMeasure_mul N P m s l
    _ = (averagedQuotientMeasure N P m 1).map
          (continuous_const_smul s).measurable.aemeasurable := by
      rw [averagedQuotientMeasure_lattice N P m l hl]
    _ = averagedQuotientMeasure N P m s := by
      rw [← averagedQuotientMeasure_mul N P m s 1]
      simp

/-- The averaged measure descends from Hall representatives to the actual
reduced Hall--Petresco group. -/
def reducedGroupAveragedMeasure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant] :
    ReducedGroup N → ProbabilityMeasure (Quotient N P.lattice) := by
  intro r
  exact Quotient.liftOn' r
    (averagedQuotientMeasure N P m)
    (by
      intro s t hst
      have hb : s⁻¹ * t ∈ averagingNormalSubgroup N :=
        QuotientGroup.leftRel_apply.mp hst
      have ht : t = s * (s⁻¹ * t) := by group
      rw [ht]
      exact (averagedQuotientMeasure_mul_mem_averagingNormalSubgroup
        N P m s (s⁻¹ * t) hb).symm)

@[simp]
theorem reducedGroupAveragedMeasure_mk
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (s : subgroup N) :
    reducedGroupAveragedMeasure N P m
        (QuotientGroup.mk' (averagingNormalSubgroup N) s) =
      averagedQuotientMeasure N P m s :=
  rfl

/-- The descended reduced-group measure map remains continuous. -/
theorem continuous_reducedGroupAveragedMeasure
    {H : Type u} {X : Type v}
    [Group H] [MetricSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [CompactSpace (Quotient N P.lattice)]
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant] :
    Continuous (reducedGroupAveragedMeasure N P m) := by
  unfold reducedGroupAveragedMeasure
  apply Continuous.quotient_lift
  exact continuous_averagedQuotientMeasure N P m

/-- Progression translation on the reduced group is sent to pushforward by
the full quotient progression step. -/
theorem reducedGroupAveragedMeasure_progression
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (r : ReducedGroup N) :
    reducedGroupAveragedMeasure N P m
        (reducedProgressionGenerator N * r) =
      quotientMeasureStep N P
        (reducedGroupAveragedMeasure N P m r) := by
  refine Quotient.inductionOn' r ?_
  intro s
  change
    averagedQuotientMeasure N P m
        (progressionGenerator N * s) =
      quotientMeasureStep N P
        (averagedQuotientMeasure N P m s)
  rw [averagedQuotientMeasure_mul]
  rfl

/-- The reduced-group measure map is constant on right cosets of the
actual reduced Hall--Petresco lattice. -/
theorem reducedGroupAveragedMeasure_mul_reducedLattice
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (r b : ReducedGroup N) (hb : b ∈ reducedLattice N P.lattice) :
    reducedGroupAveragedMeasure N P m (r * b) =
      reducedGroupAveragedMeasure N P m r := by
  rcases hb with ⟨l, hl, rfl⟩
  refine Quotient.inductionOn' r ?_
  intro s
  change averagedQuotientMeasure N P m (s * l) =
    averagedQuotientMeasure N P m s
  exact averagedQuotientMeasure_mul_lattice N P m s l hl

/-- The BHK configuration-measure map on the genuine compact reduced
Hall--Petresco homogeneous space. -/
def reducedQuotientAveragedMeasure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant] :
    ReducedQuotient N P.lattice →
      ProbabilityMeasure (Quotient N P.lattice) := by
  intro y
  exact Quotient.liftOn' y
    (reducedGroupAveragedMeasure N P m)
    (by
      intro r t hrt
      have hb : r⁻¹ * t ∈ reducedLattice N P.lattice :=
        QuotientGroup.leftRel_apply.mp hrt
      have ht : t = r * (r⁻¹ * t) := by group
      rw [ht]
      exact (reducedGroupAveragedMeasure_mul_reducedLattice
        N P m r (r⁻¹ * t) hb).symm)

@[simp]
theorem reducedQuotientAveragedMeasure_mk
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (r : ReducedGroup N) :
    reducedQuotientAveragedMeasure N P m
        (QuotientGroup.mk r : ReducedQuotient N P.lattice) =
      reducedGroupAveragedMeasure N P m r :=
  rfl

/-- The genuine reduced-quotient configuration-measure map is continuous. -/
theorem continuous_reducedQuotientAveragedMeasure
    {H : Type u} {X : Type v}
    [Group H] [MetricSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [CompactSpace (Quotient N P.lattice)]
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant] :
    Continuous (reducedQuotientAveragedMeasure N P m) := by
  unfold reducedQuotientAveragedMeasure
  apply Continuous.quotient_lift
  exact continuous_reducedGroupAveragedMeasure N P m

/-- The reduced progression step is carried to pushforward by the full
Hall--Petresco quotient progression step. -/
theorem reducedQuotientAveragedMeasure_progression
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (y : ReducedQuotient N P.lattice) :
    reducedQuotientAveragedMeasure N P m (reducedStep N P.lattice y) =
      quotientMeasureStep N P (reducedQuotientAveragedMeasure N P m y) := by
  refine Quotient.inductionOn' y ?_
  intro r
  exact reducedGroupAveragedMeasure_progression N P m r

/-- The center-only representatives used in BHK Proposition 7.2 are
exactly the previously constructed central quotient points after fiber
averaging. -/
theorem averagedQuotientPoint_central
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : (((Fin N.torusDim → Circle) ×
      (Fin N.torusDim → Circle)) ×
        (Fin N.torusDim → Circle)))
    (p : X × (Fin N.torusDim → Circle)) :
    averagedQuotientPoint N P
        (centralHallElement N q 1) p =
      centralQuotientPoint N P q p := by
  unfold averagedQuotientPoint averagingOrbitPoint centralQuotientPoint
  rw [← mul_smul]
  congr 1
  apply Subtype.ext
  funext j
  simp only [Subgroup.coe_mul, Pi.mul_apply,
    centralHallElement_apply]
  change
    N.centralHom (centralExponent N q 1 j) *
        N.centralHom p.2 ^ j.val =
      N.centralHom (centralExponent N q p.2 j)
  simp [centralExponent, map_mul, map_pow, mul_pow, mul_assoc]
  exact (Subgroup.mem_center_iff.mp
    ((Subgroup.center H).pow_mem
      (N.centralHom_mem_center q.2) (j.val.choose 2))
    (N.centralHom p.2 ^ j.val)).symm

/-- Consequently the raw averaged-fiber measure specializes exactly to
the explicit central quotient measure. -/
theorem averagedQuotientMeasure_central
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m]
    (q : (((Fin N.torusDim → Circle) ×
      (Fin N.torusDim → Circle)) ×
        (Fin N.torusDim → Circle))) :
    averagedQuotientMeasure N P m (centralHallElement N q 1) =
      centralQuotientMeasure N P m q := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [averagedQuotientMeasure, centralQuotientMeasure,
    ProbabilityMeasure.toMeasure_map]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall
    (averagedQuotientPoint_central N P q)

/-- Every explicit central quotient measure is therefore in the range of
the continuous map from the actual reduced Hall--Petresco group. -/
theorem centralQuotientMeasure_mem_range_reducedGroupAveragedMeasure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (q : (((Fin N.torusDim → Circle) ×
      (Fin N.torusDim → Circle)) ×
        (Fin N.torusDim → Circle))) :
    centralQuotientMeasure N P m q ∈
      Set.range (reducedGroupAveragedMeasure N P m) := by
  refine ⟨QuotientGroup.mk' (averagingNormalSubgroup N)
      (centralHallElement N q 1), ?_⟩
  rw [reducedGroupAveragedMeasure_mk,
    averagedQuotientMeasure_central]

/-- Every central configuration measure lies in the range of the
continuous equivariant map from the genuine reduced Hall--Petresco
homogeneous space. -/
theorem centralQuotientMeasure_mem_range_reducedQuotientAveragedMeasure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (q : (((Fin N.torusDim → Circle) ×
      (Fin N.torusDim → Circle)) ×
        (Fin N.torusDim → Circle))) :
    centralQuotientMeasure N P m q ∈
      Set.range (reducedQuotientAveragedMeasure N P m) := by
  refine ⟨(QuotientGroup.mk
      (QuotientGroup.mk' (averagingNormalSubgroup N)
        (centralHallElement N q 1)) :
      ReducedQuotient N P.lattice), ?_⟩
  rw [reducedQuotientAveragedMeasure_mk,
    reducedGroupAveragedMeasure_mk,
    averagedQuotientMeasure_central]

end Chapter02.HallPetrescoAveragedQuotientMeasure
