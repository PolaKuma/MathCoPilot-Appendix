import Chapter02.HallPetresco.CentralFiberFourfold

open Classical MeasureTheory

noncomputable section

namespace Chapter02

universe u v

/-- A genuine continuous measure-preserving action of a compact central
group.  `CompactCentralAction` contains the analytic data used by the
Fourier calculation; this structure additionally records the action laws
which hold for central translations on a nilmanifold. -/
structure LawfulCompactCentralAction
    (G : Type u) (X : Type v)
    [Group G] [TopologicalSpace G] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure X) where
  toMulAction : MulAction G X
  continuous_smul :
    Continuous (fun p : G × X ↦ toMulAction.smul p.1 p.2)
  measurePreserving_smul :
    ∀ g, MeasurePreserving (toMulAction.smul g) μ μ
  measurableEmbedding_smul :
    ∀ g, MeasurableEmbedding (toMulAction.smul g)

/-- Forgetting the action laws gives exactly the analytic central-action
interface used by the checked Haar/Fourier argument. -/
def toCompactCentralAction
    {G : Type u} {X : Type v}
    [Group G] [TopologicalSpace G] [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : LawfulCompactCentralAction G X μ) :
    Chapter02.CentralFiberFourfold.CompactCentralAction G X μ where
  act := C.toMulAction.smul
  continuous_act := C.continuous_smul
  measurePreserving_act := C.measurePreserving_smul
  measurableEmbedding_act := C.measurableEmbedding_smul

@[simp]
theorem toCompactCentralAction_act
    {G : Type u} {X : Type v}
    [Group G] [TopologicalSpace G] [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : LawfulCompactCentralAction G X μ) (g : G) (x : X) :
    (toCompactCentralAction C).act g x = C.toMulAction.smul g x :=
  rfl

/-- Restrict a continuous measure-preserving action along a continuous
group homomorphism.  This constructs the central torus action from its
embedding into the ambient nilpotent group. -/
def LawfulCompactCentralAction.restrict
    {G : Type u} {H : Type*} {X : Type v}
    [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure X}
    (D : LawfulCompactCentralAction H X μ)
    (ι : G →* H) (hι : Continuous ι) :
    LawfulCompactCentralAction G X μ where
  toMulAction :=
    { smul := fun g x ↦ D.toMulAction.smul (ι g) x
      one_smul := fun x ↦ by
        change D.toMulAction.smul (ι 1) x = x
        rw [map_one]
        exact D.toMulAction.one_smul x
      mul_smul := fun g h x ↦ by
        change D.toMulAction.smul (ι (g * h)) x =
          D.toMulAction.smul (ι g) (D.toMulAction.smul (ι h) x)
        rw [map_mul]
        exact D.toMulAction.mul_smul (ι g) (ι h) x }
  continuous_smul := by
    exact D.continuous_smul.comp
      ((hι.comp continuous_fst).prodMk continuous_snd)
  measurePreserving_smul := fun g ↦ D.measurePreserving_smul (ι g)
  measurableEmbedding_smul := fun g ↦ D.measurableEmbedding_smul (ι g)

/-- Package an ordinary continuous group action preserving a Borel
probability measure into the lawful analytic interface. -/
def LawfulCompactCentralAction.ofContinuousMulAction
    {G : Type u} {X : Type v}
    [Group G] [TopologicalSpace G] [TopologicalSpace X]
    [MulAction G X] [ContinuousSMul G X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
    (hinv : ∀ g : G, MeasurePreserving (g • ·) μ μ) :
    LawfulCompactCentralAction G X μ where
  toMulAction := inferInstance
  continuous_smul := ContinuousSMul.continuous_smul
  measurePreserving_smul := hinv
  measurableEmbedding_smul := fun g ↦
    (Homeomorph.smul g).measurableEmbedding

end Chapter02
