import Chapter02.HostKra.HostKraCubeFactors
import Chapter02.HostKra.HostKraRelativeMean

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraCubeSeminorm

universe u

open HostKraCubeFactors HostKraStandardRelativeJoining

/-- One conjugate cube lift.  Iterating this operation supplies the
alternating conjugations on all vertices of a Host--Kra cube. -/
def cubeLift {X : Type u} (f : X → ℂ) : X × X → ℂ :=
  fun p ↦ f p.1 * star (f p.2)

theorem cubeLift_comp_relativeJoiningTransform
    (M : System.{u}) (f : M.X → ℂ) :
    cubeLift f ∘ relativeJoiningTransform M =
      cubeLift (f ∘ M.T) :=
  rfl

lemma cubeLift_memLp_top
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    MemLp (cubeLift f) ⊤ (relativeJoiningMeasure M hM) := by
  let ν := relativeJoiningMeasure M hM
  have hfst : MemLp (f ∘ Prod.fst) ⊤ ν :=
    hf.comp_measurePreserving (relativeJoining_fst_measurePreserving M hM)
  have hsnd : MemLp ((fun x ↦ star (f x)) ∘ Prod.snd) ⊤ ν :=
    hf.star.comp_measurePreserving
      (relativeJoining_snd_measurePreserving M hM)
  simpa only [ν, cubeLift, Function.comp_apply] using
    hsnd.mul (r := ⊤) hfst

/-- Alternating products on the 2-, 4-, and 8-vertex cube systems. -/
def cubeLiftOne
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) : (relativeCubeSystemOne M hM).X → ℂ :=
  cubeLift f

def cubeLiftTwo
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) : (relativeCubeSystemTwo M hM).X → ℂ :=
  cubeLift (cubeLiftOne M hM f)

def cubeLiftThree
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) : (relativeCubeSystemThree M hM).X → ℂ :=
  cubeLift (cubeLiftTwo M hM f)

lemma cubeLiftOne_memLp_top
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    MemLp (cubeLiftOne M hM f) ⊤ (relativeCubeSystemOne M hM).μ := by
  exact cubeLift_memLp_top M hM f hf

lemma cubeLiftTwo_memLp_top
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    MemLp (cubeLiftTwo M hM f) ⊤ (relativeCubeSystemTwo M hM).μ := by
  exact cubeLift_memLp_top (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM) (cubeLiftOne M hM f)
    (cubeLiftOne_memLp_top M hM f hf)

lemma cubeLiftThree_memLp_top
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    MemLp (cubeLiftThree M hM f) ⊤ (relativeCubeSystemThree M hM).μ := by
  exact cubeLift_memLp_top (relativeCubeSystemTwo M hM)
    (relativeCubeSystemTwo_mps M hM) (cubeLiftTwo M hM f)
    (cubeLiftTwo_memLp_top M hM f hf)

def cubeLiftOne_memLp_two
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    (relativeCubeSystemOne M hM).lpMember 2 (cubeLiftOne M hM f) := by
  let hC := relativeCubeSystemOne_mps M hM
  letI : IsProbabilityMeasure (relativeCubeSystemOne M hM).μ := hC.1
  exact (cubeLiftOne_memLp_top M hM f hf).mono_exponent (by simp)

def cubeLiftTwo_memLp_two
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    (relativeCubeSystemTwo M hM).lpMember 2 (cubeLiftTwo M hM f) := by
  let hC := relativeCubeSystemTwo_mps M hM
  letI : IsProbabilityMeasure (relativeCubeSystemTwo M hM).μ := hC.1
  exact (cubeLiftTwo_memLp_top M hM f hf).mono_exponent (by simp)

def cubeLiftThree_memLp_two
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    (relativeCubeSystemThree M hM).lpMember 2 (cubeLiftThree M hM f) := by
  let hC := relativeCubeSystemThree_mps M hM
  letI : IsProbabilityMeasure (relativeCubeSystemThree M hM).μ := hC.1
  exact (cubeLiftThree_memLp_top M hM f hf).mono_exponent (by simp)

/-- Invariant-projection energy.  This is the root-free recursive form of
the Host--Kra seminorm powers. -/
def invariantEnergy
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) : ℝ :=
  ‖HostKraRelativeMean.invariantMeanLp M hM f hf‖ ^ 2

theorem invariantEnergy_nonneg
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    0 ≤ invariantEnergy M hM f hf :=
  sq_nonneg _

theorem invariantEnergy_eq_zero_iff
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    invariantEnergy M hM f hf = 0 ↔
      HostKraRelativeMean.invariantMeanLp M hM f hf = 0 := by
  rw [invariantEnergy, sq_eq_zero_iff, norm_eq_zero]

/-- `U¹(f)²`, `U²(f)⁴`, `U³(f)⁸`, and `U⁴(f)¹⁶`, represented as
nonnegative invariant energies on successive cube systems. -/
def hostKraU1Power
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) : ℝ :=
  by
    letI : IsProbabilityMeasure M.μ := hM.1
    exact invariantEnergy M hM f (hf.mono_exponent (by simp))

def hostKraU2Power
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) : ℝ :=
  by
    let hC := relativeCubeSystemOne_mps M hM
    letI : IsProbabilityMeasure (relativeCubeSystemOne M hM).μ := hC.1
    exact invariantEnergy (relativeCubeSystemOne M hM) hC
      (cubeLiftOne M hM f)
      (cubeLiftOne_memLp_two M hM f hf)

def hostKraU3Power
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) : ℝ :=
  by
    let hC := relativeCubeSystemTwo_mps M hM
    letI : IsProbabilityMeasure (relativeCubeSystemTwo M hM).μ := hC.1
    exact invariantEnergy (relativeCubeSystemTwo M hM) hC
      (cubeLiftTwo M hM f)
      (cubeLiftTwo_memLp_two M hM f hf)

def hostKraU4Power
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) : ℝ :=
  by
    let hC := relativeCubeSystemThree_mps M hM
    letI : IsProbabilityMeasure (relativeCubeSystemThree M hM).μ := hC.1
    exact invariantEnergy (relativeCubeSystemThree M hM) hC
      (cubeLiftThree M hM f)
      (cubeLiftThree_memLp_two M hM f hf)

theorem hostKraU2Power_nonneg
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    0 ≤ hostKraU2Power M hM f hf := by
  unfold hostKraU2Power
  exact invariantEnergy_nonneg _ _ _ _

theorem hostKraU3Power_nonneg
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    0 ≤ hostKraU3Power M hM f hf := by
  unfold hostKraU3Power
  exact invariantEnergy_nonneg _ _ _ _

theorem hostKraU4Power_nonneg
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    0 ≤ hostKraU4Power M hM f hf := by
  unfold hostKraU4Power
  exact invariantEnergy_nonneg _ _ _ _

/-- Analytic null conditions which will define the `Z₂` and `Z₃`
characteristic factors once the factor-representation theorem is proved.
These names deliberately assert only seminorm vanishing at this stage. -/
def HasZeroHostKraU3
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) : Prop :=
  hostKraU3Power M hM f hf = 0

def HasZeroHostKraU4
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) : Prop :=
  hostKraU4Power M hM f hf = 0

theorem hasZeroHostKraU3_iff_invariantMean
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    HasZeroHostKraU3 M hM f hf ↔
      HostKraRelativeMean.invariantMeanLp
        (relativeCubeSystemTwo M hM)
        (relativeCubeSystemTwo_mps M hM)
        (cubeLiftTwo M hM f)
        (cubeLiftTwo_memLp_two M hM f hf) = 0 := by
  unfold HasZeroHostKraU3 hostKraU3Power
  exact invariantEnergy_eq_zero_iff _ _ _ _

theorem hasZeroHostKraU4_iff_invariantMean
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    HasZeroHostKraU4 M hM f hf ↔
      HostKraRelativeMean.invariantMeanLp
        (relativeCubeSystemThree M hM)
        (relativeCubeSystemThree_mps M hM)
        (cubeLiftThree M hM f)
        (cubeLiftThree_memLp_two M hM f hf) = 0 := by
  unfold HasZeroHostKraU4 hostKraU4Power
  exact invariantEnergy_eq_zero_iff _ _ _ _

end Chapter02.HostKraCubeSeminorm
