import Chapter02.HostKra.HostKraCubeSeminorm

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraCubeSeminormDynamics

universe u

open HostKraCubeSeminorm HostKraStandardRelativeJoining

theorem invariantMeanLp_coe_condExp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    (fun x ↦ HostKraRelativeMean.invariantMeanLp M hM f hf x) =ᵐ[M.μ]
      condExp (MeasurableSpace.generateFrom (invariantSigmaAlgebra M))
        M.μ f := by
  let result :=
    MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM f hf
  have hmean :=
    HostKraRelativeMean.invariantMeanLp_coe M hM f hf
  have hcond := result.choose_spec.2.2.2.1
  exact hmean.trans hcond.symm

theorem invariantMeanLp_comp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    let hcomp : M.lpMember 2 (f ∘ M.T) :=
      hf.comp_measurePreserving hM.2
    HostKraRelativeMean.invariantMeanLp M hM (f ∘ M.T) hcomp =
      HostKraRelativeMean.invariantMeanLp M hM f hf := by
  dsimp only
  let hcomp : M.lpMember 2 (f ∘ M.T) :=
    hf.comp_measurePreserving hM.2
  apply Lp.ext
  have hleft :=
    invariantMeanLp_coe_condExp M hM (f ∘ M.T) hcomp
  have hright :=
    invariantMeanLp_coe_condExp M hM f hf
  letI : IsProbabilityMeasure M.μ := hM.1
  have hfint : Integrable f M.μ :=
    hf.integrable (by norm_num)
  have hce :=
    Chapter02.Section01.conditionalExpectationCommutesWithKoopmanInvariantSigmaAlgebra
      M hM f hfint
  have hce' :
      condExp (MeasurableSpace.generateFrom (invariantSigmaAlgebra M))
          M.μ (f ∘ M.T) =ᵐ[M.μ]
        condExp (MeasurableSpace.generateFrom (invariantSigmaAlgebra M))
          M.μ f := by
    simpa only [Chapter01.koopman, Function.comp_def] using hce
  exact hleft.trans (hce'.trans hright.symm)

theorem invariantEnergy_comp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    let hcomp : M.lpMember 2 (f ∘ M.T) :=
      hf.comp_measurePreserving hM.2
    invariantEnergy M hM (f ∘ M.T) hcomp =
      invariantEnergy M hM f hf := by
  dsimp only
  unfold invariantEnergy
  rw [invariantMeanLp_comp M hM f hf]

theorem cubeLiftOne_comp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) :
    cubeLiftOne M hM (f ∘ M.T) =
      cubeLiftOne M hM f ∘ (relativeCubeSystemOne M hM).T :=
  rfl

theorem cubeLiftTwo_comp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) :
    cubeLiftTwo M hM (f ∘ M.T) =
      cubeLiftTwo M hM f ∘ (relativeCubeSystemTwo M hM).T :=
  rfl

theorem cubeLiftThree_comp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) :
    cubeLiftThree M hM (f ∘ M.T) =
      cubeLiftThree M hM f ∘ (relativeCubeSystemThree M hM).T :=
  rfl

theorem hostKraU2Power_comp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    let hfT : MemLp (f ∘ M.T) ⊤ M.μ :=
      hf.comp_measurePreserving hM.2
    hostKraU2Power M hM (f ∘ M.T) hfT =
      hostKraU2Power M hM f hf := by
  dsimp only
  unfold hostKraU2Power
  cases cubeLiftOne_comp M hM f
  exact invariantEnergy_comp
    (relativeCubeSystemOne M hM) (relativeCubeSystemOne_mps M hM)
    (cubeLiftOne M hM f) (cubeLiftOne_memLp_two M hM f hf)

theorem hostKraU3Power_comp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    let hfT : MemLp (f ∘ M.T) ⊤ M.μ :=
      hf.comp_measurePreserving hM.2
    hostKraU3Power M hM (f ∘ M.T) hfT =
      hostKraU3Power M hM f hf := by
  dsimp only
  unfold hostKraU3Power
  cases cubeLiftTwo_comp M hM f
  exact invariantEnergy_comp
    (relativeCubeSystemTwo M hM) (relativeCubeSystemTwo_mps M hM)
    (cubeLiftTwo M hM f) (cubeLiftTwo_memLp_two M hM f hf)

theorem hostKraU4Power_comp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    let hfT : MemLp (f ∘ M.T) ⊤ M.μ :=
      hf.comp_measurePreserving hM.2
    hostKraU4Power M hM (f ∘ M.T) hfT =
      hostKraU4Power M hM f hf := by
  dsimp only
  unfold hostKraU4Power
  cases cubeLiftThree_comp M hM f
  exact invariantEnergy_comp
    (relativeCubeSystemThree M hM) (relativeCubeSystemThree_mps M hM)
    (cubeLiftThree M hM f) (cubeLiftThree_memLp_two M hM f hf)

theorem hasZeroHostKraU3_comp_iff
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    let hfT : MemLp (f ∘ M.T) ⊤ M.μ :=
      hf.comp_measurePreserving hM.2
    HasZeroHostKraU3 M hM (f ∘ M.T) hfT ↔
      HasZeroHostKraU3 M hM f hf := by
  dsimp only
  unfold HasZeroHostKraU3
  rw [hostKraU3Power_comp M hM f hf]

theorem hasZeroHostKraU4_comp_iff
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    let hfT : MemLp (f ∘ M.T) ⊤ M.μ :=
      hf.comp_measurePreserving hM.2
    HasZeroHostKraU4 M hM (f ∘ M.T) hfT ↔
      HasZeroHostKraU4 M hM f hf := by
  dsimp only
  unfold HasZeroHostKraU4
  rw [hostKraU4Power_comp M hM f hf]

end Chapter02.HostKraCubeSeminormDynamics
