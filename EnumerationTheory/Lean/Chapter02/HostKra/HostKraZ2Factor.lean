import Chapter02.Ergodic.AlgebraSubSigma
import Chapter02.HostKra.HostKraZ2Characteristic

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HostKraZ2Factor

universe u

open HostKraZ2Characteristic

/-- Representative-level realization of the analytic `Z₂` subspace. -/
def hostKraZ2Functions
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Set (M.X → ℂ) :=
  {f | ∃ hf : M.lpMember 2 f,
    hf.toLp f ∈ hostKraZ2Subspace M hM}

theorem hostKraZ2Functions_isClosedL2FunctionSubspace
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    IsClosedL2FunctionSubspace M (hostKraZ2Functions M hM) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨MemLp.zero', ?_⟩
    change MemLp.zero'.toLp (0 : M.X → ℂ) ∈ hostKraZ2Subspace M hM
    rw [MemLp.toLp_zero]
    exact (hostKraZ2Subspace M hM).zero_mem
  · intro f hf
    exact hf.choose
  · intro f hf g hg a b
    rcases hf with ⟨hf2, hfZ⟩
    rcases hg with ⟨hg2, hgZ⟩
    let haf := hf2.const_smul a
    let hbg := hg2.const_smul b
    let hab := haf.add hbg
    refine ⟨hab, ?_⟩
    have hmem :=
      (hostKraZ2Subspace M hM).add_mem
        ((hostKraZ2Subspace M hM).smul_mem a hfZ)
        ((hostKraZ2Subspace M hM).smul_mem b hgZ)
    simpa only [Pi.smul_apply, smul_eq_mul, MemLp.toLp_add,
      MemLp.toLp_const_smul] using hmem
  · intro f hf g hfg
    rcases hf with ⟨hf2, hfZ⟩
    have hg2 : M.lpMember 2 g := (memLp_congr_ae hfg).mp hf2
    refine ⟨hg2, ?_⟩
    rw [← MemLp.toLp_congr hf2 hg2 hfg]
    exact hfZ
  · intro fseq hfseq f hf2 hconv
    choose hfseq2 hfseqZ using hfseq
    let Fseq : ℕ → Lp ℂ 2 M.μ :=
      fun n ↦ (hfseq2 n).toLp (fseq n)
    let F : Lp ℂ 2 M.μ := hf2.toLp f
    have hlim : Tendsto Fseq atTop (nhds F) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      have hreal :=
        (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hconv
      convert hreal using 1
      funext n
      change ‖(hfseq2 n).toLp (fseq n) - hf2.toLp f‖ =
        (eLpNorm (fun x ↦ fseq n x - f x) 2 M.μ).toReal
      change ‖(hfseq2 n).toLp (fseq n) - hf2.toLp f‖ =
        (eLpNorm (fseq n - f) 2 M.μ).toReal
      rw [← Lp.norm_toLp _ ((hfseq2 n).sub hf2), MemLp.toLp_sub]
    have hclosed :
        IsClosed (hostKraZ2Subspace M hM : Set (Lp ℂ 2 M.μ)) :=
      Submodule.isClosed_orthogonal _
    refine ⟨hf2, hclosed.isSeqClosed hfseqZ hlim⟩

theorem one_mem_hostKraZ2Functions
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M) :
    (fun _ : M.X ↦ (1 : ℂ)) ∈ hostKraZ2Functions M hM := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let hone : M.lpMember 2 (fun _ : M.X ↦ (1 : ℂ)) :=
    memLp_const 1
  refine ⟨hone, ?_⟩
  have heq :
      hone.toLp (fun _ : M.X ↦ (1 : ℂ)) =
        CorrelationMean.oneLp M hM := by
    apply Lp.ext
    exact hone.coeFn_toLp.trans (WeakSpectrum.oneLp_coe M hM).symm
  rw [heq]
  exact oneLp_mem_hostKraZ2Subspace M hM hErg

theorem star_mem_hostKraZ2Functions
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {f : M.X → ℂ} (hf : f ∈ hostKraZ2Functions M hM) :
    (fun x ↦ star (f x)) ∈ hostKraZ2Functions M hM := by
  rcases hf with ⟨hf2, hfZ⟩
  let hstar2 := ForwardKroneckerFactor.memLp_pointwiseStar hf2
  refine ⟨hstar2, ?_⟩
  have heq :
      hstar2.toLp (fun x ↦ star (f x)) =
        ForwardKroneckerFactor.lpStar M (hf2.toLp f) := by
    apply Lp.ext
    filter_upwards [hstar2.coeFn_toLp,
      ForwardKroneckerFactor.lpStar_coe M (hf2.toLp f),
      hf2.coeFn_toLp] with x hraw hstar hrawF
    rw [hraw, hstar, hrawF]
  rw [heq]
  exact lpStar_mem_hostKraZ2Subspace M hM hfZ

/-- Every representative of a forward almost-periodic Koopman vector is an
analytic `Z₂` function.  Thus the already constructed Kronecker factor embeds
into the Host--Kra candidate at the representative level. -/
theorem forwardAlmostPeriodic_mem_hostKraZ2Functions
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    {f : M.X → ℂ}
    (hf : f ∈ ForwardKroneckerFactor.forwardAlmostPeriodicFunctions M hErg) :
    f ∈ hostKraZ2Functions M hM := by
  refine ⟨hf.1, ?_⟩
  exact almostPeriodic_mem_hostKraZ2Subspace
    M hM hErg (hf.2 hf.1)

/-- The measurable sets whose indicators lie in the analytic `Z₂`
subspace.  Proving that this family is a sigma-algebra is the exact
factor-realization step. -/
def hostKraZ2SetFamily
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    SetFamily M.X :=
  AlgebraSubSigma.indicatorFamily M (hostKraZ2Functions M hM)

/-- The remaining algebraic Host--Kra obligation at level `Z₂`, stated
without adding it to any theorem: intersections of structured indicator
sets are again structured. -/
def HasIndicatorIntersectionClosure
  (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) : Prop :=
  ∀ {A B : Set M.X},
    AlgebraSubSigma.indicatorOne A ∈ hostKraZ2Functions M hM →
    AlgebraSubSigma.indicatorOne B ∈ hostKraZ2Functions M hM →
    AlgebraSubSigma.indicatorOne (A ∩ B) ∈
      hostKraZ2Functions M hM

lemma indicatorOne_inter
    {X : Type*} (A B : Set X) :
    AlgebraSubSigma.indicatorOne (A ∩ B) =
      fun x ↦ AlgebraSubSigma.indicatorOne A x *
        AlgebraSubSigma.indicatorOne B x := by
  funext x
  by_cases hx : x ∈ A <;> by_cases hy : x ∈ B <;>
    simp [AlgebraSubSigma.indicatorOne, hx, hy]

/-- Intersections of two forward-Kronecker sets already satisfy the analytic
`Z₂` indicator obligation.  Consequently the unresolved multiplication
closure is confined to genuinely higher-order `Z₂` indicators. -/
theorem forwardKronecker_indicator_inter_mem_hostKraZ2Functions
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    {A B : Set M.X}
    (hA : AlgebraSubSigma.indicatorOne A ∈
      ForwardKroneckerFactor.forwardAlmostPeriodicFunctions M hErg)
    (hB : AlgebraSubSigma.indicatorOne B ∈
      ForwardKroneckerFactor.forwardAlmostPeriodicFunctions M hErg) :
    AlgebraSubSigma.indicatorOne (A ∩ B) ∈
      hostKraZ2Functions M hM := by
  rw [indicatorOne_inter]
  exact forwardAlmostPeriodic_mem_hostKraZ2Functions M hM hErg
    (ForwardKroneckerFactor.indicator_mul_mem M hErg hA hB)

/-- The forward Kronecker sigma-algebra is a subfamily of the analytic `Z₂`
indicator family. -/
theorem forwardKroneckerSets_le_hostKraZ2SetFamily
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M) :
    ForwardKroneckerFactor.forwardKroneckerSets M hErg ⊆
      hostKraZ2SetFamily M hM := by
  intro A hA
  exact ⟨hA.1,
    forwardAlmostPeriodic_mem_hostKraZ2Functions M hM hErg hA.2⟩

/-- Once the exact indicator-intersection obligation is discharged, the
existing generic `AlgebraSubSigma` machinery turns analytic `Z₂` into a
sigma-algebra. -/
theorem hostKraZ2SetFamily_isSigmaAlgebra
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (hinter : HasIndicatorIntersectionClosure M hM) :
    Chapter00.IsSigmaAlgebraFamily (hostKraZ2SetFamily M hM) := by
  apply AlgebraSubSigma.indicatorFamily_isSigmaAlgebra_of_indicator_mul
    M (hostKraZ2Functions M hM) hM
    (hostKraZ2Functions_isClosedL2FunctionSubspace M hM)
    (one_mem_hostKraZ2Functions M hM hErg)
  intro A B hA hB
  rw [← indicatorOne_inter A B]
  exact hinter hA hB

end Chapter02.HostKraZ2Factor
