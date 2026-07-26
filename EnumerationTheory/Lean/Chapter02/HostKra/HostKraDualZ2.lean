import Chapter02.HostKra.HostKraGowersCauchySchwarz
import Chapter02.HostKra.HostKraDualFunctionFour
import Chapter02.HostKra.HostKraZ2Characteristic

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraDualZ2

universe u

open HostKraDualFunction
open HostKraDualFunctionFour
open HostKraZ2Characteristic
open HostKraCubeSeminorm

/-- A single parity-conjugated seven-vertex dual detects bounded
`U³`-nullity exactly. -/
theorem hasZeroHostKraU3_iff_inner_lpStar_parityDual_eq_zero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    HasZeroHostKraU3 M hM (fun x ↦ F x) hFtop ↔
      let Fs := ForwardKroneckerFactor.lpStar M F
      let hFstop := lpStar_memLp_top M F hFtop
      @inner ℂ (Lp ℂ 2 M.μ) _ Fs
          (sevenVertexDualFunction M hM
            Fs Fs F Fs F F Fs
            hFstop hFstop hFtop hFstop hFtop hFtop) = 0 := by
  dsimp only
  let Fs := ForwardKroneckerFactor.lpStar M F
  let hFstop := lpStar_memLp_top M F hFtop
  constructor
  · intro hzero
    have hstarRaw :=
      Chapter02.HostKraU3Nullspace.hasZeroHostKraU3_star
        M hM (fun x ↦ F x) hFtop hzero
    have hFszero :
        HasZeroHostKraU3 M hM (fun x ↦ Fs x) hFstop :=
      Chapter02.HostKraU3Nullspace.hasZeroHostKraU3_congr
        M hM (fun x ↦ star (F x)) (fun x ↦ Fs x)
        hFtop.star hFstop
        (ForwardKroneckerFactor.lpStar_coe M F).symm hstarRaw
    exact
      Chapter02.HostKraGowersCauchySchwarz.inner_sevenVertexDualFunction_eq_zero_of_hasZeroHostKraU3
        M hM Fs Fs F Fs F F Fs Fs
        hFstop hFstop hFtop hFstop hFtop hFtop
        hFstop hFszero
  · intro hpair
    have henergy :=
      inner_lpStar_paritySevenDual_eq_hostKraU3Power M hM F hFtop
    dsimp only at henergy
    rw [hpair] at henergy
    change HostKraCubeSeminorm.hostKraU3Power
      M hM (fun x ↦ F x) hFtop = 0
    exact_mod_cast henergy.symm

/-- Orthogonality to every bounded seven-vertex dual function. -/
def IsOrthogonalToSevenVertexDuals
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : Lp ℂ 2 M.μ) : Prop :=
  ∀ (F001 F010 F011 F100 F101 F110 F111 : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ),
    @inner ℂ (Lp ℂ 2 M.μ) _ H
      (sevenVertexDualFunction M hM
        F001 F010 F011 F100 F101 F110 F111
        hF001top hF010top hF011top
        hF100top hF101top hF110top) = 0

/-- For bounded vectors, `U³`-nullity is exactly orthogonality to all
seven-vertex dual functions. -/
theorem hasZeroHostKraU3_iff_orthogonalToSevenVertexDuals
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : Lp ℂ 2 M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ) :
    HasZeroHostKraU3 M hM (fun x ↦ H x) hHtop ↔
      IsOrthogonalToSevenVertexDuals M hM H := by
  constructor
  · intro hzero F001 F010 F011 F100 F101 F110 F111
      hF001top hF010top hF011top hF100top hF101top hF110top
    exact
      Chapter02.HostKraGowersCauchySchwarz.inner_sevenVertexDualFunction_eq_zero_of_hasZeroHostKraU3
        M hM F001 F010 F011 F100 F101 F110 F111 H
        hF001top hF010top hF011top
        hF100top hF101top hF110top hHtop hzero
  · intro horth
    let F := ForwardKroneckerFactor.lpStar M H
    let hFtop := lpStar_memLp_top M H hHtop
    have hpair :
        let Fs := ForwardKroneckerFactor.lpStar M F
        let hFstop := lpStar_memLp_top M F hFtop
        @inner ℂ (Lp ℂ 2 M.μ) _ Fs
            (sevenVertexDualFunction M hM
              Fs Fs F Fs F F Fs
              hFstop hFstop hFtop hFstop hFtop hFtop) = 0 := by
      dsimp only
      simpa only [F, HostKraDualFunctionFour.lpStar_lpStar] using
        horth
          (ForwardKroneckerFactor.lpStar M F)
          (ForwardKroneckerFactor.lpStar M F) F
          (ForwardKroneckerFactor.lpStar M F) F F
          (ForwardKroneckerFactor.lpStar M F)
          (lpStar_memLp_top M F hFtop)
          (lpStar_memLp_top M F hFtop) hFtop
          (lpStar_memLp_top M F hFtop) hFtop hFtop
    have hFzero :
        HasZeroHostKraU3 M hM (fun x ↦ F x) hFtop :=
      (hasZeroHostKraU3_iff_inner_lpStar_parityDual_eq_zero
        M hM F hFtop).2 hpair
    have hstarRaw :=
      Chapter02.HostKraU3Nullspace.hasZeroHostKraU3_star
        M hM (fun x ↦ F x) hFtop hFzero
    have heq :
        (fun x ↦ star (F x)) =ᵐ[M.μ] fun x ↦ H x := by
      have h := ForwardKroneckerFactor.lpStar_coe M F
      rw [show ForwardKroneckerFactor.lpStar M F = H by
        exact HostKraDualFunctionFour.lpStar_lpStar M H] at h
      exact h.symm
    exact
      Chapter02.HostKraU3Nullspace.hasZeroHostKraU3_congr
        M hM (fun x ↦ star (F x)) (fun x ↦ H x)
        hFtop.star hHtop heq hstarRaw

/-- Every seven-vertex order-two dual function belongs to the analytic
Host--Kra `Z₂` subspace. -/
theorem sevenVertexDualFunction_mem_hostKraZ2Subspace
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 F100 F101 F110 F111 : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ) :
    sevenVertexDualFunction M hM
        F001 F010 F011 F100 F101 F110 F111
        hF001top hF010top hF011top
        hF100top hF101top hF110top ∈
      hostKraZ2Subspace M hM := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let D :=
    sevenVertexDualFunction M hM
      F001 F010 F011 F100 F101 F110 F111
      hF001top hF010top hF011top
      hF100top hF101top hF110top
  let K : Submodule ℂ (Lp ℂ 2 M.μ) :=
    (Submodule.span ℂ ({D} : Set (Lp ℂ 2 M.μ)))ᗮ
  have hspan : u3NullSpan M hM ≤ K := by
    apply Submodule.span_le.mpr
    intro G hG
    rcases hG with ⟨f, hf, hzero, rfl⟩
    let H := boundedToLp M hM f hf
    have hHcoe : (fun x ↦ H x) =ᵐ[M.μ] f := by
      unfold H boundedToLp
      exact (hf.mono_exponent (by simp)).coeFn_toLp
    have hHtop : MemLp (fun x ↦ H x) ⊤ M.μ :=
      (memLp_congr_ae hHcoe).mpr hf
    have hHzero : HasZeroHostKraU3 M hM (fun x ↦ H x) hHtop :=
      Chapter02.HostKraU3Nullspace.hasZeroHostKraU3_congr
        M hM f (fun x ↦ H x) hf hHtop hHcoe.symm hzero
    change H ∈
      (Submodule.span ℂ ({D} : Set (Lp ℂ 2 M.μ)))ᗮ
    rw [Submodule.mem_orthogonal]
    intro Y hY
    have hYD : Y ∈ Submodule.span ℂ ({D} : Set (Lp ℂ 2 M.μ)) := hY
    refine Submodule.span_induction
      (p := fun Y _ ↦ @inner ℂ (Lp ℂ 2 M.μ) _ Y H = 0)
      ?_ ?_ ?_ ?_ hYD
    · intro Y hY
      have hYD' : Y = D := by simpa using hY
      subst Y
      exact inner_eq_zero_symm.mpr
        (Chapter02.HostKraGowersCauchySchwarz.inner_sevenVertexDualFunction_eq_zero_of_hasZeroHostKraU3
            M hM F001 F010 F011 F100 F101 F110 F111 H
            hF001top hF010top hF011top
            hF100top hF101top hF110top hHtop hHzero)
    · exact inner_zero_left H
    · intro Y Z _ _ hY hZ
      rw [inner_add_left, hY, hZ, add_zero]
    · intro c Y _ hY
      rw [inner_smul_left, hY, mul_zero]
  have hclosed : u3NullClosedSpan M hM ≤ K :=
    Submodule.topologicalClosure_minimal
      (u3NullSpan M hM) hspan (Submodule.isClosed_orthogonal _)
  rw [hostKraZ2Subspace, Submodule.mem_orthogonal]
  intro G hG
  have hGK : G ∈ K := hclosed hG
  rw [Submodule.mem_orthogonal] at hGK
  exact inner_eq_zero_symm.mpr
    (hGK D (Submodule.subset_span (by simp)))

end Chapter02.HostKraDualZ2
