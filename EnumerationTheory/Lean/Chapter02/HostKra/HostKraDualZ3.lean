import Chapter02.HostKra.HostKraGowersCauchySchwarzFour
import Chapter02.HostKra.HostKraZ3Characteristic

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraDualZ3

universe u

open HostKraCubeSeminorm
open HostKraDualFunctionFour
open HostKraZ3Characteristic

/-- A single parity-conjugated fifteen-vertex dual detects bounded
`U⁴`-nullity exactly. -/
theorem hasZeroHostKraU4_iff_inner_lpStar_parityDual_eq_zero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    HasZeroHostKraU4 M hM (fun x ↦ F x) hFtop ↔
      let Fs := ForwardKroneckerFactor.lpStar M F
      let hFstop :=
        HostKraDualFunction.lpStar_memLp_top M F hFtop
      @inner ℂ (Lp ℂ 2 M.μ) _ Fs
          (fifteenVertexDualFunction M hM
            Fs Fs F Fs F F Fs
            Fs F F Fs F Fs Fs F
            hFstop hFstop hFtop hFstop hFtop hFtop hFstop
            hFstop hFtop hFtop hFstop hFtop hFstop hFstop) = 0 := by
  dsimp only
  let Fs := ForwardKroneckerFactor.lpStar M F
  let hFstop := HostKraDualFunction.lpStar_memLp_top M F hFtop
  constructor
  · intro hzero
    have hstarRaw :=
      Chapter02.HostKraU4Nullspace.hasZeroHostKraU4_star
        M hM (fun x ↦ F x) hFtop hzero
    have hFszero :
        HasZeroHostKraU4 M hM (fun x ↦ Fs x) hFstop :=
      Chapter02.HostKraU4Nullspace.hasZeroHostKraU4_congr
        M hM (fun x ↦ star (F x)) (fun x ↦ Fs x)
        hFtop.star hFstop
        (ForwardKroneckerFactor.lpStar_coe M F).symm hstarRaw
    exact
      Chapter02.HostKraGowersCauchySchwarzFour.inner_fifteenVertexDualFunction_eq_zero_of_hasZeroHostKraU4
        M hM
        Fs Fs F Fs F F Fs
        Fs F F Fs F Fs Fs F Fs
        hFstop hFstop hFtop hFstop hFtop hFtop hFstop
        hFstop hFtop hFtop hFstop hFtop hFstop hFstop
        hFstop hFszero
  · intro hpair
    have henergy :=
      inner_lpStar_parityDual_eq_hostKraU4Power M hM F hFtop
    dsimp only at henergy
    rw [hpair] at henergy
    change HostKraCubeSeminorm.hostKraU4Power
      M hM (fun x ↦ F x) hFtop = 0
    exact_mod_cast henergy.symm

/-- Orthogonality to every bounded fifteen-vertex dual function. -/
def IsOrthogonalToFifteenVertexDuals
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : Lp ℂ 2 M.μ) : Prop :=
  ∀ (F0001 F0010 F0011 F0100 F0101 F0110 F0111
      F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111 :
      Lp ℂ 2 M.μ)
    (hF0001top : MemLp (fun x ↦ F0001 x) ⊤ M.μ)
    (hF0010top : MemLp (fun x ↦ F0010 x) ⊤ M.μ)
    (hF0011top : MemLp (fun x ↦ F0011 x) ⊤ M.μ)
    (hF0100top : MemLp (fun x ↦ F0100 x) ⊤ M.μ)
    (hF0101top : MemLp (fun x ↦ F0101 x) ⊤ M.μ)
    (hF0110top : MemLp (fun x ↦ F0110 x) ⊤ M.μ)
    (hF0111top : MemLp (fun x ↦ F0111 x) ⊤ M.μ)
    (hF1000top : MemLp (fun x ↦ F1000 x) ⊤ M.μ)
    (hF1001top : MemLp (fun x ↦ F1001 x) ⊤ M.μ)
    (hF1010top : MemLp (fun x ↦ F1010 x) ⊤ M.μ)
    (hF1011top : MemLp (fun x ↦ F1011 x) ⊤ M.μ)
    (hF1100top : MemLp (fun x ↦ F1100 x) ⊤ M.μ)
    (hF1101top : MemLp (fun x ↦ F1101 x) ⊤ M.μ)
    (hF1110top : MemLp (fun x ↦ F1110 x) ⊤ M.μ),
    @inner ℂ (Lp ℂ 2 M.μ) _ H
      (fifteenVertexDualFunction M hM
        F0001 F0010 F0011 F0100 F0101 F0110 F0111
        F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
        hF0001top hF0010top hF0011top
        hF0100top hF0101top hF0110top hF0111top
        hF1000top hF1001top hF1010top hF1011top
        hF1100top hF1101top hF1110top) = 0

/-- For bounded vectors, `U⁴`-nullity is exactly orthogonality to all
fifteen-vertex dual functions. -/
theorem hasZeroHostKraU4_iff_orthogonalToFifteenVertexDuals
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : Lp ℂ 2 M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ) :
    HasZeroHostKraU4 M hM (fun x ↦ H x) hHtop ↔
      IsOrthogonalToFifteenVertexDuals M hM H := by
  constructor
  · intro hzero
      F0001 F0010 F0011 F0100 F0101 F0110 F0111
      F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
      hF0001top hF0010top hF0011top
      hF0100top hF0101top hF0110top hF0111top
      hF1000top hF1001top hF1010top hF1011top
      hF1100top hF1101top hF1110top
    exact
      Chapter02.HostKraGowersCauchySchwarzFour.inner_fifteenVertexDualFunction_eq_zero_of_hasZeroHostKraU4
        M hM
        F0001 F0010 F0011 F0100 F0101 F0110 F0111
        F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111 H
        hF0001top hF0010top hF0011top
        hF0100top hF0101top hF0110top hF0111top
        hF1000top hF1001top hF1010top hF1011top
        hF1100top hF1101top hF1110top hHtop hzero
  · intro horth
    let F := ForwardKroneckerFactor.lpStar M H
    let hFtop := HostKraDualFunction.lpStar_memLp_top M H hHtop
    have hpair :
        let Fs := ForwardKroneckerFactor.lpStar M F
        let hFstop :=
          HostKraDualFunction.lpStar_memLp_top M F hFtop
        @inner ℂ (Lp ℂ 2 M.μ) _ Fs
            (fifteenVertexDualFunction M hM
              Fs Fs F Fs F F Fs
              Fs F F Fs F Fs Fs F
              hFstop hFstop hFtop hFstop hFtop hFtop hFstop
              hFstop hFtop hFtop hFstop hFtop hFstop hFstop) = 0 := by
      dsimp only
      simpa only [F, lpStar_lpStar] using
        horth
          (ForwardKroneckerFactor.lpStar M F)
          (ForwardKroneckerFactor.lpStar M F) F
          (ForwardKroneckerFactor.lpStar M F) F F
          (ForwardKroneckerFactor.lpStar M F)
          (ForwardKroneckerFactor.lpStar M F) F F
          (ForwardKroneckerFactor.lpStar M F) F
          (ForwardKroneckerFactor.lpStar M F)
          (ForwardKroneckerFactor.lpStar M F) F
          (HostKraDualFunction.lpStar_memLp_top M F hFtop)
          (HostKraDualFunction.lpStar_memLp_top M F hFtop) hFtop
          (HostKraDualFunction.lpStar_memLp_top M F hFtop) hFtop hFtop
          (HostKraDualFunction.lpStar_memLp_top M F hFtop)
          (HostKraDualFunction.lpStar_memLp_top M F hFtop) hFtop hFtop
          (HostKraDualFunction.lpStar_memLp_top M F hFtop) hFtop
          (HostKraDualFunction.lpStar_memLp_top M F hFtop)
          (HostKraDualFunction.lpStar_memLp_top M F hFtop)
    have hFzero :
        HasZeroHostKraU4 M hM (fun x ↦ F x) hFtop :=
      (hasZeroHostKraU4_iff_inner_lpStar_parityDual_eq_zero
        M hM F hFtop).2 hpair
    have hstarRaw :=
      Chapter02.HostKraU4Nullspace.hasZeroHostKraU4_star
        M hM (fun x ↦ F x) hFtop hFzero
    have heq :
        (fun x ↦ star (F x)) =ᵐ[M.μ] fun x ↦ H x := by
      have h := ForwardKroneckerFactor.lpStar_coe M F
      rw [show ForwardKroneckerFactor.lpStar M F = H by
        exact lpStar_lpStar M H] at h
      exact h.symm
    exact
      Chapter02.HostKraU4Nullspace.hasZeroHostKraU4_congr
        M hM (fun x ↦ star (F x)) (fun x ↦ H x)
        hFtop.star hHtop heq hstarRaw

/-- A vector orthogonal to every bounded `U⁴`-null vector belongs to the
analytic Host--Kra `Z₃` subspace. -/
theorem mem_hostKraZ3Subspace_of_inner_bounded_u4Null_eq_zero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (D : Lp ℂ 2 M.μ)
    (horth : ∀ (H : Lp ℂ 2 M.μ)
      (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ),
      HasZeroHostKraU4 M hM (fun x ↦ H x) hHtop →
        @inner ℂ (Lp ℂ 2 M.μ) _ H D = 0) :
    D ∈ hostKraZ3Subspace M hM := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let K : Submodule ℂ (Lp ℂ 2 M.μ) :=
    (Submodule.span ℂ ({D} : Set (Lp ℂ 2 M.μ)))ᗮ
  have hspan : u4NullSpan M hM ≤ K := by
    apply Submodule.span_le.mpr
    intro G hG
    rcases hG with ⟨f, hf, hzero, rfl⟩
    let H := Chapter02.HostKraZ2Characteristic.boundedToLp M hM f hf
    have hHcoe : (fun x ↦ H x) =ᵐ[M.μ] f := by
      unfold H Chapter02.HostKraZ2Characteristic.boundedToLp
      exact (hf.mono_exponent (by simp)).coeFn_toLp
    have hHtop : MemLp (fun x ↦ H x) ⊤ M.μ :=
      (memLp_congr_ae hHcoe).mpr hf
    have hHzero : HasZeroHostKraU4 M hM (fun x ↦ H x) hHtop :=
      Chapter02.HostKraU4Nullspace.hasZeroHostKraU4_congr
        M hM f (fun x ↦ H x) hf hHtop hHcoe.symm hzero
    change H ∈
      (Submodule.span ℂ ({D} : Set (Lp ℂ 2 M.μ)))ᗮ
    rw [Submodule.mem_orthogonal]
    intro Y hY
    refine Submodule.span_induction
      (p := fun Y _ ↦ @inner ℂ (Lp ℂ 2 M.μ) _ Y H = 0)
      ?_ ?_ ?_ ?_ hY
    · intro Y hY
      have hYD : Y = D := by simpa using hY
      subst Y
      exact inner_eq_zero_symm.mpr (horth H hHtop hHzero)
    · exact inner_zero_left H
    · intro Y Z _ _ hY hZ
      rw [inner_add_left, hY, hZ, add_zero]
    · intro c Y _ hY
      rw [inner_smul_left, hY, mul_zero]
  have hclosed : u4NullClosedSpan M hM ≤ K :=
    Submodule.topologicalClosure_minimal
      (u4NullSpan M hM) hspan (Submodule.isClosed_orthogonal _)
  rw [hostKraZ3Subspace, Submodule.mem_orthogonal]
  intro G hG
  have hGK : G ∈ K := hclosed hG
  rw [Submodule.mem_orthogonal] at hGK
  exact inner_eq_zero_symm.mpr
    (hGK D (Submodule.subset_span (by simp)))

/-- Every fifteen-vertex order-three dual function belongs to the analytic
Host--Kra `Z₃` subspace. -/
theorem fifteenVertexDualFunction_mem_hostKraZ3Subspace
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F0001 F0010 F0011 F0100 F0101 F0110 F0111
      F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111 :
      Lp ℂ 2 M.μ)
    (hF0001top : MemLp (fun x ↦ F0001 x) ⊤ M.μ)
    (hF0010top : MemLp (fun x ↦ F0010 x) ⊤ M.μ)
    (hF0011top : MemLp (fun x ↦ F0011 x) ⊤ M.μ)
    (hF0100top : MemLp (fun x ↦ F0100 x) ⊤ M.μ)
    (hF0101top : MemLp (fun x ↦ F0101 x) ⊤ M.μ)
    (hF0110top : MemLp (fun x ↦ F0110 x) ⊤ M.μ)
    (hF0111top : MemLp (fun x ↦ F0111 x) ⊤ M.μ)
    (hF1000top : MemLp (fun x ↦ F1000 x) ⊤ M.μ)
    (hF1001top : MemLp (fun x ↦ F1001 x) ⊤ M.μ)
    (hF1010top : MemLp (fun x ↦ F1010 x) ⊤ M.μ)
    (hF1011top : MemLp (fun x ↦ F1011 x) ⊤ M.μ)
    (hF1100top : MemLp (fun x ↦ F1100 x) ⊤ M.μ)
    (hF1101top : MemLp (fun x ↦ F1101 x) ⊤ M.μ)
    (hF1110top : MemLp (fun x ↦ F1110 x) ⊤ M.μ) :
    fifteenVertexDualFunction M hM
        F0001 F0010 F0011 F0100 F0101 F0110 F0111
        F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
        hF0001top hF0010top hF0011top
        hF0100top hF0101top hF0110top hF0111top
        hF1000top hF1001top hF1010top hF1011top
        hF1100top hF1101top hF1110top ∈
      hostKraZ3Subspace M hM := by
  apply mem_hostKraZ3Subspace_of_inner_bounded_u4Null_eq_zero
  intro H hHtop hzero
  exact
    Chapter02.HostKraGowersCauchySchwarzFour.inner_fifteenVertexDualFunction_eq_zero_of_hasZeroHostKraU4
        M hM
        F0001 F0010 F0011 F0100 F0101 F0110 F0111
        F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111 H
        hF0001top hF0010top hF0011top
        hF0100top hF0101top hF0110top hF0111top
        hF1000top hF1001top hF1010top hF1011top
        hF1100top hF1101top hF1110top hHtop hzero

end Chapter02.HostKraDualZ3
