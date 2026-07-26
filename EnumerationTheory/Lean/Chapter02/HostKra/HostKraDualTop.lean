import Chapter02.HostKra.HostKraConditionalTop
import Chapter02.HostKra.HostKraDualFunctionFour

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraDualTop

universe u

open HostKraCubeFactors
open HostKraDualFunction
open HostKraDualFunctionFour
open HostKraConditionalTop
open HostKraStandardRelativeJoining

/-- A seven-vertex Host--Kra dual function is essentially bounded. -/
theorem sevenVertexDualFunction_memLp_top
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 F100 F101 F110 F111 : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ)
    (hF111top : MemLp (fun x ↦ F111 x) ⊤ M.μ) :
    MemLp
      (fun x ↦ sevenVertexDualFunction M hM
        F001 F010 F011 F100 F101 F110 F111
        hF001top hF010top hF011top
        hF100top hF101top hF110top x)
      ⊤ M.μ := by
  have h3 := sevenVertexCubeProduct_memLp_top M hM
    F001 F010 F011 F100 F101 F110 F111
    hF001top hF010top hF011top
    hF100top hF101top hF110top hF111top
  have h2 := relativeFstConditionalCLM_memLp_top
    (relativeCubeSystemTwo M hM)
    (relativeCubeSystemTwo_mps M hM)
    (sevenVertexCubeProduct M hM
      F001 F010 F011 F100 F101 F110 F111
      hF001top hF010top hF011top
      hF100top hF101top hF110top) h3
  have h1 := relativeFstConditionalCLM_memLp_top
    (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM) _ h2
  exact relativeFstConditionalCLM_memLp_top M hM _ h1

/-- The fifteen-vertex cube product is essentially bounded. -/
lemma fifteenVertexCubeProduct_memLp_top
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
    (hF1110top : MemLp (fun x ↦ F1110 x) ⊤ M.μ)
    (hF1111top : MemLp (fun x ↦ F1111 x) ⊤ M.μ) :
    MemLp
      (fun r ↦ fifteenVertexCubeProduct M hM
        F0001 F0010 F0011 F0100 F0101 F0110 F0111
        F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
        hF0001top hF0010top hF0011top
        hF0100top hF0101top hF0110top hF0111top
        hF1000top hF1001top hF1010top hF1011top
        hF1100top hF1101top hF1110top r)
      ⊤
      (relativeJoiningMeasure
        (relativeCubeSystemThree M hM)
        (relativeCubeSystemThree_mps M hM)) := by
  exact relativeEdgeProduct_memLp_top
    (relativeCubeSystemThree M hM)
    (relativeCubeSystemThree_mps M hM)
    (sevenVertexCubeProduct M hM
      F0001 F0010 F0011 F0100 F0101 F0110 F0111
      hF0001top hF0010top hF0011top
      hF0100top hF0101top hF0110top)
    (eightVertexCubeProduct M hM
      F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
      hF1000top hF1001top hF1010top hF1011top
      hF1100top hF1101top hF1110top)
    (sevenVertexCubeProduct_memLp_top M hM
      F0001 F0010 F0011 F0100 F0101 F0110 F0111
      hF0001top hF0010top hF0011top
      hF0100top hF0101top hF0110top hF0111top)
    (eightVertexCubeProduct_memLp_top M hM
      F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
      hF1000top hF1001top hF1010top hF1011top
      hF1100top hF1101top hF1110top hF1111top)

/-- A fifteen-vertex Host--Kra dual function is essentially bounded. -/
theorem fifteenVertexDualFunction_memLp_top
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
    (hF1110top : MemLp (fun x ↦ F1110 x) ⊤ M.μ)
    (hF1111top : MemLp (fun x ↦ F1111 x) ⊤ M.μ) :
    MemLp
      (fun x ↦ fifteenVertexDualFunction M hM
        F0001 F0010 F0011 F0100 F0101 F0110 F0111
        F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
        hF0001top hF0010top hF0011top
        hF0100top hF0101top hF0110top hF0111top
        hF1000top hF1001top hF1010top hF1011top
        hF1100top hF1101top hF1110top x)
      ⊤ M.μ := by
  have h4 := fifteenVertexCubeProduct_memLp_top M hM
    F0001 F0010 F0011 F0100 F0101 F0110 F0111
    F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
    hF0001top hF0010top hF0011top
    hF0100top hF0101top hF0110top hF0111top
    hF1000top hF1001top hF1010top hF1011top
    hF1100top hF1101top hF1110top hF1111top
  have h3 := relativeFstConditionalCLM_memLp_top
    (relativeCubeSystemThree M hM)
    (relativeCubeSystemThree_mps M hM)
    (fifteenVertexCubeProduct M hM
      F0001 F0010 F0011 F0100 F0101 F0110 F0111
      F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
      hF0001top hF0010top hF0011top
      hF0100top hF0101top hF0110top hF0111top
      hF1000top hF1001top hF1010top hF1011top
      hF1100top hF1101top hF1110top) h4
  have h2 := relativeFstConditionalCLM_memLp_top
    (relativeCubeSystemTwo M hM)
    (relativeCubeSystemTwo_mps M hM) _ h3
  have h1 := relativeFstConditionalCLM_memLp_top
    (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM) _ h2
  exact relativeFstConditionalCLM_memLp_top M hM _ h1

end Chapter02.HostKraDualTop
