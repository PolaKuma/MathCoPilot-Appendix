import Chapter07.Section02

noncomputable section

open Classical Filter MeasureTheory
open scoped BigOperators

namespace Chapter07

universe u

namespace Section03

def varyingErgodicAverage (M : MeasurableSystem.{u})
    (g : ℕ -> M.X -> ℂ) (N : ℕ) (x : M.X) : ℂ :=
  if N = 0 then 0 else (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, g n ((M.T^[n]) x)

def reverseVaryingErgodicAverage (M : MeasurableSystem.{u})
    (g : ℕ -> M.X -> ℂ) (N : ℕ) (x : M.X) : ℂ :=
  if N = 0 then 0 else (N : ℂ)⁻¹ *
    ∑ n ∈ Finset.range N, g (N - n - 1) ((M.T^[n]) x)

def invariantConditionalExpectation (M : MeasurableSystem.{u})
    (g : M.X -> ℂ) : M.X -> ℂ :=
  MeasureTheory.condExp
    (MeasurableSpace.generateFrom (Chapter02.invariantSigmaAlgebra M)) M.μ g

/-- Source: Lemma 7.3.1 (Breiman). -/
theorem breimanLemma
    (M : MeasurableSystem.{u}) (gseq : ℕ -> M.X -> ℂ) (g : M.X -> ℂ)
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hint : ∀ n, MeasureTheory.Integrable (gseq n) M.μ)
    (hg : MeasureTheory.Integrable g M.μ)
    (hae : ∀ᵐ x ∂M.μ, Tendsto (fun n => gseq n x) atTop (nhds (g x)))
    (hdom : (∫⁻ x, ⨆ n, ENNReal.ofReal ‖gseq n x‖ ∂M.μ) < ⊤) :
    (∀ᵐ x ∂M.μ, Tendsto (fun N => varyingErgodicAverage M gseq N x)
      atTop (nhds (invariantConditionalExpectation M g x))) ∧
    Tendsto (fun N => MeasureTheory.eLpNorm
      (fun x => varyingErgodicAverage M gseq N x -
        invariantConditionalExpectation M g x) 1 M.μ) atTop (nhds 0) := by
  sorry

/-- Source: Remark 7.3.2. -/
theorem reversedBreimanAverages
    (M : MeasurableSystem.{u}) (gseq : ℕ -> M.X -> ℂ) (g : M.X -> ℂ)
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hint : ∀ n, MeasureTheory.Integrable (gseq n) M.μ)
    (hg : MeasureTheory.Integrable g M.μ)
    (hae : ∀ᵐ x ∂M.μ, Tendsto (fun n => gseq n x) atTop (nhds (g x)))
    (hdom : (∫⁻ x, ⨆ n, ENNReal.ofReal ‖gseq n x‖ ∂M.μ) < ⊤) :
    (∀ᵐ x ∂M.μ, Tendsto (fun N => reverseVaryingErgodicAverage M gseq N x)
      atTop (nhds (invariantConditionalExpectation M g x))) ∧
    Tendsto (fun N => MeasureTheory.eLpNorm
      (fun x => reverseVaryingErgodicAverage M gseq N x -
        invariantConditionalExpectation M g x) 1 M.μ) atTop (nhds 0) := by
  sorry

/-- Source: Theorem 7.3.3 (Shannon--McMillan--Breiman). -/
theorem shannonMcMillanBreimanTheorem
    (M : MeasurableSystem.{u}) (α : CountableMeasurablePartition M)
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hfinite : countablePartitionEntropy M α < ⊤) :
    let g := fun x => countableConditionalInformation M α
      (countablePastSigmaAlgebra M α) x
    (∀ᵐ x ∂M.μ, Tendsto (fun N =>
      countableBlockInformation M α (N + 1) x / (N + 1 : ℝ)) atTop
        (nhds ((invariantConditionalExpectation M (fun y => (g y : ℂ)) x).re))) ∧
    Tendsto (fun N => MeasureTheory.eLpNorm (fun x =>
      (countableBlockInformation M α (N + 1) x / (N + 1 : ℝ) : ℂ) -
        invariantConditionalExpectation M (fun y => (g y : ℂ)) x) 1 M.μ)
      atTop (nhds 0) ∧
    Tendsto (fun N => countableBlockEntropy M α (N + 1) / (N + 1 : EReal))
      atTop (nhds (countablePartitionEntropyRate M α)) ∧
    (Chapter02.IsErgodic M ->
      (∀ᵐ x ∂M.μ, Tendsto (fun N =>
          countableBlockInformation M α (N + 1) x / (N + 1 : ℝ)) atTop
            (nhds (countablePartitionEntropyRate M α).toReal)) ∧
      Tendsto (fun N => MeasureTheory.eLpNorm (fun x =>
        (countableBlockInformation M α (N + 1) x / (N + 1 : ℝ) : ℂ) -
          ((countablePartitionEntropyRate M α).toReal : ℂ)) 1 M.μ)
        atTop (nhds 0)) := by
  sorry

/-- Source: Corollary 7.3.4. -/
theorem shannonMcMillanBreiman_typicalAtoms
    (M : MeasurableSystem.{u}) (α : CountableMeasurablePartition M)
    (hfinite : countablePartitionEntropy M α < ⊤)
    (hM : Chapter02.IsErgodic M) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n ->
      ∃ good bad : Set (Set M.X),
        good ∪ bad = countableBlockAtoms M α n ∧ Disjoint good bad ∧
        M.μ (⋃₀ bad) < ENNReal.ofReal δ ∧
        (∀ A ∈ good,
          Real.exp (-(n : ℝ) * ((countablePartitionEntropyRate M α).toReal + ε)) ≤
            (M.μ A).toReal ∧
          (M.μ A).toReal ≤
            Real.exp (-(n : ℝ) * ((countablePartitionEntropyRate M α).toReal - ε))) ∧
        Real.exp ((n : ℝ) * ((countablePartitionEntropyRate M α).toReal - ε)) ≤
          good.ncard ∧
        good.ncard ≤
          Real.exp ((n : ℝ) * ((countablePartitionEntropyRate M α).toReal + ε)) ∧
        ∃ E : Set M.X, MeasurableSet E ∧ M.μ E < ENNReal.ofReal δ ∧
          good.Finite ∧ (∀ A ∈ good, A ⊆ Eᶜ) := by
  sorry

end Section03
end Chapter07
