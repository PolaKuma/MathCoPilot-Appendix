import Chapter02.Spectral.OrderedSpectralDecomposition
import Chapter02.Spectral.DirectSumSpectralModel

open Classical

noncomputable section

namespace Chapter02.OrderedDirectSum

universe u

set_option maxRecDepth 100000 in
theorem directSumStatement (D : HilbertOperatorData.{u}) :
    DirectSumOfCyclicMultiplicationModelsStatement D := by
  intro hsep hD
  let hex := OrderedSpectralDecomposition.exists_orderedSpectralDecomposition D hsep hD
  let x := Classical.choose hex
  have hx : IsOrderedSpectralDecomposition D x := Classical.choose_spec hex
  choose μ hμ hμuniq using fun n ↦ SpectralMeasure.spectralMeasure D hD (x n)
  let W := DirectSumSpectralModel.directSumW D hD x μ hμ
  refine ⟨x, μ, W, hx, hμ, ?_, ?_⟩
  · exact DirectSumSpectralModel.directSumModel_of_orthogonal_decomposition
      D hD x μ hμ hx.1
  · intro n
    exact DirectSumSpectralModel.directSumW_basis D hD x μ hμ n

end Chapter02.OrderedDirectSum
