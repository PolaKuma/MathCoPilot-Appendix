import Chapter07.Section08

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter07

universe u v

namespace Section09

def IsHaarProbabilityMeasure {G : Type u} [TopologicalSpace G] [Group G]
    (μ : MeasureOn G) : Prop :=
  Chapter06.IsProbabilityBorelMeasure μ ∧
    ∀ a : G, ∀ B : Set G, @MeasurableSet G (borel G) B ->
      μ.measure ((fun x => a * x) ⁻¹' B) = μ.measure B

def affineGroupSystem {G : Type u} [TopologicalSpace G] [Group G]
    (a : G) (A : G →* G) : System.{u} where
  X := G
  topology := inferInstance
  T := fun x => a * A x

def groupEndomorphismSystem {G : Type u} [TopologicalSpace G] [Group G]
    (A : G →* G) : System.{u} where
  X := G
  topology := inferInstance
  T := A

def groupBowenBall {G : Type u} [TopologicalSpace G] [Group G]
    [PseudoMetricSpace G] (A : G →* G) (n : ℕ) (ε : ℝ) : Set G :=
  ⋂ i : Fin n, (A^[i.1]) ⁻¹' Metric.ball 1 ε

/-- Source: Theorem 7.9.1. -/
theorem compactAbelianGroup_affineEntropyFormula
    {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [PseudoMetricSpace G] [CompactSpace G]
    (a : G) (A : G →* G) (hA : Continuous A)
    (μ : MeasureOn G) (hhaar : IsHaarProbabilityMeasure μ)
    (hmetric : ∀ x y z : G, dist (z * x) (z * y) = dist x y) :
    entropyMap (affineGroupSystem a A) μ = entropyMap (groupEndomorphismSystem A) μ ∧
    entropyMap (groupEndomorphismSystem A) μ =
      topologicalEntropy (groupEndomorphismSystem A) ∧
    topologicalEntropy (groupEndomorphismSystem A) =
      topologicalEntropy (affineGroupSystem a A) ∧
    topologicalEntropy (affineGroupSystem a A) =
      sSup {r : EReal | ∃ ε : ℝ, 0 < ε ∧
        r = limsup (fun n : ℕ =>
          - ENNReal.log (μ.measure (groupBowenBall A (n + 1) ε)) /
            (n + 1 : EReal)) atTop} := by
  sorry

def IsLocalIsometricSurjectionAtScale
    (S : System.{u}) (R : System.{v}) [PseudoMetricSpace S.X]
    [PseudoMetricSpace R.X] (π : S.X -> R.X) (δ : ℝ) : Prop :=
  0 < δ ∧ Continuous π ∧ Function.Surjective π ∧
    ∀ x : S.X, Set.MapsTo π (Metric.ball x δ) (Metric.ball (π x) δ) ∧
      Set.SurjOn π (Metric.ball x δ) (Metric.ball (π x) δ) ∧
      ∀ y z, y ∈ Metric.ball x δ -> z ∈ Metric.ball x δ ->
        dist (π y) (π z) = dist y z

/-- Source: Theorem 7.9.2, entropy lifting through a locally isometric
surjection. -/
theorem entropyPreservedByLocallyIsometricLift
    (S : System.{u}) (R : System.{v}) [PseudoMetricSpace S.X]
    [PseudoMetricSpace R.X] (π : S.X -> R.X) (δ : ℝ)
    (hloc : IsLocalIsometricSurjectionAtScale S R π δ)
    (hsemiconj : π ∘ S.T = R.T ∘ π) :
    bowenMetricEntropy S = bowenMetricEntropy R := by
  sorry

def HasToralLinearLift (S : System.{u}) (R : System.{v})
    [PseudoMetricSpace S.X] [PseudoMetricSpace R.X] (lift : S.X -> R.X) : Prop :=
  ∃ δ : ℝ, IsLocalIsometricSurjectionAtScale S R lift δ ∧
    lift ∘ S.T = R.T ∘ lift

/-- Source: Corollary 7.9.3. -/
theorem toralAutomorphism_entropyEqualsLinearLiftEntropy
    (torusSystem : System.{u}) (linearLift : System.{v})
    [PseudoMetricSpace torusSystem.X] [PseudoMetricSpace linearLift.X]
    (π : linearLift.X -> torusSystem.X)
    (hlift : HasToralLinearLift linearLift torusSystem π) :
    bowenMetricEntropy torusSystem = bowenMetricEntropy linearLift := by
  sorry

def realLinearSystem {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : System.{0} where
  X := Fin d -> ℝ
  topology := inferInstance
  T := A.mulVec

def IsComplexEigenvalueList {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (eigenvalues : Fin d -> ℂ) : Prop :=
  A.charpoly.map (algebraMap ℝ ℂ) =
    ∏ i : Fin d, (Polynomial.X - Polynomial.C (eigenvalues i))

def realLinearBowenEntropy {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) : EReal := by
  letI : PseudoMetricSpace (realLinearSystem A).X :=
    inferInstanceAs (PseudoMetricSpace (Fin d -> ℝ))
  exact bowenMetricEntropy (realLinearSystem A)

def realLinearBowenBall {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (ε : ℝ) : Set (Fin d -> ℝ) :=
  ⋂ i : Fin n, (A.mulVec^[i.1]) ⁻¹' Metric.ball 0 ε

/-- Source: Lemma 7.9.4, the Bowen-ball volume formula and norm
independence, packaged at the level needed by Theorem 7.9.5. -/
theorem linearMap_volumeGrowthFormula
    {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    realLinearBowenEntropy A =
      sSup {r : EReal | ∃ ε : ℝ, 0 < ε ∧
        r = limsup (fun n : ℕ =>
          - ENNReal.log (MeasureTheory.volume
            (realLinearBowenBall A (n + 1) ε)) / (n + 1 : EReal)) atTop} := by
  sorry

/-- Source: Theorem 7.9.5. -/
theorem finiteDimensionalLinearMap_entropyFormula
    {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (eigenvalues : Fin d -> ℂ)
    (heigen : IsComplexEigenvalueList A eigenvalues) :
    realLinearBowenEntropy A =
      ∑ i : Fin d, (max 0 (Real.log ‖eigenvalues i‖) : ℝ) := by
  sorry

def IsToralAffineRealization {d : ℕ}
    (S : System.{u}) (A : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ L : System.{0}, L = realLinearSystem A ∧
    ∃ _ : PseudoMetricSpace S.X, ∃ _ : PseudoMetricSpace L.X,
      ∃ π : L.X -> S.X, HasToralLinearLift L S π

/-- Source: Theorem 7.9.6. -/
theorem toralAffineMap_entropyFormula
    {d : ℕ} (S : System.{u}) (A : Matrix (Fin d) (Fin d) ℝ)
    (eigenvalues : Fin d -> ℂ) (μ : MeasureOn S.X)
    (htorus : IsToralAffineRealization S A)
    (heigen : IsComplexEigenvalueList A eigenvalues)
    (hhaar : Chapter06.IsInvariantMeasure S μ) :
    topologicalEntropy S = entropyMap S μ ∧
      entropyMap S μ = ∑ i : Fin d, (max 0 (Real.log ‖eigenvalues i‖) : ℝ) := by
  sorry

end Section09
end Chapter07
