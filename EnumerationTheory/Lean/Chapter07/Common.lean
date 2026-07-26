import Chapter06.Section05
import Mathlib.Dynamics.TopologicalEntropy.NetEntropy

noncomputable section

open Classical Filter
open scoped BigOperators

set_option linter.unusedVariables false

namespace Chapter07

universe u v w

abbrev System := Chapter06.System
abbrev MeasurableSystem := Chapter06.MeasurableSystem
abbrev MeasureOn := Chapter06.MeasureOn

/-- The probability-space hypothesis used throughout the nondynamical part of
Chapter 7.  `MeasurableSystem` is deliberately only raw data, so the hypothesis
must not be silently omitted from entropy statements. -/
def IsProbabilityMeasurableSystem (M : MeasurableSystem.{u}) : Prop :=
  MeasureTheory.IsProbabilityMeasure M.μ

def measurableSets (M : MeasurableSystem.{u}) : Set (Set M.X) :=
  {A | @MeasurableSet M.X M.measurableSpace A}

def measurableIterateSystem (M : MeasurableSystem.{u}) (n : ℕ) : MeasurableSystem.{u} where
  X := M.X
  measurableSpace := M.measurableSpace
  μ := M.μ
  T := M.T^[n]

def measurableIntegerPowerSystem (M : MeasurableSystem.{u})
    (inv : M.X -> M.X) (n : ℤ) : MeasurableSystem.{u} where
  X := M.X
  measurableSpace := M.measurableSpace
  μ := M.μ
  T := if 0 ≤ n then M.T^[n.toNat] else inv^[n.natAbs]

structure FiniteMeasurablePartition (M : MeasurableSystem.{u}) where
  atoms : Finset (Set M.X)
  measurable_atoms : ∀ A ∈ atoms, A ∈ M.𝓧
  covers_univ : ⋃₀ (atoms : Set (Set M.X)) = Set.univ
  pairwise_disjoint : ∀ A ∈ atoms, ∀ B ∈ atoms, A ≠ B -> Disjoint A B

def finitePartitionForMap (M : MeasurableSystem.{u}) (T : M.X -> M.X)
    (α : FiniteMeasurablePartition M) : FiniteMeasurablePartition { M with T := T } where
  atoms := α.atoms
  measurable_atoms := α.measurable_atoms
  covers_univ := α.covers_univ
  pairwise_disjoint := α.pairwise_disjoint

structure CountableMeasurablePartition (M : MeasurableSystem.{u}) where
  atoms : ℕ -> Set M.X
  measurable_atoms : ∀ n, atoms n ∈ M.𝓧
  covers_univ : (⋃ n, atoms n) = Set.univ
  pairwise_disjoint : ∀ m n, m ≠ n -> Disjoint (atoms m) (atoms n)

def countablePartitionEntropy (M : MeasurableSystem.{u})
    (α : CountableMeasurablePartition M) : EReal :=
  ∑' n : ℕ, ((- (M.μ (α.atoms n)).toReal *
    Real.log (M.μ (α.atoms n)).toReal : ℝ) : EReal)

def countableBlockAtom (M : MeasurableSystem.{u})
    (α : CountableMeasurablePartition M) (n : ℕ) (x : M.X) : Set M.X :=
  {y | ∀ i : Fin n, ∀ j : ℕ,
    (M.T^[i.1]) x ∈ α.atoms j ↔ (M.T^[i.1]) y ∈ α.atoms j}

def countableBlockInformation (M : MeasurableSystem.{u})
    (α : CountableMeasurablePartition M) (n : ℕ) (x : M.X) : ℝ :=
  - Real.log (M.μ (countableBlockAtom M α n x)).toReal

def countableBlockEntropy (M : MeasurableSystem.{u})
    (α : CountableMeasurablePartition M) (n : ℕ) : EReal :=
  ∑' word : Fin n -> ℕ,
    let A := {x | ∀ i : Fin n, (M.T^[i.1]) x ∈ α.atoms (word i)}
    ((- (M.μ A).toReal * Real.log (M.μ A).toReal : ℝ) : EReal)

def countableBlockAtoms (M : MeasurableSystem.{u})
    (α : CountableMeasurablePartition M) (n : ℕ) : Set (Set M.X) :=
  Set.range fun word : Fin n -> ℕ =>
    {x | ∀ i : Fin n, (M.T^[i.1]) x ∈ α.atoms (word i)}

def countablePartitionEntropyRate (M : MeasurableSystem.{u})
    (α : CountableMeasurablePartition M) : EReal :=
  sInf {r : EReal | ∃ n : ℕ, 0 < n ∧
    r = countableBlockEntropy M α n / (n : EReal)}

def partitionEntropy (M : MeasurableSystem.{u}) (α : FiniteMeasurablePartition M) : ℝ :=
  α.atoms.sum fun A => - (M.μ A).toReal * Real.log (M.μ A).toReal

def informationFunction (M : MeasurableSystem.{u}) (α : FiniteMeasurablePartition M) :
    M.X -> ℝ :=
  fun x => α.atoms.sum fun A => if x ∈ A then - Real.log (M.μ A).toReal else 0

def IsConditionalProbabilityVersion (M : MeasurableSystem.{u})
    (A : Set M.X) (𝒯 : Set (Set M.X)) (g : M.X -> ℝ) : Prop :=
  Chapter00.IsMeasurableForFamily 𝒯 (fun x => (g x : ℂ)) ∧
    MeasureTheory.Integrable g M.μ ∧ (∀ᵐ x ∂M.μ, 0 ≤ g x) ∧
    ∀ B ∈ 𝒯, MeasurableSet B ->
      ∫ x in B, g x ∂M.μ = (M.μ (A ∩ B)).toReal

def conditionalProbability (M : MeasurableSystem.{u})
    (A : Set M.X) (𝒯 : Set (Set M.X)) (x : M.X) : ℝ :=
  MeasureTheory.condExp (MeasurableSpace.generateFrom 𝒯) M.μ
    (A.indicator fun _ => (1 : ℝ)) x

theorem conditionalProbability_spec (M : MeasurableSystem.{u})
    (A : Set M.X) (𝒯 : Set (Set M.X))
    (hμ : MeasureTheory.IsProbabilityMeasure M.μ)
    (hA : MeasurableSet A)
    (h𝒯 : Chapter00.IsSigmaAlgebraFamily 𝒯) (hsub : 𝒯 ⊆ M.𝓧) :
    IsConditionalProbabilityVersion M A 𝒯 (conditionalProbability M A 𝒯) := by
  sorry

def conditionalInformation (M : MeasurableSystem.{u}) (α : FiniteMeasurablePartition M)
    (𝒯 : Set (Set M.X)) : M.X -> ℝ :=
  fun x => α.atoms.sum fun A =>
    if x ∈ A then - Real.log (conditionalProbability M A 𝒯 x) else 0

def countablePastSigmaAlgebra (M : MeasurableSystem.{u})
    (α : CountableMeasurablePartition M) : Set (Set M.X) :=
  Chapter00.generatedSigmaAlgebra
    {A | ∃ n : ℕ, 0 < n ∧ ∃ j : ℕ, A = (M.T^[n]) ⁻¹' α.atoms j}

def countableConditionalInformation (M : MeasurableSystem.{u})
    (α : CountableMeasurablePartition M) (F : Set (Set M.X)) (x : M.X) : ℝ :=
  ∑' j : ℕ, if x ∈ α.atoms j then
    - Real.log (conditionalProbability M (α.atoms j) F x) else 0

def countableConditionalEntropy (M : MeasurableSystem.{u})
    (α : CountableMeasurablePartition M) (F : Set (Set M.X)) : ℝ :=
  ∫ x, countableConditionalInformation M α F x ∂M.μ

def countablePartitionSigmaAlgebra (M : MeasurableSystem.{u})
    (α : CountableMeasurablePartition M) : Set (Set M.X) :=
  Chapter00.generatedSigmaAlgebra (Set.range α.atoms)

def countableJoinConditionalInformation (M : MeasurableSystem.{u})
    (α β : CountableMeasurablePartition M) (F : Set (Set M.X)) (x : M.X) : ℝ :=
  ∑' p : ℕ × ℕ, if x ∈ α.atoms p.1 ∩ β.atoms p.2 then
    - Real.log (conditionalProbability M (α.atoms p.1 ∩ β.atoms p.2) F x) else 0

def countableJoinConditionalEntropy (M : MeasurableSystem.{u})
    (α β : CountableMeasurablePartition M) (F : Set (Set M.X)) : ℝ :=
  ∫ x, countableJoinConditionalInformation M α β F x ∂M.μ

def conditionalEntropy (M : MeasurableSystem.{u}) (α : FiniteMeasurablePartition M)
    (𝓕 : Set (Set M.X)) : ℝ :=
  (M.integral fun x => (conditionalInformation M α 𝓕 x : ℂ)).re

def joinPartition (M : MeasurableSystem.{u}) (α β : FiniteMeasurablePartition M) :
    FiniteMeasurablePartition M :=
  { atoms := (α.atoms.product β.atoms).image (fun p => p.1 ∩ p.2)
    measurable_atoms := by
      intro C hC
      rcases Finset.mem_image.mp hC with ⟨p, hp, rfl⟩
      exact (α.measurable_atoms p.1 (Finset.mem_product.mp hp).1).inter
        (β.measurable_atoms p.2 (Finset.mem_product.mp hp).2)
    covers_univ := by
      apply Set.eq_univ_of_univ_subset
      intro x _
      have hxα : x ∈ ⋃₀ (α.atoms : Set (Set M.X)) := by rw [α.covers_univ]; trivial
      have hxβ : x ∈ ⋃₀ (β.atoms : Set (Set M.X)) := by rw [β.covers_univ]; trivial
      rcases hxα with ⟨A, hA, hxA⟩
      rcases hxβ with ⟨B, hB, hxB⟩
      refine ⟨A ∩ B, ?_, hxA, hxB⟩
      simp only [Finset.coe_image, Set.mem_image]
      exact ⟨(A, B), by simp_all, rfl⟩
    pairwise_disjoint := by
      intro C hC D hD hCD
      rcases Finset.mem_image.mp hC with ⟨p, hp, rfl⟩
      rcases Finset.mem_image.mp hD with ⟨q, hq, rfl⟩
      rw [Set.disjoint_left]
      intro x hxp hxq
      by_cases hfirst : p.1 = q.1
      · have hsecond : p.2 ≠ q.2 := by
          intro hs
          apply hCD
          simp [hfirst, hs]
        exact (Set.disjoint_left.1 (β.pairwise_disjoint p.2
          (Finset.mem_product.mp hp).2 q.2 (Finset.mem_product.mp hq).2 hsecond))
          hxp.2 hxq.2
      · exact (Set.disjoint_left.1 (α.pairwise_disjoint p.1
          (Finset.mem_product.mp hp).1 q.1 (Finset.mem_product.mp hq).1 hfirst))
          hxp.1 hxq.1 }

def pullbackPartition (M : MeasurableSystem.{u}) (α : FiniteMeasurablePartition M) :
    FiniteMeasurablePartition M :=
  if h : ∀ A ∈ α.atoms, M.T ⁻¹' A ∈ M.𝓧 then
    { atoms := α.atoms.image (fun A => M.T ⁻¹' A)
      measurable_atoms := by
        intro B hB
        rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
        exact h A hA
      covers_univ := by
        apply Set.eq_univ_of_univ_subset
        intro x _
        have hx : M.T x ∈ ⋃₀ (α.atoms : Set (Set M.X)) := by
          rw [α.covers_univ]
          trivial
        rcases hx with ⟨A, hA, hxA⟩
        exact ⟨M.T ⁻¹' A, by simpa using Finset.mem_image.mpr ⟨A, hA, rfl⟩, hxA⟩
      pairwise_disjoint := by
        intro B hB C hC hBC
        rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
        rcases Finset.mem_image.mp hC with ⟨D, hD, rfl⟩
        have hAD : A ≠ D := by
          intro had
          apply hBC
          simp [had]
        exact (α.pairwise_disjoint A hA D hD hAD).preimage M.T }
  else α

/-- The pullback `(T^[n])⁻¹ α`.  The fallback branch only makes this a total
definition on raw data; all entropy theorems use it under the measurable-map
hypothesis, where the first branch is selected. -/
def pullbackPartitionByIterate (M : MeasurableSystem.{u})
    (α : FiniteMeasurablePartition M) (n : ℕ) : FiniteMeasurablePartition M :=
  if h : ∀ A ∈ α.atoms,
      @MeasurableSet M.X M.measurableSpace ((M.T^[n]) ⁻¹' A) then
    { atoms := α.atoms.image (fun A => (M.T^[n]) ⁻¹' A)
      measurable_atoms := by
        intro B hB
        rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
        exact h A hA
      covers_univ := by
        apply Set.eq_univ_of_univ_subset
        intro x _
        have hx : (M.T^[n]) x ∈ ⋃₀ (α.atoms : Set (Set M.X)) := by
          rw [α.covers_univ]
          trivial
        rcases hx with ⟨A, hA, hxA⟩
        exact ⟨(M.T^[n]) ⁻¹' A,
          by simpa using Finset.mem_image.mpr ⟨A, hA, rfl⟩, hxA⟩
      pairwise_disjoint := by
        intro B hB C hC hBC
        rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
        rcases Finset.mem_image.mp hC with ⟨D, hD, rfl⟩
        have hAD : A ≠ D := by
          intro had
          apply hBC
          simp [had]
        exact (α.pairwise_disjoint A hA D hD hAD).preimage (M.T^[n]) }
  else α

def trivialMeasurablePartition (M : MeasurableSystem.{u}) :
    FiniteMeasurablePartition M where
  atoms := {Set.univ}
  measurable_atoms := by
    intro A hA
    have h : A = Set.univ := by simpa using hA
    subst A
    exact MeasurableSet.univ
  covers_univ := by simp
  pairwise_disjoint := by simp

def partitionRefines (M : MeasurableSystem.{u}) (α β : FiniteMeasurablePartition M) : Prop :=
  ∀ A ∈ α.atoms, ∃ B ∈ β.atoms, A ⊆ B

def isSubSigmaAlgebra (M : MeasurableSystem.{u}) (𝓕 : Set (Set M.X)) : Prop :=
  Set.univ ∈ 𝓕 ∧ (∀ A ∈ 𝓕, Aᶜ ∈ 𝓕) ∧ (∀ s : ℕ -> Set M.X, (∀ n, s n ∈ 𝓕) -> (⋃ n, s n) ∈ 𝓕) ∧
    ∀ A ∈ 𝓕, A ∈ M.𝓧

/-- Conditional probabilities exist for measurable events relative to a
sub-sigma-algebra of a probability space. -/
theorem conditionalProbability_exists (M : MeasurableSystem.{u})
    (hprob : IsProbabilityMeasurableSystem M)
    (A : Set M.X) (hA : MeasurableSet A) (𝒯 : Set (Set M.X))
    (h𝒯 : isSubSigmaAlgebra M 𝒯) :
    ∃ g : M.X -> ℝ, IsConditionalProbabilityVersion M A 𝒯 g := by
  sorry

def partitionMeasurableWith (M : MeasurableSystem.{u}) (α : FiniteMeasurablePartition M)
    (𝓕 : Set (Set M.X)) : Prop :=
  ∀ A ∈ α.atoms, A ∈ 𝓕

def independentPartitions (M : MeasurableSystem.{u}) (α β : FiniteMeasurablePartition M) :
    Prop :=
  ∀ A ∈ α.atoms, ∀ B ∈ β.atoms, M.μ (A ∩ B) = M.μ A * M.μ B

def iteratedJoinPartition (M : MeasurableSystem.{u}) (α : FiniteMeasurablePartition M) :
    ℕ -> FiniteMeasurablePartition M
  | 0 => trivialMeasurablePartition M
  | n + 1 => joinPartition M (iteratedJoinPartition M α n)
      (pullbackPartitionByIterate M α n)

def finitePartitionSequenceJoin (M : MeasurableSystem.{u})
    (α : ℕ -> FiniteMeasurablePartition M) : ℕ -> FiniteMeasurablePartition M
  | 0 => trivialMeasurablePartition M
  | n + 1 => joinPartition M (finitePartitionSequenceJoin M α n) (α n)

def partitionEntropyRate (M : MeasurableSystem.{u}) (α : FiniteMeasurablePartition M) : ℝ :=
  sInf {r : ℝ | ∃ n : ℕ, 0 < n ∧
    r = partitionEntropy M (iteratedJoinPartition M α n) / (n : ℝ)}

def measureEntropy (M : MeasurableSystem.{u}) : EReal :=
  sSup {r : EReal | ∃ α : FiniteMeasurablePartition M,
    r = (partitionEntropyRate M α : EReal)}

def finitePartitionSigmaAlgebra (M : MeasurableSystem.{u})
    (α : FiniteMeasurablePartition M) : Set (Set M.X) :=
  Chapter00.generatedSigmaAlgebra {A | A ∈ α.atoms}

def partitionDistance (M : MeasurableSystem.{u}) (α β : FiniteMeasurablePartition M) : ℝ :=
  conditionalEntropy M α (finitePartitionSigmaAlgebra M β) +
    conditionalEntropy M β (finitePartitionSigmaAlgebra M α)

structure OpenCover (X : Type u) [TopologicalSpace X] where
  sets : Set (Set X)
  is_open : ∀ U ∈ sets, IsOpen U
  covers_univ : ⋃₀ sets = Set.univ

/-- A cover of a bare set, used for the combinatorial entropy statements that
precede the topological specialization in Section 7.4. -/
structure SetCover (X : Type u) where
  sets : Set (Set X)
  covers_univ : ⋃₀ sets = Set.univ

def setCoverNumber {X : Type u} (𝓤 : SetCover X) : ENNReal :=
  sInf {n : ENNReal | ∃ F : Finset (Set X), (∀ U ∈ F, U ∈ 𝓤.sets) ∧
    ⋃₀ (F : Set (Set X)) = Set.univ ∧ n = F.card}

def setCoverEntropy {X : Type u} (𝓤 : SetCover X) : EReal :=
  ENNReal.log (setCoverNumber 𝓤)

def setCoverRefines {X : Type u} (𝓤 𝓥 : SetCover X) : Prop :=
  ∀ U ∈ 𝓤.sets, ∃ V ∈ 𝓥.sets, U ⊆ V

def setCoverJoin {X : Type u} (𝓤 𝓥 : SetCover X) : SetCover X where
  sets := {W | ∃ U ∈ 𝓤.sets, ∃ V ∈ 𝓥.sets, W = U ∩ V}
  covers_univ := by
    apply Set.eq_univ_of_univ_subset
    intro x _
    have hxU : x ∈ ⋃₀ 𝓤.sets := by rw [𝓤.covers_univ]; trivial
    have hxV : x ∈ ⋃₀ 𝓥.sets := by rw [𝓥.covers_univ]; trivial
    rcases hxU with ⟨U, hU, hxU⟩
    rcases hxV with ⟨V, hV, hxV⟩
    exact ⟨U ∩ V, ⟨U, hU, V, hV, rfl⟩, hxU, hxV⟩

def setCoverPullback {X : Type u} (T : X -> X) (𝓤 : SetCover X) : SetCover X where
  sets := {V | ∃ U ∈ 𝓤.sets, V = T ⁻¹' U}
  covers_univ := by
    apply Set.eq_univ_of_univ_subset
    intro x _
    have hx : T x ∈ ⋃₀ 𝓤.sets := by rw [𝓤.covers_univ]; trivial
    rcases hx with ⟨U, hU, hxU⟩
    exact ⟨T ⁻¹' U, ⟨U, hU, rfl⟩, hxU⟩

def trivialSetCover (X : Type u) : SetCover X where
  sets := {Set.univ}
  covers_univ := by
    simp

def iteratedSetCoverPullback {X : Type u} (T : X -> X) (𝓤 : SetCover X) :
    ℕ -> SetCover X
  | 0 => 𝓤
  | n + 1 => setCoverPullback T (iteratedSetCoverPullback T 𝓤 n)

def setCoverIterateJoin {X : Type u} (T : X -> X) (𝓤 : SetCover X) :
    ℕ -> SetCover X
  | 0 => trivialSetCover X
  | n + 1 => setCoverJoin (setCoverIterateJoin T 𝓤 n)
      (iteratedSetCoverPullback T 𝓤 n)

def combinatorialCoverEntropyRate {X : Type u} (T : X -> X) (𝓤 : SetCover X) : EReal :=
  sInf {r : EReal | ∃ n : ℕ, 0 < n ∧
    r = setCoverEntropy (setCoverIterateJoin T 𝓤 n) / (n : EReal)}

def coverNumber {X : Type u} [TopologicalSpace X] (𝓤 : OpenCover X) : ENNReal :=
  sInf {n : ENNReal | ∃ F : Finset (Set X), (∀ U ∈ F, U ∈ 𝓤.sets) ∧
    ⋃₀ (F : Set (Set X)) = Set.univ ∧ n = F.card}

def coverEntropy {X : Type u} [TopologicalSpace X] (𝓤 : OpenCover X) : EReal :=
  ENNReal.log (coverNumber 𝓤)

def coverRefines {X : Type u} [TopologicalSpace X] (𝓤 𝓥 : OpenCover X) : Prop :=
  ∀ U ∈ 𝓤.sets, ∃ V ∈ 𝓥.sets, U ⊆ V

def coverJoin {X : Type u} [TopologicalSpace X] (𝓤 𝓥 : OpenCover X) : OpenCover X where
  sets := {W | ∃ U ∈ 𝓤.sets, ∃ V ∈ 𝓥.sets, W = U ∩ V}
  is_open := by
    rintro W ⟨U, hU, V, hV, rfl⟩
    exact (𝓤.is_open U hU).inter (𝓥.is_open V hV)
  covers_univ := by
    apply Set.eq_univ_of_univ_subset
    intro x _
    have hxU : x ∈ ⋃₀ 𝓤.sets := by rw [𝓤.covers_univ]; trivial
    have hxV : x ∈ ⋃₀ 𝓥.sets := by rw [𝓥.covers_univ]; trivial
    rcases hxU with ⟨U, hU, hxU⟩
    rcases hxV with ⟨V, hV, hxV⟩
    exact ⟨U ∩ V, ⟨U, hU, V, hV, rfl⟩, hxU, hxV⟩

def pullbackCover (S : System.{u}) (𝓤 : OpenCover S.X) : OpenCover S.X :=
  if h : Continuous S.T then
    { sets := {V | ∃ U ∈ 𝓤.sets, V = S.T ⁻¹' U}
      is_open := by
        rintro V ⟨U, hU, rfl⟩
        exact (𝓤.is_open U hU).preimage h
      covers_univ := by
        apply Set.eq_univ_of_univ_subset
        intro x _
        have hx : S.T x ∈ ⋃₀ 𝓤.sets := by rw [𝓤.covers_univ]; trivial
        rcases hx with ⟨U, hU, hxU⟩
        exact ⟨S.T ⁻¹' U, ⟨U, hU, rfl⟩, hxU⟩ }
  else 𝓤

/-- The one-element cover used as the empty join. -/
def trivialOpenCover (X : Type u) [TopologicalSpace X] : OpenCover X where
  sets := {Set.univ}
  is_open := by
    intro U hU
    have hU' : U = Set.univ := by simpa using hU
    rw [hU']
    exact isOpen_univ
  covers_univ := by
    simp

/-- The cover `(T^[n])⁻¹ 𝓤`, formed recursively.  For a topological dynamical
system the continuity assumption makes every recursive pullback genuine. -/
def iteratedPullbackCover (S : System.{u}) (𝓤 : OpenCover S.X) : ℕ -> OpenCover S.X
  | 0 => 𝓤
  | n + 1 => pullbackCover S (iteratedPullbackCover S 𝓤 n)

def coverIterateJoin (S : System.{u}) (𝓤 : OpenCover S.X) : ℕ -> OpenCover S.X
  | 0 => trivialOpenCover S.X
  | n + 1 => coverJoin (coverIterateJoin S 𝓤 n) (iteratedPullbackCover S 𝓤 n)

def topologicalCoverEntropyRate (S : System.{u}) (𝓤 : OpenCover S.X) : EReal :=
  sInf {r : EReal | ∃ n : ℕ, 0 < n ∧
    r = coverEntropy (coverIterateJoin S 𝓤 n) / (n : EReal)}

def topologicalEntropy (S : System.{u}) : EReal :=
  sSup {r : EReal | ∃ 𝓤 : OpenCover S.X, r = topologicalCoverEntropyRate S 𝓤}

/-- The diameter of a cover is the supremum of the diameters of its members. -/
def openCoverDiameter (S : System.{u}) [PseudoMetricSpace S.X]
    (cover : OpenCover S.X) : ℝ :=
  sSup {r : ℝ | ∃ U ∈ cover.sets, r = Metric.diam U}

/-- The system whose time-one map is the `m`-th positive iterate. -/
def iterateSystem (S : System.{u}) (m : ℕ) : System.{u} where
  X := S.X
  topology := S.topology
  T := S.T^[m]

/-- The system whose time-one map is an integer iterate of a specified
continuous inverse. -/
def integerPowerSystem (S : System.{u}) (inv : S.X -> S.X) (m : ℤ) : System.{u} where
  X := S.X
  topology := S.topology
  T := Chapter05.ziterate S inv m

/-- The product of two topological systems. -/
def productSystem (S : System.{u}) (R : System.{v}) : System.{max u v} where
  X := S.X × R.X
  topology := inferInstance
  T := fun p => (S.T p.1, R.T p.2)

/-- The join of the pullbacks `T^{-i} cover`, for `-n ≤ i ≤ n`, using a
specified inverse. -/
def twoSidedCoverIterateJoin (S : System.{u}) [PseudoMetricSpace S.X]
    (inv : S.X -> S.X) (_hT : Continuous S.T)
    (_hinv : Chapter05.IsContinuousInverse S inv)
    (cover : OpenCover S.X) (n : ℕ) : OpenCover S.X where
  sets := {W | ∃ choice : {i : ℤ // i ∈ Set.Icc (-(n : ℤ)) (n : ℤ)} -> Set S.X,
    (∀ i, choice i ∈ cover.sets) ∧
      W = ⋂ i, (Chapter05.ziterate S inv i.1) ⁻¹' choice i}
  is_open := by
    rintro W ⟨choice, hchoice, rfl⟩
    apply isOpen_iInter_of_finite
    intro i
    apply (cover.is_open (choice i) (hchoice i)).preimage
    unfold Chapter05.ziterate
    split_ifs
    · exact _hT.iterate _
    · exact _hinv.1.iterate _
  covers_univ := by
    apply Set.eq_univ_of_univ_subset
    intro x _
    have hx : ∀ i : {i : ℤ // i ∈ Set.Icc (-(n : ℤ)) (n : ℤ)},
        ∃ U ∈ cover.sets, Chapter05.ziterate S inv i.1 x ∈ U := by
      intro i
      have hxi : Chapter05.ziterate S inv i.1 x ∈ ⋃₀ cover.sets := by
        rw [cover.covers_univ]
        trivial
      simpa only [Set.mem_sUnion] using hxi
    choose choice hchoice hxchoice using hx
    refine ⟨⋂ i, (Chapter05.ziterate S inv i.1) ⁻¹' choice i, ?_, ?_⟩
    · exact ⟨choice, hchoice, rfl⟩
    · simp only [Set.mem_iInter, Set.mem_preimage]
      exact hxchoice

/-- Restriction of a topological system to an invariant subset. -/
def restrictedSystem (S : System.{u}) (A : Set S.X) (hA : Set.MapsTo S.T A A) : System.{u} where
  X := A
  topology := inferInstance
  T := fun x => ⟨S.T x, hA x.property⟩

/-- The nonwandering set is forward invariant for a continuous map. -/
theorem nonwanderingSet_mapsTo (S : System.{u}) (_hT : Continuous S.T) :
    Set.MapsTo S.T (Chapter05.nonwanderingSet S) (Chapter05.nonwanderingSet S) := by
  intro x hx U hU hTxU
  have hpreOpen : IsOpen (S.T ⁻¹' U) := hU.preimage _hT
  rcases hx (S.T ⁻¹' U) hpreOpen hTxU with ⟨n, hn, y, hy, hyn⟩
  refine ⟨n, hn, S.T y, hy, ?_⟩
  have hcomm : ∀ k : ℕ, ∀ z : S.X,
      (S.T^[k]) (S.T z) = S.T ((S.T^[k]) z) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro z
        simpa [Function.iterate_succ_apply] using ih (S.T z)
  change (S.T^[n]) (S.T y) ∈ U
  rw [hcomm n]
  exact hyn

/-- The subsystem obtained by restricting a continuous system to its
nonwandering set. -/
def nonwanderingRestrictedSystem (S : System.{u}) (hT : Continuous S.T) : System.{u} :=
  restrictedSystem S (Chapter05.nonwanderingSet S) (nonwanderingSet_mapsTo S hT)

def eventualRange (S : System.{u}) : Set S.X :=
  ⋂ n : ℕ, Set.range (S.T^[n])

theorem eventualRange_mapsTo (S : System.{u}) :
    Set.MapsTo S.T (eventualRange S) (eventualRange S) := by
  intro x hx
  rw [eventualRange] at hx ⊢
  simp only [Set.mem_iInter] at hx ⊢
  intro n
  cases n with
  | zero =>
      exact ⟨S.T x, by simp⟩
  | succ n =>
      rcases hx n with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      have hcomm : ∀ k : ℕ, ∀ z : S.X,
          (S.T^[k]) (S.T z) = S.T ((S.T^[k]) z) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
            intro z
            simpa [Function.iterate_succ_apply] using ih (S.T z)
      rw [Function.iterate_succ_apply, hcomm n, hy]

def eventualRangeSystem (S : System.{u}) : System.{u} :=
  restrictedSystem S (eventualRange S) (eventualRange_mapsTo S)

/-- A measurable system regarded as a topological system on the same type and
with the same transformation. -/
def topologicalSystemOfMeasurable (M : MeasurableSystem.{u})
    [TopologicalSpace M.X] : System.{u} where
  X := M.X
  topology := inferInstance
  T := M.T

/-- The diameter of a finite measurable partition. -/
def finitePartitionDiameter (M : MeasurableSystem.{u}) [PseudoMetricSpace M.X]
    (ξ : FiniteMeasurablePartition M) : ℝ :=
  sSup {r : ℝ | ∃ A ∈ ξ.atoms, r = Metric.diam A}

/-- The family of all atoms in all two-sided iterates of a partition. -/
def twoSidedPartitionOrbitSets (M : MeasurableSystem.{u}) [TopologicalSpace M.X]
    (inv : M.X -> M.X) (ξ : FiniteMeasurablePartition M) : Set (Set M.X) :=
  {A | ∃ n : ℤ, ∃ B ∈ ξ.atoms,
    A = (Chapter05.ziterate (topologicalSystemOfMeasurable M) inv n) ⁻¹' B}

/-- The full two-sided shift on `k` symbols. -/
abbrev FullShiftSpace (k : ℕ) := ℤ -> Fin k

def shiftMap {k : ℕ} (x : FullShiftSpace k) : FullShiftSpace k :=
  fun n => x (n + 1)

def fullShiftSystem (k : ℕ) : System.{0} where
  X := FullShiftSpace k
  topology := inferInstance
  T := shiftMap

/-- The system induced by the shift on a forward-invariant subshift. -/
def subshiftSystem (k : ℕ) (Y : Set (FullShiftSpace k))
    (hY : Set.MapsTo shiftMap Y Y) : System.{0} :=
  restrictedSystem (fullShiftSystem k) Y hY

/-- The length-`n` words occurring at coordinates `0,…,n-1` in `Y`. -/
def subshiftLanguage (k : ℕ) (Y : Set (FullShiftSpace k)) (n : ℕ) :
    Finset (Fin n -> Fin k) :=
  Finset.univ.filter fun w => ∃ x ∈ Y, ∀ i : Fin n, x (i : ℤ) = w i

def subshiftWordComplexity (k : ℕ) (Y : Set (FullShiftSpace k)) (n : ℕ) : ℕ :=
  (subshiftLanguage k Y n).card

/-- A zero-one matrix. -/
def IsZeroOneMatrix {k : ℕ} (A : Fin k -> Fin k -> ℕ) : Prop :=
  ∀ i j, A i j = 0 ∨ A i j = 1

/-- Irreducibility expressed by a positive-length admissible path between every
ordered pair of states. -/
def IsIrreducibleMatrix {k : ℕ} (A : Fin k -> Fin k -> ℕ) : Prop :=
  ∀ i j, ∃ n : ℕ, 0 < n ∧ ∃ p : Fin (n + 1) -> Fin k,
    p 0 = i ∧ p (Fin.last n) = j ∧
      ∀ t : Fin n, A (p t.castSucc) (p t.succ) = 1

/-- `ρ` is the largest positive real eigenvalue of a nonnegative matrix. -/
def IsPerronRoot {k : ℕ} (A : Fin k -> Fin k -> ℕ) (ρ : ℝ) : Prop :=
  0 < ρ ∧
    (∃ v : Fin k -> ℝ, (∀ i, 0 < v i) ∧
      ∀ i, ∑ j, (A i j : ℝ) * v j = ρ * v i) ∧
    ∀ r : ℝ, 0 < r ->
      (∃ v : Fin k -> ℝ, v ≠ 0 ∧
        ∀ i, ∑ j, (A i j : ℝ) * v j = r * v i) -> r ≤ ρ

def markovShiftSpace {k : ℕ} (A : Fin k -> Fin k -> ℕ) :
    Set (FullShiftSpace k) :=
  {x | ∀ n : ℤ, A (x n) (x (n + 1)) = 1}

theorem shiftMap_mapsTo_markovShiftSpace {k : ℕ}
    (A : Fin k -> Fin k -> ℕ) :
    Set.MapsTo shiftMap (markovShiftSpace A) (markovShiftSpace A) := by
  intro x hx n
  exact hx (n + 1)

def markovShiftSystem {k : ℕ} (A : Fin k -> Fin k -> ℕ) : System.{0} :=
  subshiftSystem k (markovShiftSpace A) (shiftMap_mapsTo_markovShiftSpace A)

/-- The one-sided full shift on `k` symbols. -/
abbrev OneSidedShiftSpace (k : ℕ) := ℕ -> Fin k

def oneSidedShiftMap {k : ℕ} (x : OneSidedShiftSpace k) : OneSidedShiftSpace k :=
  fun n => x (n + 1)

def oneSidedFullShiftSystem (k : ℕ) : System.{0} where
  X := OneSidedShiftSpace k
  topology := inferInstance
  T := oneSidedShiftMap

/-- Lexicographic comparison of two one-sided symbolic sequences. -/
def LexLE {k : ℕ} (x y : OneSidedShiftSpace k) : Prop :=
  x = y ∨ ∃ n : ℕ, (∀ j < n, x j = y j) ∧ (x n).val < (y n).val

/-- The digits and remainders produced by the greedy expansion of `1` in base
`β`; the alphabet has exactly `⌊β⌋+1` symbols. -/
def IsGreedyBetaExpansion (β : ℝ) (k : ℕ) (digits : ℕ -> Fin k)
    (remainder : ℕ -> ℝ) : Prop :=
  1 < β ∧ k = (Int.floor β).toNat + 1 ∧ remainder 0 = 1 ∧
    ∀ n : ℕ,
      (digits n).val = (Int.floor (β * remainder n)).toNat ∧
      remainder (n + 1) = β * remainder n - (digits n).val ∧
      0 ≤ remainder (n + 1) ∧ remainder (n + 1) < 1

/-- The one-sided beta-shift determined by the greedy expansion of `1`. -/
def betaShiftSpace {k : ℕ} (digits : ℕ -> Fin k) :
    Set (OneSidedShiftSpace k) :=
  {x | ∀ m : ℕ, LexLE (fun n => x (m + n)) digits}

theorem oneSidedShiftMap_mapsTo_betaShiftSpace {k : ℕ}
    (digits : ℕ -> Fin k) :
    Set.MapsTo oneSidedShiftMap (betaShiftSpace digits) (betaShiftSpace digits) := by
  intro x hx m
  simpa [oneSidedShiftMap, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx (m + 1)

def betaShiftSystem {k : ℕ} (digits : ℕ -> Fin k) : System.{0} :=
  restrictedSystem (oneSidedFullShiftSystem k) (betaShiftSpace digits)
    (oneSidedShiftMap_mapsTo_betaShiftSpace digits)

def oneSidedLanguage (k : ℕ) (Y : Set (OneSidedShiftSpace k)) (n : ℕ) :
    Finset (Fin n -> Fin k) :=
  Finset.univ.filter fun w => ∃ x ∈ Y, ∀ i : Fin n, x i = w i

def oneSidedWordComplexity (k : ℕ) (Y : Set (OneSidedShiftSpace k)) (n : ℕ) : ℕ :=
  (oneSidedLanguage k Y n).card

/-- The natural two-sided extension of a one-sided beta-shift. -/
def twoSidedBetaShiftSpace {k : ℕ} (digits : ℕ -> Fin k) :
    Set (FullShiftSpace k) :=
  {x | ∀ i : ℤ, (fun n : ℕ => x (i + n)) ∈ betaShiftSpace digits}

theorem shiftMap_mapsTo_twoSidedBetaShiftSpace {k : ℕ}
    (digits : ℕ -> Fin k) :
    Set.MapsTo shiftMap (twoSidedBetaShiftSpace digits) (twoSidedBetaShiftSpace digits) := by
  intro x hx i
  simpa [shiftMap, add_assoc, add_comm, add_left_comm] using hx (i + 1)

def twoSidedBetaShiftSystem {k : ℕ} (digits : ℕ -> Fin k) : System.{0} :=
  subshiftSystem k (twoSidedBetaShiftSpace digits)
    (shiftMap_mapsTo_twoSidedBetaShiftSpace digits)

/-- Compatibility of the ambient topology with the current pseudo-metric instance. -/
def MetricCompatibleWithTopology (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  ∀ U : Set S.X, IsOpen U ↔
    ∀ x ∈ U, ∃ ε : ℝ, 0 < ε ∧ Metric.ball x ε ⊆ U

/-- Compatibility stated directly on a type, for situations where the same
carrier also bears a measurable-system structure. -/
def MetricTopologyCompatible (X : Type u) [TopologicalSpace X]
    [PseudoMetricSpace X] : Prop :=
  ∀ U : Set X, IsOpen U ↔
    ∀ x ∈ U, ∃ ε : ℝ, 0 < ε ∧ Metric.ball x ε ⊆ U

def integerIterateMap {X : Type u} (T inv : X -> X) (n : ℤ) : X -> X :=
  if 0 ≤ n then T^[n.toNat] else inv^[n.natAbs]

/-- A map and its inverse are continuous and expansive with the specified
constant, stated without packaging the carrier into a `System`. -/
def IsExpansiveMapWithConstant {X : Type u} [TopologicalSpace X]
    [PseudoMetricSpace X] (T inv : X -> X) (δ : ℝ) : Prop :=
  Continuous T ∧ Continuous inv ∧
  Function.LeftInverse inv T ∧ Function.RightInverse inv T ∧
  0 < δ ∧ ∀ x y : X, x ≠ y -> ∃ n : ℤ,
    dist (integerIterateMap T inv n x) (integerIterateMap T inv n y) > δ

/-- Bowen's `n`-step orbit distance. -/
def bowenDistance (S : System.{u}) [PseudoMetricSpace S.X]
    (n : ℕ) (x y : S.X) : ℝ :=
  sSup {r : ℝ | ∃ k : ℕ, k < n ∧ r = dist ((S.T^[k]) x) ((S.T^[k]) y)}

def IsMetricSeparatedOn (S : System.{u}) [PseudoMetricSpace S.X]
    (F : Set S.X) (n : ℕ) (ε : ℝ) (A : Finset S.X) : Prop :=
  (↑A : Set S.X) ⊆ F ∧ ∀ x ∈ A, ∀ y ∈ A, x ≠ y -> ε ≤ bowenDistance S n x y

def IsMetricSpanningFor (S : System.{u}) [PseudoMetricSpace S.X]
    (F : Set S.X) (n : ℕ) (ε : ℝ) (A : Finset S.X) : Prop :=
  ∀ x ∈ F, ∃ y ∈ A, bowenDistance S n x y < ε

def metricSeparatedNumber (S : System.{u}) [PseudoMetricSpace S.X]
    (F : Set S.X) (n : ℕ) (ε : ℝ) : ENNReal :=
  sSup {r : ENNReal | ∃ A : Finset S.X,
    IsMetricSeparatedOn S F n ε A ∧ r = A.card}

def metricSpanningNumber (S : System.{u}) [PseudoMetricSpace S.X]
    (F : Set S.X) (n : ℕ) (ε : ℝ) : ENNReal :=
  sInf {r : ENNReal | ∃ A : Finset S.X,
    IsMetricSpanningFor S F n ε A ∧ r = A.card}

def metricSeparatedEntropyAtScale (S : System.{u}) [PseudoMetricSpace S.X]
    (F : Set S.X) (ε : ℝ) : EReal :=
  limsup (fun n : ℕ =>
    ENNReal.log (metricSeparatedNumber S F (n + 1) ε) / (n + 1 : EReal)) atTop

def metricSpanningEntropyAtScale (S : System.{u}) [PseudoMetricSpace S.X]
    (F : Set S.X) (ε : ℝ) : EReal :=
  limsup (fun n : ℕ =>
    ENNReal.log (metricSpanningNumber S F (n + 1) ε) / (n + 1 : EReal)) atTop

def metricSeparatedEntropy (S : System.{u}) [PseudoMetricSpace S.X]
    (F : Set S.X) : EReal :=
  sSup {r : EReal | ∃ ε : ℝ, 0 < ε ∧ r = metricSeparatedEntropyAtScale S F ε}

def metricSpanningEntropy (S : System.{u}) [PseudoMetricSpace S.X]
    (F : Set S.X) : EReal :=
  sSup {r : EReal | ∃ ε : ℝ, 0 < ε ∧ r = metricSpanningEntropyAtScale S F ε}

/-- Bowen entropy of a possibly noncompact metric system, taking the supremum
over compact subsets. -/
def bowenMetricEntropy (S : System.{u}) [PseudoMetricSpace S.X] : EReal :=
  sSup {r : EReal | ∃ K : Set S.X, IsCompact K ∧ r = metricSpanningEntropy S K}

/-- The same map and subset evaluated using an explicitly supplied uniformity. -/
def coverEntropyWithUniformity (S : System.{u})
    (u : UniformSpace S.X) (F : Set S.X) : EReal :=
  @Dynamics.coverEntropy S.X u S.T F

/-- Bowen entropy for an explicitly supplied uniformity, with the noncompact
definition taken as the supremum over compact subsets. -/
def bowenEntropyWithUniformity (S : System.{u}) (u : UniformSpace S.X) : EReal :=
  sSup {r : EReal | ∃ K : Set S.X, IsCompact K ∧
    r = coverEntropyWithUniformity S u K}

/-- A finite Borel partition of the phase space of a topological system. -/
structure FiniteBorelPartition (S : System.{u}) where
  atoms : Finset (Set S.X)
  measurable_atoms : ∀ A ∈ atoms, @MeasurableSet S.X (borel S.X) A
  covers_univ : ⋃₀ (atoms : Set (Set S.X)) = Set.univ
  pairwise_disjoint : ∀ A ∈ atoms, ∀ B ∈ atoms, A ≠ B -> Disjoint A B

def borelPartitionEntropy (S : System.{u}) (μ : MeasureOn S.X)
    (α : FiniteBorelPartition S) : ℝ :=
  α.atoms.sum fun A => - (μ.measure A).toReal * Real.log (μ.measure A).toReal

def joinBorelPartition (S : System.{u})
    (α β : FiniteBorelPartition S) : FiniteBorelPartition S where
  atoms := (α.atoms.product β.atoms).image (fun p => p.1 ∩ p.2)
  measurable_atoms := by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨p, hp, rfl⟩
    exact (α.measurable_atoms p.1 (Finset.mem_product.mp hp).1).inter
      (β.measurable_atoms p.2 (Finset.mem_product.mp hp).2)
  covers_univ := by
    apply Set.eq_univ_of_univ_subset
    intro x _
    have hxα : x ∈ ⋃₀ (α.atoms : Set (Set S.X)) := by rw [α.covers_univ]; trivial
    have hxβ : x ∈ ⋃₀ (β.atoms : Set (Set S.X)) := by rw [β.covers_univ]; trivial
    rcases hxα with ⟨A, hA, hxA⟩
    rcases hxβ with ⟨B, hB, hxB⟩
    refine ⟨A ∩ B, ?_, hxA, hxB⟩
    simp only [Finset.coe_image, Set.mem_image]
    exact ⟨(A, B), by simp_all, rfl⟩
  pairwise_disjoint := by
    intro C hC D hD hCD
    rcases Finset.mem_image.mp hC with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hD with ⟨q, hq, rfl⟩
    rw [Set.disjoint_left]
    intro x hxp hxq
    by_cases hfirst : p.1 = q.1
    · have hsecond : p.2 ≠ q.2 := by
        intro hs
        apply hCD
        simp [hfirst, hs]
      exact (Set.disjoint_left.1 (β.pairwise_disjoint p.2
        (Finset.mem_product.mp hp).2 q.2 (Finset.mem_product.mp hq).2 hsecond))
        hxp.2 hxq.2
    · exact (Set.disjoint_left.1 (α.pairwise_disjoint p.1
        (Finset.mem_product.mp hp).1 q.1 (Finset.mem_product.mp hq).1 hfirst))
        hxp.1 hxq.1

def trivialBorelPartition (S : System.{u}) : FiniteBorelPartition S where
  atoms := {Set.univ}
  measurable_atoms := by simp
  covers_univ := by simp
  pairwise_disjoint := by simp

def pullbackBorelPartitionByIterate (S : System.{u})
    (α : FiniteBorelPartition S) (n : ℕ) : FiniteBorelPartition S :=
  if h : ∀ A ∈ α.atoms, @MeasurableSet S.X (borel S.X) ((S.T^[n]) ⁻¹' A) then
    { atoms := α.atoms.image (fun A => (S.T^[n]) ⁻¹' A)
      measurable_atoms := by
        intro B hB
        rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
        exact h A hA
      covers_univ := by
        apply Set.eq_univ_of_univ_subset
        intro x _
        have hx : (S.T^[n]) x ∈ ⋃₀ (α.atoms : Set (Set S.X)) := by
          rw [α.covers_univ]
          trivial
        rcases hx with ⟨A, hA, hxA⟩
        exact ⟨(S.T^[n]) ⁻¹' A,
          by simpa using Finset.mem_image.mpr ⟨A, hA, rfl⟩, hxA⟩
      pairwise_disjoint := by
        intro B hB C hC hBC
        rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
        rcases Finset.mem_image.mp hC with ⟨D, hD, rfl⟩
        have hAD : A ≠ D := by
          intro had
          apply hBC
          simp [had]
        exact (α.pairwise_disjoint A hA D hD hAD).preimage (S.T^[n]) }
  else α

/-- `⋁ⁿ⁻¹ᵢ₌₀ T⁻ⁱ α`; the zero case is the empty join. -/
def iteratedJoinBorelPartition (S : System.{u}) (α : FiniteBorelPartition S) :
    ℕ -> FiniteBorelPartition S
  | 0 => trivialBorelPartition S
  | n + 1 => joinBorelPartition S (iteratedJoinBorelPartition S α n)
      (pullbackBorelPartitionByIterate S α n)

def borelPartitionEntropyRate (S : System.{u}) (μ : MeasureOn S.X)
    (α : FiniteBorelPartition S) : ℝ :=
  sInf {r : ℝ | ∃ n : ℕ, 0 < n ∧
    r = borelPartitionEntropy S μ (iteratedJoinBorelPartition S α n) / (n : ℝ)}

/-- Kolmogorov--Sinai entropy of the Borel system `(X,μ,T)`, expressed as
the supremum of entropy rates over finite Borel partitions. -/
def entropyMap (S : System.{u}) (μ : MeasureOn S.X) : EReal :=
  sSup {r : EReal | ∃ α : FiniteBorelPartition S,
    r = (borelPartitionEntropyRate S μ α : EReal)}

def fixedPointSet (S : System.{u}) (n : ℕ) : Set S.X :=
  {x | (S.T^[n]) x = x}

def IsUniformMeasureOnFiniteSet {X : Type u} [TopologicalSpace X]
    (μ : MeasureOn X) (F : Finset X) : Prop :=
  μ.measure (F : Set X) = 1 ∧
    ∀ x : X, μ.measure {x} = if x ∈ F then (F.card : ENNReal)⁻¹ else 0

def shiftCylinder {k n : ℕ} (start : ℤ) (word : Fin n -> Fin k) :
    Set (FullShiftSpace k) :=
  {x | ∀ i : Fin n, x (start + (i : ℕ)) = word i}

def IsUniformBernoulliMeasure (k : ℕ) (μ : MeasureOn (FullShiftSpace k)) : Prop :=
  Chapter06.IsInvariantMeasure (fullShiftSystem k) μ ∧ 0 < k ∧
    ∀ n : ℕ, ∀ start : ℤ, ∀ word : Fin n -> Fin k,
      μ.measure (shiftCylinder start word) =
        ENNReal.ofReal ((k : ℝ) ^ (-(n : ℤ)))

/-- Upper semicontinuity with respect to the weak-star topology, written in a
finite-test-function neighborhood basis. -/
def EntropyMapUpperSemicontinuous (S : System.{u}) : Prop :=
  ∀ μ : MeasureOn S.X, Chapter06.IsInvariantMeasure S μ ->
    ∀ ε : ℝ, 0 < ε -> ∃ tests : Finset (S.X -> ℂ), ∃ δ : ℝ, 0 < δ ∧
      (∀ f ∈ tests, Continuous f) ∧
      ∀ ν : MeasureOn S.X, Chapter06.IsInvariantMeasure S ν ->
        ν ∈ Chapter06.weakStarNeighborhood μ tests δ ->
          entropyMap S ν < entropyMap S μ + (ε : EReal)

/-- All averages below are taken against the same genuine ergodic-decomposition
probability measure. -/
structure EntropyErgodicDecompositionData (S : System.{u})
    (μ : MeasureOn S.X) extends Chapter06.ErgodicDecompositionData S where
  represents : ∀ f : S.X -> ℂ, Continuous f ->
    μ.integral f = toErgodicDecompositionData.weight.integral (fun ν => ν.integral f)

namespace EntropyErgodicDecompositionData

def averageReal {S : System.{u}} {μ : MeasureOn S.X}
    (D : EntropyErgodicDecompositionData S μ) (f : MeasureOn S.X -> ℝ) : ℝ :=
  D.toErgodicDecompositionData.weight.realIntegral f

def averageEReal {S : System.{u}} {μ : MeasureOn S.X}
    (D : EntropyErgodicDecompositionData S μ) (f : MeasureOn S.X -> EReal) : EReal :=
  D.toErgodicDecompositionData.weight.eRealLIntegral f

end EntropyErgodicDecompositionData

def measureOfMaximalEntropy (S : System.{u}) (μ : MeasureOn S.X) : Prop :=
  Chapter06.IsInvariantMeasure S μ ∧ entropyMap S μ = topologicalEntropy S

def hasMeasureOfMaximalEntropy (S : System.{u}) : Prop :=
  ∃ μ : MeasureOn S.X, measureOfMaximalEntropy S μ

def binaryPartition (M : MeasurableSystem.{u}) (A : Set M.X) (hA : A ∈ M.𝓧)
    (hAc : Aᶜ ∈ M.𝓧) :
    FiniteMeasurablePartition M where
  atoms := {A, Aᶜ}
  measurable_atoms := by
    intro B hB
    rw [Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with rfl | rfl
    · exact hA
    · exact hAc
  covers_univ := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      by_cases hx : x ∈ A
      · exact ⟨A, by simp, hx⟩
      · exact ⟨Aᶜ, by simp, hx⟩
  pairwise_disjoint := by
    intro B hB C hC hBC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB hC
    rcases hB with rfl | rfl <;> rcases hC with rfl | rfl
    · exact (hBC rfl).elim
    · rw [Set.disjoint_left]
      intro x hx hxcomp
      exact hxcomp hx
    · rw [Set.disjoint_left]
      intro x hxcomp hx
      exact hxcomp hx
    · exact (hBC rfl).elim

def binaryPinskerCharacterization (M : MeasurableSystem.{u}) : Set (Set M.X) :=
  {A | ∃ hA : A ∈ M.𝓧, ∃ hAc : Aᶜ ∈ M.𝓧,
    partitionEntropyRate M (binaryPartition M A hA hAc) = 0}

def binaryPartitionsHavePositiveEntropy (M : MeasurableSystem.{u}) : Prop :=
  ∀ A ∈ M.𝓧, Aᶜ ∈ M.𝓧 -> A ≠ ∅ -> A ≠ Set.univ ->
    ∀ hA : A ∈ M.𝓧, ∀ hAc : Aᶜ ∈ M.𝓧,
      0 < partitionEntropyRate M (binaryPartition M A hA hAc)

def partitionSigmaAlgebra (M : MeasurableSystem.{u})
    (α : FiniteMeasurablePartition M) : Set (Set M.X) :=
  Chapter00.generatedSigmaAlgebra (α.atoms : Set (Set M.X))

def pastPartitionSigmaAlgebra (M : MeasurableSystem.{u})
    (α : FiniteMeasurablePartition M) : Set (Set M.X) :=
  Chapter00.generatedSigmaAlgebra
    {A | ∃ n : ℕ, 0 < n ∧ ∃ B ∈ α.atoms, A = (M.T^[n]) ⁻¹' B}

def futurePartitionSigmaAlgebra (M : MeasurableSystem.{u})
    (α : FiniteMeasurablePartition M) : Set (Set M.X) :=
  Chapter00.generatedSigmaAlgebra
    {A | ∃ n : ℕ, ∃ B ∈ α.atoms, A = (M.T^[n]) ⁻¹' B}

def orbitPartitionSigmaAlgebra (M : MeasurableSystem.{u})
    (inv : M.X -> M.X) (α : FiniteMeasurablePartition M) : Set (Set M.X) :=
  Chapter00.generatedSigmaAlgebra
    {A | ∃ n : ℤ, ∃ B ∈ α.atoms,
      A = (if 0 ≤ n then M.T^[n.toNat] else inv^[n.natAbs]) ⁻¹' B}

def sigmaJoin {X : Type u} (A B : Set (Set X)) : Set (Set X) :=
  Chapter00.generatedSigmaAlgebra (A ∪ B)

def tailSigmaAlgebra (M : MeasurableSystem.{u})
    (α : FiniteMeasurablePartition M) : Set (Set M.X) :=
  ⋂ n : ℕ, Chapter00.generatedSigmaAlgebra
    {A | ∃ k : ℕ, n ≤ k ∧ ∃ B ∈ α.atoms, A = (M.T^[k]) ⁻¹' B}

def EqualModuloMeasure (M : MeasurableSystem.{u})
    (A B : Set (Set M.X)) : Prop :=
  (∀ U ∈ A, ∃ V ∈ B, M.μ (Chapter00.symmDiff U V) = 0) ∧
    ∀ V ∈ B, ∃ U ∈ A, M.μ (Chapter00.symmDiff U V) = 0

def pinskerGenerators (M : MeasurableSystem.{u}) : Set (Set M.X) :=
  {A | ∃ α : FiniteMeasurablePartition M,
    partitionEntropyRate M α = 0 ∧ A ∈ partitionSigmaAlgebra M α}

/-- The least sigma-algebra generated by all zero-entropy finite partitions. -/
def pinskerSigmaAlgebra (M : MeasurableSystem.{u}) : Set (Set M.X) :=
  Chapter00.generatedSigmaAlgebra (pinskerGenerators M)

def hasCompletelyPositiveEntropy (M : MeasurableSystem.{u}) : Prop :=
  EqualModuloMeasure M (pinskerSigmaAlgebra M) {∅, Set.univ}

def isMeasureKSystem (M : MeasurableSystem.{u}) : Prop :=
  hasCompletelyPositiveEntropy M ∧ Chapter02.IsErgodic M

def isBernoulliMeasureSystem (M : MeasurableSystem.{u}) : Prop :=
  ∃ α : CountableMeasurablePartition M,
    MeasurableSpace.generateFrom
      {A : Set M.X | ∃ n k : ℕ, A = (M.T^[n]) ⁻¹' α.atoms k} =
        M.measurableSpace ∧
    ∀ F : Finset ℕ, ∀ a : ℕ -> ℕ,
      M.μ (⋂ n : F, (M.T^[n.val]) ⁻¹' α.atoms (a n.val)) =
        F.prod (fun n => M.μ (α.atoms (a n)))

def IsNontrivialOpenCover {X : Type u} [TopologicalSpace X]
    (cover : OpenCover X) : Prop :=
  ∀ U ∈ cover.sets, U ≠ ∅ ∧ ¬ Dense U

def hasUniformlyPositiveEntropy (S : System.{u}) : Prop :=
  ∀ cover : OpenCover S.X, cover.sets.Nonempty -> cover.sets.ncard = 2 ->
    IsNontrivialOpenCover cover -> 0 < topologicalCoverEntropyRate S cover

def topologicalKSystem (S : System.{u}) : Prop :=
  ∀ n : ℕ, 2 ≤ n -> ∀ cover : OpenCover S.X,
    cover.sets.ncard = n -> IsNontrivialOpenCover cover ->
      0 < topologicalCoverEntropyRate S cover

def IsAdmissibleOpenCover (S : System.{u}) {n : ℕ}
    (x : Fin n -> S.X) (cover : OpenCover S.X) : Prop :=
  ∀ U ∈ cover.sets, ¬ Set.range x ⊆ closure U

def topologicalEntropyTuple (S : System.{u}) (n : ℕ) (x : Fin n -> S.X) : Prop :=
  2 ≤ n ∧ (∃ i j : Fin n, i ≠ j ∧ x i ≠ x j) ∧
    ∀ cover : OpenCover S.X, IsAdmissibleOpenCover S x cover ->
      0 < topologicalCoverEntropyRate S cover

def IsAdmissibleBorelPartition (S : System.{u}) {n : ℕ}
    (x : Fin n -> S.X) (α : FiniteBorelPartition S) : Prop :=
  ∀ A ∈ α.atoms, ¬ Set.range x ⊆ closure A

def measureEntropyTuple (S : System.{u}) (μ : MeasureOn S.X) (n : ℕ)
    (x : Fin n -> S.X) : Prop :=
  Chapter06.IsInvariantMeasure S μ ∧ 2 ≤ n ∧
    (∃ i j : Fin n, i ≠ j ∧ x i ≠ x j) ∧
    ∀ α : FiniteBorelPartition S, IsAdmissibleBorelPartition S x α ->
      0 < borelPartitionEntropyRate S μ α

def topologicalPinskerFactor (S : System.{u}) : Prop :=
  ∃ R : System.{u}, topologicalEntropy R = 0 ∧
    ∃ π : S.X -> R.X, Chapter05.IsFactorMap S R π ∧
      ∀ Z : System.{u}, topologicalEntropy Z = 0 ->
      ∀ ρ : S.X -> Z.X, Chapter05.IsFactorMap S Z ρ ->
        ∃ σ : R.X -> Z.X, Chapter05.IsFactorMap R Z σ ∧ ρ = σ ∘ π

def coverJoinAlongTimes (S : System.{u}) (cover : OpenCover S.X)
    (times : ℕ -> ℕ) : ℕ -> OpenCover S.X
  | 0 => trivialOpenCover S.X
  | n + 1 => coverJoin (coverJoinAlongTimes S cover times n)
      (iteratedPullbackCover S cover (times n))

def sequenceTopologicalEntropy (S : System.{u}) (A : Set ℕ)
    (cover : OpenCover S.X) : EReal :=
  sSup {r : EReal | ∃ times : ℕ -> ℕ, StrictMono times ∧ Set.range times = A ∧
    r = limsup (fun n : ℕ =>
      coverEntropy (coverJoinAlongTimes S cover times (n + 1)) / (n + 1 : EReal)) atTop}

def partitionJoinAlongTimes (M : MeasurableSystem.{u})
    (α : FiniteMeasurablePartition M) (times : ℕ -> ℕ) :
    ℕ -> FiniteMeasurablePartition M
  | 0 => trivialMeasurablePartition M
  | n + 1 => joinPartition M (partitionJoinAlongTimes M α times n)
      (pullbackPartitionByIterate M α (times n))

def sequenceMeasureEntropy (M : MeasurableSystem.{u}) (A : Set ℕ)
    (α : FiniteMeasurablePartition M) : ℝ :=
  sSup {r : ℝ | ∃ times : ℕ -> ℕ, StrictMono times ∧ Set.range times = A ∧
    r = limsup (fun n : ℕ => partitionEntropy M
      (partitionJoinAlongTimes M α times (n + 1)) / (n + 1 : ℝ)) atTop}

def sequenceTopologicalEntropyOfSystem (S : System.{u}) (A : Set ℕ) : EReal :=
  sSup {r : EReal | ∃ cover : OpenCover S.X,
    r = sequenceTopologicalEntropy S A cover}

def sequenceMeasureEntropyOfSystem (M : MeasurableSystem.{u}) (A : Set ℕ) : EReal :=
  sSup {r : EReal | ∃ α : FiniteMeasurablePartition M,
    r = (sequenceMeasureEntropy M A α : EReal)}

def isNullSystem (S : System.{u}) : Prop :=
  ∀ A : Set ℕ, A.Infinite -> sequenceTopologicalEntropyOfSystem S A = 0

def IsNullMeasureSystem (M : MeasurableSystem.{u}) : Prop :=
  ∀ A : Set ℕ, A.Infinite -> sequenceMeasureEntropyOfSystem M A = 0

def patternJoinCover (S : System.{u}) (cover : OpenCover S.X)
    {n : ℕ} (times : Fin n -> ℕ) : OpenCover S.X :=
  if hT : Continuous S.T then
    { sets := {W | ∃ choice : Fin n -> Set S.X, (∀ i, choice i ∈ cover.sets) ∧
        W = ⋂ i, (S.T^[times i]) ⁻¹' choice i}
      is_open := by
        rintro W ⟨choice, hchoice, rfl⟩
        apply isOpen_iInter_of_finite
        intro i
        exact (cover.is_open (choice i) (hchoice i)).preimage (hT.iterate (times i))
      covers_univ := by
        apply Set.eq_univ_of_univ_subset
        intro x _
        have hx : ∀ i : Fin n, ∃ U ∈ cover.sets, (S.T^[times i]) x ∈ U := by
          intro i
          have hxi : (S.T^[times i]) x ∈ ⋃₀ cover.sets := by
            rw [cover.covers_univ]
            trivial
          simpa only [Set.mem_sUnion] using hxi
        choose choice hchoice hxchoice using hx
        refine ⟨⋂ i, (S.T^[times i]) ⁻¹' choice i, ?_, ?_⟩
        · exact ⟨choice, hchoice, rfl⟩
        · simp only [Set.mem_iInter, Set.mem_preimage]
          exact hxchoice }
  else cover

def maximalPatternCoverNumber (S : System.{u}) (cover : OpenCover S.X)
    (n : ℕ) : ENNReal :=
  sSup {r : ENNReal | ∃ times : Fin n -> ℕ, StrictMono times ∧
    r = coverNumber (patternJoinCover S cover times)}

def maximalPatternCoverEntropy (S : System.{u}) (cover : OpenCover S.X) : EReal :=
  limsup (fun n : ℕ => ENNReal.log (maximalPatternCoverNumber S cover (n + 1)) /
    (n + 1 : EReal)) atTop

def maximalPatternEntropy (S : System.{u}) : EReal :=
  sSup {r : EReal | ∃ cover : OpenCover S.X,
    r = maximalPatternCoverEntropy S cover}

def upperDensity (J : Set ℕ) : EReal :=
  limsup (fun n : ℕ =>
    (((Finset.range (n + 1)).filter fun j => j ∈ J).card : EReal) /
      (n + 1 : EReal)) atTop

def hasWeakHorseshoe (S : System.{u}) : Prop :=
  ∃ A B : Set S.X, IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧
    ∃ J : Set ℕ, 0 < upperDensity J ∧ ∀ s : J -> Bool, ∃ x : S.X,
      ∀ j : J, if s j then (S.T^[j]) x ∈ A else (S.T^[j]) x ∈ B

def hasDiscreteSpectrum (M : MeasurableSystem.{u}) : Prop :=
  Chapter02.HasDiscreteSpectrum M

end Chapter07
