import Chapter02.Recurrence.MultipleKhintchineSyndetic

open Classical Set MeasureTheory

noncomputable section

namespace Chapter02.MultipleKhintchineFactor

universe u v

/-- The canonical representative of a factor set on the invariant conull
cores carried by `Chapter01.IsFactorMap`. -/
def corePullback
    {E : System.{u}} {M : System.{v}} (π : E.X → M.X)
    (E₀ : Set E.X) (M₀ : Set M.X) (A : Set M.X) : Set E.X :=
  E₀ ∩ π ⁻¹' (A ∩ M₀)

/-- Iterates of a factor map intertwine on its invariant source core. -/
lemma iterate_intertwine_on_core
    {E : System.{u}} {M : System.{v}} (π : E.X → M.X)
    (E₀ : Set E.X)
    (hET : ∀ x ∈ E₀, E.T x ∈ E₀)
    (hπT : ∀ x ∈ E₀, π (E.T x) = M.T (π x))
    (n : ℕ) {x : E.X} (hx : x ∈ E₀) :
    (E.T^[n]) x ∈ E₀ ∧
      π ((E.T^[n]) x) = (M.T^[n]) (π x) := by
  induction n with
  | zero => exact ⟨hx, rfl⟩
  | succ n ih =>
      constructor
      · rw [Function.iterate_succ_apply']
        exact hET _ ih.1
      · calc
          π ((E.T^[n + 1]) x) =
              π (E.T ((E.T^[n]) x)) := by
                rw [Function.iterate_succ_apply']
          _ = M.T (π ((E.T^[n]) x)) := hπT _ ih.1
          _ = M.T ((M.T^[n]) (π x)) := congrArg M.T ih.2
          _ = (M.T^[n + 1]) (π x) := by
            rw [Function.iterate_succ_apply']

/-- Pullback along a factor map preserves the measure of every measurable
set, when represented on the factor map's invariant conull cores. -/
lemma measure_corePullback
    {E : System.{u}} {M : System.{v}} (π : E.X → M.X)
    (hπ : Chapter01.IsFactorMap E M π)
    (A : Set M.X) (hA : MeasurableSet A) :
    ∃ E₀ : Set E.X, ∃ M₀ : Set M.X,
      MeasurableSet (corePullback π E₀ M₀ A) ∧
      E.μ (corePullback π E₀ M₀ A) = M.μ A := by
  rcases hπ with
    ⟨hE, hM, E₀, M₀, hE₀, hM₀, hET, hMT, hfull, hπT⟩
  rcases hfull with ⟨hE₀m, hM₀m, -, -, hπcore, hπμ⟩
  letI : IsProbabilityMeasure E.μ := hE.1
  letI : IsProbabilityMeasure M.μ := hM.1
  have hM₀c : M.μ M₀ᶜ = 0 := by
    rw [measure_compl hM₀m (by rw [hM₀]; simp)]
    simp [hM₀]
  refine ⟨E₀, M₀, (hπμ A hA).1, ?_⟩
  unfold corePullback
  rw [(hπμ A hA).2]
  rw [show A ∩ M₀ = A \ M₀ᶜ by ext y; simp]
  exact measure_diff_null hM₀c

/-- For the invariant cores in a factor map, a pulled-back progression
intersection is exactly the pullback of the corresponding progression
intersection in the factor. -/
lemma corePullback_progression
    {E : System.{u}} {M : System.{v}} (π : E.X → M.X)
    (E₀ : Set E.X) (M₀ : Set M.X)
    (hET : ∀ x ∈ E₀, E.T x ∈ E₀)
    (hMT : ∀ y ∈ M₀, M.T y ∈ M₀)
    (_hπcore : ∀ x ∈ E₀, π x ∈ M₀)
    (hπT : ∀ x ∈ E₀, π (E.T x) = M.T (π x))
    (A : Set M.X) (n r : ℕ) :
    corePullback π E₀ M₀ A ∩
        preimageIter E (r * n) (corePullback π E₀ M₀ A) =
      corePullback π E₀ M₀
        (A ∩ preimageIter M (r * n) A) := by
  ext x
  constructor
  · rintro ⟨⟨hxE, hxA, hxM⟩, hxiter⟩
    have hi := iterate_intertwine_on_core π E₀ hET hπT (r * n) hxE
    refine ⟨hxE, ⟨hxA, ?_⟩, hxM⟩
    have hxiterA : π ((E.T^[r * n]) x) ∈ A := by
      simpa [preimageIter, Chapter01.iterateMap] using hxiter.2.1
    rw [hi.2] at hxiterA
    exact hxiterA
  · rintro ⟨hxE, ⟨hxA, hxiterA⟩, hxM⟩
    have hi := iterate_intertwine_on_core π E₀ hET hπT (r * n) hxE
    refine ⟨⟨hxE, hxA, hxM⟩, hi.1, ?_, ?_⟩
    · have : π ((E.T^[r * n]) x) ∈ A := by
        rw [hi.2]
        simpa [preimageIter, Chapter01.iterateMap] using hxiterA
      simpa [preimageIter, Chapter01.iterateMap] using this
    · have hiM := (iterate_intertwine_on_core id M₀ hMT
          (fun _ _ => rfl) (r * n) hxM).1
      have hp : π ((E.T^[r * n]) x) ∈ M₀ := by
        rw [hi.2]
        exact hiM
      simpa [preimageIter, Chapter01.iterateMap] using hp

/-- A finite progression intersection with coefficient set `s`; coefficient
zero is represented separately by the leading membership in `A`. -/
def finiteProgressionIntersection
    (M : System.{u}) (A : Set M.X) (s : Finset ℕ) (n : ℕ) : Set M.X :=
  {x | x ∈ A ∧ ∀ r ∈ s, (M.T^[r * n]) x ∈ A}

lemma finiteProgressionIntersection_measurable
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) (s : Finset ℕ) (n : ℕ) :
    MeasurableSet (finiteProgressionIntersection M A s n) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa [finiteProgressionIntersection] using hA
  | @insert r s hrs ih =>
      rw [show finiteProgressionIntersection M A (insert r s) n =
          finiteProgressionIntersection M A s n ∩
            (M.T^[r * n]) ⁻¹' A by
        ext x
        simp [finiteProgressionIntersection]
        tauto]
      exact ih.inter (hA.preimage (hM.2.measurable.iterate (r * n)))

/-- Pullback commutes exactly with every finite progression intersection on
the factor map's invariant cores. -/
lemma finiteProgressionIntersection_corePullback
    {E : System.{u}} {M : System.{v}} (π : E.X → M.X)
    (E₀ : Set E.X) (M₀ : Set M.X)
    (hET : ∀ x ∈ E₀, E.T x ∈ E₀)
    (hMT : ∀ y ∈ M₀, M.T y ∈ M₀)
    (hπT : ∀ x ∈ E₀, π (E.T x) = M.T (π x))
    (A : Set M.X) (s : Finset ℕ) (n : ℕ) :
    finiteProgressionIntersection E (corePullback π E₀ M₀ A) s n =
      corePullback π E₀ M₀ (finiteProgressionIntersection M A s n) := by
  ext x
  constructor
  · rintro ⟨⟨hxE, hxA, hxM⟩, hall⟩
    refine ⟨hxE, ⟨hxA, ?_⟩, hxM⟩
    intro r hr
    have hi := iterate_intertwine_on_core π E₀ hET hπT (r * n) hxE
    have hpull := hall r hr
    have hp : π ((E.T^[r * n]) x) ∈ A := hpull.2.1
    rw [hi.2] at hp
    exact hp
  · rintro ⟨hxE, ⟨hxA, hall⟩, hxM⟩
    refine ⟨⟨hxE, hxA, hxM⟩, ?_⟩
    intro r hr
    have hi := iterate_intertwine_on_core π E₀ hET hπT (r * n) hxE
    have hiM := (iterate_intertwine_on_core id M₀ hMT
      (fun _ _ => rfl) (r * n) hxM).1
    refine ⟨hi.1, ?_, ?_⟩
    · rw [hi.2]
      exact hall r hr
    · rw [hi.2]
      exact hiM

/-- Every finite progression intersection has the same measure as its
canonical pullback through a factor map. -/
lemma finiteProgression_realMeasure_corePullback
    (E : System.{u}) (M : System.{v}) (π : E.X → M.X)
    (hπ : Chapter01.IsFactorMap E M π)
    (A : Set M.X) (hA : MeasurableSet A) (s : Finset ℕ) (n : ℕ) :
    ∃ E₀ : Set E.X, ∃ M₀ : Set M.X,
      MeasurableSet (corePullback π E₀ M₀ A) ∧
      realMeasure E
          (finiteProgressionIntersection E
            (corePullback π E₀ M₀ A) s n) =
        realMeasure M (finiteProgressionIntersection M A s n) ∧
      realMeasure E (corePullback π E₀ M₀ A) = realMeasure M A := by
  rcases hπ with
    ⟨hE, hM, E₀, M₀, hE₀, hM₀, hET, hMT, hfull, hπT⟩
  rcases hfull with ⟨hE₀m, hM₀m, -, -, hπcore, hπμ⟩
  letI : IsProbabilityMeasure E.μ := hE.1
  letI : IsProbabilityMeasure M.μ := hM.1
  have hM₀c : M.μ M₀ᶜ = 0 := by
    rw [measure_compl hM₀m (by rw [hM₀]; simp)]
    simp [hM₀]
  have hpull_measure (B : Set M.X) (hB : MeasurableSet B) :
      E.μ (corePullback π E₀ M₀ B) = M.μ B := by
    unfold corePullback
    rw [(hπμ B hB).2]
    rw [show B ∩ M₀ = B \ M₀ᶜ by ext y; simp]
    exact measure_diff_null hM₀c
  have hprog :=
    finiteProgressionIntersection_corePullback π E₀ M₀ hET hMT hπT A s n
  have hprogMeas :=
    finiteProgressionIntersection_measurable M hM A hA s n
  refine ⟨E₀, M₀, (hπμ A hA).1, ?_, ?_⟩
  · unfold realMeasure
    rw [hprog, hpull_measure _ hprogMeas]
  · unfold realMeasure
    rw [hpull_measure A hA]

/-- Triple progression correlations are unchanged under a factor pullback. -/
lemma tripleCorrelation_corePullback
    (E : System.{u}) (M : System.{v}) (π : E.X → M.X)
    (hπ : Chapter01.IsFactorMap E M π)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) :
    ∃ E₀ : Set E.X, ∃ M₀ : Set M.X,
      MeasurableSet (corePullback π E₀ M₀ A) ∧
      realMeasure E
          (corePullback π E₀ M₀ A ∩
            preimageIter E n (corePullback π E₀ M₀ A) ∩
            preimageIter E (2 * n) (corePullback π E₀ M₀ A)) =
        realMeasure M
          (A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A) ∧
      realMeasure E (corePullback π E₀ M₀ A) = realMeasure M A := by
  rcases hπ with
    ⟨hE, hM, E₀, M₀, hE₀, hM₀, hET, hMT, hfull, hπT⟩
  rcases hfull with ⟨hE₀m, hM₀m, -, -, hπcore, hπμ⟩
  letI : IsProbabilityMeasure E.μ := hE.1
  letI : IsProbabilityMeasure M.μ := hM.1
  have hM₀c : M.μ M₀ᶜ = 0 := by
    rw [measure_compl hM₀m (by rw [hM₀]; simp)]
    simp [hM₀]
  have hpull_measure (B : Set M.X) (hB : MeasurableSet B) :
      E.μ (corePullback π E₀ M₀ B) = M.μ B := by
    unfold corePullback
    rw [(hπμ B hB).2]
    rw [show B ∩ M₀ = B \ M₀ᶜ by ext y; simp]
    exact measure_diff_null hM₀c
  have hAn (r : ℕ) :
      MeasurableSet (preimageIter M (r * n) A) := by
    exact hA.preimage (hM.2.measurable.iterate (r * n))
  let B : Set M.X :=
    A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A
  have hB : MeasurableSet B := by
    exact (hA.inter (by simpa using hAn 1)).inter (hAn 2)
  have hset :
      corePullback π E₀ M₀ A ∩
          preimageIter E n (corePullback π E₀ M₀ A) ∩
          preimageIter E (2 * n) (corePullback π E₀ M₀ A) =
        corePullback π E₀ M₀ B := by
    ext x
    constructor
    · rintro ⟨⟨⟨hxE, hxA, hxM⟩, hx1⟩, hx2⟩
      have hi1 := iterate_intertwine_on_core π E₀ hET hπT n hxE
      have hi2 := iterate_intertwine_on_core π E₀ hET hπT (2 * n) hxE
      refine ⟨hxE, ⟨⟨hxA, ?_⟩, ?_⟩, hxM⟩
      · have hp : π ((E.T^[n]) x) ∈ A := by
          simpa [preimageIter, Chapter01.iterateMap] using hx1.2.1
        rw [hi1.2] at hp
        exact hp
      · have hp : π ((E.T^[2 * n]) x) ∈ A := by
          simpa [preimageIter, Chapter01.iterateMap] using hx2.2.1
        rw [hi2.2] at hp
        exact hp
    · rintro ⟨hxE, ⟨⟨hxA, hx1A⟩, hx2A⟩, hxM⟩
      have hi1 := iterate_intertwine_on_core π E₀ hET hπT n hxE
      have hi2 := iterate_intertwine_on_core π E₀ hET hπT (2 * n) hxE
      have hiM1 := (iterate_intertwine_on_core id M₀ hMT
        (fun _ _ => rfl) n hxM).1
      have hiM2 := (iterate_intertwine_on_core id M₀ hMT
        (fun _ _ => rfl) (2 * n) hxM).1
      refine ⟨⟨⟨hxE, hxA, hxM⟩, hi1.1, ?_, ?_⟩, hi2.1, ?_, ?_⟩
      · have hp : π ((E.T^[n]) x) ∈ A := by
          rw [hi1.2]
          exact hx1A
        simpa [preimageIter, Chapter01.iterateMap] using hp
      · have hp : π ((E.T^[n]) x) ∈ M₀ := by
          rw [hi1.2]
          exact hiM1
        simpa [preimageIter, Chapter01.iterateMap] using hp
      · have hp : π ((E.T^[2 * n]) x) ∈ A := by
          rw [hi2.2]
          exact hx2A
        simpa [preimageIter, Chapter01.iterateMap] using hp
      · have hp : π ((E.T^[2 * n]) x) ∈ M₀ := by
          rw [hi2.2]
          exact hiM2
        simpa [preimageIter, Chapter01.iterateMap] using hp
  refine ⟨E₀, M₀, (hπμ A hA).1, ?_, ?_⟩
  · unfold realMeasure
    rw [hset, hpull_measure B hB]
  · unfold realMeasure
    rw [hpull_measure A hA]

lemma finiteProgressionIntersection_one_two
    (N : System.{u}) (B : Set N.X) (n : ℕ) :
    finiteProgressionIntersection N B {1, 2} n =
      B ∩ preimageIter N n B ∩ preimageIter N (2 * n) B := by
  ext x
  simp [finiteProgressionIntersection, preimageIter,
    Chapter01.iterateMap]
  tauto

lemma finiteProgressionIntersection_one_two_three
    (N : System.{u}) (B : Set N.X) (n : ℕ) :
    finiteProgressionIntersection N B {1, 2, 3} n =
      B ∩ preimageIter N n B ∩ preimageIter N (2 * n) B ∩
        preimageIter N (3 * n) B := by
  ext x
  simp [finiteProgressionIntersection, preimageIter,
    Chapter01.iterateMap]
  tauto

/-- The exact triple and quadruple uniform block bounds descend through a
factor map.  This is the bridge that allows the noninvertible theorem to be
proved on an invertible natural extension without adding invertibility to the
statement. -/
theorem uniformBlockBounds_of_factorMap
    (E : System.{u}) (M : System.{v}) (π : E.X → M.X)
    (hπ : Chapter01.IsFactorMap E M π)
    (hEerg : IsErgodic E)
    (hEbounds :
      MultipleKhintchineSyndetic.MultipleKhintchineUniformBlockBounds E) :
    MultipleKhintchineSyndetic.MultipleKhintchineUniformBlockBounds M := by
  intro hMerg A hA hApos ε hε
  rcases hπ with
    ⟨hEsys, hMsys, E₀, M₀, hE₀, hM₀, hET, hMT, hfull, hπT⟩
  rcases hfull with ⟨hE₀m, hM₀m, -, -, hπcore, hπμ⟩
  letI : IsProbabilityMeasure E.μ := hEsys.1
  letI : IsProbabilityMeasure M.μ := hMsys.1
  let A' : Set E.X := corePullback π E₀ M₀ A
  have hA'm : MeasurableSet A' := (hπμ A hA).1
  have hM₀c : M.μ M₀ᶜ = 0 := by
    rw [measure_compl hM₀m (by rw [hM₀]; simp)]
    simp [hM₀]
  have hpull_measure (B : Set M.X) (hB : MeasurableSet B) :
      E.μ (corePullback π E₀ M₀ B) = M.μ B := by
    unfold corePullback
    rw [(hπμ B hB).2]
    rw [show B ∩ M₀ = B \ M₀ᶜ by ext y; simp]
    exact measure_diff_null hM₀c
  have hA'measure : realMeasure E A' = realMeasure M A := by
    unfold A' realMeasure
    rw [hpull_measure A hA]
  have hA'pos : 0 < E.μ A' := by
    rw [show E.μ A' = M.μ A by
      dsimp [A']
      exact hpull_measure A hA]
    exact hApos
  have hfinite (s : Finset ℕ) (n : ℕ) :
      realMeasure E (finiteProgressionIntersection E A' s n) =
        realMeasure M (finiteProgressionIntersection M A s n) := by
    have hset :=
      finiteProgressionIntersection_corePullback
        π E₀ M₀ hET hMT hπT A s n
    have hm :=
      finiteProgressionIntersection_measurable M hMsys A hA s n
    unfold A'
    unfold realMeasure
    rw [hset, hpull_measure _ hm]
  have htriple (n : ℕ) :
      MultipleKhintchineSyndetic.tripleCorrelation E A' n =
        MultipleKhintchineSyndetic.tripleCorrelation M A n := by
    unfold MultipleKhintchineSyndetic.tripleCorrelation
    rw [← finiteProgressionIntersection_one_two E A' n,
      ← finiteProgressionIntersection_one_two M A n]
    exact hfinite {1, 2} n
  have hquadruple (n : ℕ) :
      MultipleKhintchineSyndetic.quadrupleCorrelation E A' n =
        MultipleKhintchineSyndetic.quadrupleCorrelation M A n := by
    unfold MultipleKhintchineSyndetic.quadrupleCorrelation
    rw [← finiteProgressionIntersection_one_two_three E A' n,
      ← finiteProgressionIntersection_one_two_three M A n]
    exact hfinite {1, 2, 3} n
  obtain ⟨hthree, hfour⟩ :=
    hEbounds hEerg A' hA'm hA'pos ε hε
  constructor
  · unfold MultipleKhintchineSyndetic.HasUniformBlockLowerBound at hthree ⊢
    simpa only [htriple, hA'measure] using hthree
  · unfold MultipleKhintchineSyndetic.HasUniformBlockLowerBound at hfour ⊢
    simpa only [hquadruple, hA'measure] using hfour

end Chapter02.MultipleKhintchineFactor
