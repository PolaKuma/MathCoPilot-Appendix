import Chapter04.Section05

noncomputable section

open Classical
open scoped ENNReal

namespace Chapter04Counterexample

def counterP : Chapter04.ProbabilitySpace.{0} where
  X := ℝ
  measurableSpace := ⊤
  μ := @MeasureTheory.Measure.count ℝ ⊤

def finiteFamily : Set (Set counterP.X) :=
  {A | A.Finite}

theorem finiteFamily_hereditary :
    Chapter04.IsHereditaryFamily finiteFamily := by
  constructor
  · exact ⟨∅, Set.finite_empty⟩
  · intro A B hAB hB
    exact hB.subset hAB

theorem exhaustionLemma_missing_finite_measure_counterexample :
    ¬ ∃ U : Set counterP.X,
      Chapter04.HasMeasurableUnion finiteFamily
        {A : Set ℝ | MeasurableSet A} counterP.μ U := by
  rintro ⟨U, hUmeas, A, hAfin, hdisj, hU, hmax⟩
  have hcountable : (⋃ n, A n).Countable :=
    Set.countable_iUnion (fun n => (hAfin n).countable)
  have hne : (⋃ n, A n) ≠ (Set.univ : Set ℝ) := by
    intro heq
    apply Set.not_countable_univ (α := ℝ)
    simpa [heq] using hcountable
  have hex : ∃ x : ℝ, x ∉ ⋃ n, A n := by
    by_contra h
    push_neg at h
    exact hne (Set.eq_univ_of_forall h)
  obtain ⟨x, hx⟩ := hex
  have hsingleton : ({x} : Set ℝ) ∈ finiteFamily := Set.finite_singleton x
  have hzero := hmax {x} hsingleton
  have hdiff : ({x} : Set ℝ) \ U = {x} := by
    subst U
    ext y
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · intro hy
      subst y
      exact ⟨rfl, hx⟩
  rw [hdiff] at hzero
  have hzero' : MeasureTheory.Measure.count {x} = 0 := by
    simpa [counterP] using hzero
  rw [MeasureTheory.Measure.count_singleton] at hzero'
  exact one_ne_zero hzero'

def trivialBoolMeasurableSpace : MeasurableSpace Bool where
  MeasurableSet' A := A = ∅ ∨ A = Set.univ
  measurableSet_empty := Or.inl rfl
  measurableSet_compl A hA := by
    rcases hA with rfl | rfl
    · exact Or.inr (by simp)
    · exact Or.inl (by simp)
  measurableSet_iUnion A hA := by
    by_cases h : ∃ n, A n = Set.univ
    · right
      obtain ⟨n, hn⟩ := h
      apply Set.eq_univ_of_forall
      intro x
      exact Set.mem_iUnion.mpr ⟨n, by simp [hn]⟩
    · left
      have hempty : ∀ n, A n = ∅ := by
        intro n
        rcases hA n with hn | hn
        · exact hn
        · exact False.elim (h ⟨n, hn⟩)
      ext x
      simp [hempty]

def counterProbability : Chapter04.ProbabilitySpace.{0} where
  X := Bool
  measurableSpace := trivialBoolMeasurableSpace
  μ := @MeasureTheory.Measure.dirac Bool trivialBoolMeasurableSpace false

def nonmeasurableHereditaryFamily : Set (Set counterProbability.X) :=
  {A | A ⊆ {false}}

theorem counterProbability_isProbability :
    Chapter01.IsProbabilitySpace counterProbability := by
  letI : MeasurableSpace Bool := trivialBoolMeasurableSpace
  change MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.dirac false)
  infer_instance

theorem nonmeasurableHereditaryFamily_hereditary :
    Chapter04.IsHereditaryFamily nonmeasurableHereditaryFamily := by
  constructor
  · exact ⟨∅, Set.empty_subset _⟩
  · intro A B hAB hB
    exact hAB.trans hB

theorem exhaustionLemma_missing_measurable_family_counterexample :
    ¬ ∃ U : Set counterProbability.X,
      Chapter04.HasMeasurableUnion nonmeasurableHereditaryFamily
        {A : Set Bool | @MeasurableSet Bool trivialBoolMeasurableSpace A}
        counterProbability.μ U := by
  rintro ⟨U, hUmeas, A, hAfamily, hdisj, hU, hmax⟩
  have hUsub : U ⊆ {false} := by
    rw [hU]
    exact Set.iUnion_subset (fun n => hAfamily n)
  have hUcases : U = ∅ ∨ U = Set.univ := by
    change @MeasurableSet Bool trivialBoolMeasurableSpace U at hUmeas
    exact hUmeas
  have hUne : U ≠ Set.univ := by
    intro hUniv
    have : true ∈ ({false} : Set Bool) := hUsub (by simp [hUniv])
    simp at this
  have hUempty : U = ∅ := hUcases.resolve_right hUne
  have hsingleton : ({false} : Set Bool) ∈ nonmeasurableHereditaryFamily :=
    Set.Subset.rfl
  have hzero := hmax {false} hsingleton
  rw [hUempty, Set.diff_empty] at hzero
  have hzero' : (@MeasureTheory.Measure.dirac Bool trivialBoolMeasurableSpace false)
      ({false} : Set Bool) = 0 := by
    simpa [counterProbability] using hzero
  have hone : (@MeasureTheory.Measure.dirac Bool trivialBoolMeasurableSpace false)
      ({false} : Set Bool) = 1 :=
    @MeasureTheory.Measure.dirac_apply_of_mem Bool trivialBoolMeasurableSpace
      {false} false (by simp)
  have : (1 : ENNReal) = 0 := hone.symm.trans hzero'
  exact one_ne_zero this

end Chapter04Counterexample
