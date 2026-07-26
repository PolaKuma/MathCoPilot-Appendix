import Chapter02.Common

open Classical Set MeasureTheory

noncomputable section

namespace Chapter02.MultiplicityStrata

variable {X : Type*}

def noExitSet (T : ℕ → Set X) : Set X := ⋂ k, T k

def exitSet (T : ℕ → Set X) (k : ℕ) : Set X :=
  (T k)ᶜ ∩ ⋂ j : {j // j < k}, T j

/-- Multiplicity `0` denotes infinitely many active layers; finite
multiplicity `1` also absorbs the complement of the maximal spectral support. -/
def stratum (T : ℕ → Set X) : ℕ → Set X
  | 0 => noExitSet T
  | 1 => exitSet T 0 ∪ exitSet T 1
  | k + 2 => exitSet T (k + 2)

theorem measurableSet_noExitSet [MeasurableSpace X] {T : ℕ → Set X}
    (hT : ∀ k, MeasurableSet (T k)) : MeasurableSet (noExitSet T) := by
  exact MeasurableSet.iInter hT

theorem measurableSet_exitSet [MeasurableSpace X] {T : ℕ → Set X}
    (hT : ∀ k, MeasurableSet (T k)) (k : ℕ) : MeasurableSet (exitSet T k) := by
  exact (hT k).compl.inter (MeasurableSet.iInter fun j ↦ hT j)

theorem measurableSet_stratum [MeasurableSpace X] {T : ℕ → Set X}
    (hT : ∀ k, MeasurableSet (T k)) : ∀ n, MeasurableSet (stratum T n)
  | 0 => measurableSet_noExitSet hT
  | 1 => (measurableSet_exitSet hT 0).union (measurableSet_exitSet hT 1)
  | _ + 2 => measurableSet_exitSet hT _

theorem exitSet_disjoint {T : ℕ → Set X} {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (exitSet T k) (exitSet T l) := by
  wlog hlt : k < l generalizing k l
  · exact (this hkl.symm (lt_of_le_of_ne (Nat.le_of_not_gt hlt) hkl.symm)).symm
  refine Set.disjoint_left.2 ?_
  intro z hzk hzl
  have hnot : z ∉ T k := hzk.1
  have hmem : z ∈ T k := by
    have hall := Set.mem_iInter.mp hzl.2
    exact hall ⟨k, hlt⟩
  exact hnot hmem

theorem noExitSet_disjoint_exitSet {T : ℕ → Set X} (k : ℕ) :
    Disjoint (noExitSet T) (exitSet T k) := by
  refine Set.disjoint_left.2 ?_
  intro z hz hk
  exact hk.1 (Set.mem_iInter.mp hz k)

theorem stratum_pairwise_disjoint (T : ℕ → Set X) :
    ∀ n m, n ≠ m → Disjoint (stratum T n) (stratum T m) := by
  intro n m hnm
  rcases n with _ | _ | n <;> rcases m with _ | _ | m
  · exact (hnm rfl).elim
  · exact (noExitSet_disjoint_exitSet 0).union_right
      (noExitSet_disjoint_exitSet 1)
  · exact noExitSet_disjoint_exitSet (m + 2)
  · exact ((noExitSet_disjoint_exitSet 0).union_right
      (noExitSet_disjoint_exitSet 1)).symm
  · exact (hnm rfl).elim
  · exact (exitSet_disjoint (by omega)).union_left
      (exitSet_disjoint (by omega))
  · exact (noExitSet_disjoint_exitSet (n + 2)).symm
  · exact ((exitSet_disjoint (by omega)).union_left
      (exitSet_disjoint (by omega))).symm
  · exact exitSet_disjoint (by omega)

theorem iUnion_stratum (T : ℕ → Set X) :
    (⋃ n, stratum T n) = Set.univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases hall : ∀ k, z ∈ T k
  · exact ⟨0, Set.mem_iInter.2 hall⟩
  · push_neg at hall
    let k := Nat.find hall
    have hknot : z ∉ T k := Nat.find_spec hall
    have hkprev : ∀ j < k, z ∈ T j := by
      intro j hj
      exact Classical.byContradiction fun hjnot ↦
        (not_le_of_gt hj) (Nat.find_min' hall hjnot)
    have hkexit : z ∈ exitSet T k := by
      exact ⟨hknot, Set.mem_iInter.2 fun j ↦ hkprev j j.property⟩
    rcases k with _ | _ | k
    · exact ⟨1, Or.inl hkexit⟩
    · exact ⟨1, Or.inr hkexit⟩
    · exact ⟨k + 2, hkexit⟩

end Chapter02.MultiplicityStrata
