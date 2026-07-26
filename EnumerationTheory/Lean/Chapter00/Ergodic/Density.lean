import Chapter00.Common

noncomputable section

open Classical Filter

namespace Chapter00

/-- The filter on translated intervals whose length tends to infinity. -/
def intervalLengthFilter (α : Type*) : Filter (α × ℕ) :=
  Filter.comap Prod.snd atTop

instance intervalLengthFilter_neBot (α : Type*) [Nonempty α] :
    (intervalLengthFilter α).NeBot := by
  unfold intervalLengthFilter
  rw [Filter.comap_neBot_iff]
  intro s hs
  rcases (Filter.mem_atTop_sets.mp hs) with ⟨N, hN⟩
  exact ⟨(Classical.choice ‹Nonempty α›, N), hN N le_rfl⟩

theorem eventually_intervalLengthFilter_iff {α : Type*} [Nonempty α]
    {P : α × ℕ → Prop} :
    (∀ᶠ p in intervalLengthFilter α, P p) ↔
      ∃ N : ℕ, ∀ a : α, ∀ n : ℕ, N ≤ n → P (a, n) := by
  rw [intervalLengthFilter, Filter.eventually_comap]
  simp only [Filter.eventually_atTop]
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun a n hn => hN n hn (a, n) rfl⟩
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n hn p hp => ?_⟩
    rcases p with ⟨a, m⟩
    simp only at hp
    subst m
    exact hN a n hn

theorem lowerBanachDensity_eq_liminf (A : Set ℕ) :
    lowerBanachDensity A =
      Filter.liminf (fun p : ℕ × ℕ => natIntervalDensity A p.1 p.2)
        (intervalLengthFilter ℕ) := by
  rw [lowerBanachDensity, Filter.liminf_eq]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, eventually_intervalLengthFilter_iff]

theorem upperBanachDensity_eq_limsup (A : Set ℕ) :
    upperBanachDensity A =
      Filter.limsup (fun p : ℕ × ℕ => natIntervalDensity A p.1 p.2)
        (intervalLengthFilter ℕ) := by
  rw [upperBanachDensity, Filter.limsup_eq]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, eventually_intervalLengthFilter_iff]

theorem lowerAsymptoticDensity_eq_liminf (A : Set ℕ) :
    lowerAsymptoticDensity A = Filter.liminf (natInitialDensity A) atTop := by
  rw [lowerAsymptoticDensity, Filter.liminf_eq]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, Filter.eventually_atTop]

theorem upperAsymptoticDensity_eq_limsup (A : Set ℕ) :
    upperAsymptoticDensity A = Filter.limsup (natInitialDensity A) atTop := by
  rw [upperAsymptoticDensity, Filter.limsup_eq]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, Filter.eventually_atTop]

theorem lowerBanachDensityInt_eq_liminf (A : Set ℤ) :
    lowerBanachDensityInt A =
      Filter.liminf (fun p : ℤ × ℕ => intIntervalDensity A p.1 p.2)
        (intervalLengthFilter ℤ) := by
  rw [lowerBanachDensityInt, Filter.liminf_eq]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, eventually_intervalLengthFilter_iff]

theorem upperBanachDensityInt_eq_limsup (A : Set ℤ) :
    upperBanachDensityInt A =
      Filter.limsup (fun p : ℤ × ℕ => intIntervalDensity A p.1 p.2)
        (intervalLengthFilter ℤ) := by
  rw [upperBanachDensityInt, Filter.limsup_eq]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, eventually_intervalLengthFilter_iff]

theorem lowerAsymptoticDensityInt_eq_liminf (A : Set ℤ) :
    lowerAsymptoticDensityInt A = Filter.liminf (intSymmetricDensity A) atTop := by
  rw [lowerAsymptoticDensityInt, Filter.liminf_eq]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, Filter.eventually_atTop]

theorem upperAsymptoticDensityInt_eq_limsup (A : Set ℤ) :
    upperAsymptoticDensityInt A = Filter.limsup (intSymmetricDensity A) atTop := by
  rw [upperAsymptoticDensityInt, Filter.limsup_eq]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, Filter.eventually_atTop]

theorem natInterval_card (a n : ℕ) : (natInterval a n).card = n := by
  simp [natInterval]

theorem intInterval_card (a : ℤ) (n : ℕ) : (intInterval a n).card = n := by
  calc
    (intInterval a n).card = (Finset.range n).card := by
      apply Finset.card_image_iff.mpr
      intro i hi j hj hij
      exact_mod_cast (add_left_cancel hij)
    _ = n := Finset.card_range n

theorem natIntervalDensity_nonneg (A : Set ℕ) (a n : ℕ) :
    0 ≤ natIntervalDensity A a n := by
  exact div_nonneg (by positivity) (Nat.cast_nonneg n)

theorem natIntervalDensity_le_one (A : Set ℕ) (a n : ℕ) :
    natIntervalDensity A a n ≤ 1 := by
  rcases n with _ | n
  · simp [natIntervalDensity]
  · rw [natIntervalDensity, div_le_one (by positivity)]
    exact_mod_cast (Finset.card_filter_le (natInterval a (n + 1)) fun k => k ∈ A).trans_eq
      (natInterval_card a (n + 1))

theorem intIntervalDensity_nonneg (A : Set ℤ) (a : ℤ) (n : ℕ) :
    0 ≤ intIntervalDensity A a n := by
  exact div_nonneg (by positivity) (Nat.cast_nonneg n)

theorem intIntervalDensity_le_one (A : Set ℤ) (a : ℤ) (n : ℕ) :
    intIntervalDensity A a n ≤ 1 := by
  rcases n with _ | n
  · simp [intIntervalDensity]
  · rw [intIntervalDensity, div_le_one (by positivity)]
    exact_mod_cast (Finset.card_filter_le (intInterval a (n + 1)) fun k => k ∈ A).trans_eq
      (intInterval_card a (n + 1))

theorem intSymmetricDensity_nonneg (A : Set ℤ) (n : ℕ) :
    0 ≤ intSymmetricDensity A n := intIntervalDensity_nonneg A _ _

theorem intSymmetricDensity_le_one (A : Set ℤ) (n : ℕ) :
    intSymmetricDensity A n ≤ 1 := intIntervalDensity_le_one A _ _

section FilterBounds

variable {ι : Type*} (F : Filter ι) [F.NeBot]

theorem boundedAbove_of_zero_one {f : ι → ℝ} (hf : ∀ i, f i ≤ 1) :
    F.IsBoundedUnder (· ≤ ·) f :=
  isBoundedUnder_of_eventually_le (Eventually.of_forall hf)

theorem boundedBelow_of_zero_one {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    F.IsBoundedUnder (· ≥ ·) f :=
  isBoundedUnder_of_eventually_ge (Eventually.of_forall hf)

theorem limsup_add_le_of_zero_one {f g h : ι → ℝ}
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1)
    (hg0 : ∀ i, 0 ≤ g i) (hg1 : ∀ i, g i ≤ 1)
    (hh0 : ∀ i, 0 ≤ h i) (hh1 : ∀ i, h i ≤ 1)
    (hh : ∀ i, h i ≤ f i + g i) :
    Filter.limsup h F ≤ Filter.limsup f F + Filter.limsup g F := by
  refine (Filter.limsup_le_limsup (Eventually.of_forall hh)
    (boundedBelow_of_zero_one F hh0).isCoboundedUnder_le
    (isBoundedUnder_of_eventually_le (a := 2)
      (Eventually.of_forall fun i => by linarith [hf1 i, hg1 i]))).trans
    (limsup_add_le (boundedBelow_of_zero_one F hf0)
      (boundedAbove_of_zero_one F hf1)
      (boundedBelow_of_zero_one F hg0).isCoboundedUnder_le
      (boundedAbove_of_zero_one F hg1))

theorem le_liminf_add_of_zero_one {f g h : ι → ℝ}
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1)
    (hg0 : ∀ i, 0 ≤ g i) (hg1 : ∀ i, g i ≤ 1)
    (hh0 : ∀ i, 0 ≤ h i) (hh1 : ∀ i, h i ≤ 1)
    (hh : ∀ i, f i + g i ≤ h i) :
    Filter.liminf f F + Filter.liminf g F ≤ Filter.liminf h F := by
  refine (le_liminf_add (boundedBelow_of_zero_one F hf0)
      (boundedAbove_of_zero_one F hf1)
      (boundedBelow_of_zero_one F hg0)
      (boundedAbove_of_zero_one F hg1).isCoboundedUnder_ge).trans ?_
  exact Filter.liminf_le_liminf (Eventually.of_forall hh)
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall fun i =>
      add_nonneg (hf0 i) (hg0 i)))
    (boundedAbove_of_zero_one F hh1).isCoboundedUnder_ge

theorem limsup_one_sub {f : ι → ℝ}
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) :
    Filter.limsup (fun i => 1 - f i) F = 1 - Filter.liminf f F := by
  exact limsup_const_sub F f 1
    (boundedAbove_of_zero_one F hf1).isCoboundedUnder_ge
    (boundedBelow_of_zero_one F hf0)

theorem liminf_one_sub {f : ι → ℝ}
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) :
    Filter.liminf (fun i => 1 - f i) F = 1 - Filter.limsup f F := by
  exact liminf_const_sub F f 1
    (boundedAbove_of_zero_one F hf1)
    (boundedBelow_of_zero_one F hf0).isCoboundedUnder_le

theorem liminf_nonneg {f : ι → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) :
    0 ≤ Filter.liminf f F := by
  rw [← Filter.liminf_const (f := F) (0 : ℝ)]
  exact Filter.liminf_le_liminf (Eventually.of_forall hf0)
    isBoundedUnder_const (boundedAbove_of_zero_one F hf1).isCoboundedUnder_ge

theorem liminf_le_one {f : ι → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) :
    Filter.liminf f F ≤ 1 := by
  exact (Filter.liminf_le_limsup (boundedAbove_of_zero_one F hf1)
    (boundedBelow_of_zero_one F hf0)).trans
      (by
        rw [← Filter.limsup_const (f := F) (1 : ℝ)]
        exact Filter.limsup_le_limsup (Eventually.of_forall hf1)
          (boundedBelow_of_zero_one F hf0).isCoboundedUnder_le isBoundedUnder_const)

theorem limsup_nonneg {f : ι → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) :
    0 ≤ Filter.limsup f F :=
  (liminf_nonneg F hf0 hf1).trans
    (Filter.liminf_le_limsup (boundedAbove_of_zero_one F hf1)
      (boundedBelow_of_zero_one F hf0))

theorem limsup_le_one {f : ι → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) :
    Filter.limsup f F ≤ 1 := by
  rw [← Filter.limsup_const (f := F) (1 : ℝ)]
  exact Filter.limsup_le_limsup (Eventually.of_forall hf1)
    (boundedBelow_of_zero_one F hf0).isCoboundedUnder_le isBoundedUnder_const

end FilterBounds

section FiniteDensities

variable {α : Type*} [DecidableEq α]

private theorem filter_union_eq (s : Finset α) (A B : Set α) :
    s.filter (fun x => x ∈ A ∪ B) =
      s.filter (fun x => x ∈ A) ∪ s.filter (fun x => x ∈ B) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union]
  tauto

theorem filteredCard_union_le (s : Finset α) (A B : Set α) :
    (s.filter fun x => x ∈ A ∪ B).card ≤
      (s.filter fun x => x ∈ A).card + (s.filter fun x => x ∈ B).card := by
  rw [filter_union_eq]
  exact Finset.card_union_le _ _

theorem filteredCard_union_eq_of_disjoint (s : Finset α) (A B : Set α)
    (hAB : Disjoint A B) :
    (s.filter fun x => x ∈ A ∪ B).card =
      (s.filter fun x => x ∈ A).card + (s.filter fun x => x ∈ B).card := by
  rw [filter_union_eq, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro x hxA hxB
  exact Set.disjoint_left.1 hAB (Finset.mem_filter.1 hxA).2 (Finset.mem_filter.1 hxB).2

theorem filteredCard_compl (s : Finset α) (A : Set α) :
    (s.filter fun x => x ∈ Aᶜ).card = s.card - (s.filter fun x => x ∈ A).card := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := s) (fun x => x ∈ A)
  have heq : (s.filter fun x => ¬x ∈ A) = (s.filter fun x => x ∈ Aᶜ) := by
    ext x
    simp
  rw [heq] at h
  omega

end FiniteDensities

theorem natIntervalDensity_union_le (A B : Set ℕ) (a n : ℕ) :
    natIntervalDensity (A ∪ B) a n ≤
      natIntervalDensity A a n + natIntervalDensity B a n := by
  rw [natIntervalDensity, natIntervalDensity, natIntervalDensity, ← add_div]
  gcongr
  norm_cast
  convert filteredCard_union_le (natInterval a n) A B using 1
  apply congrArg Finset.card
  apply Finset.filter_congr_decidable

theorem natIntervalDensity_union_eq_of_disjoint (A B : Set ℕ) (hAB : Disjoint A B)
    (a n : ℕ) :
    natIntervalDensity (A ∪ B) a n =
      natIntervalDensity A a n + natIntervalDensity B a n := by
  rw [natIntervalDensity, natIntervalDensity, natIntervalDensity, ← add_div]
  congr 1
  norm_cast
  convert filteredCard_union_eq_of_disjoint (natInterval a n) A B hAB using 1
  apply congrArg Finset.card
  apply Finset.filter_congr_decidable

theorem natIntervalDensity_compl (A : Set ℕ) (a n : ℕ) (hn : 0 < n) :
    natIntervalDensity Aᶜ a n = 1 - natIntervalDensity A a n := by
  have hc := filteredCard_compl (natInterval a n) A
  have hc' : (natInterval a n |>.filter fun k => k ∈ Aᶜ).card =
      (natInterval a n).card - (natInterval a n |>.filter fun k => k ∈ A).card := by
    simpa only using hc
  have hcR : ((natInterval a n |>.filter fun k => k ∈ Aᶜ).card : ℝ) =
      ((natInterval a n).card - (natInterval a n |>.filter fun k => k ∈ A).card : ℕ) := by
    exact_mod_cast hc'
  rw [natIntervalDensity, natIntervalDensity]
  have hcR' : ((natInterval a n |>.filter fun k => k ∈ Aᶜ).card : ℝ) =
      ((natInterval a n).card - (natInterval a n |>.filter fun k => k ∈ A).card : ℕ) := by
    simpa only [Finset.filter_congr_decidable] using hcR
  have hfinal :
      ((natInterval a n |>.filter fun k => k ∈ Aᶜ).card : ℝ) / n =
        1 - ((natInterval a n |>.filter fun k => k ∈ A).card : ℝ) / n := by
    calc
      ((natInterval a n |>.filter fun k => k ∈ Aᶜ).card : ℝ) / n =
          (((natInterval a n).card -
            (natInterval a n |>.filter fun k => k ∈ A).card : ℕ) : ℝ) / n := by
        apply congrArg (fun x : ℝ => x / (n : ℝ))
        convert hcR' using 1
      _ = 1 - ((natInterval a n |>.filter fun k => k ∈ A).card : ℝ) / n := by
        have hcard : (natInterval a n |>.filter fun k => k ∈ A).card ≤ n := by
          exact (Finset.card_filter_le _ _).trans_eq (natInterval_card a n)
        rw [natInterval_card, Nat.cast_sub hcard, sub_div]
        field_simp [Nat.ne_of_gt hn]
  convert hfinal using 1
  · apply congrArg (fun x : ℝ => x / (n : ℝ))
    apply congrArg (fun m : ℕ => (m : ℝ))
    apply congrArg Finset.card
    apply Finset.filter_congr_decidable

theorem intIntervalDensity_union_le (A B : Set ℤ) (a : ℤ) (n : ℕ) :
    intIntervalDensity (A ∪ B) a n ≤
      intIntervalDensity A a n + intIntervalDensity B a n := by
  rw [intIntervalDensity, intIntervalDensity, intIntervalDensity, ← add_div]
  gcongr
  norm_cast
  convert filteredCard_union_le (intInterval a n) A B using 1
  apply congrArg Finset.card
  apply Finset.filter_congr_decidable

theorem intIntervalDensity_union_eq_of_disjoint (A B : Set ℤ) (hAB : Disjoint A B)
    (a : ℤ) (n : ℕ) :
    intIntervalDensity (A ∪ B) a n =
      intIntervalDensity A a n + intIntervalDensity B a n := by
  rw [intIntervalDensity, intIntervalDensity, intIntervalDensity, ← add_div]
  congr 1
  norm_cast
  convert filteredCard_union_eq_of_disjoint (intInterval a n) A B hAB using 1
  apply congrArg Finset.card
  apply Finset.filter_congr_decidable

theorem intIntervalDensity_compl (A : Set ℤ) (a : ℤ) (n : ℕ) (hn : 0 < n) :
    intIntervalDensity Aᶜ a n = 1 - intIntervalDensity A a n := by
  have hc := filteredCard_compl (intInterval a n) A
  have hc' : (intInterval a n |>.filter fun k => k ∈ Aᶜ).card =
      (intInterval a n).card - (intInterval a n |>.filter fun k => k ∈ A).card := by
    simpa only using hc
  have hcR : ((intInterval a n |>.filter fun k => k ∈ Aᶜ).card : ℝ) =
      ((intInterval a n).card - (intInterval a n |>.filter fun k => k ∈ A).card : ℕ) := by
    exact_mod_cast hc'
  rw [intIntervalDensity, intIntervalDensity]
  have hcR' : ((intInterval a n |>.filter fun k => k ∈ Aᶜ).card : ℝ) =
      ((intInterval a n).card - (intInterval a n |>.filter fun k => k ∈ A).card : ℕ) := by
    simpa only [Finset.filter_congr_decidable] using hcR
  have hfinal :
      ((intInterval a n |>.filter fun k => k ∈ Aᶜ).card : ℝ) / n =
        1 - ((intInterval a n |>.filter fun k => k ∈ A).card : ℝ) / n := by
    calc
      ((intInterval a n |>.filter fun k => k ∈ Aᶜ).card : ℝ) / n =
          (((intInterval a n).card -
            (intInterval a n |>.filter fun k => k ∈ A).card : ℕ) : ℝ) / n := by
        apply congrArg (fun x : ℝ => x / (n : ℝ))
        convert hcR' using 1
      _ = 1 - ((intInterval a n |>.filter fun k => k ∈ A).card : ℝ) / n := by
        have hcard : (intInterval a n |>.filter fun k => k ∈ A).card ≤ n := by
          exact (Finset.card_filter_le _ _).trans_eq (intInterval_card a n)
        rw [intInterval_card, Nat.cast_sub hcard, sub_div]
        field_simp [Nat.ne_of_gt hn]
  convert hfinal using 1
  · apply congrArg (fun x : ℝ => x / (n : ℝ))
    apply congrArg (fun m : ℕ => (m : ℝ))
    apply congrArg Finset.card
    apply Finset.filter_congr_decidable

theorem tendsto_natInitial_to_intervals :
    Tendsto (fun n : ℕ => (0, n)) atTop (intervalLengthFilter ℕ) := by
  rw [intervalLengthFilter, Filter.tendsto_comap_iff]
  simpa [Function.comp_def] using (tendsto_id : Tendsto id atTop atTop)

theorem tendsto_intSymmetric_to_intervals :
    Tendsto (fun n : ℕ => (-(n : ℤ), 2 * n + 1)) atTop (intervalLengthFilter ℤ) := by
  rw [intervalLengthFilter, Filter.tendsto_comap_iff]
  apply Filter.tendsto_atTop.2
  intro N
  exact Filter.eventually_atTop.2 ⟨N, fun n hn => by
    simp only [Function.comp_apply]
    omega⟩

theorem lowerBanachDensity_le_lowerAsymptoticDensity (A : Set ℕ) :
    lowerBanachDensity A ≤ lowerAsymptoticDensity A := by
  rw [lowerBanachDensity_eq_liminf, lowerAsymptoticDensity_eq_liminf]
  have h := tendsto_natInitial_to_intervals
  have hbound : (intervalLengthFilter ℕ).IsBoundedUnder (· ≥ ·)
      (fun p : ℕ × ℕ => natIntervalDensity A p.1 p.2) :=
    boundedBelow_of_zero_one _ (fun p => natIntervalDensity_nonneg A p.1 p.2)
  have hcob : (Filter.map (fun n : ℕ => (0, n)) atTop).IsCoboundedUnder (· ≥ ·)
      (fun p : ℕ × ℕ => natIntervalDensity A p.1 p.2) :=
    ((boundedAbove_of_zero_one (intervalLengthFilter ℕ)
      (fun p : ℕ × ℕ => natIntervalDensity_le_one A p.1 p.2)).mono h).isCoboundedUnder_ge
  simpa [natInitialDensity, Filter.liminf_comp, Function.comp_def] using
    Filter.liminf_le_liminf_of_le h hbound hcob

theorem upperAsymptoticDensity_le_upperBanachDensity (A : Set ℕ) :
    upperAsymptoticDensity A ≤ upperBanachDensity A := by
  rw [upperAsymptoticDensity_eq_limsup, upperBanachDensity_eq_limsup]
  have h := tendsto_natInitial_to_intervals
  have hbound : (intervalLengthFilter ℕ).IsBoundedUnder (· ≤ ·)
      (fun p : ℕ × ℕ => natIntervalDensity A p.1 p.2) :=
    boundedAbove_of_zero_one _ (fun p => natIntervalDensity_le_one A p.1 p.2)
  have hcob : (Filter.map (fun n : ℕ => (0, n)) atTop).IsCoboundedUnder (· ≤ ·)
      (fun p : ℕ × ℕ => natIntervalDensity A p.1 p.2) :=
    (boundedBelow_of_zero_one _ (fun p : ℕ × ℕ => natIntervalDensity_nonneg A p.1 p.2)).mono h
      |>.isCoboundedUnder_le
  simpa [natInitialDensity, Filter.limsup_comp, Function.comp_def] using
    Filter.limsup_le_limsup_of_le h hcob hbound

theorem lowerAsymptoticDensity_le_upperAsymptoticDensity (A : Set ℕ) :
    lowerAsymptoticDensity A ≤ upperAsymptoticDensity A := by
  rw [lowerAsymptoticDensity_eq_liminf, upperAsymptoticDensity_eq_limsup]
  exact Filter.liminf_le_limsup
    (boundedAbove_of_zero_one _ (fun n => natIntervalDensity_le_one A 0 n))
    (boundedBelow_of_zero_one _ (fun n => natIntervalDensity_nonneg A 0 n))

theorem upperBanachDensity_union_le (A B : Set ℕ) :
    upperBanachDensity (A ∪ B) ≤ upperBanachDensity A + upperBanachDensity B := by
  simp only [upperBanachDensity_eq_limsup]
  exact limsup_add_le_of_zero_one (intervalLengthFilter ℕ)
    (fun p => natIntervalDensity_nonneg A p.1 p.2)
    (fun p => natIntervalDensity_le_one A p.1 p.2)
    (fun p => natIntervalDensity_nonneg B p.1 p.2)
    (fun p => natIntervalDensity_le_one B p.1 p.2)
    (fun p => natIntervalDensity_nonneg (A ∪ B) p.1 p.2)
    (fun p => natIntervalDensity_le_one (A ∪ B) p.1 p.2)
    (fun p => natIntervalDensity_union_le A B p.1 p.2)

theorem lowerBanachDensity_union_ge_of_disjoint (A B : Set ℕ) (hAB : Disjoint A B) :
    lowerBanachDensity A + lowerBanachDensity B ≤ lowerBanachDensity (A ∪ B) := by
  simp only [lowerBanachDensity_eq_liminf]
  exact le_liminf_add_of_zero_one (intervalLengthFilter ℕ)
    (fun p => natIntervalDensity_nonneg A p.1 p.2)
    (fun p => natIntervalDensity_le_one A p.1 p.2)
    (fun p => natIntervalDensity_nonneg B p.1 p.2)
    (fun p => natIntervalDensity_le_one B p.1 p.2)
    (fun p => natIntervalDensity_nonneg (A ∪ B) p.1 p.2)
    (fun p => natIntervalDensity_le_one (A ∪ B) p.1 p.2)
    (fun p => (natIntervalDensity_union_eq_of_disjoint A B hAB p.1 p.2).ge)

theorem upperAsymptoticDensity_union_le (A B : Set ℕ) :
    upperAsymptoticDensity (A ∪ B) ≤
      upperAsymptoticDensity A + upperAsymptoticDensity B := by
  simp only [upperAsymptoticDensity_eq_limsup]
  exact limsup_add_le_of_zero_one atTop
    (fun n => natIntervalDensity_nonneg A 0 n) (fun n => natIntervalDensity_le_one A 0 n)
    (fun n => natIntervalDensity_nonneg B 0 n) (fun n => natIntervalDensity_le_one B 0 n)
    (fun n => natIntervalDensity_nonneg (A ∪ B) 0 n)
    (fun n => natIntervalDensity_le_one (A ∪ B) 0 n)
    (fun n => natIntervalDensity_union_le A B 0 n)

theorem lowerAsymptoticDensity_union_ge_of_disjoint (A B : Set ℕ)
    (hAB : Disjoint A B) :
    lowerAsymptoticDensity A + lowerAsymptoticDensity B ≤
      lowerAsymptoticDensity (A ∪ B) := by
  simp only [lowerAsymptoticDensity_eq_liminf]
  exact le_liminf_add_of_zero_one atTop
    (fun n => natIntervalDensity_nonneg A 0 n) (fun n => natIntervalDensity_le_one A 0 n)
    (fun n => natIntervalDensity_nonneg B 0 n) (fun n => natIntervalDensity_le_one B 0 n)
    (fun n => natIntervalDensity_nonneg (A ∪ B) 0 n)
    (fun n => natIntervalDensity_le_one (A ∪ B) 0 n)
    (fun n => (natIntervalDensity_union_eq_of_disjoint A B hAB 0 n).ge)

theorem upperAsymptoticDensity_compl (A : Set ℕ) :
    upperAsymptoticDensity A = 1 - lowerAsymptoticDensity Aᶜ := by
  rw [upperAsymptoticDensity_eq_limsup, lowerAsymptoticDensity_eq_liminf]
  have hcongr : ∀ᶠ n in atTop,
      natInitialDensity A n = 1 - natInitialDensity Aᶜ n := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    simpa [natInitialDensity, compl_compl] using natIntervalDensity_compl Aᶜ 0 n hn
  rw [Filter.limsup_congr hcongr]
  exact limsup_one_sub atTop
    (fun n => natIntervalDensity_nonneg Aᶜ 0 n)
    (fun n => natIntervalDensity_le_one Aᶜ 0 n)

theorem upperBanachDensity_compl (A : Set ℕ) :
    upperBanachDensity A = 1 - lowerBanachDensity Aᶜ := by
  rw [upperBanachDensity_eq_limsup, lowerBanachDensity_eq_liminf]
  have hcongr : ∀ᶠ p in intervalLengthFilter ℕ,
      natIntervalDensity A p.1 p.2 = 1 - natIntervalDensity Aᶜ p.1 p.2 := by
    rw [eventually_intervalLengthFilter_iff]
    exact ⟨1, fun a n hn => by
      simpa [compl_compl] using natIntervalDensity_compl Aᶜ a n hn⟩
  rw [Filter.limsup_congr hcongr]
  exact limsup_one_sub (intervalLengthFilter ℕ)
    (fun p => natIntervalDensity_nonneg Aᶜ p.1 p.2)
    (fun p => natIntervalDensity_le_one Aᶜ p.1 p.2)

theorem lowerBanachDensityInt_le_lowerAsymptoticDensityInt (A : Set ℤ) :
    lowerBanachDensityInt A ≤ lowerAsymptoticDensityInt A := by
  rw [lowerBanachDensityInt_eq_liminf, lowerAsymptoticDensityInt_eq_liminf]
  have h := tendsto_intSymmetric_to_intervals
  have hbound := boundedBelow_of_zero_one (intervalLengthFilter ℤ)
    (fun p : ℤ × ℕ => intIntervalDensity_nonneg A p.1 p.2)
  have hcob := ((boundedAbove_of_zero_one (intervalLengthFilter ℤ)
    (fun p : ℤ × ℕ => intIntervalDensity_le_one A p.1 p.2)).mono h).isCoboundedUnder_ge
  simpa [intSymmetricDensity, Filter.liminf_comp, Function.comp_def] using
    Filter.liminf_le_liminf_of_le h hbound hcob

theorem upperAsymptoticDensityInt_le_upperBanachDensityInt (A : Set ℤ) :
    upperAsymptoticDensityInt A ≤ upperBanachDensityInt A := by
  rw [upperAsymptoticDensityInt_eq_limsup, upperBanachDensityInt_eq_limsup]
  have h := tendsto_intSymmetric_to_intervals
  have hbound := boundedAbove_of_zero_one (intervalLengthFilter ℤ)
    (fun p : ℤ × ℕ => intIntervalDensity_le_one A p.1 p.2)
  have hcob := ((boundedBelow_of_zero_one (intervalLengthFilter ℤ)
    (fun p : ℤ × ℕ => intIntervalDensity_nonneg A p.1 p.2)).mono h).isCoboundedUnder_le
  simpa [intSymmetricDensity, Filter.limsup_comp, Function.comp_def] using
    Filter.limsup_le_limsup_of_le h hcob hbound

theorem lowerAsymptoticDensityInt_le_upperAsymptoticDensityInt (A : Set ℤ) :
    lowerAsymptoticDensityInt A ≤ upperAsymptoticDensityInt A := by
  rw [lowerAsymptoticDensityInt_eq_liminf, upperAsymptoticDensityInt_eq_limsup]
  exact Filter.liminf_le_limsup
    (boundedAbove_of_zero_one _ (intSymmetricDensity_le_one A))
    (boundedBelow_of_zero_one _ (intSymmetricDensity_nonneg A))

theorem upperBanachDensityInt_union_le (A B : Set ℤ) :
    upperBanachDensityInt (A ∪ B) ≤ upperBanachDensityInt A + upperBanachDensityInt B := by
  simp only [upperBanachDensityInt_eq_limsup]
  exact limsup_add_le_of_zero_one (intervalLengthFilter ℤ)
    (fun p => intIntervalDensity_nonneg A p.1 p.2) (fun p => intIntervalDensity_le_one A p.1 p.2)
    (fun p => intIntervalDensity_nonneg B p.1 p.2) (fun p => intIntervalDensity_le_one B p.1 p.2)
    (fun p => intIntervalDensity_nonneg (A ∪ B) p.1 p.2)
    (fun p => intIntervalDensity_le_one (A ∪ B) p.1 p.2)
    (fun p => intIntervalDensity_union_le A B p.1 p.2)

theorem lowerBanachDensityInt_union_ge_of_disjoint (A B : Set ℤ) (hAB : Disjoint A B) :
    lowerBanachDensityInt A + lowerBanachDensityInt B ≤ lowerBanachDensityInt (A ∪ B) := by
  simp only [lowerBanachDensityInt_eq_liminf]
  exact le_liminf_add_of_zero_one (intervalLengthFilter ℤ)
    (fun p => intIntervalDensity_nonneg A p.1 p.2) (fun p => intIntervalDensity_le_one A p.1 p.2)
    (fun p => intIntervalDensity_nonneg B p.1 p.2) (fun p => intIntervalDensity_le_one B p.1 p.2)
    (fun p => intIntervalDensity_nonneg (A ∪ B) p.1 p.2)
    (fun p => intIntervalDensity_le_one (A ∪ B) p.1 p.2)
    (fun p => (intIntervalDensity_union_eq_of_disjoint A B hAB p.1 p.2).ge)

theorem upperAsymptoticDensityInt_union_le (A B : Set ℤ) :
    upperAsymptoticDensityInt (A ∪ B) ≤
      upperAsymptoticDensityInt A + upperAsymptoticDensityInt B := by
  simp only [upperAsymptoticDensityInt_eq_limsup, intSymmetricDensity]
  exact limsup_add_le_of_zero_one atTop
    (fun n => intIntervalDensity_nonneg A (-(n : ℤ)) (2*n+1))
    (fun n => intIntervalDensity_le_one A (-(n : ℤ)) (2*n+1))
    (fun n => intIntervalDensity_nonneg B (-(n : ℤ)) (2*n+1))
    (fun n => intIntervalDensity_le_one B (-(n : ℤ)) (2*n+1))
    (fun n => intIntervalDensity_nonneg (A ∪ B) (-(n : ℤ)) (2*n+1))
    (fun n => intIntervalDensity_le_one (A ∪ B) (-(n : ℤ)) (2*n+1))
    (fun n => intIntervalDensity_union_le A B (-(n : ℤ)) (2*n+1))

theorem lowerAsymptoticDensityInt_union_ge_of_disjoint (A B : Set ℤ)
    (hAB : Disjoint A B) :
    lowerAsymptoticDensityInt A + lowerAsymptoticDensityInt B ≤
      lowerAsymptoticDensityInt (A ∪ B) := by
  simp only [lowerAsymptoticDensityInt_eq_liminf, intSymmetricDensity]
  exact le_liminf_add_of_zero_one atTop
    (fun n => intIntervalDensity_nonneg A (-(n : ℤ)) (2*n+1))
    (fun n => intIntervalDensity_le_one A (-(n : ℤ)) (2*n+1))
    (fun n => intIntervalDensity_nonneg B (-(n : ℤ)) (2*n+1))
    (fun n => intIntervalDensity_le_one B (-(n : ℤ)) (2*n+1))
    (fun n => intIntervalDensity_nonneg (A ∪ B) (-(n : ℤ)) (2*n+1))
    (fun n => intIntervalDensity_le_one (A ∪ B) (-(n : ℤ)) (2*n+1))
    (fun n => (intIntervalDensity_union_eq_of_disjoint A B hAB (-(n : ℤ)) (2*n+1)).ge)

theorem upperAsymptoticDensityInt_compl (A : Set ℤ) :
    upperAsymptoticDensityInt A = 1 - lowerAsymptoticDensityInt Aᶜ := by
  rw [upperAsymptoticDensityInt_eq_limsup, lowerAsymptoticDensityInt_eq_liminf]
  have hcongr : ∀ᶠ n in atTop,
      intSymmetricDensity A n = 1 - intSymmetricDensity Aᶜ n := by
    exact Eventually.of_forall fun n => by
      simpa [intSymmetricDensity, compl_compl] using
        intIntervalDensity_compl Aᶜ (-(n : ℤ)) (2*n+1) (by omega)
  rw [Filter.limsup_congr hcongr]
  exact limsup_one_sub atTop (intSymmetricDensity_nonneg Aᶜ) (intSymmetricDensity_le_one Aᶜ)

theorem upperBanachDensityInt_compl (A : Set ℤ) :
    upperBanachDensityInt A = 1 - lowerBanachDensityInt Aᶜ := by
  rw [upperBanachDensityInt_eq_limsup, lowerBanachDensityInt_eq_liminf]
  have hcongr : ∀ᶠ p in intervalLengthFilter ℤ,
      intIntervalDensity A p.1 p.2 = 1 - intIntervalDensity Aᶜ p.1 p.2 := by
    rw [eventually_intervalLengthFilter_iff]
    exact ⟨1, fun a n hn => by
      simpa [compl_compl] using intIntervalDensity_compl Aᶜ a n hn⟩
  rw [Filter.limsup_congr hcongr]
  exact limsup_one_sub (intervalLengthFilter ℤ)
    (fun p => intIntervalDensity_nonneg Aᶜ p.1 p.2)
    (fun p => intIntervalDensity_le_one Aᶜ p.1 p.2)

section DensityFamilies

theorem natIntervalDensity_mono {A B : Set ℕ} (hAB : A ⊆ B) (a n : ℕ) :
    natIntervalDensity A a n ≤ natIntervalDensity B a n := by
  unfold natIntervalDensity
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact_mod_cast Finset.card_le_card (by
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hAB hx.2⟩)

theorem intIntervalDensity_mono {A B : Set ℤ} (hAB : A ⊆ B) (a : ℤ) (n : ℕ) :
    intIntervalDensity A a n ≤ intIntervalDensity B a n := by
  unfold intIntervalDensity
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact_mod_cast Finset.card_le_card (by
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hAB hx.2⟩)

theorem lowerAsymptoticDensity_nonneg (A : Set ℕ) :
    0 ≤ lowerAsymptoticDensity A := by
  rw [lowerAsymptoticDensity_eq_liminf]
  exact liminf_nonneg atTop
    (fun n => natIntervalDensity_nonneg A 0 n)
    (fun n => natIntervalDensity_le_one A 0 n)

theorem lowerAsymptoticDensity_le_one (A : Set ℕ) :
    lowerAsymptoticDensity A ≤ 1 := by
  rw [lowerAsymptoticDensity_eq_liminf]
  exact liminf_le_one atTop
    (fun n => natIntervalDensity_nonneg A 0 n)
    (fun n => natIntervalDensity_le_one A 0 n)

theorem upperAsymptoticDensity_nonneg (A : Set ℕ) :
    0 ≤ upperAsymptoticDensity A := by
  rw [upperAsymptoticDensity_eq_limsup]
  exact limsup_nonneg atTop
    (fun n => natIntervalDensity_nonneg A 0 n)
    (fun n => natIntervalDensity_le_one A 0 n)

theorem lowerBanachDensity_nonneg (A : Set ℕ) : 0 ≤ lowerBanachDensity A := by
  rw [lowerBanachDensity_eq_liminf]
  exact liminf_nonneg (intervalLengthFilter ℕ)
    (fun p => natIntervalDensity_nonneg A p.1 p.2)
    (fun p => natIntervalDensity_le_one A p.1 p.2)

theorem lowerBanachDensity_le_one (A : Set ℕ) : lowerBanachDensity A ≤ 1 := by
  rw [lowerBanachDensity_eq_liminf]
  exact liminf_le_one (intervalLengthFilter ℕ)
    (fun p => natIntervalDensity_nonneg A p.1 p.2)
    (fun p => natIntervalDensity_le_one A p.1 p.2)

theorem upperBanachDensity_nonneg (A : Set ℕ) : 0 ≤ upperBanachDensity A := by
  rw [upperBanachDensity_eq_limsup]
  exact limsup_nonneg (intervalLengthFilter ℕ)
    (fun p => natIntervalDensity_nonneg A p.1 p.2)
    (fun p => natIntervalDensity_le_one A p.1 p.2)

theorem lowerAsymptoticDensity_mono {A B : Set ℕ} (hAB : A ⊆ B) :
    lowerAsymptoticDensity A ≤ lowerAsymptoticDensity B := by
  rw [lowerAsymptoticDensity_eq_liminf, lowerAsymptoticDensity_eq_liminf]
  exact Filter.liminf_le_liminf
    (Eventually.of_forall fun n => natIntervalDensity_mono hAB 0 n)
    (boundedBelow_of_zero_one atTop fun n => natIntervalDensity_nonneg A 0 n)
    (boundedAbove_of_zero_one atTop
      (fun n => natIntervalDensity_le_one B 0 n)).isCoboundedUnder_ge

theorem lowerBanachDensity_mono {A B : Set ℕ} (hAB : A ⊆ B) :
    lowerBanachDensity A ≤ lowerBanachDensity B := by
  rw [lowerBanachDensity_eq_liminf, lowerBanachDensity_eq_liminf]
  exact Filter.liminf_le_liminf
    (Eventually.of_forall fun p => natIntervalDensity_mono hAB p.1 p.2)
    (boundedBelow_of_zero_one (intervalLengthFilter ℕ)
      fun p => natIntervalDensity_nonneg A p.1 p.2)
    (boundedAbove_of_zero_one (intervalLengthFilter ℕ)
      (fun p => natIntervalDensity_le_one B p.1 p.2)).isCoboundedUnder_ge

theorem lowerAsymptoticDensity_empty : lowerAsymptoticDensity (∅ : Set ℕ) = 0 := by
  rw [lowerAsymptoticDensity_eq_liminf]
  rw [show natInitialDensity (∅ : Set ℕ) = fun _ => 0 by
    funext n
    simp [natInitialDensity, natIntervalDensity]]
  exact Filter.liminf_const (f := atTop) (0 : ℝ)

theorem lowerBanachDensity_empty : lowerBanachDensity (∅ : Set ℕ) = 0 := by
  rw [lowerBanachDensity_eq_liminf]
  simp [natIntervalDensity]

theorem lowerAsymptoticDensity_univ : lowerAsymptoticDensity (Set.univ : Set ℕ) = 1 := by
  have h := upperAsymptoticDensity_compl (∅ : Set ℕ)
  have hz : upperAsymptoticDensity (∅ : Set ℕ) = 0 := by
    rw [upperAsymptoticDensity_eq_limsup]
    rw [show natInitialDensity (∅ : Set ℕ) = fun _ => 0 by
      funext n
      simp [natInitialDensity, natIntervalDensity]]
    exact Filter.limsup_const (f := atTop) (0 : ℝ)
  simp only [Set.compl_empty] at h
  linarith

theorem lowerBanachDensity_univ : lowerBanachDensity (Set.univ : Set ℕ) = 1 := by
  have h := upperBanachDensity_compl (∅ : Set ℕ)
  have hz : upperBanachDensity (∅ : Set ℕ) = 0 := by
    rw [upperBanachDensity_eq_limsup]
    simp [natIntervalDensity]
  simp only [Set.compl_empty] at h
  linarith

theorem lowerAsymptoticDensityInt_nonneg (A : Set ℤ) :
    0 ≤ lowerAsymptoticDensityInt A := by
  rw [lowerAsymptoticDensityInt_eq_liminf]
  exact liminf_nonneg atTop
    (fun n => intSymmetricDensity_nonneg A n)
    (fun n => intSymmetricDensity_le_one A n)

theorem lowerAsymptoticDensityInt_le_one (A : Set ℤ) :
    lowerAsymptoticDensityInt A ≤ 1 := by
  rw [lowerAsymptoticDensityInt_eq_liminf]
  exact liminf_le_one atTop
    (fun n => intSymmetricDensity_nonneg A n)
    (fun n => intSymmetricDensity_le_one A n)

theorem upperAsymptoticDensityInt_nonneg (A : Set ℤ) :
    0 ≤ upperAsymptoticDensityInt A := by
  rw [upperAsymptoticDensityInt_eq_limsup]
  exact limsup_nonneg atTop
    (fun n => intSymmetricDensity_nonneg A n)
    (fun n => intSymmetricDensity_le_one A n)

theorem lowerBanachDensityInt_nonneg (A : Set ℤ) : 0 ≤ lowerBanachDensityInt A := by
  rw [lowerBanachDensityInt_eq_liminf]
  exact liminf_nonneg (intervalLengthFilter ℤ)
    (fun p => intIntervalDensity_nonneg A p.1 p.2)
    (fun p => intIntervalDensity_le_one A p.1 p.2)

theorem lowerBanachDensityInt_le_one (A : Set ℤ) : lowerBanachDensityInt A ≤ 1 := by
  rw [lowerBanachDensityInt_eq_liminf]
  exact liminf_le_one (intervalLengthFilter ℤ)
    (fun p => intIntervalDensity_nonneg A p.1 p.2)
    (fun p => intIntervalDensity_le_one A p.1 p.2)

theorem upperBanachDensityInt_nonneg (A : Set ℤ) : 0 ≤ upperBanachDensityInt A := by
  rw [upperBanachDensityInt_eq_limsup]
  exact limsup_nonneg (intervalLengthFilter ℤ)
    (fun p => intIntervalDensity_nonneg A p.1 p.2)
    (fun p => intIntervalDensity_le_one A p.1 p.2)

theorem lowerAsymptoticDensityInt_mono {A B : Set ℤ} (hAB : A ⊆ B) :
    lowerAsymptoticDensityInt A ≤ lowerAsymptoticDensityInt B := by
  rw [lowerAsymptoticDensityInt_eq_liminf, lowerAsymptoticDensityInt_eq_liminf]
  exact Filter.liminf_le_liminf
    (Eventually.of_forall fun n => intIntervalDensity_mono hAB (-(n : ℤ)) (2 * n + 1))
    (boundedBelow_of_zero_one atTop fun n => intSymmetricDensity_nonneg A n)
    (boundedAbove_of_zero_one atTop
      (fun n => intSymmetricDensity_le_one B n)).isCoboundedUnder_ge

theorem lowerBanachDensityInt_mono {A B : Set ℤ} (hAB : A ⊆ B) :
    lowerBanachDensityInt A ≤ lowerBanachDensityInt B := by
  rw [lowerBanachDensityInt_eq_liminf, lowerBanachDensityInt_eq_liminf]
  exact Filter.liminf_le_liminf
    (Eventually.of_forall fun p => intIntervalDensity_mono hAB p.1 p.2)
    (boundedBelow_of_zero_one (intervalLengthFilter ℤ)
      fun p => intIntervalDensity_nonneg A p.1 p.2)
    (boundedAbove_of_zero_one (intervalLengthFilter ℤ)
      (fun p => intIntervalDensity_le_one B p.1 p.2)).isCoboundedUnder_ge

theorem lowerAsymptoticDensityInt_empty :
    lowerAsymptoticDensityInt (∅ : Set ℤ) = 0 := by
  rw [lowerAsymptoticDensityInt_eq_liminf]
  rw [show intSymmetricDensity (∅ : Set ℤ) = fun _ => 0 by
    funext n
    simp [intSymmetricDensity, intIntervalDensity]]
  exact Filter.liminf_const (f := atTop) (0 : ℝ)

theorem lowerBanachDensityInt_empty : lowerBanachDensityInt (∅ : Set ℤ) = 0 := by
  rw [lowerBanachDensityInt_eq_liminf]
  simp [intIntervalDensity]

theorem lowerAsymptoticDensityInt_univ :
    lowerAsymptoticDensityInt (Set.univ : Set ℤ) = 1 := by
  have h := upperAsymptoticDensityInt_compl (∅ : Set ℤ)
  have hz : upperAsymptoticDensityInt (∅ : Set ℤ) = 0 := by
    rw [upperAsymptoticDensityInt_eq_limsup]
    rw [show intSymmetricDensity (∅ : Set ℤ) = fun _ => 0 by
      funext n
      simp [intSymmetricDensity, intIntervalDensity]]
    exact Filter.limsup_const (f := atTop) (0 : ℝ)
  simp only [Set.compl_empty] at h
  linarith

theorem lowerBanachDensityInt_univ : lowerBanachDensityInt (Set.univ : Set ℤ) = 1 := by
  have h := upperBanachDensityInt_compl (∅ : Set ℤ)
  have hz : upperBanachDensityInt (∅ : Set ℤ) = 0 := by
    rw [upperBanachDensityInt_eq_limsup]
    simp [intIntervalDensity]
  simp only [Set.compl_empty] at h
  linarith

theorem densityOneFilter_generic {X : Type*} (lower upper : Set X → ℝ)
    (hl1 : ∀ A, lower A ≤ 1)
    (hu0 : ∀ A, 0 ≤ upper A)
    (hmono : ∀ ⦃A B⦄, A ⊆ B → lower A ≤ lower B)
    (hempty : lower ∅ = 0) (huniv : lower Set.univ = 1)
    (hunion : ∀ A B, upper (A ∪ B) ≤ upper A + upper B)
    (hcompl : ∀ A, upper A = 1 - lower Aᶜ) :
    IsFilterFamily {A : Set X | lower A = 1} := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro A B hA hAB
    change lower A = 1 at hA
    change lower B = 1
    exact le_antisymm (hl1 B) (hA ▸ hmono hAB)
  · change lower ∅ ≠ 1
    rw [hempty]
    norm_num
  · exact huniv
  · intro A hA B hB
    change lower A = 1 at hA
    change lower B = 1 at hB
    have hAc : upper Aᶜ = 0 := by
      rw [hcompl, compl_compl, hA]
      norm_num
    have hBc : upper Bᶜ = 0 := by
      rw [hcompl, compl_compl, hB]
      norm_num
    have hU : upper (Aᶜ ∪ Bᶜ) = 0 :=
      le_antisymm (by simpa [hAc, hBc] using hunion Aᶜ Bᶜ) (hu0 _)
    have hc := hcompl (Aᶜ ∪ Bᶜ)
    rw [hU] at hc
    simp only [Set.compl_union, compl_compl] at hc
    change lower (A ∩ B) = 1
    linarith

theorem densityOneDual_generic {X : Type*} (lower upper : Set X → ℝ)
    (hl1 : ∀ A, lower A ≤ 1)
    (hcompl : ∀ A, upper A = 1 - lower Aᶜ) :
    familyDual {A : Set X | lower A = 1} = {A : Set X | 0 < upper A} := by
  ext A
  simp only [familyDual, Set.mem_setOf_eq]
  change lower Aᶜ ≠ 1 ↔ 0 < upper A
  rw [hcompl A]
  constructor
  · intro hne
    have hle := hl1 Aᶜ
    have hlt : lower Aᶜ < 1 := lt_of_le_of_ne hle hne
    linarith
  · intro hpos heq
    linarith

end DensityFamilies

end Chapter00
