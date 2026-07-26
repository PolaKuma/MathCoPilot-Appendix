import Chapter04.Common

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter04.LebesgueSpectrum

universe u

theorem act_ofNat_eq_iterate (M : System.{u}) (U : MeasureIntegerActionData M)
    (n : ℕ) : U.act (n : ℤ) = M.T^[n] := by
  induction n with
  | zero => simpa using U.zero_act
  | succ n ih =>
      rw [Nat.cast_succ]
      rw [U.add_act, U.one_act, ih]
      exact Function.iterate_succ M.T n

theorem orbit_correlation
    (M : System.{u}) (U : MeasureIntegerActionData M)
    (f : ℕ → M.X → ℂ) (i j : ℕ) (m l : ℤ) (n : ℕ) :
    Chapter02.functionCorrelation M
      (Chapter01.koopman (U.act m) (f i))
      (Chapter01.koopman (U.act l) (f j)) n =
      l2Inner M
        (Chapter01.koopman (U.act (m + (n : ℤ))) (f i))
        (Chapter01.koopman (U.act l) (f j)) := by
  unfold Chapter02.functionCorrelation l2Inner Chapter01.koopman
  congr 1
  funext x
  rw [← act_ofNat_eq_iterate M U n]
  rw [U.add_act]
  rfl

theorem orbit_correlation_eq
    (M : System.{u}) (U : MeasureIntegerActionData M)
    (f : ℕ → M.X → ℂ)
    (horth : ∀ i j m n, l2Inner M
      (Chapter01.koopman (U.act m) (f i))
      (Chapter01.koopman (U.act n) (f j)) =
        if i = j ∧ m = n then 1 else 0)
    (i j : ℕ) (m l : ℤ) (n : ℕ) :
    Chapter02.functionCorrelation M
      (Chapter01.koopman (U.act m) (f i))
      (Chapter01.koopman (U.act l) (f j)) n =
      if i = j ∧ m + (n : ℤ) = l then 1 else 0 := by
  rw [orbit_correlation M U f i j m l n]
  exact horth i j (m + (n : ℤ)) l

def combination {X : Type u} (s : Finset (X → ℂ))
    (c : (X → ℂ) → ℂ) : X → ℂ :=
  fun x => ∑ g ∈ s, c g * g x

theorem combination_memLp
    (M : System.{u}) (s : Finset (M.X → ℂ)) (c : (M.X → ℂ) → ℂ)
    (hs : ∀ g ∈ s, M.lpMember 2 g) : M.lpMember 2 (combination s c) := by
  change MeasureTheory.MemLp (combination s c) 2 M.μ
  induction s using Finset.induction_on with
  | empty =>
      have hz := MeasureTheory.MemLp.zero
        (μ := M.μ) (p := (2 : ENNReal)) (ε := ℂ)
      simpa only [combination, Finset.sum_empty] using hz
  | @insert g s hnot ih =>
      have hg := (hs g (Finset.mem_insert_self g s)).const_mul (c g)
      have hs' := ih (fun h hh => hs h (Finset.mem_insert_of_mem hh))
      have heq : combination (insert g s) c =
          (fun x => c g * g x) + combination s c := by
        funext x
        simp [combination, Finset.sum_insert hnot]
      rw [heq]
      exact hg.add hs'

private theorem functionCorrelation_eq_innerLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f g : M.X → ℂ) (hf : M.lpMember 2 f) (hg : M.lpMember 2 g) (n : ℕ) :
    Chapter02.functionCorrelation M f g n =
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (hg.toLp g)
        (((hf.comp_measurePreserving (hM.2.iterate n)).toLp
          (fun x => f ((M.T^[n]) x)))) := by
  rw [MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hg.coeFn_toLp,
      (hf.comp_measurePreserving (hM.2.iterate n)).coeFn_toLp] with x hgx hfx
  simp only [RCLike.inner_apply, starRingEnd_apply]
  have hfx' :
      ((hf.comp_measurePreserving (hM.2.iterate n)).toLp
        (fun x => f ((M.T^[n]) x))) x = f ((M.T^[n]) x) := by
    simpa [Function.comp_apply] using hfx
  rw [hgx, hfx']

theorem norm_functionCorrelation_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f g : M.X → ℂ) (hf : M.lpMember 2 f) (hg : M.lpMember 2 g) (n : ℕ) :
    ‖Chapter02.functionCorrelation M f g n‖ ≤
      (MeasureTheory.eLpNorm f 2 M.μ).toReal *
        (MeasureTheory.eLpNorm g 2 M.μ).toReal := by
  rw [functionCorrelation_eq_innerLp M hM f g hf hg n]
  calc
    ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (hg.toLp g)
        ((hf.comp_measurePreserving (hM.2.iterate n)).toLp
          (fun x => f ((M.T^[n]) x)))‖ ≤
      ‖hg.toLp g‖ *
        ‖(hf.comp_measurePreserving (hM.2.iterate n)).toLp
          (fun x => f ((M.T^[n]) x))‖ := norm_inner_le_norm _ _
    _ = (MeasureTheory.eLpNorm g 2 M.μ).toReal *
        (MeasureTheory.eLpNorm f 2 M.μ).toReal := by
      rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp]
      congr 1
      exact congrArg ENNReal.toReal (by
        simpa [Function.comp_def] using
          (MeasureTheory.eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
            (hM.2.iterate n)))
    _ = _ := mul_comm _ _

theorem functionCorrelation_difference
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f g F G : M.X → ℂ)
    (hf : M.lpMember 2 f) (hg : M.lpMember 2 g)
    (hF : M.lpMember 2 F) (hG : M.lpMember 2 G) (n : ℕ) :
    Chapter02.functionCorrelation M f g n -
        Chapter02.functionCorrelation M F G n =
      Chapter02.functionCorrelation M (fun x => f x - F x) g n +
        Chapter02.functionCorrelation M F (fun x => g x - G x) n := by
  have hfg := (hf.comp_measurePreserving (hM.2.iterate n)).integrable_mul hg.star
  have hFG := (hF.comp_measurePreserving (hM.2.iterate n)).integrable_mul hG.star
  have hefg := ((hf.sub hF).comp_measurePreserving
    (hM.2.iterate n)).integrable_mul hg.star
  have hFeG := (hF.comp_measurePreserving
    (hM.2.iterate n)).integrable_mul (hg.sub hG).star
  have hfg' : MeasureTheory.Integrable
      (fun x => f ((M.T^[n]) x) * star (g x)) M.μ := by
    simpa [Function.comp_def] using hfg
  have hFG' : MeasureTheory.Integrable
      (fun x => F ((M.T^[n]) x) * star (G x)) M.μ := by
    simpa [Function.comp_def] using hFG
  have hefg'' : MeasureTheory.Integrable
      (fun x => (f ((M.T^[n]) x) - F ((M.T^[n]) x)) * star (g x)) M.μ := by
    simpa [Function.comp_def] using hefg
  have hFeG' : MeasureTheory.Integrable
      (fun x => F ((M.T^[n]) x) * star (g x - G x)) M.μ := by
    simpa [Function.comp_def] using hFeG
  unfold Chapter02.functionCorrelation
  rw [← MeasureTheory.integral_sub hfg' hFG',
    ← MeasureTheory.integral_add hefg'' hFeG']
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change f ((M.T^[n]) x) * star (g x) - F ((M.T^[n]) x) * star (G x) =
      (f ((M.T^[n]) x) - F ((M.T^[n]) x)) * star (g x) +
        F ((M.T^[n]) x) * star (g x - G x)
    rw [star_sub]
    ring

theorem functionCorrelation_combination
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (s t : Finset (M.X → ℂ)) (c d : (M.X → ℂ) → ℂ)
    (hs : ∀ g ∈ s, M.lpMember 2 g) (ht : ∀ g ∈ t, M.lpMember 2 g)
    (n : ℕ) :
    Chapter02.functionCorrelation M (combination s c) (combination t d) n =
      ∑ g ∈ s, ∑ h ∈ t,
        c g * star (d h) * Chapter02.functionCorrelation M g h n := by
  have hpoint : (fun x => combination s c ((M.T^[n]) x) *
      star (combination t d x)) = fun x =>
      ∑ g ∈ s, ∑ h ∈ t,
        (c g * star (d h)) * (g ((M.T^[n]) x) * star (h x)) := by
    funext x
    unfold combination
    rw [star_sum]
    simp_rw [star_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g hg
    apply Finset.sum_congr rfl
    intro h hh
    ring
  unfold Chapter02.functionCorrelation
  rw [hpoint]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro g hg
    rw [MeasureTheory.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro h hh
      rw [MeasureTheory.integral_const_mul]
    · intro h hh
      exact (((hs g hg).comp_measurePreserving (hM.2.iterate n)).integrable_mul
        (ht h hh).star).const_mul (c g * star (d h))
  · intro g hg
    clear hpoint
    induction t using Finset.induction_on with
    | empty => simp
    | @insert h t hnot ih =>
        have hhead := (((hs g hg).comp_measurePreserving
          (hM.2.iterate n)).integrable_mul
            (ht h (Finset.mem_insert_self h t)).star).const_mul
              (c g * star (d h))
        have htail := ih (fun k hk => ht k (Finset.mem_insert_of_mem hk))
        simpa only [Finset.sum_insert hnot] using hhead.add htail

theorem finite_orbit_combinations_eventually_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (U : MeasureIntegerActionData M) (f : ℕ → M.X → ℂ)
    (hf : ∀ i, M.lpMember 2 (f i))
    (horth : ∀ i j m n, l2Inner M
      (Chapter01.koopman (U.act m) (f i))
      (Chapter01.koopman (U.act n) (f j)) =
        if i = j ∧ m = n then 1 else 0)
    (s t : Finset (M.X → ℂ)) (c d : (M.X → ℂ) → ℂ)
    (is : (M.X → ℂ) → ℕ) (ms : (M.X → ℂ) → ℤ)
    (it : (M.X → ℂ) → ℕ) (mt : (M.X → ℂ) → ℤ)
    (hsrep : ∀ g ∈ s, g = Chapter01.koopman (U.act (ms g)) (f (is g)))
    (htrep : ∀ g ∈ t, g = Chapter01.koopman (U.act (mt g)) (f (it g))) :
    ∃ N : ℕ, ∀ n ≥ N,
      Chapter02.functionCorrelation M (combination s c) (combination t d) n = 0 := by
  let K : ℕ := ∑ g ∈ s, ∑ h ∈ t, (mt h - ms g).natAbs
  refine ⟨K + 1, ?_⟩
  intro n hn
  have hsLp (g : M.X → ℂ) (hg : g ∈ s) : M.lpMember 2 g := by
    rw [hsrep g hg]
    exact (hf (is g)).comp_measurePreserving (U.measure_preserving (ms g))
  have htLp (g : M.X → ℂ) (hg : g ∈ t) : M.lpMember 2 g := by
    rw [htrep g hg]
    exact (hf (it g)).comp_measurePreserving (U.measure_preserving (mt g))
  rw [functionCorrelation_combination M hM s t c d hsLp htLp n]
  apply Finset.sum_eq_zero
  intro g hg
  apply Finset.sum_eq_zero
  intro h hh
  have hne : ¬ (is g = it h ∧ ms g + (n : ℤ) = mt h) := by
    rintro ⟨_, heq⟩
    have hnEq : n = (mt h - ms g).natAbs := by
      have hz : (n : ℤ) = mt h - ms g := by omega
      simpa using congrArg Int.natAbs hz
    have hinner : (mt h - ms g).natAbs ≤ ∑ k ∈ t, (mt k - ms g).natAbs :=
      Finset.single_le_sum (s := t) (f := fun k => (mt k - ms g).natAbs)
        (fun _ _ => Nat.zero_le _) hh
    have houter : (∑ k ∈ t, (mt k - ms g).natAbs) ≤ K := by
      have hle := Finset.single_le_sum (s := s)
        (f := fun q => ∑ k ∈ t, (mt k - ms q).natAbs)
        (fun _ _ => Nat.zero_le _) hg
      simpa [K] using hle
    have hnK : n ≤ K := hnEq.trans_le (hinner.trans houter)
    omega
  rw [hsrep g hg, htrep h hh,
    orbit_correlation_eq M U f horth (is g) (it h) (ms g) (mt h) n]
  simp [hne]

end Chapter04.LebesgueSpectrum
