import Chapter02.Ergodic.HopfMaximal
import Chapter02.Ergodic.ErgodicAverageLp

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter02
namespace Birkhoff

universe u

lemma invariant_iterate_ae (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : IsInvariantFunction M f) :
    ∀ n : ℕ, (fun x => f ((M.T^[n]) x)) =ᵐ[M.μ] f := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hpre := hM.2.quasiMeasurePreserving.ae_eq_comp ih
      simpa only [Function.comp_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply'] using hpre.trans hf

lemma ergodicAverage_invariant_ae (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : IsInvariantFunction M f) :
    ∀ n : ℕ, 0 < n → ergodicAverage M f n =ᵐ[M.μ] f := by
  intro n hn
  have hall : ∀ᵐ x ∂M.μ, ∀ i : Fin n,
      f ((M.T^[i]) x) = f x := by
    exact Filter.eventually_all.mpr fun i => invariant_iterate_ae M hM f hf i
  filter_upwards [hall] with x hx
  unfold ergodicAverage
  rw [if_neg (Nat.ne_of_gt hn)]
  have hsum : ∑ i ∈ Finset.range n, f ((M.T^[i]) x) = n • f x := by
    calc
      _ = ∑ _i ∈ Finset.range n, f x := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hx ⟨i, Finset.mem_range.mp hi⟩
      _ = n • f x := by simp
  rw [hsum]
  simp only [nsmul_eq_mul]
  change (n : ℂ)⁻¹ * ((n : ℂ) * f x) = f x
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)]

lemma ergodicAverage_coboundary (M : System.{u})
    (q : M.X → ℂ) (n : ℕ) (hn : n ≠ 0) (x : M.X) :
    ergodicAverage M (fun y => q (M.T y) - q y) n x =
      (n : ℂ)⁻¹ * (q ((M.T^[n]) x) - q x) := by
  unfold ergodicAverage
  rw [if_neg hn]
  congr 1
  rw [Finset.sum_sub_distrib]
  calc
    (∑ i ∈ Finset.range n, q (M.T ((M.T^[i]) x))) -
          ∑ i ∈ Finset.range n, q ((M.T^[i]) x) =
        (∑ i ∈ Finset.range n, q ((M.T^[i]) (M.T x))) -
          ∑ i ∈ Finset.range n, q ((M.T^[i]) x) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            exact congrArg q ((Function.Commute.refl M.T).iterate_right i x)
    _ = _ := ErgodicAverageLp.orbitPartialSum_comp_sub M q n x

lemma simpleFunc_norm_bound {X : Type*} [MeasurableSpace X]
    (q : MeasureTheory.SimpleFunc X ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖q x‖ ≤ C := by
  obtain ⟨C, hC⟩ := Finset.exists_le (q.range.image fun z => ‖z‖)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x
  apply (hC ‖q x‖ ?_).trans (le_max_left _ _)
  exact Finset.mem_image.mpr ⟨q x, q.mem_range_self x, rfl⟩

lemma tendsto_ergodicAverage_coboundary_simple
    (M : System.{u}) (q : MeasureTheory.SimpleFunc M.X ℂ) (x : M.X) :
    Tendsto (fun n => ergodicAverage M (fun y => q (M.T y) - q y) n x)
      atTop (nhds 0) := by
  obtain ⟨C, hC0, hC⟩ := simpleFunc_norm_bound q
  have hbound (n : ℕ) (hn : n ≠ 0) :
      ‖ergodicAverage M (fun y => q (M.T y) - q y) n x‖ ≤
        (2 * C) / n := by
    rw [ergodicAverage_coboundary M q n hn x, norm_mul, norm_inv,
      Complex.norm_natCast]
    have hsub : ‖q ((M.T^[n]) x) - q x‖ ≤ 2 * C := by
      calc
        _ ≤ ‖q ((M.T^[n]) x)‖ + ‖q x‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (hC _) (hC _)
        _ = 2 * C := by ring
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hsub (by positivity)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => norm_nonneg _
  · filter_upwards [eventually_ne_atTop 0] with n hn
    exact hbound n hn
  · exact tendsto_const_div_atTop_nhds_zero_nat (2 * C)

lemma ergodicAverage_add (M : System.{u}) (f g : M.X → ℂ)
    (n : ℕ) (x : M.X) :
    ergodicAverage M (fun y => f y + g y) n x =
      ergodicAverage M f n x + ergodicAverage M g n x := by
  by_cases hn : n = 0
  · simp [ergodicAverage, hn]
  · simp only [ergodicAverage, hn, if_false, Finset.sum_add_distrib]
    ring

lemma exists_good_approximation (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 1 f)
    {δ : ENNReal} (hδ0 : δ ≠ 0) (hδtop : δ ≠ ⊤) :
    ∃ fstar h : M.X → ℂ,
      M.lpMember 1 fstar ∧ IsInvariantFunction M fstar ∧ M.lpMember 1 h ∧
      MeasureTheory.eLpNorm (fun x => f x - h x) 1 M.μ < δ ∧
      ∀ᵐ x ∂M.μ, Tendsto (fun n => ergodicAverage M h n x)
        atTop (nhds (fstar x)) := by
  obtain ⟨fstar, hfstar, hfinv, hconv, hce, hint, herg⟩ :=
    ErgodicAverageLp.meanErgodicSystemStatement_one M hM f hf
  have hδ4 : δ / 4 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hδ0, by norm_num⟩
  have hev : ∀ᶠ N : ℕ in atTop,
      MeasureTheory.eLpNorm (fun x => ergodicAverage M f N x - fstar x)
        1 M.μ < δ / 4 := by
    exact hconv.eventually (Iio_mem_nhds (by positivity))
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < N := eventually_gt_atTop 0
  obtain ⟨N, hNavg, hNpos⟩ := (hev.and hpos).exists
  let q : M.X → ℂ := ErgodicAverageLp.coboundaryApproximant M f N
  have hq : M.lpMember 1 q :=
    ErgodicAverageLp.coboundaryApproximant_memLp_one M hM f hf N
  have hδ8 : δ / 8 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hδ0, by norm_num⟩
  obtain ⟨s, hqs, hs⟩ := hq.exists_simpleFunc_eLpNorm_sub_lt
    (by norm_num : (1 : ENNReal) ≠ ⊤) hδ8
  let cob : M.X → ℂ := fun x => s (M.T x) - s x
  let h : M.X → ℂ := fun x => fstar x + cob x
  have hcob : M.lpMember 1 cob := by
    exact (hs.comp_measurePreserving hM.2).sub hs
  have hh : M.lpMember 1 h := hfstar.add hcob
  have hid : (fun x => f x - h x) =
      (fun x => ergodicAverage M f N x - fstar x) +
        ((q - ⇑s) ∘ M.T - (q - ⇑s)) := by
    funext x
    have hqidentity := ErgodicAverageLp.coboundaryApproximant_identity
      M f N (Nat.ne_of_gt hNpos) x
    dsimp [h, cob, q]
    change f x - (fstar x + (s (M.T x) - s x)) =
      (ergodicAverage M f N x - fstar x) +
        ((q (M.T x) - s (M.T x)) - (q x - s x))
    dsimp [q] at hqidentity ⊢
    rw [← hqidentity]
    ring
  have hdiff : MeasureTheory.eLpNorm
      (((q - ⇑s) ∘ M.T) - (q - ⇑s)) 1 M.μ < δ / 4 := by
    have hmeas : AEStronglyMeasurable (q - ⇑s) M.μ :=
      (hq.sub hs).aestronglyMeasurable
    calc
      _ ≤ MeasureTheory.eLpNorm ((q - ⇑s) ∘ M.T) 1 M.μ +
          MeasureTheory.eLpNorm (q - ⇑s) 1 M.μ :=
        MeasureTheory.eLpNorm_sub_le
          (hmeas.comp_quasiMeasurePreserving hM.2.quasiMeasurePreserving)
          hmeas le_rfl
      _ = MeasureTheory.eLpNorm (q - ⇑s) 1 M.μ +
          MeasureTheory.eLpNorm (q - ⇑s) 1 M.μ := by
        rw [MeasureTheory.eLpNorm_comp_measurePreserving hmeas hM.2]
      _ < δ / 8 + δ / 8 := ENNReal.add_lt_add hqs hqs
      _ = δ / 4 := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        rw [← add_mul]
        have hc : (8 : ENNReal)⁻¹ + 8⁻¹ = 4⁻¹ := by
          apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
          norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]
        rw [hc]
  have herr : MeasureTheory.eLpNorm (fun x => f x - h x) 1 M.μ < δ := by
    rw [hid]
    calc
      _ ≤ MeasureTheory.eLpNorm
            (fun x => ergodicAverage M f N x - fstar x) 1 M.μ +
          MeasureTheory.eLpNorm (((q - ⇑s) ∘ M.T) - (q - ⇑s)) 1 M.μ :=
        MeasureTheory.eLpNorm_add_le
          ((ErgodicAverageLp.ergodicAverage_memLp M hM 1 f hf N).sub hfstar).1
          ((hq.sub hs).comp_measurePreserving hM.2 |>.sub (hq.sub hs)).1 le_rfl
      _ < δ / 4 + δ / 4 := ENNReal.add_lt_add hNavg hdiff
      _ = δ / 2 := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        rw [← add_mul]
        have hc : (4 : ENNReal)⁻¹ + 4⁻¹ = 2⁻¹ := by
          apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
          norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]
        rw [hc]
      _ < δ := by
        rw [← ENNReal.toReal_lt_toReal (by finiteness) hδtop]
        simpa [ENNReal.toReal_div] using ENNReal.toReal_pos hδ0 hδtop
  refine ⟨fstar, h, hfstar, hfinv, hh, herr, ?_⟩
  have hinvAll : ∀ᵐ x ∂M.μ, ∀ n : ℕ, 0 < n →
      ergodicAverage M fstar n x = fstar x := by
    apply ae_all_iff.mpr
    intro n
    by_cases hn : 0 < n
    · exact (ergodicAverage_invariant_ae M hM fstar hfinv n hn).mono
        fun x hx _ => hx
    · exact Eventually.of_forall fun x h => (hn h).elim
  filter_upwards [hinvAll] with x hx
  have hcoblim := tendsto_ergodicAverage_coboundary_simple M s x
  have heq : ∀ᶠ n : ℕ in atTop,
      ergodicAverage M h n x = fstar x + ergodicAverage M cob n x := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [show h = fun y => fstar y + cob y by rfl,
      ergodicAverage_add, hx n hn]
  have hbase : Tendsto
      (fun n => fstar x + ergodicAverage M cob n x) atTop (nhds (fstar x)) := by
    simpa [cob] using tendsto_const_nhds.add hcoblim
  have heq' : (fun n => fstar x + ergodicAverage M cob n x) =ᶠ[atTop]
      (fun n => ergodicAverage M h n x) := by
    filter_upwards [heq] with n hn
    exact hn.symm
  exact Filter.Tendsto.congr' heq' hbase

lemma maximal_difference_measure_le (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (g : M.X → ℂ) (hg : M.lpMember 1 g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hsmall : MeasureTheory.eLpNorm g 1 M.μ < ENNReal.ofReal (a * b)) :
    M.μ {x | ∃ n : ℕ, 0 < n ∧ a < ‖ergodicAverage M g n x‖} ≤
      ENNReal.ofReal b := by
  have hweak := HopfMaximal.weakTypeMaximal M hM g hg a ha
  refine hweak.trans ?_
  have hnorm : ENNReal.ofReal (MeasureTheory.eLpNorm g 1 M.μ).toReal ≤
      ENNReal.ofReal (a * b) := by
    apply ENNReal.ofReal_le_ofReal
    have ht := (ENNReal.toReal_lt_toReal hg.eLpNorm_ne_top (by finiteness)).mpr hsmall
    rw [ENNReal.toReal_ofReal (mul_nonneg ha.le hb)] at ht
    exact le_of_lt ht
  calc
    ENNReal.ofReal (MeasureTheory.eLpNorm g 1 M.μ).toReal / ENNReal.ofReal a
        ≤ ENNReal.ofReal (a * b) / ENNReal.ofReal a :=
          ENNReal.div_le_div_right hnorm _
    _ = ENNReal.ofReal b := by
      rw [ENNReal.ofReal_mul (le_of_lt ha)]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp [ENNReal.toReal_div, ENNReal.toReal_ofReal ha.le,
        ENNReal.toReal_ofReal hb, ne_of_gt ha]

lemma ergodicAverage_sub (M : System.{u}) (f g : M.X → ℂ)
    (n : ℕ) (x : M.X) :
    ergodicAverage M (fun y => f y - g y) n x =
      ergodicAverage M f n x - ergodicAverage M g n x := by
  by_cases hn : n = 0
  · simp [ergodicAverage, hn]
  · simp only [ergodicAverage, hn, if_false, Finset.sum_sub_distrib]
    ring

lemma ae_cauchy_ergodicAverage (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 1 f) :
    ∀ᵐ x ∂M.μ, CauchySeq (fun n => ergodicAverage M f n x) := by
  let a : ℕ → ℝ := fun k => 1 / ((k + 1 : ℕ) : ℝ)
  let b : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (k + 1)
  have ha : ∀ k, 0 < a k := by
    intro k
    simp [a]
    positivity
  have hb : ∀ k, 0 < b k := by
    intro k
    positivity
  have happ : ∀ k : ℕ, ∃ fstar h : M.X → ℂ,
      M.lpMember 1 fstar ∧ IsInvariantFunction M fstar ∧ M.lpMember 1 h ∧
      MeasureTheory.eLpNorm (fun x => f x - h x) 1 M.μ <
        ENNReal.ofReal (a k * b k) ∧
      ∀ᵐ x ∂M.μ, Tendsto (fun n => ergodicAverage M h n x)
        atTop (nhds (fstar x)) := by
    intro k
    apply exists_good_approximation M hM f hf
    · exact (ENNReal.ofReal_pos.mpr (mul_pos (ha k) (hb k))).ne'
    · exact ENNReal.ofReal_ne_top
  choose fstar h hfstar hfinv hh herr hlim using happ
  let E : ℕ → Set M.X := fun k =>
    {x | ∃ n : ℕ, 0 < n ∧ a k < ‖ergodicAverage M (fun y => f y - h k y) n x‖}
  have hE : ∀ k, M.μ (E k) ≤ ENNReal.ofReal (b k) := by
    intro k
    exact maximal_difference_measure_le M hM (fun y => f y - h k y)
      (hf.sub (hh k)) (ha k) (hb k).le (herr k)
  have hEb : ∀ k, ENNReal.ofReal (b k) = (1 / 2 : ENNReal) ^ (k + 1) := by
    intro k
    rw [show b k = (1 / 2 : ℝ) ^ (k + 1) by rfl,
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]
  have hsum : (∑' k, M.μ (E k)) ≠ ⊤ := by
    have hle : (∑' k, M.μ (E k)) ≤
        ∑' k : ℕ, (1 / 2 : ENNReal) ^ (k + 1) := by
      apply ENNReal.tsum_le_tsum
      intro k
      rw [← hEb k]
      exact hE k
    have hshift : (∑' k : ℕ, (1 / 2 : ENNReal) ^ (k + 1)) ≤
        ∑' k : ℕ, (1 / 2 : ENNReal) ^ k := by
      apply ENNReal.tsum_le_tsum
      intro k
      rw [pow_succ]
      exact mul_le_of_le_one_right (by positivity) (by norm_num)
    have hgeom : (∑' k : ℕ, (1 / 2 : ENNReal) ^ (k + 1)) < ⊤ :=
      hshift.trans_lt (tsum_geometric_lt_top.mpr (by norm_num))
    exact ne_top_of_le_ne_top hgeom.ne hle
  have hnotE : ∀ᵐ x ∂M.μ, ∀ᶠ k in atTop, x ∉ E k :=
    MeasureTheory.ae_eventually_notMem hsum
  have hgood : ∀ᵐ x ∂M.μ, ∀ k, Tendsto
      (fun n => ergodicAverage M (h k) n x) atTop (nhds (fstar k x)) := by
    exact ae_all_iff.mpr hlim
  filter_upwards [hnotE, hgood] with x hxE hxgood
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hatend : Tendsto a atTop (nhds 0) := by
    have hae : a = fun n : ℕ => 1 / ((n : ℝ) + 1) := by
      funext n
      simp [a, Nat.cast_add, Nat.cast_one]
    rw [hae]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hev : ∀ᶠ k in atTop, 4 * a k < ε :=
    (hatend.const_mul 4).eventually (Iio_mem_nhds (by simpa using hε))
  obtain ⟨k, hkE, hkε⟩ := (hxE.and hev).exists
  have hkconv := hxgood k
  rw [Metric.tendsto_atTop] at hkconv
  obtain ⟨N, hN⟩ := hkconv (ε / 4) (by positivity)
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hdiff (j : ℕ) :
      ‖ergodicAverage M (fun y => f y - h k y) j x‖ ≤ a k := by
    by_cases hj : j = 0
    · subst j
      simp [ergodicAverage]
      exact (ha k).le
    · exact le_of_not_gt fun hjgt => hkE ⟨j, Nat.pos_of_ne_zero hj, hjgt⟩
  have hfm : dist (ergodicAverage M f m x) (ergodicAverage M (h k) m x) ≤ a k := by
    rw [dist_eq_norm, ← ergodicAverage_sub]
    exact hdiff m
  have hfn : dist (ergodicAverage M (h k) n x) (ergodicAverage M f n x) ≤ a k := by
    rw [dist_comm, dist_eq_norm, ← ergodicAverage_sub]
    exact hdiff n
  calc
    dist (ergodicAverage M f m x) (ergodicAverage M f n x) ≤
        dist (ergodicAverage M f m x) (ergodicAverage M (h k) m x) +
        dist (ergodicAverage M (h k) m x) (ergodicAverage M f n x) :=
      dist_triangle _ _ _
    _ ≤ dist (ergodicAverage M f m x) (ergodicAverage M (h k) m x) +
        (dist (ergodicAverage M (h k) m x) (fstar k x) +
        dist (fstar k x) (ergodicAverage M f n x)) := by
      gcongr
      exact dist_triangle _ _ _
    _ ≤ dist (ergodicAverage M f m x) (ergodicAverage M (h k) m x) +
        (dist (ergodicAverage M (h k) m x) (fstar k x) +
        (dist (fstar k x) (ergodicAverage M (h k) n x) +
        dist (ergodicAverage M (h k) n x) (ergodicAverage M f n x))) := by
      gcongr
      exact dist_triangle _ _ _
    _ ≤ a k + ε / 4 + (ε / 4 + a k) := by
      have hm' := (hN m hm).le
      have hn' : dist (fstar k x) (ergodicAverage M (h k) n x) ≤ ε / 4 := by
        simpa [dist_comm] using (hN n hn).le
      linarith
    _ < ε := by linarith

theorem birkhoffPointwiseErgodic (M : System.{u}) :
    BirkhoffPointwiseErgodicStatement M := by
  intro hM f hf
  obtain ⟨fstar, hfstar, hfinv, hnorm, hce, hint, herg⟩ :=
    ErgodicAverageLp.meanErgodicSystemStatement_one M hM f hf
  have havgMeas : ∀ n : ℕ,
      MeasureTheory.AEStronglyMeasurable (ergodicAverage M f n) M.μ := by
    intro n
    exact (ErgodicAverageLp.ergodicAverage_memLp M hM 1 f hf n).aestronglyMeasurable
  have hinMeasure : MeasureTheory.TendstoInMeasure M.μ
      (fun n => ergodicAverage M f n) atTop fstar := by
    exact MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (by norm_num) havgMeas hfstar.aestronglyMeasurable hnorm
  obtain ⟨ns, hns, hsub⟩ := hinMeasure.exists_seq_tendsto_ae
  have hcauchy := ae_cauchy_ergodicAverage M hM f hf
  have hpoint : ErgodicAverageAETends M f fstar := by
    filter_upwards [hcauchy, hsub] with x hxc hxsub
    apply tendsto_nhds_of_cauchySeq_of_subseq hxc hns.tendsto_atTop
    simpa only [Function.comp_apply] using hxsub
  exact ⟨fstar, hfstar, hfinv, hpoint, hint⟩

end Birkhoff
end Chapter02
