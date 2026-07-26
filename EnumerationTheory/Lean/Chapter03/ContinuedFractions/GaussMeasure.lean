import Chapter03.Section01

noncomputable section
open Classical Filter MeasureTheory
open scoped BigOperators ENNReal
namespace Chapter03

def gaussDensityReal (x : ℝ) : ℝ :=
  (Real.log 2 * (1 + x))⁻¹

private theorem gaussDensity_integral :
    ∫ x in Set.Icc (0 : ℝ) 1, gaussDensityReal x = 1 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num only : (0 : ℝ) ≤ 1)]
  calc
    ∫ x : ℝ in 0..1, gaussDensityReal x =
        (Real.log 2)⁻¹ * ∫ x : ℝ in 0..1, (1 + x)⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [gaussDensityReal]
      field_simp
    _ = (Real.log 2)⁻¹ * ∫ x : ℝ in 1..2, x⁻¹ := by
      rw [intervalIntegral.integral_comp_add_left (fun x : ℝ => x⁻¹) 1]
      norm_num only
    _ = (Real.log 2)⁻¹ * Real.log 2 := by
      rw [integral_inv_of_pos (by norm_num only : (0 : ℝ) < 1)
        (by norm_num only : (0 : ℝ) < 2)]
      simp only [div_one]
    _ = 1 := by
      rw [inv_mul_cancel₀ (Real.log_pos (by norm_num only : (1 : ℝ) < 2)).ne']

private theorem gaussMeasureOnReal_univ :
    gaussMeasureOnReal Set.univ = 1 := by
  let f : ℝ → ℝ := gaussDensityReal
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx hz
      have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num only)
      have hxpos : 0 < 1 + x := by linarith [hx.1]
      nlinarith
  have hfi : Integrable f (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hfcont.integrableOn_Icc
  have hfnn : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    dsimp [f, gaussDensityReal]
    exact inv_nonneg.mpr
      (mul_nonneg (Real.log_pos (by norm_num only)).le (by linarith [hx.1]))
  rw [gaussMeasureOnReal, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  change (∫⁻ a : ℝ, ENNReal.ofReal (f a)
    ∂volume.restrict (Set.Icc 0 1)) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hfnn]
  change ENNReal.ofReal
    (∫ x in Set.Icc (0 : ℝ) 1, gaussDensityReal x) = 1
  rw [gaussDensity_integral]
  simp only [ENNReal.ofReal_one]

theorem gaussMeasure_isProbability : IsProbabilityMeasure gaussMeasure := by
  constructor
  rw [gaussMeasure]
  have hproj : Measurable unitIntervalProjection := by
    apply Measurable.subtype_mk
    fun_prop
  rw [Measure.map_apply_of_aemeasurable hproj.aemeasurable MeasurableSet.univ]
  simp only [Set.preimage_univ]
  exact gaussMeasureOnReal_univ

theorem gaussMap_measurable : Measurable gaussMap := by
  apply Measurable.subtype_mk
  change Measurable fun x : GaussSpace =>
    x.1⁻¹ - (Int.floor x.1⁻¹ : ℝ)
  fun_prop

theorem gaussMeasure_apply {s : Set GaussSpace} (hs : MeasurableSet s) :
    gaussMeasure s =
      ∫⁻ x : ℝ in Subtype.val '' s,
        ENNReal.ofReal (gaussDensityReal x) ∂volume := by
  rw [gaussMeasure]
  have hproj : Measurable unitIntervalProjection := by
    apply Measurable.subtype_mk
    fun_prop
  rw [Measure.map_apply_of_aemeasurable hproj.aemeasurable hs]
  rw [gaussMeasureOnReal, withDensity_apply _ (hproj hs)]
  change (∫⁻ x : ℝ,
      ENNReal.ofReal (gaussDensityReal x)
        ∂(volume.restrict (Set.Icc 0 1)).restrict
          (unitIntervalProjection ⁻¹' s)) = _
  rw [Measure.restrict_restrict (hproj hs)]
  have hset : unitIntervalProjection ⁻¹' s ∩ Set.Icc (0 : ℝ) 1 =
      Subtype.val '' s := by
    ext x
    constructor
    · rintro ⟨hsx, hx⟩
      have hprojx : unitIntervalProjection x = ⟨x, hx⟩ := by
        apply Subtype.ext
        simp [unitIntervalProjection, min_eq_right hx.2,
          max_eq_right hx.1]
      change unitIntervalProjection x ∈ s at hsx
      rw [hprojx] at hsx
      exact ⟨⟨x, hx⟩, hsx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, y.2⟩
      have hprojy : unitIntervalProjection (y : ℝ) = y := by
        apply Subtype.ext
        simp [unitIntervalProjection, min_eq_right y.2.2,
          max_eq_right y.2.1]
      change unitIntervalProjection (y : ℝ) ∈ s
      rw [hprojy]
      exact hy
  rw [hset]

def gaussBranch (n : ℕ) (y : ℝ) : ℝ :=
  (((n + 1 : ℕ) : ℝ) + y)⁻¹

private def gaussTransferTerm (n : ℕ) (y : ℝ) : ℝ :=
  (Real.log 2)⁻¹ *
    ((((n + 1 : ℕ) : ℝ) + y) * (((n + 2 : ℕ) : ℝ) + y))⁻¹

private theorem gaussTransferTerm_nonneg (y : ℝ) (hy : 0 ≤ y) (n : ℕ) :
    0 ≤ gaussTransferTerm n y := by
  dsimp [gaussTransferTerm]
  positivity

private theorem gaussTransferTerm_eq_sub (y : ℝ) (hy : 0 ≤ y) (n : ℕ) :
    gaussTransferTerm n y =
      (Real.log 2)⁻¹ * ((((n + 1 : ℕ) : ℝ) + y)⁻¹) -
        (Real.log 2)⁻¹ * ((((n + 2 : ℕ) : ℝ) + y)⁻¹) := by
  dsimp [gaussTransferTerm]
  have h1 : (((n + 1 : ℕ) : ℝ) + y) ≠ 0 := by positivity
  have h2 : (((n + 2 : ℕ) : ℝ) + y) ≠ 0 := by positivity
  field_simp [h1, h2]
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring

private theorem tendsto_gaussTail_zero (y : ℝ) :
    Tendsto (fun n : ℕ =>
      (Real.log 2)⁻¹ * ((((n + 1 : ℕ) : ℝ) + y)⁻¹))
      atTop (nhds 0) := by
  have htop : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) + y))
      atTop atTop := by
    rw [tendsto_atTop]
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt (b - 1 - y)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at hN ⊢
    nlinarith
  have hinv := tendsto_inv_atTop_zero.comp htop
  convert tendsto_const_nhds.mul hinv using 1
  ring_nf

private theorem hasSum_gaussTransferTerm (y : ℝ) (hy : 0 ≤ y) :
    HasSum (fun n : ℕ => gaussTransferTerm n y) (gaussDensityReal y) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (gaussTransferTerm_nonneg y hy)]
  have htail := tendsto_gaussTail_zero y
  have hlim : Tendsto (fun n : ℕ =>
      (Real.log 2)⁻¹ * ((1 + y)⁻¹) -
        (Real.log 2)⁻¹ * ((((n + 1 : ℕ) : ℝ) + y)⁻¹))
      atTop (nhds ((Real.log 2)⁻¹ * ((1 + y)⁻¹))) := by
    convert tendsto_const_nhds.sub htail using 1
    ring_nf
  rw [show gaussDensityReal y =
    (Real.log 2)⁻¹ * ((1 + y)⁻¹) by
      dsimp [gaussDensityReal]
      have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num only)).ne'
      have hy1 : 1 + y ≠ 0 := by positivity
      field_simp [hlog, hy1]]
  apply hlim.congr'
  filter_upwards [] with n
  calc
    (Real.log 2)⁻¹ * (1 + y)⁻¹ -
          (Real.log 2)⁻¹ * (↑(n + 1) + y)⁻¹ =
        ∑ i ∈ Finset.range n,
          ((Real.log 2)⁻¹ * (↑(i + 1) + y)⁻¹ -
            (Real.log 2)⁻¹ * (↑(i + 2) + y)⁻¹) := by
      rw [Finset.sum_range_sub']
      norm_num only [Nat.cast_add, Nat.cast_one]
    _ = ∑ i ∈ Finset.range n, gaussTransferTerm i y := by
      apply Finset.sum_congr rfl
      intro i hi
      symm
      simpa [add_assoc] using gaussTransferTerm_eq_sub y hy i

private theorem tsum_gaussTransferTerm (y : ℝ) (hy : 0 ≤ y) :
    ∑' n : ℕ, ENNReal.ofReal (gaussTransferTerm n y) =
      ENNReal.ofReal (gaussDensityReal y) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (gaussTransferTerm_nonneg y hy)
    (hasSum_gaussTransferTerm y hy).summable]
  rw [(hasSum_gaussTransferTerm y hy).tsum_eq]

private theorem gaussBranch_hasDerivAt (n : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    HasDerivAt (gaussBranch n)
      (-((((n + 1 : ℕ) : ℝ) + y) ^ 2)⁻¹) y := by
  have hne : (((n + 1 : ℕ) : ℝ) + y) ≠ 0 := by positivity
  have h := ((hasDerivAt_id y).const_add
    (((n + 1 : ℕ) : ℝ))).inv hne
  convert h using 1
  simp [Nat.cast_add, Nat.cast_one, div_eq_mul_inv]

private theorem gaussBranch_density_identity (n : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    ENNReal.ofReal |(-((((n + 1 : ℕ) : ℝ) + y) ^ 2)⁻¹)| *
        ENNReal.ofReal (gaussDensityReal (gaussBranch n y)) =
      ENNReal.ofReal (gaussTransferTerm n y) := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  have hd : 0 < (((n + 1 : ℕ) : ℝ) + y) := by positivity
  have hd1 : 0 < (((n + 2 : ℕ) : ℝ) + y) := by positivity
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num only)).ne'
  rw [abs_neg, abs_of_nonneg (by positivity :
    0 ≤ ((((n + 1 : ℕ) : ℝ) + y) ^ 2)⁻¹)]
  dsimp [gaussDensityReal, gaussBranch, gaussTransferTerm]
  field_simp [hd.ne', hd1.ne', hlog]
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring

private theorem lintegral_gaussBranch_image (n : ℕ) (E : Set ℝ)
    (hE : MeasurableSet E) (hEnn : E ⊆ Set.Ici 0) :
    ∫⁻ x in gaussBranch n '' E, ENNReal.ofReal (gaussDensityReal x) ∂volume =
      ∫⁻ y in E, ENNReal.ofReal (gaussTransferTerm n y) ∂volume := by
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul hE
    (fun y hy => (gaussBranch_hasDerivAt n y (hEnn hy)).hasDerivWithinAt)
    (fun x hx y hy hxy => by
      dsimp [gaussBranch] at hxy
      have hxpos : 0 < (((n + 1 : ℕ) : ℝ) + x) := by
        have hx0 : 0 ≤ x := hEnn hx
        positivity
      have hypos : 0 < (((n + 1 : ℕ) : ℝ) + y) := by
        have hy0 : 0 ≤ y := hEnn hy
        positivity
      apply_fun (fun z : ℝ => z⁻¹) at hxy
      simpa [inv_inv, hxpos.ne', hypos.ne'] using hxy)]
  apply MeasureTheory.lintegral_congr_ae
  filter_upwards [ae_restrict_mem hE] with y hy
  exact gaussBranch_density_identity n y (hEnn hy)

private theorem gaussBranch_injOn (n : ℕ) (E : Set ℝ)
    (hEnn : E ⊆ Set.Ici 0) : Set.InjOn (gaussBranch n) E := by
  intro x hx y hy hxy
  dsimp [gaussBranch] at hxy
  have hxpos : 0 < (((n + 1 : ℕ) : ℝ) + x) := by
    have hx0 : 0 ≤ x := hEnn hx
    positivity
  have hypos : 0 < (((n + 1 : ℕ) : ℝ) + y) := by
    have hy0 : 0 ≤ y := hEnn hy
    positivity
  apply_fun (fun z : ℝ => z⁻¹) at hxy
  simpa [inv_inv, hxpos.ne', hypos.ne'] using hxy

private theorem gaussBranch_image_measurable (n : ℕ) (E : Set ℝ)
    (hE : MeasurableSet E) (hEnn : E ⊆ Set.Ici 0) :
    MeasurableSet (gaussBranch n '' E) := by
  apply hE.image_of_continuousOn_injOn
  · apply ContinuousOn.inv₀
    · fun_prop
    · intro y hy hzero
      have hy0 : 0 ≤ y := hEnn hy
      have : 0 < (((n + 1 : ℕ) : ℝ) + y) := by positivity
      exact this.ne' hzero
  · exact gaussBranch_injOn n E hEnn

private theorem gaussBranch_pairwiseDisjoint (E : Set ℝ)
    (hE : E ⊆ Set.Ico 0 1) :
    Pairwise (Function.onFun Disjoint fun n : ℕ => gaussBranch n '' E) := by
  intro n m hnm
  change Disjoint (gaussBranch n '' E) (gaussBranch m '' E)
  rw [Set.disjoint_left]
  intro x hx hm
  rcases hx with ⟨y, hy, rfl⟩
  rcases hm with ⟨z, hz, heq⟩
  dsimp [gaussBranch] at heq
  have hy0 := (hE hy).1
  have hy1 := (hE hy).2
  have hz0 := (hE hz).1
  have hz1 := (hE hz).2
  have hdy : 0 < (((n + 1 : ℕ) : ℝ) + y) := by positivity
  have hdz : 0 < (((m + 1 : ℕ) : ℝ) + z) := by positivity
  apply_fun (fun w : ℝ => w⁻¹) at heq
  simp only [inv_inv] at heq
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hcast : ((n : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hlt
    norm_num only [Nat.cast_add, Nat.cast_one] at heq
    linarith
  · have hcast : ((m : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hgt
    norm_num only [Nat.cast_add, Nat.cast_one] at heq
    linarith

theorem gaussMapReal_gaussBranch (n : ℕ) (y : ℝ)
    (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    gaussMapReal (gaussBranch n y) = y := by
  have hy0 : 0 ≤ y := hy.1
  have hd : 0 < (((n + 1 : ℕ) : ℝ) + y) := by positivity
  have hfloor : Int.floor y = 0 :=
    Int.floor_eq_on_Ico 0 y (by simpa using hy)
  have hinv : (gaussBranch n y)⁻¹ = (((n + 1 : ℕ) : ℝ) + y) := by
    simp [gaussBranch]
  have hfloor' : Int.floor ((((n + 1 : ℕ) : ℝ) + y)) = (n + 1 : ℕ) := by
    apply (Int.floor_eq_iff).2
    push_cast
    exact ⟨by linarith, by linarith [hy.2]⟩
  rw [gaussMapReal, hinv, hfloor']
  push_cast
  ring

theorem exists_gaussBranch_eq (x : ℝ) (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ n : ℕ, ∃ y : ℝ, y ∈ Set.Ico (0 : ℝ) 1 ∧
      gaussBranch n y = x ∧ gaussMapReal x = y := by
  let a : ℤ := Int.floor x⁻¹
  let y : ℝ := gaussMapReal x
  have hxne : x ≠ 0 := hx.1.ne'
  have hxinvpos : 0 < x⁻¹ := inv_pos.mpr hx.1
  have hxmul : x * x⁻¹ = 1 := mul_inv_cancel₀ hxne
  have hxinv : (1 : ℝ) ≤ x⁻¹ := (one_le_inv₀ hx.1).2 hx.2
  have ha : (1 : ℤ) ≤ a := by
    apply Int.le_floor.mpr
    norm_num only
    exact hxinv
  have ha0 : (0 : ℤ) ≤ a := le_trans (by norm_num only) ha
  have hatNat : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha0
  have hatNatPos : 1 ≤ a.toNat := by
    have h : (1 : ℤ) ≤ (a.toNat : ℤ) := by simpa [hatNat] using ha
    exact_mod_cast h
  have hy : y ∈ Set.Ico (0 : ℝ) 1 := by
    exact ⟨Int.fract_nonneg x⁻¹, Int.fract_lt_one x⁻¹⟩
  refine ⟨a.toNat - 1, y, hy, ?_, rfl⟩
  have hn : a.toNat - 1 + 1 = a.toNat := Nat.sub_add_cancel hatNatPos
  have hcast : (((a.toNat - 1 + 1 : ℕ) : ℝ)) = (a : ℝ) := by
    rw [hn]
    exact_mod_cast hatNat
  dsimp [gaussBranch, y, gaussMapReal]
  rw [hcast]
  have hsum : (a : ℝ) + (x⁻¹ - (a : ℝ)) = x⁻¹ := by ring
  have hfract : Int.fract x⁻¹ = x⁻¹ - (a : ℝ) := by
    rfl
  rw [hfract, hsum, inv_inv]

private theorem gaussPreimage_withoutZero (s : Set GaussSpace) :
    (Subtype.val '' (gaussMap ⁻¹' s)) \ {0} =
      ⋃ n : ℕ, gaussBranch n ''
        (Subtype.val '' s ∩ Set.Ico (0 : ℝ) 1) := by
  ext x
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hz0⟩
    have hzneq : (z : ℝ) ≠ 0 := by simpa using hz0
    have hzpos : 0 < (z : ℝ) := lt_of_le_of_ne z.2.1 hzneq.symm
    obtain ⟨n, y, hy, hbranch, hmap⟩ :=
      exists_gaussBranch_eq (z : ℝ) ⟨hzpos, z.2.2⟩
    refine Set.mem_iUnion.2 ⟨n, y, ?_, hbranch⟩
    refine ⟨?_, hy⟩
    refine ⟨gaussMap z, hz, ?_⟩
    exact hmap
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨n, y, ⟨hyS, hyI⟩, rfl⟩
    rcases hyS with ⟨w, hw, rfl⟩
    have hw0 : 0 ≤ (w : ℝ) := hyI.1
    have hbpos : 0 < gaussBranch n (w : ℝ) := by
      dsimp [gaussBranch]
      positivity
    have hble : gaussBranch n (w : ℝ) ≤ 1 := by
      have hden : 1 ≤ (((n + 1 : ℕ) : ℝ) + (w : ℝ)) := by
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        norm_num only [Nat.cast_add, Nat.cast_one] at ⊢
        linarith
      have hdenpos : 0 < (((n + 1 : ℕ) : ℝ) + (w : ℝ)) := by
        positivity
      change ((((n + 1 : ℕ) : ℝ) + (w : ℝ))⁻¹) ≤ 1
      exact (inv_le_one₀ hdenpos).2 hden
    let z : GaussSpace := ⟨gaussBranch n (w : ℝ), hbpos.le, hble⟩
    have hmapval : (gaussMap z : ℝ) = (w : ℝ) :=
      gaussMapReal_gaussBranch n (w : ℝ) hyI
    have hmap : gaussMap z = w := Subtype.ext hmapval
    refine ⟨⟨z, ?_, rfl⟩, ?_⟩
    · simpa [hmap] using hw
    · simpa [z] using hbpos.ne'

private theorem lintegral_gaussBranch_iUnion (E : Set ℝ)
    (hE : MeasurableSet E) (hEI : E ⊆ Set.Ico (0 : ℝ) 1) :
    ∫⁻ x in ⋃ n : ℕ, gaussBranch n '' E,
        ENNReal.ofReal (gaussDensityReal x) ∂volume =
      ∫⁻ y in E, ENNReal.ofReal (gaussDensityReal y) ∂volume := by
  rw [MeasureTheory.lintegral_iUnion
    (fun n => gaussBranch_image_measurable n E hE
      (fun y hy => (hEI hy).1))
    (gaussBranch_pairwiseDisjoint E hEI)]
  simp_rw [lintegral_gaussBranch_image _ E hE
    (fun y hy => (hEI hy).1)]
  rw [← MeasureTheory.lintegral_tsum]
  · apply MeasureTheory.lintegral_congr_ae
    filter_upwards [ae_restrict_mem hE] with y hy
    exact tsum_gaussTransferTerm y (hEI hy).1
  · intro n
    unfold gaussTransferTerm
    fun_prop

theorem gaussMeasure_preimage {s : Set GaussSpace} (hs : MeasurableSet s) :
    gaussMeasure (gaussMap ⁻¹' s) = gaussMeasure s := by
  have hpre : MeasurableSet (gaussMap ⁻¹' s) := gaussMap_measurable hs
  rw [gaussMeasure_apply hpre, gaussMeasure_apply hs]
  let S : Set ℝ := Subtype.val '' s
  let E : Set ℝ := S ∩ Set.Ico (0 : ℝ) 1
  have hS : MeasurableSet S := by
    exact measurableSet_Icc.subtype_image hs
  have hE : MeasurableSet E := hS.inter measurableSet_Ico
  have hEI : E ⊆ Set.Ico (0 : ℝ) 1 := Set.inter_subset_right
  have hSsub : S ⊆ Set.Icc (0 : ℝ) 1 := by
    rintro x ⟨z, hz, rfl⟩
    exact z.2
  calc
    ∫⁻ x in Subtype.val '' (gaussMap ⁻¹' s),
        ENNReal.ofReal (gaussDensityReal x) ∂volume =
        ∫⁻ x in (Subtype.val '' (gaussMap ⁻¹' s)) \ {0},
          ENNReal.ofReal (gaussDensityReal x) ∂volume := by
      apply MeasureTheory.setLIntegral_congr
      filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
      apply propext
      constructor
      · intro h
        exact ⟨h, by simpa using hx⟩
      · exact fun h => h.1
    _ = ∫⁻ x in ⋃ n : ℕ, gaussBranch n '' E,
          ENNReal.ofReal (gaussDensityReal x) ∂volume := by
      rw [gaussPreimage_withoutZero]
    _ = ∫⁻ y in E, ENNReal.ofReal (gaussDensityReal y) ∂volume :=
      lintegral_gaussBranch_iUnion E hE hEI
    _ = ∫⁻ y in S, ENNReal.ofReal (gaussDensityReal y) ∂volume := by
      apply MeasureTheory.setLIntegral_congr
      filter_upwards [volume.ae_ne (1 : ℝ)] with x hx
      apply propext
      change (x ∈ S ∧ x ∈ Set.Ico (0 : ℝ) 1) ↔ x ∈ S
      constructor
      · exact fun h => h.1
      · intro hxs
        have hxI := hSsub hxs
        exact ⟨hxs, hxI.1, lt_of_le_of_ne hxI.2 hx⟩
    _ = ∫⁻ y in Subtype.val '' s,
          ENNReal.ofReal (gaussDensityReal y) ∂volume := rfl

theorem gaussMap_measurePreserving :
    MeasurePreserving gaussMap gaussMeasure gaussMeasure := by
  refine ⟨gaussMap_measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply_of_aemeasurable gaussMap_measurable.aemeasurable hs]
  exact gaussMeasure_preimage hs

end Chapter03
