import Chapter02.Spectral.SpectralWiener
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

open Classical MeasureTheory Filter Topology
open scoped BigOperators ComplexOrder ENNReal

noncomputable section

namespace Chapter02.SpectralMeasureType

def atomSet (μ : CircleMeasureData) : Set Circle :=
  {z | μ.μ {z} ≠ 0}

lemma atomSet_countable (μ : CircleMeasureData) : (atomSet μ).Countable := by
  have h := Measure.countable_meas_pos_of_disjoint_iUnion
    (μ := μ.μ) (As := fun z : Circle => ({z} : Set Circle))
    (fun z => measurableSet_singleton z)
    (by
      intro z w hzw
      exact Set.disjoint_singleton.2 hzw)
  simpa [atomSet, pos_iff_ne_zero] using h

lemma atomSet_measurable (μ : CircleMeasureData) : MeasurableSet (atomSet μ) :=
  (atomSet_countable μ).measurableSet

noncomputable def continuousPart (μ : CircleMeasureData) : CircleMeasureData where
  μ := μ.μ.restrict (atomSet μ)ᶜ
  isFinite := inferInstance

lemma continuousPart_absolutelyContinuous (μ : CircleMeasureData) :
    (continuousPart μ).μ ≪ μ.μ := Measure.absolutelyContinuous_restrict

lemma continuousPart_isContinuous (μ : CircleMeasureData) :
    IsContinuousCircleMeasure (continuousPart μ) := by
  intro z
  change μ.μ.restrict (atomSet μ)ᶜ {z} = 0
  rw [Measure.restrict_apply (measurableSet_singleton z)]
  by_cases hz : z ∈ atomSet μ
  · have heq : ({z} : Set Circle) ∩ (atomSet μ)ᶜ = ∅ := by
      ext w
      constructor
      · rintro ⟨hwz, hwA⟩
        have hw : w = z := by simpa using hwz
        subst w
        exact (hwA hz).elim
      · intro hw
        exact hw.elim
    rw [heq, measure_empty]
  · apply measure_mono_null Set.inter_subset_left
    simpa [atomSet] using hz

lemma discrete_orthogonal_continuous (D : HilbertOperatorData)
    (x y : D.H) (hx : InDiscreteSpectralSubspace D x)
    (hy : InContinuousSpectralSubspace D y) :
    @inner ℂ D.H _ x y = 0 := by
  by_cases hy0 : y = 0
  · simp [hy0]
  by_contra hxy
  have hxypos : 0 < ‖@inner ℂ D.H _ x y‖ := norm_pos_iff.mpr hxy
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  obtain ⟨s, hs, c, hc⟩ := hx (‖@inner ℂ D.H _ x y‖ / ‖y‖)
    (div_pos hxypos hypos)
  let v : D.H := ∑ z ∈ s, c z • z
  have hvy : @inner ℂ D.H _ v y = 0 := by
    have hsum : ∀ t : Finset D.H,
        (∀ z ∈ t, IsEigenvector D z) →
          @inner ℂ D.H _ (∑ z ∈ t, c z • z) y = 0 := by
      intro t ht
      induction t using Finset.induction_on with
      | empty => simp
      | @insert z t hz ih =>
          rw [Finset.sum_insert hz, inner_add_left, ih (fun w hw => ht w (by simp [hw]))]
          have hzy : @inner ℂ D.H _ z y = 0 := by
            have hyz := hy z (ht z (by simp))
            exact inner_eq_zero_symm.mpr hyz
          simp [hzy]
    exact hsum s hs
  have heq : @inner ℂ D.H _ x y = @inner ℂ D.H _ (x - v) y := by
    rw [inner_sub_left, hvy, sub_zero]
  have hle := norm_inner_le_norm (𝕜 := ℂ) (x - v) y
  rw [← heq] at hle
  have hlt : ‖@inner ℂ D.H _ x y‖ < ‖@inner ℂ D.H _ x y‖ := by
    calc
      ‖@inner ℂ D.H _ x y‖ ≤ ‖x - v‖ * ‖y‖ := hle
      _ < (‖@inner ℂ D.H _ x y‖ / ‖y‖) * ‖y‖ :=
        (mul_lt_mul_of_pos_right (by simpa [v] using hc) hypos)
      _ = ‖@inner ℂ D.H _ x y‖ := div_mul_cancel₀ _ (ne_of_gt hypos)
  exact (lt_irrefl _ hlt)

lemma measure_eq_atomic_tsum (μ : CircleMeasureData)
    (hnull : μ.μ (atomSet μ)ᶜ = 0) (A : Set Circle) :
    μ.μ A = ∑' b : atomSet μ, if (b : Circle) ∈ A then μ.μ {(b : Circle)} else 0 := by
  have hae : ∀ᵐ z ∂μ.μ, z ∈ atomSet μ := by
    exact mem_ae_iff.mpr hnull
  have hinter : μ.μ (atomSet μ ∩ A) = μ.μ A :=
    Measure.measure_inter_eq_of_ae hae
  have hcount : (A ∩ atomSet μ).Countable :=
    (atomSet_countable μ).mono Set.inter_subset_right
  have hsum := tsum_measure_preimage_singleton
    (μ := μ.μ) (f := id) hcount
    (fun z _ => measurableSet_singleton z)
  simp only [Set.preimage_id] at hsum
  rw [← hinter, Set.inter_comm, ← hsum]
  calc
    (∑' b : ↥(A ∩ atomSet μ), μ.μ {(b : Circle)}) =
        ∑' z : Circle, (A ∩ atomSet μ).indicator (fun z => μ.μ {z}) z :=
      tsum_subtype (A ∩ atomSet μ) (fun z => μ.μ {z})
    _ = ∑' z : Circle,
        (atomSet μ).indicator (fun z => if z ∈ A then μ.μ {z} else 0) z := by
      apply tsum_congr
      intro z
      by_cases hzA : z ∈ A <;> by_cases hzatom : z ∈ atomSet μ <;>
        simp [hzA, hzatom]
    _ = ∑' b : atomSet μ, if (b : Circle) ∈ A then μ.μ {(b : Circle)} else 0 :=
      (tsum_subtype (atomSet μ) (fun z => if z ∈ A then μ.μ {z} else 0)).symm

lemma discreteMeasure_of_compl_atomSet_zero (μ : CircleMeasureData)
    (hnull : μ.μ (atomSet μ)ᶜ = 0) : IsDiscreteCircleMeasure μ := by
  letI : Encodable (atomSet μ) := (atomSet_countable μ).toEncodable
  let z : ℕ → Circle := fun n =>
    match Encodable.decode₂ (atomSet μ) n with
    | some b => b
    | none => 1
  let a : ℕ → ENNReal := fun n =>
    match Encodable.decode₂ (atomSet μ) n with
    | some b => μ.μ {(b : Circle)}
    | none => 0
  have hreindex (f : atomSet μ → ENNReal) :
      (∑' n : ℕ, match Encodable.decode₂ (atomSet μ) n with
        | some b => f b
        | none => 0) = ∑' b, f b := by
    rw [← tsum_iSup_decode₂ (fun x : ENNReal => x) rfl f]
    apply tsum_congr
    intro n
    cases hdec : Encodable.decode₂ (atomSet μ) n with
    | none => simp
    | some b => simp
  refine ⟨z, a, ?_, ?_⟩
  · have haeq : (∑' n, a n) = ∑' b : atomSet μ, μ.μ {(b : Circle)} := by
      simpa [a] using hreindex (fun b => μ.μ {(b : Circle)})
    have hmass := measure_eq_atomic_tsum μ hnull Set.univ
    simp only [Set.mem_univ, ↓reduceIte] at hmass
    rw [haeq, ← hmass]
    exact measure_lt_top μ.μ Set.univ
  · intro A _hA
    rw [measure_eq_atomic_tsum μ hnull A]
    rw [← hreindex (fun b => if (b : Circle) ∈ A then μ.μ {(b : Circle)} else 0)]
    apply tsum_congr
    intro n
    cases hdec : Encodable.decode₂ (atomSet μ) n with
    | none => simp [z, a, hdec]
    | some b => simp [z, a, hdec]

lemma compl_atomSet_zero_of_discreteMeasure (μ : CircleMeasureData)
    (hdisc : IsDiscreteCircleMeasure μ) : μ.μ (atomSet μ)ᶜ = 0 := by
  obtain ⟨z, a, ha, hμ⟩ := hdisc
  rw [hμ (atomSet μ)ᶜ (atomSet_measurable μ).compl]
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  by_cases hn : z n ∈ atomSet μ
  · simp [hn]
  · have hsingle := hμ ({z n} : Set Circle) (measurableSet_singleton (z n))
    have hz0 : μ.μ {z n} = 0 := by simpa [atomSet] using hn
    rw [hz0] at hsingle
    have hterm : (if z n ∈ ({z n} : Set Circle) then a n else 0) = 0 :=
      ENNReal.tsum_eq_zero.mp hsingle.symm n
    have han : a n = 0 := by simpa using hterm
    simp [hn, han]

lemma discrete_subspace_implies_compl_atomSet_zero
    (D : HilbertOperatorData) (hD : IsUnitary D) (x : D.H)
    (μ : CircleMeasureData) (hμ : HasSpectralMeasure D x μ)
    (hx : InDiscreteSpectralSubspace D x) : μ.μ (atomSet μ)ᶜ = 0 := by
  obtain ⟨μ₀, hμ₀, _⟩ := Herglotz.herglotz
    (SpectralMeasure.vectorCorrelation D hD x)
    (SpectralMeasure.vectorCorrelation_positiveDefinite D hD x)
  have hμ₀spec : HasSpectralMeasure D x μ₀ := by
    intro n
    rw [hμ₀ (n : ℤ)]
    exact congrArg (fun v : D.H => @inner ℂ D.H _ x v)
      (SpectralMeasure.unitaryEquiv_zpow_nat D hD x n)
  have hμeq : μ₀ = μ := SpectralMeasure.eq_of_nat_moments μ₀ μ
    (fun n => (hμ₀spec n).trans (hμ n).symm)
  subst μ₀
  let C : Set Circle := (atomSet μ)ᶜ
  have hC : MeasurableSet C := (atomSet_measurable μ).compl
  let f : Circle → ℂ := C.indicator (fun _ => 1)
  have hf : MemLp f 2 μ.μ := by
    exact memLp_indicator_const 2 hC 1 (Or.inr (measure_ne_top μ.μ C))
  let F : Lp ℂ 2 μ.μ := hf.toLp f
  let y : D.H := CyclicSpectralModel.cyclicCLM D hD x μ F
  let ν : CircleMeasureData := CyclicMeasureType.vectorDensityMeasure F
  have hνspec : HasSpectralMeasure D y ν := by
    intro n
    exact CyclicMeasureType.vectorDensityMeasure_moment D hD x μ hμ₀ F n
  have hdensity : CyclicMeasureType.spectralDensity F =ᵐ[μ.μ]
      C.indicator (fun _ => (1 : ENNReal)) := by
    filter_upwards [hf.coeFn_toLp] with w hw
    by_cases hwC : w ∈ C <;>
      simp [CyclicMeasureType.spectralDensity, F, f, hw, hwC]
  have hνmeasure : ν.μ = (continuousPart μ).μ := by
    change μ.μ.withDensity (CyclicMeasureType.spectralDensity F) = μ.μ.restrict C
    rw [withDensity_congr_ae hdensity]
    simpa only [Pi.one_apply] using (withDensity_indicator_one (μ := μ.μ) hC)
  have hνcont : IsContinuousCircleMeasure ν := by
    intro z
    rw [hνmeasure]
    exact continuousPart_isContinuous μ z
  have hycont : InContinuousSpectralSubspace D y :=
    SpectralWiener.continuous_measure_implies_continuous_subspace
      D hD y ν hνspec hνcont
  have hxy : @inner ℂ D.H _ x y = 0 :=
    discrete_orthogonal_continuous D x y hx hycont
  let hone : MemLp (fun _ : Circle => (1 : ℂ)) 2 μ.μ := memLp_const 1
  let G : Lp ℂ 2 μ.μ := hone.toLp (fun _ => 1)
  have hxmodel : CyclicSpectralModel.cyclicCLM D hD x μ G = x := by
    change CyclicSpectralModel.cyclicIsometry D hD x μ hμ₀
      (hone.toLp (fun _ => 1)) = x
    rw [← CyclicSpectralModel.rawW_toLp D hD x μ hμ₀ _ hone]
    exact CyclicSpectralModel.rawW_one D hD x μ hμ₀
  have hGF : @inner ℂ (Lp ℂ 2 μ.μ) _ G F = 0 := by
    have himap := (CyclicSpectralModel.cyclicIsometry D hD x μ hμ₀).inner_map_map G F
    change @inner ℂ D.H _
      (CyclicSpectralModel.cyclicCLM D hD x μ G)
      (CyclicSpectralModel.cyclicCLM D hD x μ F) =
        @inner ℂ (Lp ℂ 2 μ.μ) _ G F at himap
    rw [hxmodel] at himap
    exact himap ▸ hxy
  have hGFself : @inner ℂ (Lp ℂ 2 μ.μ) _ G F = @inner ℂ (Lp ℂ 2 μ.μ) _ F F := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hone.coeFn_toLp, hf.coeFn_toLp] with w hwG hwF
    rw [RCLike.inner_apply, RCLike.inner_apply, hwG, hwF]
    by_cases hwC : w ∈ C <;> simp [f, hwC]
  have hF0 : F = 0 := inner_self_eq_zero.mp (hGFself ▸ hGF)
  have hFcoe0 : (fun w => F w) =ᵐ[μ.μ] 0 := by
    rw [hF0]
    exact Lp.coeFn_zero ℂ 2 μ.μ
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hf.coeFn_toLp, hFcoe0] with w hwF hw0
  intro hwC
  have hwCin : w ∈ C := by simpa [C] using hwC
  have hfw0 : f w = 0 := by
    rw [← hwF]
    exact hw0
  rw [show f w = 1 by simp [f, hwCin]] at hfw0
  exact one_ne_zero hfw0

def atomFinsetSet (μ : CircleMeasureData) (t : Finset (atomSet μ)) : Set Circle :=
  Subtype.val '' (t : Set (atomSet μ))

lemma atomFinsetSet_measurable (μ : CircleMeasureData) (t : Finset (atomSet μ)) :
    MeasurableSet (atomFinsetSet μ t) := by
  exact (t.countable_toSet.image Subtype.val).measurableSet

@[simp] lemma atom_mem_atomFinsetSet (μ : CircleMeasureData)
    (t : Finset (atomSet μ)) (b : atomSet μ) :
    (b : Circle) ∈ atomFinsetSet μ t ↔ b ∈ t := by
  constructor
  · rintro ⟨c, hc, hcb⟩
    have : c = b := Subtype.ext hcb
    simpa [this] using hc
  · intro hb
    exact ⟨b, hb, rfl⟩

lemma measure_compl_atomFinsetSet (μ : CircleMeasureData)
    (hnull : μ.μ (atomSet μ)ᶜ = 0) (t : Finset (atomSet μ)) :
    μ.μ (atomFinsetSet μ t)ᶜ =
      ∑' b : {b : atomSet μ // b ∉ t}, μ.μ {((b : atomSet μ) : Circle)} := by
  rw [measure_eq_atomic_tsum μ hnull (atomFinsetSet μ t)ᶜ]
  trans ∑' b : atomSet μ,
    {b : atomSet μ | b ∉ t}.indicator (fun b => μ.μ {(b : Circle)}) b
  · apply tsum_congr
    intro b
    by_cases hb : b ∈ t <;> simp [hb]
  · exact (tsum_subtype {b : atomSet μ | b ∉ t}
      (fun b => μ.μ {(b : Circle)})).symm

noncomputable def atomLp (μ : CircleMeasureData) (b : atomSet μ) : Lp ℂ 2 μ.μ :=
  (memLp_indicator_const (μ := μ.μ) 2 (measurableSet_singleton (b : Circle))
    (1 : ℂ) (Or.inr (measure_ne_top μ.μ {(b : Circle)}))).toLp
      (({(b : Circle)} : Set Circle).indicator fun _ => (1 : ℂ))

lemma atomLp_coe (μ : CircleMeasureData) (b : atomSet μ) :
    (fun z => atomLp μ b z) =ᵐ[μ.μ]
      ({(b : Circle)} : Set Circle).indicator (fun _ => (1 : ℂ)) := by
  exact (memLp_indicator_const (μ := μ.μ) 2 (measurableSet_singleton (b : Circle))
    (1 : ℂ) (Or.inr (measure_ne_top μ.μ {(b : Circle)}))).coeFn_toLp

lemma atomLp_ne_zero (μ : CircleMeasureData) (b : atomSet μ) : atomLp μ b ≠ 0 := by
  intro hzero
  have hcoe0 : (fun z => atomLp μ b z) =ᵐ[μ.μ] 0 := by
    rw [hzero]
    exact Lp.coeFn_zero ℂ 2 μ.μ
  have hae : ∀ᵐ z ∂μ.μ, z ∉ ({(b : Circle)} : Set Circle) := by
    filter_upwards [atomLp_coe μ b, hcoe0] with z hzb hz0
    intro hmem
    rw [hzb, Set.indicator_of_mem hmem] at hz0
    exact one_ne_zero hz0
  exact b.2 (measure_eq_zero_iff_ae_notMem.mpr hae)

lemma coordinate_atomLp (μ : CircleMeasureData) (b : atomSet μ) :
    CyclicSpectralModel.coordinateLinear μ (atomLp μ b) =
      ((b : Circle) : ℂ) • atomLp μ b := by
  apply Lp.ext
  filter_upwards [CyclicSpectralModel.coordinateLp_coe μ (atomLp μ b),
    atomLp_coe μ b, Lp.coeFn_smul ((b : Circle) : ℂ) (atomLp μ b)] with z hzcoord hzF hzsmul
  change CyclicSpectralModel.coordinateLp μ (atomLp μ b) z =
    (((b : Circle) : ℂ) • atomLp μ b) z
  rw [hzcoord, hzsmul, hzF]
  change (z : ℂ) * ({(b : Circle)} : Set Circle).indicator (fun _ => (1 : ℂ)) z =
    ((b : Circle) : ℂ) * atomLp μ b z
  by_cases hzb : z = (b : Circle)
  · subst z
    rw [hzF]
  · rw [hzF]
    simp [hzb]

lemma cyclic_atom_isEigenvector (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j) (b : atomSet μ) :
    IsEigenvector D (CyclicSpectralModel.cyclicCLM D hD x μ (atomLp μ b)) := by
  let v := CyclicSpectralModel.cyclicCLM D hD x μ (atomLp μ b)
  have hv0 : v ≠ 0 := by
    intro hv
    have heq : CyclicSpectralModel.cyclicIsometry D hD x μ hμ (atomLp μ b) =
        CyclicSpectralModel.cyclicIsometry D hD x μ hμ 0 := by
      change CyclicSpectralModel.cyclicCLM D hD x μ (atomLp μ b) =
        CyclicSpectralModel.cyclicCLM D hD x μ 0
      simpa [v] using hv
    exact atomLp_ne_zero μ b
      ((CyclicSpectralModel.cyclicIsometry D hD x μ hμ).injective heq)
  refine ⟨hv0, ((b : Circle) : ℂ), ?_⟩
  change D.U (CyclicSpectralModel.cyclicCLM D hD x μ (atomLp μ b)) =
    ((b : Circle) : ℂ) • CyclicSpectralModel.cyclicCLM D hD x μ (atomLp μ b)
  rw [← CyclicSpectralModel.cyclicCLM_intertwines D hD x μ hμ,
    coordinate_atomLp]
  exact map_smul _ _ _

lemma sum_atomLp_coe (μ : CircleMeasureData) (t : Finset (atomSet μ)) :
    (fun w => (∑ b ∈ t, atomLp μ b) w) =ᵐ[μ.μ]
      fun w => ∑ b ∈ t,
        ({(b : Circle)} : Set Circle).indicator (fun _ => (1 : ℂ)) w := by
  induction t using Finset.induction_on with
  | empty =>
      filter_upwards [Lp.coeFn_zero ℂ 2 μ.μ] with w hw
      exact hw
  | @insert b t hb ih =>
      filter_upwards [Lp.coeFn_add (atomLp μ b) (∑ c ∈ t, atomLp μ c),
        atomLp_coe μ b, ih] with w hadd hbcoe htail
      rw [Finset.sum_insert hb, hadd]
      change atomLp μ b w + (∑ c ∈ t, atomLp μ c) w = _
      rw [hbcoe, htail, Finset.sum_insert hb]

noncomputable def oneLp (μ : CircleMeasureData) : Lp ℂ 2 μ.μ :=
  (memLp_const (μ := μ.μ) (p := (2 : ℝ≥0∞)) (1 : ℂ)).toLp (fun _ => 1)

lemma oneLp_coe (μ : CircleMeasureData) :
    (fun z => oneLp μ z) =ᵐ[μ.μ] fun _ => (1 : ℂ) := by
  exact (memLp_const (μ := μ.μ) (p := (2 : ℝ≥0∞)) (1 : ℂ)).coeFn_toLp

lemma sum_singleton_indicators_at_atom (μ : CircleMeasureData)
    (t : Finset (atomSet μ)) (w : Circle) (hw : w ∈ atomSet μ) :
    (∑ b ∈ t, ({(b : Circle)} : Set Circle).indicator (fun _ => (1 : ℂ)) w) =
      if (⟨w, hw⟩ : atomSet μ) ∈ t then 1 else 0 := by
  let b₀ : atomSet μ := ⟨w, hw⟩
  by_cases hb₀ : b₀ ∈ t
  · rw [if_pos hb₀]
    rw [Finset.sum_eq_single b₀]
    · simp [b₀]
    · intro b hb hne
      have hwb : w ≠ (b : Circle) := by
        intro heq
        apply hne
        exact Subtype.ext heq.symm
      simp [hwb]
    · simp [hb₀]
  · rw [if_neg hb₀]
    apply Finset.sum_eq_zero
    intro b hb
    have hwb : w ≠ (b : Circle) := by
      intro heq
      apply hb₀
      have : b₀ = b := Subtype.ext heq
      simpa [this] using hb
    simp [hwb]

lemma oneLp_sub_sum_atomLp_coe (μ : CircleMeasureData)
    (hnull : μ.μ (atomSet μ)ᶜ = 0) (t : Finset (atomSet μ)) :
    (fun w => (oneLp μ - ∑ b ∈ t, atomLp μ b) w) =ᵐ[μ.μ]
      (atomFinsetSet μ t)ᶜ.indicator (fun _ => (1 : ℂ)) := by
  have hae : ∀ᵐ w ∂μ.μ, w ∈ atomSet μ := mem_ae_iff.mpr hnull
  filter_upwards [hae, Lp.coeFn_sub (oneLp μ) (∑ b ∈ t, atomLp μ b),
    oneLp_coe μ, sum_atomLp_coe μ t] with w hw hsub hone hsum
  rw [hsub]
  change oneLp μ w - (∑ b ∈ t, atomLp μ b) w = _
  rw [hone, hsum, sum_singleton_indicators_at_atom μ t w hw]
  by_cases hwt : (⟨w, hw⟩ : atomSet μ) ∈ t
  · have hwB : w ∈ atomFinsetSet μ t := by
      exact (atom_mem_atomFinsetSet μ t ⟨w, hw⟩).2 hwt
    simp [hwt, hwB]
  · have hwB : w ∉ atomFinsetSet μ t := by
      intro hwB
      exact hwt ((atom_mem_atomFinsetSet μ t ⟨w, hw⟩).1 hwB)
    simp [hwt, hwB]

lemma norm_sq_oneLp_sub_sum_atomLp (μ : CircleMeasureData)
    (hnull : μ.μ (atomSet μ)ᶜ = 0) (t : Finset (atomSet μ)) :
    ‖oneLp μ - ∑ b ∈ t, atomLp μ b‖ ^ 2 = μ.μ.real (atomFinsetSet μ t)ᶜ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rw [L2.inner_def]
  have hint :
    (∫ w, @inner ℂ ℂ _
        ((oneLp μ - ∑ b ∈ t, atomLp μ b) w)
        ((oneLp μ - ∑ b ∈ t, atomLp μ b) w) ∂μ.μ) =
        (μ.μ.real (atomFinsetSet μ t)ᶜ : ℂ) := by
    calc
      (∫ w, @inner ℂ ℂ _
          ((oneLp μ - ∑ b ∈ t, atomLp μ b) w)
          ((oneLp μ - ∑ b ∈ t, atomLp μ b) w) ∂μ.μ) =
          ∫ w, (atomFinsetSet μ t)ᶜ.indicator (fun _ => (1 : ℂ)) w ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards [oneLp_sub_sum_atomLp_coe μ hnull t] with w hw
        rw [hw, RCLike.inner_apply]
        by_cases hwB : w ∈ (atomFinsetSet μ t)ᶜ <;> simp [hwB]
      _ = (μ.μ.real (atomFinsetSet μ t)ᶜ : ℂ) := by
        rw [integral_indicator (atomFinsetSet_measurable μ t).compl]
        simp [measureReal_def]
  simpa using congrArg Complex.re hint

lemma cyclic_atom_injective (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j) :
    Function.Injective
      (fun b : atomSet μ => CyclicSpectralModel.cyclicCLM D hD x μ (atomLp μ b)) := by
  intro b c hbc
  let vb := CyclicSpectralModel.cyclicCLM D hD x μ (atomLp μ b)
  have hvb0 : vb ≠ 0 := (cyclic_atom_isEigenvector D hD x μ hμ b).1
  have hb : D.U vb = ((b : Circle) : ℂ) • vb := by
    change D.U (CyclicSpectralModel.cyclicCLM D hD x μ (atomLp μ b)) = _
    rw [← CyclicSpectralModel.cyclicCLM_intertwines D hD x μ hμ,
      coordinate_atomLp]
    exact map_smul _ _ _
  have hc : D.U vb = ((c : Circle) : ℂ) • vb := by
    have hc' : D.U (CyclicSpectralModel.cyclicCLM D hD x μ (atomLp μ c)) =
        ((c : Circle) : ℂ) • CyclicSpectralModel.cyclicCLM D hD x μ (atomLp μ c) := by
      rw [← CyclicSpectralModel.cyclicCLM_intertwines D hD x μ hμ,
        coordinate_atomLp]
      exact map_smul _ _ _
    have hvc : vb = CyclicSpectralModel.cyclicCLM D hD x μ (atomLp μ c) := hbc
    rw [hvc]
    exact hc'
  have hscalar : ((b : Circle) : ℂ) = ((c : Circle) : ℂ) :=
    smul_left_injective ℂ hvb0 (hb.symm.trans hc)
  apply Subtype.ext
  exact Subtype.ext hscalar

lemma discrete_measure_implies_discrete_subspace
    (D : HilbertOperatorData) (hD : IsUnitary D) (x : D.H)
    (μ : CircleMeasureData) (hμ : HasSpectralMeasure D x μ)
    (hdisc : IsDiscreteCircleMeasure μ) : InDiscreteSpectralSubspace D x := by
  have hnull := compl_atomSet_zero_of_discreteMeasure μ hdisc
  obtain ⟨μ₀, hμ₀, _⟩ := Herglotz.herglotz
    (SpectralMeasure.vectorCorrelation D hD x)
    (SpectralMeasure.vectorCorrelation_positiveDefinite D hD x)
  have hμ₀spec : HasSpectralMeasure D x μ₀ := by
    intro n
    rw [hμ₀ (n : ℤ)]
    exact congrArg (fun v : D.H => @inner ℂ D.H _ x v)
      (SpectralMeasure.unitaryEquiv_zpow_nat D hD x n)
  have hμeq : μ₀ = μ := SpectralMeasure.eq_of_nat_moments μ₀ μ
    (fun n => (hμ₀spec n).trans (hμ n).symm)
  subst μ₀
  intro ε hε
  let weight : atomSet μ → ENNReal := fun b => μ.μ {(b : Circle)}
  have hmass := measure_eq_atomic_tsum μ hnull Set.univ
  simp only [Set.mem_univ, ↓reduceIte] at hmass
  have hweightTop : (∑' b, weight b) ≠ ⊤ := by
    rw [← hmass]
    exact (measure_lt_top μ.μ Set.univ).ne
  have htailTendsto := ENNReal.tendsto_tsum_compl_atTop_zero hweightTop
  have hepssq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hofRealPos : 0 < ENNReal.ofReal (ε ^ 2) := ENNReal.ofReal_pos.mpr hepssq
  have hevent : ∀ᶠ t : Finset (atomSet μ) in atTop,
      (∑' b : {b : atomSet μ // b ∉ t}, weight b) < ENNReal.ofReal (ε ^ 2) :=
    (tendsto_order.1 htailTendsto).2 _ hofRealPos
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 hevent
  have htail := ht₀ t₀ (le_refl t₀)
  let v : atomSet μ → D.H := fun b =>
    CyclicSpectralModel.cyclicCLM D hD x μ (atomLp μ b)
  let s : Finset D.H := t₀.image v
  refine ⟨s, ?_, fun _ => (1 : ℂ), ?_⟩
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact cyclic_atom_isEigenvector D hD x μ hμ₀ b
  · have htailMeasure : μ.μ (atomFinsetSet μ t₀)ᶜ < ENNReal.ofReal (ε ^ 2) := by
      rw [measure_compl_atomFinsetSet μ hnull t₀]
      exact htail
    have htailReal : μ.μ.real (atomFinsetSet μ t₀)ᶜ < ε ^ 2 := by
      rw [measureReal_def]
      have h := (ENNReal.toReal_lt_toReal
        (measure_ne_top μ.μ (atomFinsetSet μ t₀)ᶜ) ENNReal.ofReal_ne_top).mpr htailMeasure
      simpa [ENNReal.toReal_ofReal (le_of_lt hepssq)] using h
    have hLp : ‖oneLp μ - ∑ b ∈ t₀, atomLp μ b‖ < ε := by
      have hsq := norm_sq_oneLp_sub_sum_atomLp μ hnull t₀
      nlinarith [norm_nonneg (oneLp μ - ∑ b ∈ t₀, atomLp μ b)]
    have hxmodel : CyclicSpectralModel.cyclicCLM D hD x μ (oneLp μ) = x := by
      change CyclicSpectralModel.cyclicIsometry D hD x μ hμ₀
        ((memLp_const (μ := μ.μ) (p := (2 : ℝ≥0∞)) (1 : ℂ)).toLp
          (fun _ => 1)) = x
      rw [← CyclicSpectralModel.rawW_toLp D hD x μ hμ₀ _
        (memLp_const (μ := μ.μ) (p := (2 : ℝ≥0∞)) (1 : ℂ))]
      exact CyclicSpectralModel.rawW_one D hD x μ hμ₀
    have hsumImage : (∑ y ∈ s, (1 : ℂ) • y) = ∑ b ∈ t₀, v b := by
      simp only [one_smul]
      exact Finset.sum_image (fun b _ c _ hbc =>
        cyclic_atom_injective D hD x μ hμ₀ hbc)
    rw [hsumImage]
    have hmapSum : (∑ b ∈ t₀, v b) =
        CyclicSpectralModel.cyclicCLM D hD x μ (∑ b ∈ t₀, atomLp μ b) := by
      simp [v, map_sum]
    rw [hmapSum]
    have hdiff : x - CyclicSpectralModel.cyclicCLM D hD x μ
        (∑ b ∈ t₀, atomLp μ b) =
        CyclicSpectralModel.cyclicCLM D hD x μ
          (oneLp μ - ∑ b ∈ t₀, atomLp μ b) := by
      calc
        x - CyclicSpectralModel.cyclicCLM D hD x μ (∑ b ∈ t₀, atomLp μ b) =
            CyclicSpectralModel.cyclicCLM D hD x μ (oneLp μ) -
              CyclicSpectralModel.cyclicCLM D hD x μ (∑ b ∈ t₀, atomLp μ b) :=
          congrArg (fun q => q - CyclicSpectralModel.cyclicCLM D hD x μ
            (∑ b ∈ t₀, atomLp μ b)) hxmodel.symm
        _ = CyclicSpectralModel.cyclicCLM D hD x μ
            (oneLp μ - ∑ b ∈ t₀, atomLp μ b) := (map_sub _ _ _).symm
    rw [hdiff, CyclicSpectralModel.cyclicCLM_norm D hD x μ hμ₀]
    exact hLp

theorem spectralSubspaceMeasureType (D : HilbertOperatorData) :
    SpectralSubspaceMeasureTypeStatement D := by
  intro hD x _hx0 μ hμ
  constructor
  · constructor
    · intro hx
      exact discreteMeasure_of_compl_atomSet_zero μ
        (discrete_subspace_implies_compl_atomSet_zero D hD x μ hμ hx)
    · intro hdisc
      exact discrete_measure_implies_discrete_subspace D hD x μ hμ hdisc
  · exact ⟨SpectralWiener.continuous_subspace_implies_continuous_measure
        D hD x μ hμ,
      SpectralWiener.continuous_measure_implies_continuous_subspace
        D hD x μ hμ⟩

end Chapter02.SpectralMeasureType
