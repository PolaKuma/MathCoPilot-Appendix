import Chapter02.Spectral.SpectralMeasure
import Chapter02.Spectral.CircleLaurent
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Analysis.Normed.Operator.Extend

open Classical MeasureTheory Filter Topology
open scoped BigOperators ComplexOrder ENNReal

noncomputable section

namespace Chapter02.CyclicSpectralModel

def characterHom (n : ℤ) : Circle →* ℂ :=
  Circle.coeHom.comp (zpowGroupHom n)

@[simp] theorem characterHom_apply (n : ℤ) (z : Circle) :
    characterHom n z = (z : ℂ) ^ n := rfl

theorem circle_zpow_function_injective :
    Function.Injective (fun m : ℤ => fun z : Circle => z ^ m) := by
  intro m k hmk
  by_contra hne
  have hdne : m - k ≠ 0 := sub_ne_zero.mpr hne
  let p : ℕ := (m - k).natAbs + 1
  have hp : 0 < p := by simp [p]
  letI : NeZero p := ⟨hp.ne'⟩
  obtain ⟨ζ : Circle, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Circle p
  have heval : ζ ^ m = ζ ^ k := congrFun hmk ζ
  have hpow : ζ ^ (m - k) = 1 := by
    rw [zpow_sub, heval]
    simp
  have hdvd : (p : ℤ) ∣ m - k := (hζ.zpow_eq_one_iff_dvd (m - k)).mp hpow
  have hnatdvd : p ∣ (m - k).natAbs := by
    have h := (Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := m - k)).mpr hdvd
    simpa using h
  have hle : p ≤ (m - k).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hdne) hnatdvd
  omega

theorem characterHom_injective : Function.Injective characterHom := by
  intro m n h
  apply circle_zpow_function_injective
  funext z
  apply Subtype.ext
  exact DFunLike.congr_fun h z

def continuousCoeLinear : C(Circle, ℂ) →ₗ[ℂ] (Circle → ℂ) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem character_linearIndependent :
    LinearIndependent ℂ CircleLaurent.character := by
  apply LinearIndependent.of_comp continuousCoeLinear
  simpa [continuousCoeLinear, Function.comp_def, characterHom] using
    (linearIndependent_monoidHom Circle ℂ).comp characterHom characterHom_injective

noncomputable def orbitMap (D : HilbertOperatorData) (hD : IsUnitary D) (x : D.H) :
    CircleLaurent.span →ₗ[ℂ] D.H :=
  (Finsupp.linearCombination ℂ
    (fun j : ℤ => ((SpectralMeasure.unitaryEquiv D hD) ^ j) x)).comp
      character_linearIndependent.repr

theorem repr_character (j : ℤ) :
    character_linearIndependent.repr
        ⟨CircleLaurent.character j, CircleLaurent.character_mem_span j⟩ =
      Finsupp.single j 1 := by
  apply character_linearIndependent.repr_eq
  change (Finsupp.linearCombination ℂ CircleLaurent.character)
      (Finsupp.single j 1) = CircleLaurent.character j
  rw [Finsupp.linearCombination_single]
  simp

@[simp] theorem orbitMap_character (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (j : ℤ) :
    orbitMap D hD x
        ⟨CircleLaurent.character j, CircleLaurent.character_mem_span j⟩ =
      ((SpectralMeasure.unitaryEquiv D hD) ^ j) x := by
  change (Finsupp.linearCombination ℂ
    (fun j : ℤ => ((SpectralMeasure.unitaryEquiv D hD) ^ j) x))
      (character_linearIndependent.repr
        ⟨CircleLaurent.character j, CircleLaurent.character_mem_span j⟩) = _
  rw [repr_character]
  rw [Finsupp.linearCombination_single]
  simp

theorem inner_power_power (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (m n : ℤ) :
    @inner ℂ D.H _ (((SpectralMeasure.unitaryEquiv D hD) ^ m) x)
        (((SpectralMeasure.unitaryEquiv D hD) ^ n) x) =
      SpectralMeasure.vectorCorrelation D hD x (n - m) := by
  simpa [SpectralMeasure.vectorCorrelation, sub_eq_add_neg, add_comm] using
    (SpectralMeasure.inner_negPower_negPower D hD x (-m) (-n))

theorem inner_orbitMap_eq_inner_toLp (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j)
    (q r : C(Circle, ℂ)) (hq : q ∈ CircleLaurent.span)
    (hr : r ∈ CircleLaurent.span) :
    @inner ℂ D.H _ (orbitMap D hD x ⟨q, hq⟩) (orbitMap D hD x ⟨r, hr⟩) =
      @inner ℂ (Lp ℂ 2 μ.μ) _ ((ContinuousMap.toLp 2 μ.μ ℂ) q)
        ((ContinuousMap.toLp 2 μ.μ ℂ) r) := by
  refine Submodule.span_induction
    (p := fun q hq => ∀ r (hr : r ∈ CircleLaurent.span),
      @inner ℂ D.H _ (orbitMap D hD x ⟨q, hq⟩) (orbitMap D hD x ⟨r, hr⟩) =
        @inner ℂ (Lp ℂ 2 μ.μ) _ ((ContinuousMap.toLp 2 μ.μ ℂ) q)
          ((ContinuousMap.toLp 2 μ.μ ℂ) r)) ?_ ?_ ?_ ?_ hq r hr
  · intro q hq
    obtain ⟨m, rfl⟩ := hq
    intro r hr
    refine Submodule.span_induction
      (p := fun r hr =>
        @inner ℂ D.H _
            (orbitMap D hD x ⟨CircleLaurent.character m,
              CircleLaurent.character_mem_span m⟩)
            (orbitMap D hD x ⟨r, hr⟩) =
          @inner ℂ (Lp ℂ 2 μ.μ) _
            ((ContinuousMap.toLp 2 μ.μ ℂ) (CircleLaurent.character m))
            ((ContinuousMap.toLp 2 μ.μ ℂ) r)) ?_ ?_ ?_ ?_ hr
    · intro r hr
      obtain ⟨n, rfl⟩ := hr
      rw [orbitMap_character, orbitMap_character, inner_power_power]
      rw [← hμ (n - m)]
      rw [L2.inner_def, circleFourierCoefficient]
      apply integral_congr_ae
      have hm := ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞))
        (𝕜 := ℂ) μ.μ (CircleLaurent.character m)
      have hn := ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞))
        (𝕜 := ℂ) μ.μ (CircleLaurent.character n)
      filter_upwards [hm, hn] with z hmz hnz
      rw [RCLike.inner_apply, hmz, hnz]
      simp only [CircleLaurent.character_apply]
      rw [map_zpow₀, starRingEnd_apply]
      rw [show star (z : ℂ) = (z : ℂ)⁻¹ by
        apply Complex.ext <;> simp [Complex.inv_def]]
      rw [zpow_sub₀ (Circle.coe_ne_zero z), div_eq_mul_inv, inv_zpow]
    · change @inner ℂ D.H _
          (orbitMap D hD x ⟨CircleLaurent.character m,
            CircleLaurent.character_mem_span m⟩)
          (orbitMap D hD x (0 : CircleLaurent.span)) =
        @inner ℂ (Lp ℂ 2 μ.μ) _
          ((ContinuousMap.toLp 2 μ.μ ℂ) (CircleLaurent.character m))
          ((ContinuousMap.toLp 2 μ.μ ℂ) 0)
      simp
    · intro a b _ _ ha hb
      change @inner ℂ D.H _
          (orbitMap D hD x ⟨CircleLaurent.character m,
            CircleLaurent.character_mem_span m⟩)
          (orbitMap D hD x (⟨a, ‹a ∈ CircleLaurent.span›⟩ +
            ⟨b, ‹b ∈ CircleLaurent.span›⟩)) = _
      rw [map_add, inner_add_right, ha, hb]
      simp only [map_add, inner_add_right]
    · intro c a _ ha
      change @inner ℂ D.H _
          (orbitMap D hD x ⟨CircleLaurent.character m,
            CircleLaurent.character_mem_span m⟩)
          (orbitMap D hD x (c • ⟨a, ‹a ∈ CircleLaurent.span›⟩)) = _
      rw [map_smul, inner_smul_right, ha]
      simp only [map_smul, inner_smul_right]
  · intro r hr
    change @inner ℂ D.H _ (orbitMap D hD x (0 : CircleLaurent.span))
        (orbitMap D hD x ⟨r, hr⟩) =
      @inner ℂ (Lp ℂ 2 μ.μ) _ ((ContinuousMap.toLp 2 μ.μ ℂ) 0)
        ((ContinuousMap.toLp 2 μ.μ ℂ) r)
    simp
  · intro a b _ _ ha hb r hr
    change @inner ℂ D.H _
        (orbitMap D hD x (⟨a, ‹a ∈ CircleLaurent.span›⟩ +
          ⟨b, ‹b ∈ CircleLaurent.span›⟩))
        (orbitMap D hD x ⟨r, hr⟩) = _
    rw [map_add, inner_add_left, ha r hr, hb r hr]
    simp only [map_add, inner_add_left]
  · intro c a _ ha r hr
    change @inner ℂ D.H _
        (orbitMap D hD x (c • ⟨a, ‹a ∈ CircleLaurent.span›⟩))
        (orbitMap D hD x ⟨r, hr⟩) = _
    rw [map_smul, inner_smul_left, ha r hr]
    simp only [map_smul, inner_smul_left]

noncomputable def laurentToLp (μ : CircleMeasureData) :
    CircleLaurent.span →ₗ[ℂ] Lp ℂ 2 μ.μ :=
  (ContinuousMap.toLp 2 μ.μ ℂ).toLinearMap.comp CircleLaurent.span.subtype

@[simp] theorem laurentToLp_apply (μ : CircleMeasureData) (q : CircleLaurent.span) :
    laurentToLp μ q = (ContinuousMap.toLp 2 μ.μ ℂ) q.1 := rfl

theorem denseRange_laurentToLp (μ : CircleMeasureData) :
    DenseRange (laurentToLp μ) := by
  change Dense (Set.range (laurentToLp μ))
  rw [show Set.range (laurentToLp μ) =
      (ContinuousMap.toLp 2 μ.μ ℂ) ''
        (CircleLaurent.algebra : Set C(Circle, ℂ)) by
    ext F
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.1, q.2, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩]
  exact CircleLaurent.dense_toL2 μ

theorem norm_orbitMap_eq_norm_laurentToLp (D : HilbertOperatorData)
    (hD : IsUnitary D) (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j)
    (q : CircleLaurent.span) :
    ‖orbitMap D hD x q‖ = ‖laurentToLp μ q‖ := by
  have hi := inner_orbitMap_eq_inner_toLp D hD x μ hμ q.1 q.1 q.2 q.2
  have hsquare : ‖orbitMap D hD x q‖ ^ 2 = ‖laurentToLp μ q‖ ^ 2 := by
    calc
      ‖orbitMap D hD x q‖ ^ 2 =
          (@inner ℂ D.H _ (orbitMap D hD x q) (orbitMap D hD x q)).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) (orbitMap D hD x q)).symm
      _ = (@inner ℂ (Lp ℂ 2 μ.μ) _ (laurentToLp μ q) (laurentToLp μ q)).re := by
        exact congrArg Complex.re hi
      _ = ‖laurentToLp μ q‖ ^ 2 :=
        inner_self_eq_norm_sq (𝕜 := ℂ) (laurentToLp μ q)
  nlinarith [norm_nonneg (orbitMap D hD x q), norm_nonneg (laurentToLp μ q)]

noncomputable def cyclicCLM (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData) : Lp ℂ 2 μ.μ →L[ℂ] D.H :=
  (orbitMap D hD x).extendOfNorm (laurentToLp μ)

theorem cyclicCLM_laurent (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j)
    (q : CircleLaurent.span) :
    cyclicCLM D hD x μ (laurentToLp μ q) = orbitMap D hD x q := by
  apply LinearMap.extendOfNorm_eq (denseRange_laurentToLp μ)
  refine ⟨1, ?_⟩
  intro r
  rw [norm_orbitMap_eq_norm_laurentToLp D hD x μ hμ r]
  simp

theorem cyclicCLM_norm (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j)
    (F : Lp ℂ 2 μ.μ) :
    ‖cyclicCLM D hD x μ F‖ = ‖F‖ := by
  refine (denseRange_laurentToLp μ).induction ?_ ?_ F
  · intro _ hq
    obtain ⟨q, rfl⟩ := hq
    rw [cyclicCLM_laurent D hD x μ hμ]
    exact norm_orbitMap_eq_norm_laurentToLp D hD x μ hμ q
  · exact isClosed_eq
      ((cyclicCLM D hD x μ).continuous.norm)
      continuous_norm

noncomputable def cyclicIsometry (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j) :
    Lp ℂ 2 μ.μ →ₗᵢ[ℂ] D.H where
  toLinearMap := (cyclicCLM D hD x μ).toLinearMap
  norm_map' := cyclicCLM_norm D hD x μ hμ

def aeZeroSubmodule (μ : CircleMeasureData) :
    Submodule ℂ (Circle → ℂ) where
  carrier := {f | f =ᵐ[μ.μ] 0}
  zero_mem' := by
    change (0 : Circle → ℂ) =ᵐ[μ.μ] 0
    rfl
  add_mem' := by
    intro f g hf hg
    change f + g =ᵐ[μ.μ] 0
    filter_upwards [hf, hg] with z hfz hgz
    simp [hfz, hgz]
  smul_mem' := by
    intro c f hf
    change c • f =ᵐ[μ.μ] 0
    filter_upwards [hf] with z hfz
    simp [hfz]

abbrev RawQuotient (μ : CircleMeasureData) :=
  (Circle → ℂ) ⧸ aeZeroSubmodule μ

noncomputable def lpToRawQuot (μ : CircleMeasureData) :
    Lp ℂ 2 μ.μ →ₗ[ℂ] RawQuotient μ where
  toFun F := Submodule.Quotient.mk (fun z => F z)
  map_add' F G := by
    apply (Submodule.Quotient.eq (aeZeroSubmodule μ)).2
    change (fun z => (F + G) z) - (fun z => F z + G z) =ᵐ[μ.μ] 0
    filter_upwards [Lp.coeFn_add F G] with z hz
    have hz' : (F + G) z = F z + G z := by
      simpa only [Pi.add_apply] using hz
    change (F + G) z - (F z + G z) = 0
    rw [hz']
    simp
  map_smul' c F := by
    apply (Submodule.Quotient.eq (aeZeroSubmodule μ)).2
    change (fun z => (c • F) z) - (fun z => c * F z) =ᵐ[μ.μ] 0
    filter_upwards [Lp.coeFn_smul c F] with z hz
    have hz' : (c • F) z = c * F z := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hz
    change (c • F) z - c * F z = 0
    rw [hz']
    simp

theorem lpToRawQuot_injective (μ : CircleMeasureData) :
    Function.Injective (lpToRawQuot μ) := by
  intro F G hFG
  have hmem := (Submodule.Quotient.eq (aeZeroSubmodule μ)).1 hFG
  change (fun z => F z) - (fun z => G z) =ᵐ[μ.μ] 0 at hmem
  apply Lp.ext
  filter_upwards [hmem] with z hz
  simpa using sub_eq_zero.mp hz

noncomputable def lpRangeEquiv (μ : CircleMeasureData) :
    Lp ℂ 2 μ.μ ≃ₗ[ℂ] (lpToRawQuot μ).range :=
  LinearEquiv.ofInjective (lpToRawQuot μ) (lpToRawQuot_injective μ)

noncomputable def cyclicOnRawRange (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j) :
    (lpToRawQuot μ).range →ₗ[ℂ] D.H :=
  (cyclicIsometry D hD x μ hμ).toLinearMap.comp
    (lpRangeEquiv μ).symm.toLinearMap

noncomputable def rawQuotMap (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j) :
    RawQuotient μ →ₗ[ℂ] D.H :=
  Classical.choose (LinearMap.exists_extend (cyclicOnRawRange D hD x μ hμ))

theorem rawQuotMap_comp_rangeSubtype (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j) :
    (rawQuotMap D hD x μ hμ).comp (lpToRawQuot μ).range.subtype =
      cyclicOnRawRange D hD x μ hμ :=
  Classical.choose_spec (LinearMap.exists_extend (cyclicOnRawRange D hD x μ hμ))

noncomputable def rawW (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j)
    (f : Circle → ℂ) : D.H :=
  rawQuotMap D hD x μ hμ (Submodule.Quotient.mk f)

theorem rawW_toLp (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j)
    (f : Circle → ℂ) (hf : MemLp f 2 μ.μ) :
    rawW D hD x μ hμ f = cyclicIsometry D hD x μ hμ (hf.toLp f) := by
  have hquot : Submodule.Quotient.mk f = lpToRawQuot μ (hf.toLp f) := by
    apply (Submodule.Quotient.eq (aeZeroSubmodule μ)).2
    change f - (fun z => (hf.toLp f) z) =ᵐ[μ.μ] 0
    filter_upwards [hf.coeFn_toLp] with z hz
    simp [hz]
  rw [rawW, hquot]
  let F : (lpToRawQuot μ).range :=
    ⟨lpToRawQuot μ (hf.toLp f), ⟨hf.toLp f, rfl⟩⟩
  have hext := LinearMap.congr_fun
    (rawQuotMap_comp_rangeSubtype D hD x μ hμ) F
  change rawQuotMap D hD x μ hμ (lpToRawQuot μ (hf.toLp f)) = _
  rw [show rawQuotMap D hD x μ hμ (lpToRawQuot μ (hf.toLp f)) =
      cyclicOnRawRange D hD x μ hμ F by simpa [F] using hext]
  change cyclicIsometry D hD x μ hμ ((lpRangeEquiv μ).symm F) = _
  rw [show F = lpRangeEquiv μ (hf.toLp f) by rfl]
  rw [LinearEquiv.symm_apply_apply]

theorem coordinate_memLp (μ : CircleMeasureData) (f : Circle → ℂ)
    (hf : MemLp f 2 μ.μ) : MemLp (fun z : Circle => (z : ℂ) * f z) 2 μ.μ := by
  have hzmeas : AEStronglyMeasurable (fun z : Circle => (z : ℂ)) μ.μ :=
    by
      have hcont : Continuous (fun z : Circle => (z : ℂ)) := continuous_subtype_val
      exact hcont.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun z : Circle => (z : ℂ) * f z) μ.μ :=
    hzmeas.mul hf.1
  apply hf.congr_norm hmeas
  filter_upwards [] with z
  rw [norm_mul, Circle.norm_coe, one_mul]

noncomputable def coordinateLp (μ : CircleMeasureData) (F : Lp ℂ 2 μ.μ) :
    Lp ℂ 2 μ.μ :=
  (coordinate_memLp μ (fun z => F z) (Lp.memLp F)).toLp
    (fun z => (z : ℂ) * F z)

theorem coordinateLp_coe (μ : CircleMeasureData) (F : Lp ℂ 2 μ.μ) :
    (fun z => coordinateLp μ F z) =ᵐ[μ.μ] fun z => (z : ℂ) * F z :=
  (coordinate_memLp μ (fun z => F z) (Lp.memLp F)).coeFn_toLp

noncomputable def coordinateLinear (μ : CircleMeasureData) :
    Lp ℂ 2 μ.μ →ₗ[ℂ] Lp ℂ 2 μ.μ where
  toFun := coordinateLp μ
  map_add' F G := by
    apply Lp.ext
    filter_upwards [coordinateLp_coe μ (F + G), coordinateLp_coe μ F,
      coordinateLp_coe μ G, Lp.coeFn_add F G,
      Lp.coeFn_add (coordinateLp μ F) (coordinateLp μ G)] with z hsum hF hG hFG hout
    rw [hsum, hout]
    simp only [Pi.add_apply]
    rw [hF, hG, hFG]
    simp only [Pi.add_apply]
    ring
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [coordinateLp_coe μ (c • F), coordinateLp_coe μ F,
      Lp.coeFn_smul c F, Lp.coeFn_smul c (coordinateLp μ F)] with z hsmul hF hcoe hout
    rw [hsmul]
    simp only [RingHom.id_apply]
    rw [hout]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hF, hcoe]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem coordinateLinear_norm (μ : CircleMeasureData) (F : Lp ℂ 2 μ.μ) :
    ‖coordinateLinear μ F‖ = ‖F‖ := by
  calc
    ‖coordinateLinear μ F‖ =
        (eLpNorm (fun z : Circle => (z : ℂ) * F z) 2 μ.μ).toReal :=
      MeasureTheory.Lp.norm_toLp _
        (coordinate_memLp μ (fun z => F z) (Lp.memLp F))
    _ = (eLpNorm (fun z : Circle => F z) 2 μ.μ).toReal := by
      congr 1
      apply eLpNorm_congr_norm_ae
      filter_upwards [] with z
      rw [norm_mul, Circle.norm_coe, one_mul]
    _ = ‖(Lp.memLp F).toLp (fun z : Circle => F z)‖ :=
      (MeasureTheory.Lp.norm_toLp _ (Lp.memLp F)).symm
    _ = ‖F‖ := by rw [Lp.toLp_coeFn]

noncomputable def coordinateIsometry (μ : CircleMeasureData) :
    Lp ℂ 2 μ.μ →ₗᵢ[ℂ] Lp ℂ 2 μ.μ where
  toLinearMap := coordinateLinear μ
  norm_map' := coordinateLinear_norm μ

theorem coordinateLinear_laurent (μ : CircleMeasureData) (q : CircleLaurent.span) :
    coordinateLinear μ (laurentToLp μ q) =
      laurentToLp μ
        ⟨CircleLaurent.character 1 * q.1,
          CircleLaurent.character_mul_mem_span 1 q.2⟩ := by
  change coordinateLp μ (laurentToLp μ q) =
    laurentToLp μ
      ⟨CircleLaurent.character 1 * q.1,
        CircleLaurent.character_mul_mem_span 1 q.2⟩
  apply Lp.ext
  have hq := ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞))
    (𝕜 := ℂ) μ.μ q.1
  have hmul := ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞))
    (𝕜 := ℂ) μ.μ (CircleLaurent.character 1 * q.1)
  filter_upwards [coordinateLp_coe μ (laurentToLp μ q), hq, hmul] with z hcoord hqz hmulz
  rw [hcoord]
  have hqz' : (laurentToLp μ q) z = q.1 z := hqz
  have hmulz' :
      (laurentToLp μ
        ⟨CircleLaurent.character 1 * q.1,
          CircleLaurent.character_mul_mem_span 1 q.2⟩) z =
        (CircleLaurent.character 1 * q.1) z := hmulz
  rw [hqz', hmulz']
  change (z : ℂ) * q.1 z = _
  simp

theorem orbitMap_coordinate (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (q : C(Circle, ℂ)) (hq : q ∈ CircleLaurent.span) :
    orbitMap D hD x
        ⟨CircleLaurent.character 1 * q,
          CircleLaurent.character_mul_mem_span 1 hq⟩ =
      D.U (orbitMap D hD x ⟨q, hq⟩) := by
  refine Submodule.span_induction
    (p := fun q hq =>
      orbitMap D hD x
          ⟨CircleLaurent.character 1 * q,
            CircleLaurent.character_mul_mem_span 1 hq⟩ =
        D.U (orbitMap D hD x ⟨q, hq⟩)) ?_ ?_ ?_ ?_ hq
  · intro q hq
    obtain ⟨j, rfl⟩ := hq
    have hchar :
        (⟨CircleLaurent.character 1 * CircleLaurent.character j,
          CircleLaurent.character_mul_mem_span 1
            (CircleLaurent.character_mem_span j)⟩ : CircleLaurent.span) =
        ⟨CircleLaurent.character (1 + j),
          CircleLaurent.character_mem_span (1 + j)⟩ := by
      apply Subtype.ext
      exact (CircleLaurent.character_add 1 j).symm
    rw [hchar]
    rw [orbitMap_character, orbitMap_character]
    change ((SpectralMeasure.unitaryEquiv D hD) ^ (1 + j)) x =
      (SpectralMeasure.unitaryEquiv D hD)
        (((SpectralMeasure.unitaryEquiv D hD) ^ j) x)
    rw [zpow_add]
    rfl
  · have hzero :
        (⟨CircleLaurent.character 1 * 0,
          CircleLaurent.character_mul_mem_span 1 CircleLaurent.span.zero_mem⟩ :
          CircleLaurent.span) = 0 := by
      apply Subtype.ext
      simp
    dsimp only
    rw [hzero]
    rw [show (⟨(0 : C(Circle, ℂ)), CircleLaurent.span.zero_mem⟩ :
      CircleLaurent.span) = 0 by rfl]
    simp
  · intro a b ha hb hia hib
    have hadd :
        (⟨CircleLaurent.character 1 * (a + b),
          CircleLaurent.character_mul_mem_span 1
            (CircleLaurent.span.add_mem ha hb)⟩ : CircleLaurent.span) =
        ⟨CircleLaurent.character 1 * a,
          CircleLaurent.character_mul_mem_span 1 ha⟩ +
        ⟨CircleLaurent.character 1 * b,
          CircleLaurent.character_mul_mem_span 1 hb⟩ := by
      apply Subtype.ext
      exact mul_add _ _ _
    rw [hadd]
    change orbitMap D hD x
        (⟨CircleLaurent.character 1 * a,
          CircleLaurent.character_mul_mem_span 1 ha⟩ +
         ⟨CircleLaurent.character 1 * b,
          CircleLaurent.character_mul_mem_span 1 hb⟩) =
      D.U (orbitMap D hD x (⟨a, ha⟩ + ⟨b, hb⟩))
    rw [map_add, map_add, map_add, hia, hib]
  · intro c a ha hia
    have hsmul :
        (⟨CircleLaurent.character 1 * (c • a),
          CircleLaurent.character_mul_mem_span 1
            (CircleLaurent.span.smul_mem c ha)⟩ : CircleLaurent.span) =
        c • ⟨CircleLaurent.character 1 * a,
          CircleLaurent.character_mul_mem_span 1 ha⟩ := by
      apply Subtype.ext
      simp
    rw [hsmul]
    change orbitMap D hD x
        (c • ⟨CircleLaurent.character 1 * a,
          CircleLaurent.character_mul_mem_span 1 ha⟩) =
      D.U (orbitMap D hD x (c • ⟨a, ha⟩))
    rw [map_smul, map_smul, map_smul, hia]

theorem cyclicCLM_intertwines (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j)
    (F : Lp ℂ 2 μ.μ) :
    cyclicCLM D hD x μ (coordinateLinear μ F) =
      D.U (cyclicCLM D hD x μ F) := by
  refine (denseRange_laurentToLp μ).induction ?_ ?_ F
  · intro _ hF
    obtain ⟨q, rfl⟩ := hF
    rw [coordinateLinear_laurent]
    rw [cyclicCLM_laurent D hD x μ hμ, cyclicCLM_laurent D hD x μ hμ]
    exact orbitMap_coordinate D hD x q.1 q.2
  · exact isClosed_eq
      ((cyclicCLM D hD x μ).continuous.comp
        (coordinateIsometry μ).continuous)
      (D.U.continuous.comp (cyclicCLM D hD x μ).continuous)

theorem rawW_ae (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j)
    {f g : Circle → ℂ} (hfg : f =ᵐ[μ.μ] g) :
    rawW D hD x μ hμ f = rawW D hD x μ hμ g := by
  unfold rawW
  congr 1
  apply (Submodule.Quotient.eq (aeZeroSubmodule μ)).2
  change f - g =ᵐ[μ.μ] 0
  filter_upwards [hfg] with z hz
  simp [hz]

theorem rawW_add (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j)
    (f g : Circle → ℂ) :
    rawW D hD x μ hμ (fun z => f z + g z) =
      rawW D hD x μ hμ f + rawW D hD x μ hμ g := by
  change rawQuotMap D hD x μ hμ
      (Submodule.Quotient.mk (f + g)) =
    rawQuotMap D hD x μ hμ (Submodule.Quotient.mk f) +
      rawQuotMap D hD x μ hμ (Submodule.Quotient.mk g)
  rw [show Submodule.Quotient.mk (f + g) =
      Submodule.Quotient.mk f + Submodule.Quotient.mk g by rfl]
  exact map_add _ _ _

theorem rawW_smul (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j)
    (c : ℂ) (f : Circle → ℂ) :
    rawW D hD x μ hμ (fun z => c * f z) =
      c • rawW D hD x μ hμ f := by
  change rawQuotMap D hD x μ hμ
      (Submodule.Quotient.mk (c • f)) =
    c • rawQuotMap D hD x μ hμ (Submodule.Quotient.mk f)
  rw [show Submodule.Quotient.mk (c • f) =
      c • Submodule.Quotient.mk f by rfl]
  exact map_smul _ _ _

theorem rawW_norm (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j)
    (f : Circle → ℂ) (hf : MemLp f 2 μ.μ) :
    ‖rawW D hD x μ hμ f‖ = (eLpNorm f 2 μ.μ).toReal := by
  rw [rawW_toLp D hD x μ hμ f hf]
  rw [(cyclicIsometry D hD x μ hμ).norm_map]
  exact MeasureTheory.Lp.norm_toLp f hf

theorem rawW_one (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j) :
    rawW D hD x μ hμ (fun _ => (1 : ℂ)) = x := by
  let hone : MemLp (fun _ : Circle => (1 : ℂ)) 2 μ.μ := memLp_const 1
  rw [rawW_toLp D hD x μ hμ _ hone]
  change cyclicCLM D hD x μ (hone.toLp fun _ => 1) = x
  have hconst : hone.toLp (fun _ => 1) =
      laurentToLp μ
        ⟨CircleLaurent.character 0, CircleLaurent.character_mem_span 0⟩ := by
    apply Lp.ext
    filter_upwards [hone.coeFn_toLp,
      ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) μ.μ
        (CircleLaurent.character 0)] with z honez hcharz
    have hcharz' :
        (laurentToLp μ
          ⟨CircleLaurent.character 0, CircleLaurent.character_mem_span 0⟩) z =
          CircleLaurent.character 0 z := hcharz
    rw [honez, hcharz']
    simp
  rw [hconst, cyclicCLM_laurent D hD x μ hμ, orbitMap_character]
  simp

theorem coordinateLinear_toLp (μ : CircleMeasureData) (f : Circle → ℂ)
    (hf : MemLp f 2 μ.μ) :
    coordinateLinear μ (hf.toLp f) =
      (coordinate_memLp μ f hf).toLp (fun z : Circle => (z : ℂ) * f z) := by
  change coordinateLp μ (hf.toLp f) =
    (coordinate_memLp μ f hf).toLp (fun z : Circle => (z : ℂ) * f z)
  apply Lp.ext
  filter_upwards [coordinateLp_coe μ (hf.toLp f), hf.coeFn_toLp,
    (coordinate_memLp μ f hf).coeFn_toLp] with z hcoord hfz hout
  rw [hcoord, hfz, hout]

theorem rawW_intertwines (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j)
    (f : Circle → ℂ) (hf : MemLp f 2 μ.μ) :
    rawW D hD x μ hμ (fun z => (z : ℂ) * f z) =
      D.U (rawW D hD x μ hμ f) := by
  let hcoord := coordinate_memLp μ f hf
  rw [rawW_toLp D hD x μ hμ _ hcoord,
    rawW_toLp D hD x μ hμ f hf]
  change cyclicCLM D hD x μ (hcoord.toLp fun z => (z : ℂ) * f z) =
    D.U (cyclicCLM D hD x μ (hf.toLp f))
  rw [← coordinateLinear_toLp μ f hf]
  exact cyclicCLM_intertwines D hD x μ hμ (hf.toLp f)

theorem coordinateInv_memLp (μ : CircleMeasureData) (F : Lp ℂ 2 μ.μ) :
    MemLp (fun z : Circle => (z : ℂ)⁻¹ * F z) 2 μ.μ := by
  have hzmeas : AEStronglyMeasurable (fun z : Circle => (z : ℂ)⁻¹) μ.μ := by
    have hcont : Continuous (fun z : Circle => (z : ℂ)⁻¹) :=
      continuous_subtype_val.inv₀ (fun z => Circle.coe_ne_zero z)
    exact hcont.aestronglyMeasurable
  apply (Lp.memLp F).congr_norm (hzmeas.mul (Lp.memLp F).1)
  filter_upwards [] with z
  change ‖F z‖ = ‖(z : ℂ)⁻¹ * F z‖
  rw [norm_mul, norm_inv, Circle.norm_coe, inv_one, one_mul]

theorem coordinateLinear_surjective (μ : CircleMeasureData) :
    Function.Surjective (coordinateLinear μ) := by
  intro F
  let hG := coordinateInv_memLp μ F
  let G : Lp ℂ 2 μ.μ := hG.toLp (fun z : Circle => (z : ℂ)⁻¹ * F z)
  refine ⟨G, ?_⟩
  change coordinateLp μ G = F
  apply Lp.ext
  filter_upwards [coordinateLp_coe μ G, hG.coeFn_toLp] with z hcoord hGz
  rw [hcoord, hGz]
  field_simp

def cyclicRange (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData) : Set D.H :=
  Set.range (cyclicCLM D hD x μ)

theorem cyclicRange_isClosed (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j) :
    IsClosed (cyclicRange D hD x μ) := by
  exact (cyclicIsometry D hD x μ hμ).isometry.isClosedEmbedding.isClosed_range

theorem x_mem_cyclicRange (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j) :
    x ∈ cyclicRange D hD x μ := by
  let q : CircleLaurent.span :=
    ⟨CircleLaurent.character 0, CircleLaurent.character_mem_span 0⟩
  refine ⟨laurentToLp μ q, ?_⟩
  rw [cyclicCLM_laurent D hD x μ hμ, orbitMap_character]
  simp

theorem cyclicRange_reducing (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j) :
    IsClosedReducingSubspace D (cyclicRange D hD x μ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨0, map_zero _⟩
  · rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩ a b
    refine ⟨a • F + b • G, ?_⟩
    simp
  · intro yseq hyseq y hy
    exact (cyclicRange_isClosed D hD x μ hμ).isSeqClosed hyseq hy
  · intro y
    constructor
    · rintro ⟨F, rfl⟩
      refine ⟨coordinateLinear μ F, ?_⟩
      exact cyclicCLM_intertwines D hD x μ hμ F
    · rintro ⟨F, hF⟩
      obtain ⟨G, hG⟩ := coordinateLinear_surjective μ F
      refine ⟨G, ?_⟩
      apply (SpectralMeasure.unitaryEquiv D hD).injective
      change D.U (cyclicCLM D hD x μ G) = D.U y
      rw [← cyclicCLM_intertwines D hD x μ hμ G, hG, hF]

theorem zpow_orbit_mem_reducing (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (K : Set D.H) (hK : IsClosedReducingSubspace D K)
    (hx : x ∈ K) (j : ℤ) :
    ((SpectralMeasure.unitaryEquiv D hD) ^ j) x ∈ K := by
  induction j using Int.induction_on with
  | zero => simpa using hx
  | @succ j hj =>
      have hnext := (hK.2.2.2 (((SpectralMeasure.unitaryEquiv D hD) ^ j) x)).mp hj
      change D.U (((SpectralMeasure.unitaryEquiv D hD) ^ j) x) ∈ K at hnext
      convert hnext using 1
      rw [show (j : ℤ) + 1 = 1 + (j : ℤ) by omega, zpow_add]
      rfl
  | @pred j hj =>
      apply (hK.2.2.2
        (((SpectralMeasure.unitaryEquiv D hD) ^ (-((j : ℤ)) - 1)) x)).mpr
      convert hj using 1
      change (SpectralMeasure.unitaryEquiv D hD)
        (((SpectralMeasure.unitaryEquiv D hD) ^ (-((j : ℤ)) - 1)) x) = _
      change (((SpectralMeasure.unitaryEquiv D hD) ^ (1 : ℤ)) *
        ((SpectralMeasure.unitaryEquiv D hD) ^ (-((j : ℤ)) - 1))) x = _
      rw [← zpow_add]
      congr 2
      ring

theorem orbitMap_mem_reducing (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (K : Set D.H) (hK : IsClosedReducingSubspace D K)
    (hx : x ∈ K) (q : C(Circle, ℂ)) (hq : q ∈ CircleLaurent.span) :
    orbitMap D hD x ⟨q, hq⟩ ∈ K := by
  let KS : Submodule ℂ D.H :=
    { carrier := K
      zero_mem' := hK.1
      add_mem' := by
        intro a b ha hb
        simpa using hK.2.1 a ha b hb 1 1
      smul_mem' := by
        intro c a ha
        simpa using hK.2.1 a ha 0 hK.1 c 0 }
  let c := character_linearIndependent.repr ⟨q, hq⟩
  change (Finsupp.linearCombination ℂ
    (fun j : ℤ => ((SpectralMeasure.unitaryEquiv D hD) ^ j) x)) c ∈ KS
  rw [Finsupp.linearCombination_apply]
  change (∑ j ∈ c.support,
    c j • ((SpectralMeasure.unitaryEquiv D hD) ^ j) x) ∈ KS
  apply Submodule.sum_mem
  intro j hj
  exact KS.smul_mem (c j) (zpow_orbit_mem_reducing D hD x K hK hx j)

theorem cyclicCLM_mem_reducing (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j)
    (K : Set D.H) (hK : IsClosedReducingSubspace D K) (hx : x ∈ K)
    (F : Lp ℂ 2 μ.μ) : cyclicCLM D hD x μ F ∈ K := by
  refine (denseRange_laurentToLp μ).induction ?_ ?_ F
  · intro _ hF
    obtain ⟨q, rfl⟩ := hF
    rw [cyclicCLM_laurent D hD x μ hμ]
    exact orbitMap_mem_reducing D hD x K hK hx q.1 q.2
  · have hKclosed : IsClosed K := by
      rw [← isSeqClosed_iff_isClosed]
      intro seq y hseq hy
      exact hK.2.2.1 seq hseq y hy
    exact hKclosed.preimage (cyclicCLM D hD x μ).continuous

theorem inCyclicSubspace_iff_range (D : HilbertOperatorData) (hD : IsUnitary D)
    (x y : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j) :
    InCyclicSubspace D x y ↔ ∃ F : Lp ℂ 2 μ.μ, cyclicCLM D hD x μ F = y := by
  constructor
  · intro hy
    exact hy (cyclicRange D hD x μ) (cyclicRange_reducing D hD x μ hμ)
      (x_mem_cyclicRange D hD x μ hμ)
  · rintro ⟨F, rfl⟩ K hK hx
    exact cyclicCLM_mem_reducing D hD x μ hμ K hK hx F

theorem cyclicModel (D : HilbertOperatorData) :
    CyclicSubspaceMultiplicationModelStatement D := by
  intro hD x hx
  obtain ⟨μ, hμ, _⟩ := Herglotz.herglotz
    (SpectralMeasure.vectorCorrelation D hD x)
    (SpectralMeasure.vectorCorrelation_positiveDefinite D hD x)
  have hspec : HasSpectralMeasure D x μ := by
    intro n
    rw [hμ (n : ℤ)]
    exact congrArg (fun y : D.H => @inner ℂ D.H _ x y)
      (SpectralMeasure.unitaryEquiv_zpow_nat D hD x n)
  refine ⟨μ, hspec, rawW D hD x μ hμ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g hfg
    exact rawW_ae D hD x μ hμ hfg
  · intro f g
    exact rawW_add D hD x μ hμ f g
  · intro c f
    exact rawW_smul D hD x μ hμ c f
  · intro f hf
    exact rawW_norm D hD x μ hμ f hf
  · intro y
    rw [inCyclicSubspace_iff_range D hD x y μ hμ]
    constructor
    · rintro ⟨F, hF⟩
      refine ⟨fun z => F z, Lp.memLp F, ?_⟩
      rw [rawW_toLp D hD x μ hμ _ (Lp.memLp F)]
      change cyclicCLM D hD x μ ((Lp.memLp F).toLp fun z => F z) = y
      rw [Lp.toLp_coeFn]
      exact hF
    · rintro ⟨f, hf, hfy⟩
      refine ⟨hf.toLp f, ?_⟩
      change cyclicCLM D hD x μ (hf.toLp f) = y
      rw [← hfy, rawW_toLp D hD x μ hμ f hf]
      rfl
  · exact rawW_one D hD x μ hμ
  · intro f hf
    exact rawW_intertwines D hD x μ hμ f hf

end Chapter02.CyclicSpectralModel
