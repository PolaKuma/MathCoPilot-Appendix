import Chapter02.Spectral.MaximalSpectralType

open Classical MeasureTheory Filter Set

noncomputable section

namespace Chapter02.DenseMaximalVectors

def squash (t : ℝ) : ℝ := t / (1 + |t|)

theorem squash_injective : Function.Injective squash := by
  intro a b hab
  have hda : 0 < 1 + |a| := by positivity
  have hdb : 0 < 1 + |b| := by positivity
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := by
      by_contra hb
      have hqa : 0 ≤ squash a := div_nonneg ha hda.le
      have hqb : squash b < 0 := div_neg_of_neg_of_pos (lt_of_not_ge hb) hdb
      rw [hab] at hqa
      exact (not_lt_of_ge hqa) hqb
    simp only [squash, abs_of_nonneg ha, abs_of_nonneg hb] at hab
    rw [div_eq_div_iff (ne_of_gt (by positivity))
      (ne_of_gt (by positivity))] at hab
    nlinarith
  · have ha' : a < 0 := lt_of_not_ge ha
    have hb : b < 0 := by
      by_contra hb
      have hqa : squash a < 0 := div_neg_of_neg_of_pos ha' hda
      have hqb : 0 ≤ squash b := div_nonneg (le_of_not_gt hb) hdb.le
      rw [hab] at hqa
      exact (not_lt_of_ge hqb) hqa
    simp only [squash, abs_of_neg ha', abs_of_neg hb] at hab
    have hda' : 0 < 1 + -a := by linarith
    have hdb' : 0 < 1 + -b := by linarith
    rw [div_eq_div_iff (ne_of_gt hda') (ne_of_gt hdb')] at hab
    nlinarith

theorem abs_squash_lt_one (t : ℝ) : |squash t| < 1 := by
  have hden : 0 < 1 + |t| := by positivity
  rw [squash, abs_div, abs_of_pos hden]
  exact (div_lt_one hden).2 (by linarith [abs_nonneg t])

/-- An `L²` function can be shifted by an arbitrarily small constant so that
the shifted function is nonzero almost everywhere. -/
theorem exists_small_shift_ae_ne_zero (μ : CircleMeasureData)
    (F : Lp ℂ 2 μ.μ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℂ, ‖c‖ < δ ∧ ∀ᵐ z ∂μ.μ, F z + c ≠ 0 := by
  let G : Circle → ℂ := (Lp.memLp F).1.mk F
  have hGstrong : StronglyMeasurable G := (Lp.memLp F).1.stronglyMeasurable_mk
  have hFG : (fun z ↦ F z) =ᵐ[μ.μ] G := (Lp.memLp F).1.ae_eq_mk
  let atoms : Set ℂ := {a | 0 < μ.μ (G ⁻¹' {a})}
  have hatoms : atoms.Countable := by
    apply Measure.countable_meas_pos_of_disjoint_iUnion
    · intro a
      exact hGstrong.measurable (measurableSet_singleton a)
    · intro a b hab
      change Disjoint (G ⁻¹' {a}) (G ⁻¹' {b})
      rw [Set.disjoint_left]
      intro z hza hzb
      change G z = a at hza
      change G z = b at hzb
      exact hab (hza.symm.trans hzb)
  let bad : Set ℂ := (fun c : ℂ ↦ -c) ⁻¹' atoms
  have hbad : bad.Countable :=
    hatoms.preimage (fun _ _ h ↦ neg_injective h)
  let scale : ℝ := δ / 2
  have hscale : scale ≠ 0 := by positivity
  let φ : ℝ → ℂ := fun t ↦ ((scale * squash t : ℝ) : ℂ)
  have hφ : Function.Injective φ := by
    intro t u htu
    change ((scale * squash t : ℝ) : ℂ) =
      ((scale * squash u : ℝ) : ℂ) at htu
    have hreal : scale * squash t = scale * squash u :=
      Complex.ofReal_injective htu
    exact squash_injective (mul_left_cancel₀ hscale hreal)
  have hpre : (φ ⁻¹' bad).Countable := hbad.preimage hφ
  have hex : ∃ t : ℝ, t ∉ φ ⁻¹' bad := by
    by_contra hnone
    push_neg at hnone
    have hall : φ ⁻¹' bad = Set.univ := Set.eq_univ_of_forall hnone
    exact Set.not_countable_univ (hall ▸ hpre)
  obtain ⟨t, ht⟩ := hex
  refine ⟨φ t, ?_, ?_⟩
  · change ‖((scale * squash t : ℝ) : ℂ)‖ < δ
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by dsimp [scale]; positivity)]
    dsimp [scale]
    nlinarith [abs_squash_lt_one t]
  · have hnotAtom : ¬ 0 < μ.μ (G ⁻¹' {-φ t}) := ht
    have hzero : μ.μ (G ⁻¹' {-φ t}) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hnotAtom)
    have haeNot : ∀ᵐ w ∂μ.μ, w ∉ G ⁻¹' {-φ t} :=
      MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hzero
    filter_upwards [hFG, haeNot] with w hwF hwNot
    rw [hwF]
    intro hsum
    apply hwNot
    change G w = -φ t
    exact eq_neg_of_add_eq_zero_left hsum

theorem absolutelyContinuous_vectorDensityMeasure_of_ae_ne_zero
    {μ : CircleMeasureData} (F : Lp ℂ 2 μ.μ)
    (hF : ∀ᵐ z ∂μ.μ, F z ≠ 0) :
    μ.μ ≪ (CyclicMeasureType.vectorDensityMeasure F).μ := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  have hinter : μ.μ ({z | CyclicMeasureType.spectralDensity F z ≠ 0} ∩ s) = 0 :=
    (withDensity_apply_eq_zero'
      (CyclicMeasureType.spectralDensity_aemeasurable F)).mp hzero
  rw [← hinter]
  apply measure_congr
  filter_upwards [hF] with z hz
  apply propext
  constructor
  · intro hzs
    refine ⟨?_, hzs⟩
    unfold CyclicMeasureType.spectralDensity
    exact ENNReal.ofReal_ne_zero_iff.2
      (sq_pos_of_pos (norm_pos_iff.mpr hz))
  · exact fun h ↦ h.2

theorem exists_near_spectralEquivalent_of_dominates
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (S₀ : Submodule ℂ D.H) (v : D.H) (hvS₀ : v ∈ S₀) (hv : v ≠ 0)
    (hdom : ∀ y : D.H, y ∈ S₀ → SpectralMeasureDominatesVector D v y)
    (y : D.H) (hyS₀ : y ∈ S₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : D.H, w ∈ S₀ ∧ ‖y - w‖ < ε ∧
      SpectralMeasureEquivalentVectors D v w := by
  obtain ⟨μv, hμv, _⟩ := SpectralMeasure.spectralMeasure D hD v
  have hfull := SpectralMeasure.full_moment_of_hasSpectralMeasure D hD v μv hμv
  let S := SpectralDecomposition.cyclicSubmodule D v
  let p : D.H := S.starProjection y
  let r : D.H := y - p
  have hpS : p ∈ S := S.starProjection_apply_mem y
  have hrS : r ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal y
  obtain ⟨F, hF⟩ :=
    (CyclicSpectralModel.inCyclicSubspace_iff_range D hD v p μv hfull).mp hpS
  have hδ : 0 < ε / ‖v‖ := div_pos hε (norm_pos_iff.mpr hv)
  obtain ⟨c, hcsmall, hc⟩ := exists_small_shift_ae_ne_zero μv F hδ
  let hone : MemLp (fun _ : Circle => (1 : ℂ)) 2 μv.μ := memLp_const 1
  let One : Lp ℂ 2 μv.μ := hone.toLp (fun _ => 1)
  let Fc : Lp ℂ 2 μv.μ := F + c • One
  have hOne : CyclicSpectralModel.cyclicCLM D hD v μv One = v := by
    have hw := CyclicSpectralModel.rawW_one D hD v μv hfull
    rw [CyclicSpectralModel.rawW_toLp D hD v μv hfull _ hone] at hw
    exact hw
  have hFc : CyclicSpectralModel.cyclicCLM D hD v μv Fc = p + c • v := by
    change CyclicSpectralModel.cyclicCLM D hD v μv (F + c • One) = _
    rw [map_add, map_smul, hF, hOne]
  have hFcNonzero : ∀ᵐ z ∂μv.μ, Fc z ≠ 0 := by
    filter_upwards [hc, Lp.coeFn_add F (c • One), Lp.coeFn_smul c One,
      hone.coeFn_toLp] with z hz hAdd hSmul hOneCoe
    rw [hAdd, Pi.add_apply, hSmul, Pi.smul_apply, hOneCoe]
    simpa only [smul_eq_mul, mul_one] using hz
  let q : D.H := CyclicSpectralModel.cyclicCLM D hD v μv Fc
  let w : D.H := q + r
  have hq : q = p + c • v := hFc
  have hw : w = y + c • v := by
    dsimp [w, r]
    rw [hq]
    abel
  have hwS₀ : w ∈ S₀ := by
    rw [hw]
    exact S₀.add_mem hyS₀ (S₀.smul_mem c hvS₀)
  have hclose : ‖y - w‖ < ε := by
    rw [hw]
    have : y - (y + c • v) = -(c • v) := by abel
    rw [this, norm_neg, norm_smul]
    exact (lt_div_iff₀ (norm_pos_iff.mpr hv)).mp hcsmall
  let μq := CyclicMeasureType.vectorDensityMeasure Fc
  have hμq : HasSpectralMeasure D q μq := by
    intro n
    exact CyclicMeasureType.vectorDensityMeasure_moment D hD v μv hfull Fc n
  obtain ⟨μr, hμr, _⟩ := SpectralMeasure.spectralMeasure D hD r
  obtain ⟨μw, hμw, _⟩ := SpectralMeasure.spectralMeasure D hD w
  have hSred : IsClosedReducingSubspace D (S : Set D.H) :=
    SpectralDecomposition.cyclicSubmodule_reducing D v
  have hSored : IsClosedReducingSubspace D (Sᗮ : Set D.H) :=
    SpectralRelations.orthogonal_reducing D hD S hSred
  have hqS : q ∈ S := by
    exact CyclicSpectralModel.cyclicCLM_mem_reducing D hD v μv hfull
      S hSred (SpectralDecomposition.generator_mem_cyclicSubmodule D v) Fc
  have hqr : OrthogonalCyclicSubspaces D q r :=
    SpectralRelations.cyclic_subspaces_orthogonal_of_mem D S q r
      hSred hSored hqS hrS
  have hμwsum : μw.μ = μq.μ + μr.μ := by
    exact SpectralRelations.orthogonal_sum_spectral_measure D q r μq μr μw
      hqr hμq hμr hμw
  have hacvq : μv.μ ≪ μq.μ :=
    absolutelyContinuous_vectorDensityMeasure_of_ae_ne_zero Fc hFcNonzero
  have hacvw : μv.μ ≪ μw.μ := by
    rw [hμwsum]
    exact hacvq.add_right μr.μ
  refine ⟨w, hwS₀, hclose, hdom w hwS₀, ?_⟩
  intro μw' μv' hμw' hμv'
  have heqw : μw' = μw := SpectralMeasure.eq_of_nat_moments _ _
    (fun n ↦ (hμw' n).trans (hμw n).symm)
  have heqv : μv' = μv := SpectralMeasure.eq_of_nat_moments _ _
    (fun n ↦ (hμv' n).trans (hμv n).symm)
  simpa [heqw, heqv] using hacvw

theorem spectralMeasureDominatesVector_trans
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D) {x y z : D.H}
    (hxy : SpectralMeasureDominatesVector D x y)
    (hyz : SpectralMeasureDominatesVector D y z) :
    SpectralMeasureDominatesVector D x z := by
  intro μx μz hμx hμz
  obtain ⟨μy, hμy, _⟩ := SpectralMeasure.spectralMeasure D hD y
  exact (hyz μy μz hμy hμz).trans (hxy μx μy hμx hμy)

theorem eq_zero_of_zero_dominates
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D) (y : D.H)
    (hdom : SpectralMeasureDominatesVector D 0 y) : y = 0 := by
  obtain ⟨μ0, hμ0, _⟩ := SpectralMeasure.spectralMeasure D hD 0
  obtain ⟨μy, hμy, _⟩ := SpectralMeasure.spectralMeasure D hD y
  have hμ0zero : μ0.μ = 0 := by
    apply Measure.ext
    intro s hs
    exact measure_mono_null (Set.subset_univ s)
      (by
        rw [MaximalSpectralType.spectralMeasure_univ D 0 μ0 hμ0]
        simp)
  have hμyzero : μy.μ = 0 := by
    apply Measure.ext
    intro s hs
    apply hdom μ0 μy hμ0 hμy
    rw [hμ0zero]
    simp
  have hm := hμy 0
  have hm0 : @inner ℂ D.H _ y y = 0 := by
    simpa [circleFourierCoefficient, hμyzero] using hm.symm
  exact inner_self_eq_zero.mp hm0

theorem spectralMeasureDominatesVector_refl
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D) (x : D.H) :
    SpectralMeasureDominatesVector D x x := by
  intro μ ν hμ hν
  have hEq : μ = ν := SpectralMeasure.eq_of_nat_moments μ ν
    (fun n ↦ (hμ n).trans (hν n).symm)
  subst ν
  exact Measure.AbsolutelyContinuous.rfl

/-- Every closed reducing subspace contains maximal-type vectors arbitrarily
close to each of its vectors.  The zero subspace is handled separately. -/
theorem exists_near_maximalVector_on_submodule
    (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (S : Submodule ℂ D.H) (hS : IsClosedReducingSubspace D (S : Set D.H))
    (y : D.H) (hyS : y ∈ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : D.H, w ∈ S ∧ ‖y - w‖ < ε ∧
      ∀ z : D.H, z ∈ S → SpectralMeasureDominatesVector D w z := by
  by_cases hSbot : S = ⊥
  · subst S
    have hy : y = 0 := by simpa using hyS
    subst y
    refine ⟨0, by simp, by simpa using hε, ?_⟩
    intro z hz
    have hz0 : z = 0 := by simpa using hz
    subst z
    exact spectralMeasureDominatesVector_refl D hD 0
  · obtain ⟨x, hxS, horth, hcomplete⟩ :=
      OrthogonalCyclicDecomposition.exists_orthogonalFamily_complete_on_submodule
        D hsep hD S hS
    choose μ hμ hμprob using fun n ↦ SpectralMeasure.spectralMeasure D hD (x n)
    let v : D.H := MaximalSpectralType.maximalTypeVector D x
    have hvS : v ∈ S :=
      MaximalSpectralType.maximalTypeVector_mem_submodule D S hS x hxS
    have hdom : ∀ z : D.H, z ∈ S → SpectralMeasureDominatesVector D v z :=
      MaximalSpectralType.maximalTypeVector_dominates_on_submodule
        D hD S x horth hcomplete μ hμ
    have hex : ∃ z : D.H, z ∈ S ∧ z ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hSbot
      ext z
      constructor
      · intro hz
        have : z = 0 := hn z hz
        simpa [this]
      · intro hz
        have : z = 0 := by simpa using hz
        simpa [this]
    have hv : v ≠ 0 := by
      obtain ⟨z, hzS, hz⟩ := hex
      intro hv0
      have hz0 := eq_zero_of_zero_dominates D hD z (by simpa [hv0] using hdom z hzS)
      exact hz hz0
    obtain ⟨w, hwS, hwy, hequiv⟩ :=
      exists_near_spectralEquivalent_of_dominates
        D hD S v hvS hv hdom y hyS hε
    refine ⟨w, hwS, hwy, ?_⟩
    intro z hzS
    exact spectralMeasureDominatesVector_trans D hD hequiv.2 (hdom z hzS)

end Chapter02.DenseMaximalVectors
