import Chapter02.Spectral.CircleFourierUniqueness
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

open Classical Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace Chapter02.WienerInvariant

/-- The closed subspace in the textbook statement, transferred from raw functions
to the Hilbert space `L²(μ)`. The a.e.-saturation assumption makes membership
independent of the chosen representative. -/
def rawSubmodule (μ : CircleMeasureData) (H : Set (Circle → ℂ))
    (hH : IsClosedCircleL2Subspace μ H) : Submodule ℂ (Lp ℂ 2 μ.μ) where
  carrier := {F | (fun z => F z) ∈ H}
  zero_mem' := by
    apply hH.2.2.2.1 (fun _ => 0) hH.1
    exact (Lp.coeFn_zero ℂ 2 μ.μ).symm
  add_mem' := by
    intro F G hF hG
    apply hH.2.2.2.1 (fun z => 1 * F z + 1 * G z)
    · exact hH.2.2.1 (fun z => F z) hF (fun z => G z) hG 1 1
    · filter_upwards [Lp.coeFn_add F G] with z hz
      simpa using hz.symm
  smul_mem' := by
    intro c F hF
    apply hH.2.2.2.1 (fun z => c * F z + 0 * F z)
    · exact hH.2.2.1 (fun z => F z) hF (fun z => F z) hF c 0
    · filter_upwards [Lp.coeFn_smul c F] with z hz
      simpa [smul_eq_mul] using hz.symm

theorem rawSubmodule_isClosed (μ : CircleMeasureData) (H : Set (Circle → ℂ))
    (hH : IsClosedCircleL2Subspace μ H) :
    IsClosed (rawSubmodule μ H hH : Set (Lp ℂ 2 μ.μ)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro Fseq F hFseq hlim
  apply hH.2.2.2.2 (fun n z => Fseq n z)
  · intro n
    exact hFseq n
  · exact Lp.memLp F
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' Fseq F).mp hlim

/-- A closed textbook subspace has the orthogonal projection needed in Wiener's proof. -/
theorem hasOrthogonalProjection (μ : CircleMeasureData) (H : Set (Circle → ℂ))
    (hH : IsClosedCircleL2Subspace μ H) :
    (rawSubmodule μ H hH).HasOrthogonalProjection := by
  let S := rawSubmodule μ H hH
  letI : IsClosed (S : Set (Lp ℂ 2 μ.μ)) := rawSubmodule_isClosed μ H hH
  letI : CompleteSpace S := IsClosed.completeSpace_coe
  infer_instance

theorem coordinateInv_mul_mem
    (H : Set (Circle → ℂ))
    (hback : ∀ f : Circle → ℂ, (fun z : Circle => (z : ℂ) * f z) ∈ H → f ∈ H)
    {f : Circle → ℂ} (hf : f ∈ H) :
    (fun z : Circle => (z : ℂ)⁻¹ * f z) ∈ H := by
  apply hback
  convert hf using 1
  funext z
  field_simp

/-- Forward and backward invariance under the coordinate multiplier imply
invariance under every integer Laurent character. -/
theorem character_mul_mem
    (H : Set (Circle → ℂ))
    (hforward : ∀ f : Circle → ℂ, f ∈ H →
      (fun z : Circle => (z : ℂ) * f z) ∈ H)
    (hback : ∀ f : Circle → ℂ,
      (fun z : Circle => (z : ℂ) * f z) ∈ H → f ∈ H)
    {f : Circle → ℂ} (hf : f ∈ H) (n : ℤ) :
    (fun z : Circle => (z : ℂ) ^ n * f z) ∈ H := by
  induction n using Int.induction_on with
  | zero => simpa using hf
  | @succ n hn =>
      have h := hforward _ hn
      convert h using 1
      funext z
      rw [zpow_add_one₀ (Circle.coe_ne_zero z)]
      ring
  | @pred n hn =>
      have h := coordinateInv_mul_mem H hback hn
      convert h using 1
      funext z
      rw [zpow_sub_one₀ (Circle.coe_ne_zero z)]
      ring

/-- Consequently the subspace is invariant under every Laurent polynomial. -/
theorem laurent_mul_mem
    (μ : CircleMeasureData) (H : Set (Circle → ℂ))
    (hH : IsClosedCircleL2Subspace μ H)
    (hforward : ∀ f : Circle → ℂ, f ∈ H →
      (fun z : Circle => (z : ℂ) * f z) ∈ H)
    (hback : ∀ f : Circle → ℂ,
      (fun z : Circle => (z : ℂ) * f z) ∈ H → f ∈ H)
    {f : Circle → ℂ} (hf : f ∈ H) {q : C(Circle, ℂ)}
    (hq : q ∈ CircleLaurent.span) :
    (fun z => q z * f z) ∈ H := by
  refine Submodule.span_induction (p := fun q _ => (fun z => q z * f z) ∈ H) ?_ ?_ ?_ ?_ hq
  · intro q hq
    obtain ⟨n, rfl⟩ := hq
    exact character_mul_mem H hforward hback hf n
  · convert hH.1 using 1
    funext z
    simp
  · intro q r _ _ hq hr
    convert hH.2.2.1 (fun z => q z * f z) hq (fun z => r z * f z) hr 1 1 using 1
    funext z
    change (q z + r z) * f z = _
    ring
  · intro c q _ hq
    convert hH.2.2.1 (fun z => q z * f z) hq (fun _ => 0) hH.1 c 0 using 1
    funext z
    change (c * q z) * f z = _
    ring

theorem memLp_star {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {f : α → ℂ} (hf : MemLp f p μ) :
    MemLp (fun x => star (f x)) p μ := by
  apply hf.congr_norm hf.1.star
  filter_upwards [] with x
  exact (norm_star (f x)).symm

/-- The projection of `1` onto a two-sided coordinate-invariant subspace is
pointwise idempotent almost everywhere. This is the core step in Wiener's
classification theorem. -/
theorem exists_projection_indicator_candidate
    (μ : CircleMeasureData) (H : Set (Circle → ℂ))
    (hH : IsClosedCircleL2Subspace μ H)
    (hforward : ∀ f : Circle → ℂ, f ∈ H →
      (fun z : Circle => (z : ℂ) * f z) ∈ H)
    (hback : ∀ f : Circle → ℂ,
      (fun z : Circle => (z : ℂ) * f z) ∈ H → f ∈ H) :
    ∃ h : Circle → ℂ, h ∈ H ∧ MemLp h 2 μ.μ ∧
      (fun z => star ((1 : ℂ) - h z) * h z) =ᵐ[μ.μ] 0 ∧
      ∀ f ∈ H, (fun z => star ((1 : ℂ) - h z) * f z) =ᵐ[μ.μ] 0 := by
  let S := rawSubmodule μ H hH
  letI : IsClosed (S : Set (Lp ℂ 2 μ.μ)) := rawSubmodule_isClosed μ H hH
  letI : CompleteSpace S := IsClosed.completeSpace_coe
  let one : Circle → ℂ := fun _ => 1
  let hone : MemLp one 2 μ.μ := memLp_const 1
  let One : Lp ℂ 2 μ.μ := hone.toLp one
  let hLp : Lp ℂ 2 μ.μ := S.starProjection One
  let kLp : Lp ℂ 2 μ.μ := One - hLp
  have hhS : hLp ∈ S := S.starProjection_apply_mem One
  have hkOrth : kLp ∈ Sᗮ := S.sub_starProjection_mem_orthogonal One
  have horth : ∀ f : Circle → ℂ, f ∈ H →
      (fun z => star (kLp z) * f z) =ᵐ[μ.μ] 0 := by
    intro f hf
    have hfMem : MemLp f 2 μ.μ := hH.2.1 f hf
    have hprodInt : Integrable (fun z => star (kLp z) * f z) μ.μ :=
      (memLp_star (Lp.memLp kLp)).integrable_mul hfMem
    have hmom : ∀ q : C(Circle, ℂ), q ∈ CircleLaurent.span →
        ∫ z, q z * (star (kLp z) * f z) ∂μ.μ = 0 := by
      intro q hq
      have hqRaw : (fun z => q z * f z) ∈ H :=
        laurent_mul_mem μ H hH hforward hback hf hq
      have hqMem : MemLp (fun z => q z * f z) 2 μ.μ := hH.2.1 _ hqRaw
      let Q : Lp ℂ 2 μ.μ := hqMem.toLp (fun z => q z * f z)
      have hQS : Q ∈ S := by
        apply hH.2.2.2.1 (fun z => q z * f z) hqRaw
        exact hqMem.coeFn_toLp.symm
      have hinner : @inner ℂ (Lp ℂ 2 μ.μ) _ kLp Q = 0 :=
        (S.mem_orthogonal' kLp).mp hkOrth Q hQS
      rw [L2.inner_def] at hinner
      calc
        (∫ z, q z * (star (kLp z) * f z) ∂μ.μ) =
            ∫ z, @inner ℂ ℂ _ (kLp z) (Q z) ∂μ.μ := by
          apply integral_congr_ae
          filter_upwards [hqMem.coeFn_toLp] with z hz
          rw [RCLike.inner_apply, hz]
          simp only [Complex.star_def]
          ring
        _ = 0 := hinner
    exact CircleFourierUniqueness.complex_ae_zero_of_laurent_moments
      μ hprodInt hmom
  have hkCoe : (fun z => kLp z) =ᵐ[μ.μ] fun z => 1 - hLp z := by
    filter_upwards [hone.coeFn_toLp, Lp.coeFn_sub One hLp] with z honez hkz
    rw [show kLp z = One z - hLp z by exact hkz, honez]
  refine ⟨fun z => hLp z, hhS, Lp.memLp hLp, ?_, ?_⟩
  · filter_upwards [horth (fun z => hLp z) hhS, hkCoe] with z hz hkz
    simpa [hkz] using hz
  · intro f hf
    filter_upwards [horth f hf, hkCoe] with z hz hkz
    simpa [hkz] using hz

/-- Theorem 2.6.3: every closed two-sided coordinate-invariant subspace of
`L²(μ)` consists exactly of the functions supported on a measurable set. -/
theorem wienerInvariantSubspace : WienerInvariantSubspaceStatement := by
  intro μ H hH hforward hback
  obtain ⟨h, hh, hhLp, hhIdem, horth⟩ :=
    exists_projection_indicator_candidate μ H hH hforward hback
  let hm : Circle → ℂ := hhLp.1.mk h
  have hhm : Measurable hm := hhLp.1.stronglyMeasurable_mk.measurable
  have hheq : h =ᵐ[μ.μ] hm := hhLp.1.ae_eq_mk
  have hhmH : hm ∈ H := hH.2.2.2.1 h hh hm hheq
  have hhmLp : MemLp hm 2 μ.μ := (memLp_congr_ae hheq).mp hhLp
  let B : Set Circle := {z | hm z = 1}
  have hB : MeasurableSet B := measurableSet_eq_fun hhm measurable_const
  have hhmIndicator : hm =ᵐ[μ.μ] fun z => if z ∈ B then 1 else 0 := by
    filter_upwards [hhIdem, hheq] with z hz hhz
    by_cases hzB : z ∈ B
    · change hm z = 1 at hzB
      rw [if_pos]
      · exact hzB
      · change hm z = 1
        exact hzB
    · have hne : (1 : ℂ) - hm z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzB)
      have hsne : star ((1 : ℂ) - hm z) ≠ 0 := star_ne_zero.mpr hne
      have hmz : hm z = 0 := (mul_eq_zero.mp (by simpa [hhz] using hz)).resolve_left hsne
      simp [hzB, hmz]
  refine ⟨B, hB, Set.ext ?_⟩
  intro f
  constructor
  · intro hf
    refine ⟨hH.2.1 f hf, ?_⟩
    have hof := horth f hf
    filter_upwards [hof, hheq] with z hz hhz
    by_cases hzB : z ∈ B
    · simp [hzB]
    · have hne : (1 : ℂ) - hm z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzB)
      have hsne : star ((1 : ℂ) - hm z) ≠ 0 := star_ne_zero.mpr hne
      have hfz : f z = 0 := (mul_eq_zero.mp (by simpa [hhz] using hz)).resolve_left hsne
      simp [hzB, hfz]
  · rintro ⟨hfLp, hfsupp⟩
    let F : Lp ℂ 2 μ.μ := hfLp.toLp f
    have hFclosure : F ∈ closure
        ((ContinuousMap.toLp 2 μ.μ ℂ) '' (CircleLaurent.algebra : Set C(Circle, ℂ))) := by
      have hd := CircleLaurent.dense_toL2 μ
      rw [dense_iff_closure_eq] at hd
      rw [hd]
      trivial
    obtain ⟨Qseq, hQseq, hQlim⟩ := mem_closure_iff_seq_limit.mp hFclosure
    choose q hqAlg hqEq using hQseq
    have hqSpan : ∀ n, q n ∈ CircleLaurent.span := hqAlg
    let fseq : ℕ → Circle → ℂ := fun n z => q n z * hm z
    apply hH.2.2.2.2 fseq
    · intro n
      exact laurent_mul_mem μ H hH hforward hback hhmH (hqSpan n)
    · exact hfLp
    · have hbase : Tendsto (fun n => eLpNorm (fun z => q n z - f z) 2 μ.μ)
          atTop (nhds 0) := by
        have hnorm := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' Qseq F).mp hQlim
        convert hnorm using 1
        funext n
        apply eLpNorm_congr_ae
        rw [← hqEq n]
        have hqcoe := ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞))
          (𝕜 := ℂ) μ.μ (q n)
        filter_upwards [hqcoe, hfLp.coeFn_toLp] with z hqz hfz
        rw [Pi.sub_apply, hqz, hfz]
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (nhds 0)) hbase
      · intro n
        exact bot_le
      · intro n
        apply eLpNorm_mono_ae
        filter_upwards [hhmIndicator, hfsupp] with z hmz hfz
        change ‖q n z * hm z - f z‖ ≤ ‖q n z - f z‖
        by_cases hzB : z ∈ B
        · rw [if_pos hzB] at hmz
          rw [hmz]
          simp
        · rw [if_neg hzB] at hmz hfz
          rw [hmz, hfz]
          simp

end Chapter02.WienerInvariant
