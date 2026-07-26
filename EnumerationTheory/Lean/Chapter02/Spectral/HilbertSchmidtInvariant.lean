import Chapter02.Spectral.SeparatedKernelDensity
import Chapter02.Spectral.CompactKernelConsequences
import Chapter02.Spectral.AlmostPeriodicIsometry
import Chapter02.Ergodic.MeanErgodicL2
import Chapter02.Ergodic.ProductWeakMixing
import Chapter02.Spectral.EigenfunctionLemmas

open Classical Filter Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Chapter02.HilbertSchmidtInvariant

universe u

theorem integral_comp_measurePreserving
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    (T : X → Y) (hT : MeasurePreserving T μ ν)
    (f : Y → ℂ) (hf : AEStronglyMeasurable f ν) :
    ∫ x, f (T x) ∂μ = ∫ y, f y ∂ν := by
  have hmap := integral_map hT.measurable.aemeasurable (by
    rw [hT.map_eq]
    exact hf)
  calc
    ∫ x, f (T x) ∂μ = ∫ y, f y ∂Measure.map T μ := hmap.symm
    _ = ∫ y, f y ∂ν := by rw [hT.map_eq]

lemma memLp_separatedProduct
    (M : System.{u}) (_hM : Chapter01.IsMeasurePreservingSystem M)
    (a b : M.X → ℂ) (ha : M.lpMember 2 a) (hb : M.lpMember 2 b) :
    MemLp (fun p : M.X × M.X => a p.1 * b p.2) 2 (M.μ.prod M.μ) := by
  letI : IsProbabilityMeasure M.μ := _hM.1
  have hmeas :
      AEStronglyMeasurable
        (fun p : M.X × M.X => a p.1 * b p.2) (M.μ.prod M.μ) :=
    (ha.1.comp_fst).mul (hb.1.comp_snd)
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have ha2 : Integrable (fun x => ‖a x‖ ^ (2 : ℕ)) M.μ :=
    (memLp_two_iff_integrable_sq_norm ha.1).1 ha
  have hb2 : Integrable (fun y => ‖b y‖ ^ (2 : ℕ)) M.μ :=
    (memLp_two_iff_integrable_sq_norm hb.1).1 hb
  simpa only [norm_mul, mul_pow] using ha2.mul_prod hb2

lemma inner_separatedProduct_kernel
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ))
    (a b : M.X → ℂ) (ha : M.lpMember 2 a) (hb : M.lpMember 2 b) :
    @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) inferInstance
        ((memLp_separatedProduct M hM a b ha hb).toLp
          (fun p => a p.1 * b p.2))
        (hH.toLp H) =
      @inner ℂ (Lp ℂ 2 M.μ) inferInstance
        (ha.toLp a)
        ((HilbertSchmidtConsequences.kernelAction_memLp_two
          M hM H hH (fun y => star (b y)) hb.star).toLp
            (kernelAction M H (fun y => star (b y)))) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let hab := memLp_separatedProduct M hM a b ha hb
  let hK := HilbertSchmidtConsequences.kernelAction_memLp_two
    M hM H hH (fun y => star (b y)) hb.star
  have hsep :
      Integrable
        (fun p : M.X × M.X =>
          star (a p.1 * b p.2) * H p) (M.μ.prod M.μ) := by
    exact hab.star.integrable_mul hH
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ p,
        @inner ℂ ℂ inferInstance
          ((hab.toLp (fun p => a p.1 * b p.2)) p)
          ((hH.toLp H) p) ∂M.μ.prod M.μ) =
        ∫ p, star (a p.1 * b p.2) * H p ∂M.μ.prod M.μ := by
      apply integral_congr_ae
      filter_upwards [hab.coeFn_toLp, hH.coeFn_toLp] with p hp hHp
      rw [hp, hHp]
      exact RCLike.inner_apply' _ _
    _ = ∫ x, ∫ y,
          star (a x * b y) * H (x, y) ∂M.μ ∂M.μ :=
      integral_prod _ hsep
    _ = ∫ x, star (a x) *
          (∫ y, H (x, y) * star (b y) ∂M.μ) ∂M.μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      change
        (starRingEnd ℂ) (a x * b y) * H (x, y) =
          (starRingEnd ℂ) (a x) *
            (H (x, y) * (starRingEnd ℂ) (b y))
      rw [map_mul]
      ring
    _ = ∫ x,
        @inner ℂ ℂ inferInstance
          ((ha.toLp a) x)
          ((hK.toLp
            (kernelAction M H (fun y => star (b y)))) x) ∂M.μ := by
      apply integral_congr_ae
      filter_upwards [ha.coeFn_toLp, hK.coeFn_toLp] with x hax hKx
      rw [hax, hKx]
      change
        star (a x) *
            (∫ y, H (x, y) * star (b y) ∂M.μ) =
          (∫ y, H (x, y) * star (b y) ∂M.μ) * star (a x)
      ring

lemma finiteSeparatedKernel_inner_eq_sum
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H G : M.X × M.X → ℂ)
    (hH : MemLp H 2 (M.μ.prod M.μ))
    (hG : MemLp G 2 (M.μ.prod M.μ))
    (n : ℕ) (a b : Fin n → M.X → ℂ)
    (ha : ∀ i, M.lpMember 2 (a i)) (hb : ∀ i, M.lpMember 2 (b i))
    (hform : G = fun p => ∑ i, a i p.1 * b i p.2) :
    @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) inferInstance
        (hG.toLp G) (hH.toLp H) =
      ∑ i,
        @inner ℂ (Lp ℂ 2 M.μ) inferInstance
          ((ha i).toLp (a i))
          ((HilbertSchmidtConsequences.kernelAction_memLp_two
            M hM H hH (fun y => star (b i y)) (hb i).star).toLp
              (kernelAction M H (fun y => star (b i y)))) := by
  let q : Fin n → M.X × M.X → ℂ :=
    fun i p => a i p.1 * b i p.2
  let hq (i : Fin n) : MemLp (q i) 2 (M.μ.prod M.μ) :=
    memLp_separatedProduct M hM (a i) (b i) (ha i) (hb i)
  let V : Fin n → Lp ℂ 2 (M.μ.prod M.μ) :=
    fun i => (hq i).toLp (q i)
  have hsumcoe :
      ∀ᵐ p ∂M.μ.prod M.μ,
        ((∑ i, V i : Lp ℂ 2 (M.μ.prod M.μ)) p) =
          ∑ i, q i p := by
    have haux :
        ∀ s : Finset (Fin n),
          ∀ᵐ p ∂M.μ.prod M.μ,
            ((∑ i ∈ s, V i : Lp ℂ 2 (M.μ.prod M.μ)) p) =
              ∑ i ∈ s, q i p := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact Lp.coeFn_zero ℂ 2 (M.μ.prod M.μ)
      | @insert i s his ih =>
          filter_upwards [
            Lp.coeFn_add (V i) (∑ j ∈ s, V j),
            (hq i).coeFn_toLp, ih] with p hadd hi hs
          rw [Finset.sum_insert his, Finset.sum_insert his, hadd]
          simp only [Pi.add_apply]
          rw [hi, hs]
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
      haux Finset.univ
  have htoLp :
      hG.toLp G = ∑ i, V i := by
    apply Lp.ext (μ := M.μ.prod M.μ)
    filter_upwards [hG.coeFn_toLp, hsumcoe] with p hleft hright
    rw [hleft, hright, hform]
  rw [htoLp, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  exact inner_separatedProduct_kernel M hM H hH
    (a i) (b i) (ha i) (hb i)

/-- A nonzero `L²` kernel induces a nonzero integral operator.  The proof
tests against the dense span of finite-rectangle kernels. -/
theorem exists_nonzero_kernelAction
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ))
    (hH0 : ¬ H =ᵐ[M.μ.prod M.μ] 0) :
    ∃ f : M.X → ℂ, ∃ _hf : M.lpMember 2 f,
      ¬ kernelAction M H f =ᵐ[M.μ] 0 := by
  by_contra hex
  push_neg at hex
  let HLp : Lp ℂ 2 (M.μ.prod M.μ) := hH.toLp H
  have hgen :
      ∀ Y ∈ SeparatedKernelDensity.finiteRectangleIndicatorGenerators M hM,
        @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) inferInstance Y HLp = 0 := by
    rintro Y ⟨s, hs, hfin, c, rfl⟩
    let hA := SeparatedKernelDensity.finiteRectangleAlgebra_measureDense M hM
    let G : M.X × M.X → ℂ := s.indicator fun _ => c
    let hG : MemLp G 2 (M.μ.prod M.μ) :=
      memLp_indicator_const 2 (hA.measurable s hs) c (Or.inr hfin)
    obtain ⟨n, a, b, ha, hb, hform⟩ :=
      SeparatedKernelDensity.finiteRectangle_indicator_isFiniteSeparated
        M hM s hs c
    have hinner :=
      finiteSeparatedKernel_inner_eq_sum M hM H G hH hG
        n a b ha hb hform
    have hYG :
        indicatorConstLp 2 (hA.measurable s hs) hfin c = hG.toLp G := by
      rfl
    rw [hYG, hinner]
    apply Finset.sum_eq_zero
    intro i hi
    let hK := HilbertSchmidtConsequences.kernelAction_memLp_two
      M hM H hH (fun y => star (b i y)) (hb i).star
    have hKzero :
        hK.toLp (kernelAction M H (fun y => star (b i y))) = 0 := by
      apply Lp.ext (μ := M.μ)
      exact hK.coeFn_toLp.trans
        (hex (fun y => star (b i y)) (hb i).star) |>.trans
          (Lp.coeFn_zero ℂ 2 M.μ).symm
    rw [hKzero, inner_zero_right]
  have hspan :
      ∀ Y ∈ SeparatedKernelDensity.finiteRectangleIndicatorSpan M hM,
        @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) inferInstance Y HLp = 0 := by
    intro Y hY
    change Y ∈ Submodule.span ℂ
      (SeparatedKernelDensity.finiteRectangleIndicatorGenerators M hM) at hY
    induction hY using Submodule.span_induction with
    | mem Y hY => exact hgen Y hY
    | zero => simp
    | add X Y hX hY ihX ihY =>
        rw [inner_add_left, ihX, ihY, add_zero]
    | smul z Y hY ih =>
        rw [inner_smul_left, ih, mul_zero]
  have hHLp0 : HLp = 0 := by
    by_contra hne
    have hnorm : 0 < ‖HLp‖ := norm_pos_iff.mpr hne
    obtain ⟨Y, hYspan, happrox⟩ :=
      SeparatedKernelDensity.exists_finiteRectangleSpan_approx
        M hM H hH (‖HLp‖ / 2) (by positivity)
    have hYorth := hspan Y hYspan
    have heq :
        @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) inferInstance HLp HLp =
          @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) inferInstance
            (HLp - Y) HLp := by
      rw [inner_sub_left, hYorth, sub_zero]
    have hle :=
      norm_inner_le_norm (𝕜 := ℂ) (HLp - Y) HLp
    rw [← heq] at hle
    have hinnernorm :
        ‖@inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) inferInstance HLp HLp‖ =
          ‖HLp‖ * ‖HLp‖ := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
      ring
    rw [hinnernorm] at hle
    have hlt : ‖HLp‖ * ‖HLp‖ < ‖HLp‖ * ‖HLp‖ := by
      calc
        ‖HLp‖ * ‖HLp‖ ≤ ‖HLp - Y‖ * ‖HLp‖ := hle
        _ < (‖HLp‖ / 2) * ‖HLp‖ :=
          mul_lt_mul_of_pos_right happrox hnorm
        _ < ‖HLp‖ * ‖HLp‖ := by nlinarith
    exact (lt_irrefl _ hlt)
  apply hH0
  have hcoe := hH.coeFn_toLp
  change (fun p => HLp p) =ᵐ[M.μ.prod M.μ] H at hcoe
  rw [hHLp0] at hcoe
  exact hcoe.symm.trans (Lp.coeFn_zero ℂ 2 (M.μ.prod M.μ))

def kernelTranspose (M : System.{u}) (H : M.X × M.X → ℂ)
    (p : M.X × M.X) : ℂ :=
  H (p.2, p.1)

lemma kernelTranspose_memLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ)
    (hH : MemLp H 2 (M.μ.prod M.μ)) :
    MemLp (kernelTranspose M H) 2 (M.μ.prod M.μ) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  simpa only [kernelTranspose, Function.comp_apply] using
    hH.comp_measurePreserving
      (Measure.measurePreserving_swap (μ := M.μ) (ν := M.μ))

lemma kernelTranspose_invariant
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ)
    (hH : H ∘ productTransformation M =ᵐ[M.μ.prod M.μ] H) :
    kernelTranspose M H ∘ productTransformation M =ᵐ[M.μ.prod M.μ]
      kernelTranspose M H := by
  letI : IsProbabilityMeasure M.μ := hM.1
  have hswap :=
    (Measure.measurePreserving_swap
      (μ := M.μ) (ν := M.μ)).quasiMeasurePreserving.ae hH
  simpa only [kernelTranspose, Function.comp_apply, productTransformation,
    Prod.swap_prod_mk] using hswap

lemma columnMean_memLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ)) :
    M.lpMember 2 (fun y => ∫ x, H (x, y) ∂M.μ) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  have htr := kernelTranspose_memLp M hM H hH
  have hone : M.lpMember 2 (fun _ : M.X => (1 : ℂ)) := memLp_const 1
  have hident :
      kernelAction M (kernelTranspose M H) (fun _ => (1 : ℂ)) =
        fun y => ∫ x, H (x, y) ∂M.μ := by
    funext y
    simp [kernelAction, kernelTranspose]
  rw [← hident]
  exact
    HilbertSchmidtConsequences.kernelAction_memLp_two
      M hM (kernelTranspose M H) htr (fun _ => (1 : ℂ)) hone

/-- A product-invariant `L²` kernel intertwines its integral operator with
the forward Koopman isometry.  Surjectivity of the transformation is not
needed: invariance of the measure changes variables in the second
coordinate. -/
theorem kernelAction_koopman_ae
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : IsInvariantL2Kernel M H)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    (fun x => kernelAction M H f (M.T x)) =ᵐ[M.μ]
      kernelAction M H (fun y => f (M.T y)) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  have hslice :
      ∀ᵐ x ∂M.μ, AEStronglyMeasurable (fun y => H (x, y)) M.μ :=
    hH.1.1.prodMk_left
  have hsliceT :
      ∀ᵐ x ∂M.μ, AEStronglyMeasurable (fun y => H (M.T x, y)) M.μ := by
    simpa only using hM.2.quasiMeasurePreserving.ae hslice
  have hinv :
      ∀ᵐ x ∂M.μ, ∀ᵐ y ∂M.μ, H (M.T x, M.T y) = H (x, y) := by
    have h := Measure.ae_ae_of_ae_prod hH.2
    simpa only [Function.comp_apply, productTransformation] using h
  filter_upwards [hsliceT, hinv] with x hxmeas hxeq
  simp only [kernelAction]
  calc
    (∫ y, H (M.T x, y) * f y ∂M.μ) =
        ∫ y, H (M.T x, M.T y) * f (M.T y) ∂M.μ := by
      symm
      exact integral_comp_measurePreserving M.T hM.2
        (fun y => H (M.T x, y) * f y) (hxmeas.mul hf.1)
    _ = ∫ y, H (x, y) * f (M.T y) ∂M.μ := by
      apply integral_congr_ae
      filter_upwards [hxeq] with y hy
      rw [hy]

lemma columnMean_invariant
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : IsInvariantL2Kernel M H) :
    IsInvariantFunction M (fun y => ∫ x, H (x, y) ∂M.μ) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let Htr := kernelTranspose M H
  have hHtr : IsInvariantL2Kernel M Htr :=
    ⟨kernelTranspose_memLp M hM H hH.1,
      kernelTranspose_invariant M hM H hH.2⟩
  have hone : M.lpMember 2 (fun _ : M.X => (1 : ℂ)) := memLp_const 1
  have hcomm :=
    kernelAction_koopman_ae M hM Htr hHtr (fun _ => (1 : ℂ)) hone
  have hident :
      kernelAction M Htr (fun _ => (1 : ℂ)) =
        fun y => ∫ x, H (x, y) ∂M.μ := by
    funext y
    simp [kernelAction, Htr, kernelTranspose]
  rw [hident] at hcomm
  simpa only [Chapter01.koopman] using hcomm

lemma columnMean_ae_constant
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (H : M.X × M.X → ℂ) (hH : IsInvariantL2Kernel M H) :
    ∃ c : ℂ, (fun y => ∫ x, H (x, y) ∂M.μ) =ᵐ[M.μ] fun _ => c := by
  exact
    ((Section01.ergodicityInvariantFunctionCharacterizations M hM).mp hErg)
      _ (columnMean_memLp M hM H hH.1)
      (columnMean_invariant M hM H hH)

lemma rowMean_memLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ)) :
    M.lpMember 2 (fun x => ∫ y, H (x, y) ∂M.μ) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  have hone : M.lpMember 2 (fun _ : M.X => (1 : ℂ)) := memLp_const 1
  have hident :
      kernelAction M H (fun _ => (1 : ℂ)) =
        fun x => ∫ y, H (x, y) ∂M.μ := by
    funext x
    simp [kernelAction]
  rw [← hident]
  exact
    HilbertSchmidtConsequences.kernelAction_memLp_two
      M hM H hH (fun _ => (1 : ℂ)) hone

lemma rowMean_invariant
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : IsInvariantL2Kernel M H) :
    IsInvariantFunction M (fun x => ∫ y, H (x, y) ∂M.μ) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  have hone : M.lpMember 2 (fun _ : M.X => (1 : ℂ)) := memLp_const 1
  have hcomm :=
    kernelAction_koopman_ae M hM H hH (fun _ => (1 : ℂ)) hone
  have hident :
      kernelAction M H (fun _ => (1 : ℂ)) =
        fun x => ∫ y, H (x, y) ∂M.μ := by
    funext x
    simp [kernelAction]
  rw [hident] at hcomm
  simpa only [Chapter01.koopman] using hcomm

lemma rowMean_ae_constant
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (H : M.X × M.X → ℂ) (hH : IsInvariantL2Kernel M H) :
    ∃ c : ℂ, (fun x => ∫ y, H (x, y) ∂M.μ) =ᵐ[M.μ] fun _ => c := by
  exact
    ((Section01.ergodicityInvariantFunctionCharacterizations M hM).mp hErg)
      _ (rowMean_memLp M hM H hH.1)
      (rowMean_invariant M hM H hH)

lemma rowColumnMean_constants_eq
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ))
    (c d : ℂ)
    (hc : (fun x => ∫ y, H (x, y) ∂M.μ) =ᵐ[M.μ] fun _ => c)
    (hd : (fun y => ∫ x, H (x, y) ∂M.μ) =ᵐ[M.μ] fun _ => d) :
    c = d := by
  letI : IsProbabilityMeasure M.μ := hM.1
  have hHint : Integrable H (M.μ.prod M.μ) :=
    hH.integrable (by norm_num)
  calc
    c = ∫ _x : M.X, c ∂M.μ := by simp
    _ = ∫ x, ∫ y, H (x, y) ∂M.μ ∂M.μ :=
      (integral_congr_ae hc).symm
    _ = ∫ p, H p ∂M.μ.prod M.μ := (integral_prod H hHint).symm
    _ = ∫ y, ∫ x, H (x, y) ∂M.μ ∂M.μ :=
      integral_prod_symm H hHint
    _ = ∫ _y : M.X, d ∂M.μ := integral_congr_ae hd
    _ = d := by simp

lemma integral_kernelAction_eq_zero_of_columnMean
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ))
    (f : M.X → ℂ) (hf : M.lpMember 2 f)
    (hcol : (fun y => ∫ x, H (x, y) ∂M.μ) =ᵐ[M.μ] 0) :
    ∫ x, kernelAction M H f x ∂M.μ = 0 := by
  letI : IsProbabilityMeasure M.μ := hM.1
  have hfprod : MemLp (fun p : M.X × M.X => f p.2) 2 (M.μ.prod M.μ) :=
    hf.comp_snd M.μ
  have hprod :
      Integrable (fun p : M.X × M.X => H p * f p.2)
        (M.μ.prod M.μ) :=
    hH.integrable_mul hfprod
  calc
    (∫ x, kernelAction M H f x ∂M.μ) =
        ∫ x, ∫ y, H (x, y) * f y ∂M.μ ∂M.μ := rfl
    _ = ∫ y, ∫ x, H (x, y) * f y ∂M.μ ∂M.μ :=
      integral_integral_swap hprod
    _ = ∫ y, (∫ x, H (x, y) ∂M.μ) * f y ∂M.μ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [← integral_mul_const]
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hcol] with y hy
      rw [hy]
      simp

lemma tensorSquare_memLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    MemLp (TensorSquare M f) 2 (M.μ.prod M.μ) := by
  simpa only [TensorSquare] using
    memLp_separatedProduct M hM f (fun x => star (f x)) hf hf.star

lemma inner_tensorSquare
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f g : M.X → ℂ) (hf : M.lpMember 2 f) (hg : M.lpMember 2 g) :
    @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) inferInstance
        ((tensorSquare_memLp M hM f hf).toLp (TensorSquare M f))
        ((tensorSquare_memLp M hM g hg).toLp (TensorSquare M g)) =
      @inner ℂ (Lp ℂ 2 M.μ) inferInstance (hf.toLp f) (hg.toLp g) *
        star (@inner ℂ (Lp ℂ 2 M.μ) inferInstance
          (hf.toLp f) (hg.toLp g)) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let hfT := tensorSquare_memLp M hM f hf
  let hgT := tensorSquare_memLp M hM g hg
  rw [L2.inner_def]
  calc
    (∫ p,
      @inner ℂ ℂ inferInstance
        ((hfT.toLp (TensorSquare M f)) p)
        ((hgT.toLp (TensorSquare M g)) p) ∂M.μ.prod M.μ) =
        ∫ p, (g p.1 * star (f p.1)) *
          (f p.2 * star (g p.2)) ∂M.μ.prod M.μ := by
      apply integral_congr_ae
      filter_upwards [hfT.coeFn_toLp, hgT.coeFn_toLp] with p hfp hgp
      rw [hfp, hgp, RCLike.inner_apply]
      simp only [TensorSquare, starRingEnd_apply, map_mul, star_star]
      ring
    _ = (∫ x, g x * star (f x) ∂M.μ) *
          ∫ y, f y * star (g y) ∂M.μ :=
      by
        simpa only [mul_assoc] using
          (integral_prod_mul
            (μ := M.μ) (ν := M.μ)
            (fun x => g x * star (f x))
            (fun y => f y * star (g y)))
    _ = @inner ℂ (Lp ℂ 2 M.μ) inferInstance (hf.toLp f) (hg.toLp g) *
        @inner ℂ (Lp ℂ 2 M.μ) inferInstance (hg.toLp g) (hf.toLp f) := by
      congr 1
      · rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
        rw [hfx, hgx, RCLike.inner_apply]
        simp only [starRingEnd_apply]
      · rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
        rw [hfx, hgx, RCLike.inner_apply]
        simp only [starRingEnd_apply]
    _ = _ := by
      congr 1
      have hs :
          star (@inner ℂ (Lp ℂ 2 M.μ) inferInstance
            (hf.toLp f) (hg.toLp g)) =
            @inner ℂ (Lp ℂ 2 M.μ) inferInstance
              (hg.toLp g) (hf.toLp f) :=
        inner_conj_symm (hg.toLp g) (hf.toLp f)
      exact hs.symm

/-- If a nonzero vector in the range of an operator commuting with an
isometry has discrete spectrum, then the operator range itself contains a
nonzero eigenvector. -/
theorem exists_range_eigenvector_of_discrete
    (D : HilbertOperatorData.{u})
    (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (K : D.H →L[ℂ] D.H) (hcomm : ∀ x, D.U (K x) = K (D.U x))
    (f : D.H) (hKf0 : K f ≠ 0)
    (hdisc : InDiscreteSpectralSubspace D (K f)) :
    ∃ z : D.H, ∃ lam : ℂ,
      z ≠ 0 ∧ K z ≠ 0 ∧
      D.U z = lam • z ∧ D.U (K z) = lam • K z := by
  obtain ⟨y, hy, hKfy⟩ :=
    AlmostPeriodicIsometry.exists_eigenvector_inner_ne_zero_of_discrete
      D (K f) hdisc hKf0
  obtain ⟨lam, hlam⟩ := hy.2
  have hlamnorm : ‖lam‖ = 1 := by
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy.1
    have heq : ‖y‖ = ‖lam‖ * ‖y‖ := by
      calc
        ‖y‖ = ‖D.U y‖ := (hU y).symm
        _ = ‖lam • y‖ := by rw [hlam]
        _ = ‖lam‖ * ‖y‖ := norm_smul _ _
    nlinarith
  have hlamstar : lam * star lam = 1 := by
    change lam * (starRingEnd ℂ) lam = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hlamnorm]
    norm_num
  have hstarlam : star lam * lam = 1 := by
    rw [mul_comm, hlamstar]
  let V : D.H →ₗᵢ[ℂ] D.H :=
    { toLinearMap := D.U.toLinearMap
      norm_map' := hU }
  have hUadj_y : D.U.adjoint y = star lam • y := by
    refine ext_inner_left ℂ fun w => ?_
    have hyrepr : y = star lam • D.U y := by
      rw [hlam, smul_smul, hstarlam, one_smul]
    rw [D.U.adjoint_inner_right, inner_smul_right]
    calc
      @inner ℂ D.H inferInstance (D.U w) y =
          @inner ℂ D.H inferInstance (D.U w) (star lam • D.U y) := by
            rw [← hyrepr]
      _ = star lam *
          @inner ℂ D.H inferInstance (D.U w) (D.U y) :=
        inner_smul_right _ _ _
      _ = star lam * @inner ℂ D.H inferInstance w y := by
        congr 1
        exact V.inner_map_map w y
  let z : D.H := K.adjoint y
  have hz0 : z ≠ 0 := by
    intro hz
    apply hKfy
    rw [← K.adjoint_inner_right]
    change @inner ℂ D.H inferInstance f z = 0
    rw [hz, inner_zero_right]
  have hUadj_z : D.U.adjoint z = star lam • z := by
    refine ext_inner_left ℂ fun w => ?_
    change
      @inner ℂ D.H inferInstance w (D.U.adjoint (K.adjoint y)) =
        @inner ℂ D.H inferInstance w (star lam • K.adjoint y)
    calc
      @inner ℂ D.H inferInstance w (D.U.adjoint (K.adjoint y)) =
          @inner ℂ D.H inferInstance (D.U w) (K.adjoint y) :=
        D.U.adjoint_inner_right w (K.adjoint y)
      _ = @inner ℂ D.H inferInstance (K (D.U w)) y :=
        K.adjoint_inner_right (D.U w) y
      _ = @inner ℂ D.H inferInstance (D.U (K w)) y := by rw [hcomm]
      _ = @inner ℂ D.H inferInstance (K w) (D.U.adjoint y) :=
        (D.U.adjoint_inner_right (K w) y).symm
      _ = @inner ℂ D.H inferInstance (K w) (star lam • y) := by
        rw [hUadj_y]
      _ = star lam * @inner ℂ D.H inferInstance (K w) y :=
        inner_smul_right _ _ _
      _ = star lam * @inner ℂ D.H inferInstance w (K.adjoint y) := by
        rw [K.adjoint_inner_right]
      _ = @inner ℂ D.H inferInstance w (star lam • K.adjoint y) :=
        (inner_smul_right _ _ _).symm
  have hUzinner :
      @inner ℂ D.H inferInstance (D.U z) (lam • z) =
        @inner ℂ D.H inferInstance z z := by
    rw [inner_smul_right, ← D.U.adjoint_inner_right, hUadj_z,
      inner_smul_right]
    rw [← mul_assoc, hlamstar, one_mul]
  have hUzeig : D.U z = lam • z := by
    have hsq : ‖D.U z - lam • z‖ ^ 2 = 0 := by
      rw [norm_sub_sq (𝕜 := ℂ), hU, norm_smul, hlamnorm, one_mul,
        hUzinner]
      have hre :
          Complex.re (@inner ℂ D.H inferInstance z z) = ‖z‖ ^ 2 := by
        simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) z)
      change ‖z‖ ^ 2 -
        2 * Complex.re (@inner ℂ D.H inferInstance z z) + ‖z‖ ^ 2 = 0
      rw [hre]
      ring
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
  have hg0 : K z ≠ 0 := by
    intro hg
    have hself :
        @inner ℂ D.H inferInstance z z =
          @inner ℂ D.H inferInstance (K z) y := by
      change
        @inner ℂ D.H inferInstance (K.adjoint y) (K.adjoint y) =
          @inner ℂ D.H inferInstance (K (K.adjoint y)) y
      rw [K.adjoint_inner_right]
    rw [hg, inner_zero_left] at hself
    exact hz0 (inner_self_eq_zero.mp hself)
  refine ⟨z, lam, hz0, hg0, hUzeig, ?_⟩
  rw [hcomm, hUzeig, map_smul]

/-- Operator-level form of `kernelAction_koopman_ae`. -/
theorem kernelOperator_commutes_koopman
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : IsInvariantL2Kernel M H)
    (F : Lp ℂ 2 M.μ) :
    (WeakSpectrum.koopmanData M hM).U
        (HilbertSchmidtConsequences.kernelOperator M hM H hH.1 F) =
      HilbertSchmidtConsequences.kernelOperator M hM H hH.1
        ((WeakSpectrum.koopmanData M hM).U F) := by
  let UF : Lp ℂ 2 M.μ := (WeakSpectrum.koopmanData M hM).U F
  change
    (WeakSpectrum.koopmanData M hM).U
        (HilbertSchmidtConsequences.kernelOperator M hM H hH.1 F) =
      HilbertSchmidtConsequences.kernelOperator M hM H hH.1 UF
  let hKF := HilbertSchmidtConsequences.kernelAction_memLp_two
    M hM H hH.1 F (Lp.memLp F)
  let hKUF := HilbertSchmidtConsequences.kernelAction_memLp_two
    M hM H hH.1 (fun x => UF x) (Lp.memLp UF)
  have hUcoe :
      (fun x => UF x) =ᵐ[M.μ] fun x => F (M.T x) :=
    Lp.coeFn_compMeasurePreserving F hM.2
  have hraw := kernelAction_koopman_ae M hM H hH F (Lp.memLp F)
  have hcongr :
      kernelAction M H
          (fun x => UF x) =
        kernelAction M H (fun x => F (M.T x)) :=
    HilbertSchmidtConsequences.kernelAction_congr_ae M H hUcoe
  have hKFcoeT :
      (fun x => (hKF.toLp (kernelAction M H F)) (M.T x)) =ᵐ[M.μ]
        fun x => kernelAction M H F (M.T x) := by
    simpa only [Function.comp_apply] using
      hM.2.quasiMeasurePreserving.ae_eq_comp hKF.coeFn_toLp
  rw [HilbertSchmidtConsequences.kernelOperator_apply,
    HilbertSchmidtConsequences.kernelOperator_apply]
  apply Lp.ext (μ := M.μ)
  filter_upwards [
    Lp.coeFn_compMeasurePreserving
      (HilbertSchmidtConsequences.kernelLinearMap M hM H hH.1 F) hM.2,
    hKFcoeT, hKUF.coeFn_toLp, hraw] with x hleft hKFcoe hKUFcoe hrawx
  change
    (Lp.compMeasurePreserving M.T hM.2
      (HilbertSchmidtConsequences.kernelLinearMap M hM H hH.1 F)) x =
      (HilbertSchmidtConsequences.kernelLinearMap M hM H hH.1
        ((WeakSpectrum.koopmanData M hM).U F)) x
  rw [hleft]
  change
      (HilbertSchmidtConsequences.kernelLinearMap M hM H hH.1 F)
        (M.T x) =
      (HilbertSchmidtConsequences.kernelLinearMap M hM H hH.1
        UF) x
  change
    (hKF.toLp (kernelAction M H F)) (M.T x) =
      (hKUF.toLp
        (kernelAction M H
          (fun x => UF x))) x
  rw [hKFcoe, hKUFcoe, hcongr, hrawx]

/-- Every vector in the range of an invariant Hilbert--Schmidt kernel has a
totally bounded forward Koopman orbit. -/
theorem kernelOperator_range_almostPeriodic
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : IsInvariantL2Kernel M H)
    (F : Lp ℂ 2 M.μ) :
    IsAlmostPeriodicVector (WeakSpectrum.koopmanData M hM)
      (HilbertSchmidtConsequences.kernelOperator M hM H hH.1 F) := by
  apply HilbertSchmidtConsequences.compact_commutant_range_almostPeriodic
    (WeakSpectrum.koopmanData M hM)
    (fun X => (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map X)
    (HilbertSchmidtConsequences.kernelOperator M hM H hH.1)
    (SeparatedKernelDensity.kernelOperator_hasCompactClosedBallImage
      M hM H hH.1)
    (kernelOperator_commutes_koopman M hM H hH)

/-- The range-spanning part of Theorem 2.5.17 for an arbitrary
measure-preserving endomorphism. -/
theorem kernelRangeSpannedByEigenfunctions
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : IsInvariantL2Kernel M H) :
    KernelRangeSpannedByEigenfunctions M H := by
  intro g hg ε hε
  obtain ⟨f, hf, hgf⟩ := hg
  let F : Lp ℂ 2 M.μ := hf.toLp f
  let K : Lp ℂ 2 M.μ :=
    HilbertSchmidtConsequences.kernelOperator M hM H hH.1 F
  have hKap : IsAlmostPeriodicVector (WeakSpectrum.koopmanData M hM) K :=
    kernelOperator_range_almostPeriodic M hM H hH F
  have hKdisc : InDiscreteSpectralSubspace (WeakSpectrum.koopmanData M hM) K :=
    AlmostPeriodicIsometry.almostPeriodic_implies_discrete
      (WeakSpectrum.koopmanData M hM)
      (fun X => (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map X) K hKap
  obtain ⟨s, hs, c, hKapprox⟩ :=
    CompactDiscrete.discreteVector_to_rawEigenApprox M hM K hKdisc ε hε
  refine ⟨s, hs, c, ?_⟩
  let hKF := HilbertSchmidtConsequences.kernelAction_memLp_two
    M hM H hH.1 F (Lp.memLp F)
  have hFraw : (fun x => F x) =ᵐ[M.μ] f := hf.coeFn_toLp
  have haction :
      kernelAction M H (fun x => F x) = kernelAction M H f :=
    HilbertSchmidtConsequences.kernelAction_congr_ae M H hFraw
  have hKraw : (fun x => K x) =ᵐ[M.μ] kernelAction M H f := by
    change
      (fun x =>
        (HilbertSchmidtConsequences.kernelOperator M hM H hH.1 F) x)
          =ᵐ[M.μ] kernelAction M H f
    rw [HilbertSchmidtConsequences.kernelOperator_apply]
    change
      (fun x => (hKF.toLp (kernelAction M H F)) x)
        =ᵐ[M.μ] kernelAction M H f
    exact hKF.coeFn_toLp.trans (EventuallyEq.of_eq haction)
  have hgK : g =ᵐ[M.μ] fun x => K x := hgf.trans hKraw.symm
  apply lt_of_eq_of_lt _ hKapprox
  apply eLpNorm_congr_ae
  exact hgK.sub EventuallyEq.rfl

/-- The nonconstant-eigenfunction part of Theorem 2.5.17. -/
theorem exists_nonconstant_eigenfunction_in_kernelRange
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (H : M.X × M.X → ℂ) (hH : IsInvariantL2Kernel M H)
    (hHnonconst : ¬ IsAEEqConstantKernel M H) :
    ∃ g : M.X → ℂ, InKernelRange M H g ∧
      ∃ lam : ℂ, Eigenfunction M lam g ∧ ¬ IsAEEqConstant M g := by
  letI : IsProbabilityMeasure M.μ := hM.1
  obtain ⟨c, hrow⟩ := rowMean_ae_constant M hM hErg H hH
  obtain ⟨d, hcol'⟩ := columnMean_ae_constant M hM hErg H hH
  have hcd : c = d :=
    rowColumnMean_constants_eq M hM H hH.1 c d hrow hcol'
  have hcol :
      (fun y => ∫ x, H (x, y) ∂M.μ) =ᵐ[M.μ] fun _ => c := by
    simpa only [hcd] using hcol'
  let G : M.X × M.X → ℂ := fun _ => c
  let hG : MemLp G 2 (M.μ.prod M.μ) := memLp_const c
  let C : M.X × M.X → ℂ := fun p => H p - G p
  let hCmem : MemLp C 2 (M.μ.prod M.μ) := hH.1.sub hG
  have hCinv :
      C ∘ productTransformation M =ᵐ[M.μ.prod M.μ] C := by
    filter_upwards [hH.2] with p hp
    change H (productTransformation M p) = H p at hp
    change H (productTransformation M p) - c = H p - c
    rw [hp]
  have hC : IsInvariantL2Kernel M C := ⟨hCmem, hCinv⟩
  have hC0 : ¬ C =ᵐ[M.μ.prod M.μ] 0 := by
    intro hzero
    apply hHnonconst
    refine ⟨c, ?_⟩
    filter_upwards [hzero] with p hp
    change H p - c = 0 at hp
    simpa using sub_eq_zero.mp hp
  have hHint : Integrable H (M.μ.prod M.μ) :=
    hH.1.integrable (by norm_num)
  have hrowC :
      (fun x => ∫ y, C (x, y) ∂M.μ) =ᵐ[M.μ] 0 := by
    filter_upwards [hrow, hHint.prod_right_ae] with x hx hHx
    change (∫ y, H (x, y) - c ∂M.μ) = 0
    rw [integral_sub hHx (integrable_const c)]
    simpa using sub_eq_zero.mpr hx
  have hcolC :
      (fun y => ∫ x, C (x, y) ∂M.μ) =ᵐ[M.μ] 0 := by
    filter_upwards [hcol, hHint.prod_left_ae] with y hy hHy
    change (∫ x, H (x, y) - c ∂M.μ) = 0
    rw [integral_sub hHy (integrable_const c)]
    simpa using sub_eq_zero.mpr hy
  obtain ⟨f, hf, hCf0⟩ :=
    exists_nonzero_kernelAction M hM C hCmem hC0
  let F : Lp ℂ 2 M.μ := hf.toLp f
  let K : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ :=
    HilbertSchmidtConsequences.kernelOperator M hM C hCmem
  let hKF := HilbertSchmidtConsequences.kernelAction_memLp_two
    M hM C hCmem F (Lp.memLp F)
  have hFraw : (fun x => F x) =ᵐ[M.μ] f := hf.coeFn_toLp
  have hKraw :
      (fun x => (K F) x) =ᵐ[M.μ] kernelAction M C f := by
    change
      (fun x =>
        (HilbertSchmidtConsequences.kernelOperator M hM C hCmem F) x)
          =ᵐ[M.μ] kernelAction M C f
    rw [HilbertSchmidtConsequences.kernelOperator_apply]
    exact hKF.coeFn_toLp.trans
      (EventuallyEq.of_eq
        (HilbertSchmidtConsequences.kernelAction_congr_ae M C hFraw))
  have hKF0 : K F ≠ 0 := by
    intro hz
    apply hCf0
    have hzero := Lp.coeFn_zero ℂ 2 M.μ
    rw [hz] at hKraw
    exact hKraw.symm.trans hzero
  have hKap :
      IsAlmostPeriodicVector (WeakSpectrum.koopmanData M hM) (K F) :=
    kernelOperator_range_almostPeriodic M hM C hC F
  have hKdisc :
      InDiscreteSpectralSubspace (WeakSpectrum.koopmanData M hM) (K F) :=
    AlmostPeriodicIsometry.almostPeriodic_implies_discrete
      (WeakSpectrum.koopmanData M hM)
      (fun X => (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map X)
      (K F) hKap
  obtain ⟨z, lam, hz0, hKz0, hzeig, hKzeig⟩ :=
    exists_range_eigenvector_of_discrete
      (WeakSpectrum.koopmanData M hM)
      (fun X => (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map X)
      K (kernelOperator_commutes_koopman M hM C hC) F hKF0 hKdisc
  change Lp ℂ 2 M.μ at z
  let Z : M.X → ℂ := fun x => z x
  have hZmem : M.lpMember 2 Z := Lp.memLp z
  have hlam1 : lam ≠ 1 := by
    intro hlam
    have hzeig1 :
        (WeakSpectrum.koopmanData M hM).U z = z := by
      simpa [hlam] using hzeig
    have hZinv : IsInvariantFunction M Z := by
      have hcomp := Lp.coeFn_compMeasurePreserving z hM.2
      change Lp.compMeasurePreserving M.T hM.2 z = z at hzeig1
      have heq :
          (fun x => (Lp.compMeasurePreserving M.T hM.2 z) x) =ᵐ[M.μ]
              fun x => z x := by rw [hzeig1]
      filter_upwards [hcomp, heq] with x hcx hex
      change z (M.T x) = z x
      exact (by simpa [Function.comp_apply] using hcx.symm.trans hex)
    obtain ⟨a, ha⟩ :=
      ((Section01.ergodicityInvariantFunctionCharacterizations M hM).mp hErg)
        Z hZmem hZinv
    have hCZzero : kernelAction M C Z =ᵐ[M.μ] 0 := by
      have hcongr :=
        HilbertSchmidtConsequences.kernelAction_congr_ae M C ha
      filter_upwards [EventuallyEq.of_eq hcongr, hrowC] with x hx hrowx
      rw [hx]
      change (∫ y, C (x, y) * a ∂M.μ) = 0
      rw [integral_mul_const]
      simpa only [Pi.zero_apply, zero_mul] using
        congrArg (fun q => q * a) hrowx
    let hKZ := HilbertSchmidtConsequences.kernelAction_memLp_two
      M hM C hCmem Z hZmem
    have hKzraw :
        (fun x => (K z) x) =ᵐ[M.μ] kernelAction M C Z := by
      change
        (fun x =>
          (HilbertSchmidtConsequences.kernelOperator M hM C hCmem z) x)
            =ᵐ[M.μ] kernelAction M C Z
      rw [HilbertSchmidtConsequences.kernelOperator_apply]
      change
        (fun x => (hKZ.toLp (kernelAction M C Z)) x) =ᵐ[M.μ]
          kernelAction M C Z
      exact hKZ.coeFn_toLp
    apply hKz0
    apply Lp.ext (μ := M.μ)
    exact hKzraw.trans hCZzero |>.trans (Lp.coeFn_zero ℂ 2 M.μ).symm
  have hZeigraw :
      (fun x => Z (M.T x)) =ᵐ[M.μ] fun x => lam * Z x := by
    have hcomp := Lp.coeFn_compMeasurePreserving z hM.2
    have hsmul := Lp.coeFn_smul lam z
    change Lp.compMeasurePreserving M.T hM.2 z = lam • z at hzeig
    have heq :
        (fun x => (Lp.compMeasurePreserving M.T hM.2 z) x) =ᵐ[M.μ]
          fun x => (lam • z) x := by rw [hzeig]
    filter_upwards [hcomp, hsmul, heq] with x hcx hsx hex
    change z (M.T x) = lam * z x
    calc
      z (M.T x) = (Lp.compMeasurePreserving M.T hM.2 z) x := by
        simpa [Function.comp_apply] using hcx.symm
      _ = (lam • z) x := hex
      _ = lam * z x := by simpa [Pi.smul_apply] using hsx
  have hZint : ∫ x, Z x ∂M.μ = 0 := by
    have hpresint :=
      integral_comp_measurePreserving M.T hM.2 Z
        hZmem.1
    have heigint := integral_congr_ae hZeigraw
    rw [integral_const_mul] at heigint
    have hmul : (1 - lam) * (∫ x, Z x ∂M.μ) = 0 := by
      calc
        (1 - lam) * (∫ x, Z x ∂M.μ) =
            (∫ x, Z x ∂M.μ) - lam * (∫ x, Z x ∂M.μ) := by ring
        _ = 0 := by rw [← heigint, hpresint, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hlam1.symm)
  let g : M.X → ℂ := fun x => (K z) x
  let hKZ := HilbertSchmidtConsequences.kernelAction_memLp_two
    M hM C hCmem Z hZmem
  have hgC : g =ᵐ[M.μ] kernelAction M C Z := by
    change
      (fun x =>
        (HilbertSchmidtConsequences.kernelOperator M hM C hCmem z) x)
          =ᵐ[M.μ] kernelAction M C Z
    rw [HilbertSchmidtConsequences.kernelOperator_apply]
    change
      (fun x => (hKZ.toLp (kernelAction M C Z)) x) =ᵐ[M.μ]
        kernelAction M C Z
    exact hKZ.coeFn_toLp
  have hGZzero : kernelAction M G Z = fun _ => 0 := by
    funext x
    simp only [kernelAction, G]
    rw [integral_const_mul, hZint, mul_zero]
  have hCH :
      kernelAction M C Z =ᵐ[M.μ] kernelAction M H Z := by
    have hsub :=
      HilbertSchmidtConsequences.kernelAction_kernel_sub_ae
        M hM H G hH.1 hG Z hZmem
    simpa only [C, hGZzero, Pi.zero_apply, sub_zero] using hsub
  have hgH : g =ᵐ[M.μ] kernelAction M H Z := hgC.trans hCH
  have hgEig : IsEigenvector (WeakSpectrum.koopmanData M hM) (K z) :=
    ⟨hKz0, lam, hKzeig⟩
  obtain ⟨xi, hgEigen⟩ :=
    WeakSpectrum.eigenvector_to_eigenfunction M hM (K z) hgEig
  have hgint : ∫ x, g x ∂M.μ = 0 := by
    rw [integral_congr_ae hgC]
    exact integral_kernelAction_eq_zero_of_columnMean
      M hM C hCmem Z hZmem hcolC
  have hgnonconst : ¬ IsAEEqConstant M g := by
    rintro ⟨a, ha⟩
    have ha0 : a = 0 := by
      have hint := integral_congr_ae ha
      have hint' : (∫ x, g x ∂M.μ) = a := by simpa using hint
      exact hint'.symm.trans hgint
    apply hKz0
    apply Lp.ext (μ := M.μ)
    exact ha.trans (EventuallyEq.of_eq (funext fun x => by simp [ha0])) |>.trans
      (Lp.coeFn_zero ℂ 2 M.μ).symm
  exact ⟨g, ⟨Z, hZmem, hgH⟩, xi, hgEigen, hgnonconst⟩

theorem tensorSquare_condExp_ne_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (f : M.X → ℂ) (hfAP : IsAlmostPeriodicFunction M f)
    (hf0 : ¬ f =ᵐ[M.μ] 0)
    (hfT : MemLp (TensorSquare M f) 2 (M.μ.prod M.μ)) :
    ¬ condExp
        (MeasurableSpace.generateFrom (productInvariantSigmaAlgebra M))
        (M.μ.prod M.μ) (TensorSquare M f) =ᵐ[M.μ.prod M.μ] 0 := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let F : Lp ℂ 2 M.μ := hfAP.1.toLp f
  have hF0 : F ≠ 0 := by
    intro hzero
    apply hf0
    have hcoe := hfAP.1.coeFn_toLp
    have hFzero : (fun x => F x) =ᵐ[M.μ] 0 := by
      rw [hzero]
      exact Lp.coeFn_zero ℂ 2 M.μ
    exact hcoe.symm.trans hFzero
  have hFap : IsAlmostPeriodicVector (WeakSpectrum.koopmanData M hM) F :=
    CompactDiscrete.almostPeriodicFunction_to_vector M hM f hfAP
  have hFdisc : InDiscreteSpectralSubspace (WeakSpectrum.koopmanData M hM) F :=
    AlmostPeriodicIsometry.almostPeriodic_implies_discrete
      (WeakSpectrum.koopmanData M hM)
      (fun X => (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map X)
      F hFap
  obtain ⟨Y, hYeig, hFY⟩ :=
    AlmostPeriodicIsometry.exists_eigenvector_inner_ne_zero_of_discrete
      (WeakSpectrum.koopmanData M hM) F hFdisc hF0
  change Lp ℂ 2 M.μ at Y
  obtain ⟨lam, hYfun⟩ :=
    WeakSpectrum.eigenvector_to_eigenfunction M hM Y hYeig
  let g : M.X → ℂ := fun x => Y x
  have hg : M.lpMember 2 g := Lp.memLp Y
  have hlamnorm : ‖lam‖ = 1 :=
    (Section05.eigen_norm_modulus M hErg lam g hYfun).1
  let P := ProductWeakMixing.productSystem M M
  have hP := ProductWeakMixing.productSystem_mps M M hM hM
  have hfamily :
      invariantSigmaAlgebra P = productInvariantSigmaAlgebra M := by
    rfl
  let YT : Lp ℂ 2 (M.μ.prod M.μ) :=
    (tensorSquare_memLp M hM g hg).toLp (TensorSquare M g)
  have hYTfix : (WeakSpectrum.koopmanData P hP).U YT = YT := by
    apply Lp.ext (μ := M.μ.prod M.μ)
    have hcomp := Lp.coeFn_compMeasurePreserving YT hP.2
    have hYTcoe := (tensorSquare_memLp M hM g hg).coeFn_toLp
    have heig := hYfun.2.2
    have heigfst :=
      (Measure.quasiMeasurePreserving_fst
        (μ := M.μ) (ν := M.μ)).ae_eq_comp heig
    have heigsnd :=
      (Measure.quasiMeasurePreserving_snd
        (μ := M.μ) (ν := M.μ)).ae_eq_comp heig
    filter_upwards [hcomp, hYTcoe,
      hP.2.quasiMeasurePreserving.ae hYTcoe,
      heigfst, heigsnd] with p hcp hp hTp he1 he2
    change
      (Lp.compMeasurePreserving P.T hP.2 YT) p = YT p
    change
      (Lp.compMeasurePreserving
        (ProductWeakMixing.productSystem M M).T hP.2 YT) p = YT p
    change
      (Lp.compMeasurePreserving
        (ProductWeakMixing.productSystem M M).T hP.2 YT) p =
        (YT ∘ (ProductWeakMixing.productSystem M M).T) p at hcp
    change
      YT ((ProductWeakMixing.productSystem M M).T p) =
        TensorSquare M g ((ProductWeakMixing.productSystem M M).T p) at hTp
    rw [hcp]
    change YT ((ProductWeakMixing.productSystem M M).T p) = YT p
    rw [hTp, hp]
    change TensorSquare M g (M.T p.1, M.T p.2) = TensorSquare M g p
    change g (M.T p.1) = lam * g p.1 at he1
    change g (M.T p.2) = lam * g p.2 at he2
    simp only [TensorSquare]
    rw [he1, he2, star_mul]
    change (lam * g p.1) * (star (g p.2) * star lam) =
      g p.1 * star (g p.2)
    calc
      _ = (lam * star lam) * (g p.1 * star (g p.2)) := by ring
      _ = _ := by
        change (lam * (starRingEnd ℂ) lam) * _ = _
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hlamnorm]
        norm_num
  have hinner :
      @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) inferInstance
        (hfT.toLp (TensorSquare M f)) YT ≠ 0 := by
    have heq := inner_tensorSquare M hM f g hfAP.1 hg
    change
      @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) inferInstance
        ((tensorSquare_memLp M hM f hfAP.1).toLp (TensorSquare M f)) YT ≠ 0
    rw [heq]
    have hFY' :
        @inner ℂ (Lp ℂ 2 M.μ) inferInstance
          (hfAP.1.toLp f) (hg.toLp g) ≠ 0 := by
      have hGY : hg.toLp g = Y := by
        apply Lp.ext (μ := M.μ)
        exact hg.coeFn_toLp
      rw [hGY]
      simpa only [F] using hFY
    exact mul_ne_zero hFY' ((map_ne_zero (starRingEnd ℂ)).2 hFY')
  intro hce0
  let mInv : MeasurableSpace (M.X × M.X) :=
    MeasurableSpace.generateFrom (productInvariantSigmaAlgebra M)
  have hm : mInv ≤ P.measurableSpace := by
    apply MeasurableSpace.generateFrom_le
    intro s hs
    exact hs.1
  let CEsub := (condExpL2 (m := mInv) (m0 := P.measurableSpace)
    (μ := P.μ) ℂ ℂ hm) (hfT.toLp (TensorSquare M f))
  let CE : Lp ℂ 2 P.μ := CEsub.1
  have hCE0 : CE = 0 := by
    apply Lp.ext (μ := P.μ)
    have hceae :=
      hfT.condExpL2_ae_eq_condExp' (𝕜 := ℂ) hm
        (hfT.integrable (by norm_num))
    have hzraw :=
      hceae.trans (by simpa [mInv, P] using hce0) |>.trans
        (Lp.coeFn_zero ℂ 2 P.μ).symm
    simpa only [CE, CEsub] using hzraw
  have hYTmeas : AEStronglyMeasurable[mInv] (fun p => YT p) P.μ := by
    have hfixed :
        YT ∈ LinearMap.eqLocus
          (Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2).toContinuousLinearMap
          (1 : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ) := by
      exact hYTfix
    have hspace :=
      MeanErgodicL2.fixedSpace_eq_invariantLpMeas P hP
    rw [hspace] at hfixed
    change YT ∈ lpMeas ℂ ℂ
      (MeasurableSpace.generateFrom (invariantSigmaAlgebra P)) 2 P.μ at hfixed
    rw [hfamily] at hfixed
    exact mem_lpMeas_iff_aestronglyMeasurable.mp hfixed
  have hcondinner :=
    inner_condExpL2_eq_inner_fun (𝕜 := ℂ) hm
      (hfT.toLp (TensorSquare M f)) YT hYTmeas
  change @inner ℂ (Lp ℂ 2 P.μ) inferInstance CE YT =
    @inner ℂ (Lp ℂ 2 P.μ) inferInstance
      (hfT.toLp (TensorSquare M f)) YT at hcondinner
  rw [hCE0, inner_zero_left] at hcondinner
  apply hinner
  change @inner ℂ (Lp ℂ 2 P.μ) inferInstance
    (hfT.toLp (TensorSquare M f)) YT = 0
  exact hcondinner.symm

end Chapter02.HilbertSchmidtInvariant
