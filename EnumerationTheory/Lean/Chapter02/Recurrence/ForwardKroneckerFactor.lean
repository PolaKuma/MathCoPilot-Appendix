import Chapter02.Ergodic.AlgebraSubSigma
import Chapter02.Recurrence.MultipleKhintchineKronecker
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Analysis.Convex.Integral

open Classical Filter Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Chapter02.ForwardKroneckerFactor

universe u

lemma memLp_pointwiseStar
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p : ℝ≥0∞} {f : X → ℂ} (hf : MemLp f p μ) :
    MemLp (fun x ↦ star (f x)) p μ := by
  apply hf.congr_norm hf.1.star
  filter_upwards [] with x
  exact (norm_star (f x)).symm

lemma coe_finset_linear_combination_ae
    {M : System.{u}}
    (s : Finset (MeasureTheory.Lp ℂ 2 M.μ))
    (c : MeasureTheory.Lp ℂ 2 M.μ → ℂ) :
    (fun x ↦ (∑ y ∈ s, c y • y) x) =ᵐ[M.μ]
      (fun x ↦ ∑ y ∈ s, c y * y x) := by
  induction s using Finset.induction_on with
  | empty =>
      filter_upwards [MeasureTheory.Lp.coeFn_zero ℂ 2 M.μ] with x hx
      simpa using hx
  | @insert y s hy ih =>
      filter_upwards [ih,
        MeasureTheory.Lp.coeFn_add (c y • y) (∑ z ∈ s, c z • z),
        MeasureTheory.Lp.coeFn_smul (c y) y] with x hih hadd hsmul
      simp only [Finset.sum_insert, hy, not_false_eq_true]
      rw [hadd]
      simp only [Pi.add_apply]
      rw [hsmul, hih]
      simp only [Pi.smul_apply, smul_eq_mul]

lemma memLp_top_finset_linear_combination
    {M : System.{u}}
    (s : Finset (MeasureTheory.Lp ℂ 2 M.μ))
    (c : MeasureTheory.Lp ℂ 2 M.μ → ℂ)
    (htop : ∀ y ∈ s, M.lpMember ⊤ (fun x ↦ y x)) :
    M.lpMember ⊤ (fun x ↦ ∑ y ∈ s, c y * y x) := by
  induction s using Finset.induction_on with
  | empty =>
      convert (MeasureTheory.MemLp.zero' :
        M.lpMember ⊤ (fun _ : M.X ↦ (0 : ℂ))) using 1
  | @insert y s hy ih =>
      have hyTop : M.lpMember ⊤ (fun x ↦ c y * y x) :=
        (htop y (Finset.mem_insert_self y s)).const_mul (c y)
      have ihTop := ih (fun z hz ↦ htop z (Finset.mem_insert_of_mem hz))
      simpa [Finset.sum_insert, hy] using hyTop.add ihTop

/-- Pointwise complex conjugation on `L²`. -/
def lpStar (M : System.{u}) (F : MeasureTheory.Lp ℂ 2 M.μ) :
    MeasureTheory.Lp ℂ 2 M.μ :=
  (memLp_pointwiseStar (MeasureTheory.Lp.memLp F)).toLp
    (fun x ↦ star (F x))

lemma lpStar_coe (M : System.{u}) (F : MeasureTheory.Lp ℂ 2 M.μ) :
    (fun x ↦ lpStar M F x) =ᵐ[M.μ] (fun x ↦ star (F x)) :=
  (memLp_pointwiseStar (MeasureTheory.Lp.memLp F)).coeFn_toLp

lemma norm_lpStar (M : System.{u}) (F : MeasureTheory.Lp ℂ 2 M.μ) :
    ‖lpStar M F‖ = ‖F‖ := by
  unfold lpStar
  rw [MeasureTheory.Lp.norm_toLp]
  rw [MeasureTheory.Lp.norm_def]
  congr 1
  exact eLpNorm_congr_norm_ae
    (Filter.Eventually.of_forall fun x ↦ norm_star (F x))

lemma lpStar_sub (M : System.{u})
    (F G : MeasureTheory.Lp ℂ 2 M.μ) :
    lpStar M (F - G) = lpStar M F - lpStar M G := by
  apply MeasureTheory.Lp.ext
  filter_upwards [lpStar_coe M (F - G), lpStar_coe M F,
    lpStar_coe M G, MeasureTheory.Lp.coeFn_sub F G,
    MeasureTheory.Lp.coeFn_sub (lpStar M F) (lpStar M G)] with
      x hFG hF hG hsub hout
  rw [hFG, hsub, hout]
  simp only [Pi.sub_apply]
  rw [hF, hG]
  exact star_sub (F x) (G x)

def forwardKoopmanLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ) : MeasureTheory.Lp ℂ 2 M.μ :=
  ((MeasureTheory.Lp.memLp F).comp_measurePreserving hM.2).toLp
    (fun x ↦ F (M.T x))

lemma koopmanData_eq_forwardKoopmanLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ) :
    (MultipleKhintchineKronecker.koopmanData M hM).U F =
      forwardKoopmanLp M hM F := by
  let hf := MeasureTheory.Lp.memLp F
  have hF : hf.toLp (fun x ↦ F x) = F := by
    apply MeasureTheory.Lp.ext
    exact hf.coeFn_toLp
  calc
    (MultipleKhintchineKronecker.koopmanData M hM).U F =
        (MultipleKhintchineKronecker.koopmanData M hM).U
          (hf.toLp (fun x ↦ F x)) := congrArg
            (MultipleKhintchineKronecker.koopmanData M hM).U hF.symm
    _ = (hf.comp_measurePreserving hM.2).toLp
          (Chapter01.koopman M.T (fun x ↦ F x)) :=
      MultipleKhintchineKronecker.koopmanData_apply_toLp
        M hM (fun x ↦ F x) hf
    _ = forwardKoopmanLp M hM F := rfl

lemma forwardKoopmanLp_coe
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ) :
    (fun x ↦ forwardKoopmanLp M hM F x) =ᵐ[M.μ]
      (fun x ↦ F (M.T x)) :=
  ((MeasureTheory.Lp.memLp F).comp_measurePreserving hM.2).coeFn_toLp

lemma lpStar_koopman
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ) :
    lpStar M
        ((MultipleKhintchineKronecker.koopmanData M hM).U F) =
      (MultipleKhintchineKronecker.koopmanData M hM).U (lpStar M F) := by
  rw [koopmanData_eq_forwardKoopmanLp,
    koopmanData_eq_forwardKoopmanLp]
  apply MeasureTheory.Lp.ext
  filter_upwards [
    lpStar_coe M (forwardKoopmanLp M hM F),
    forwardKoopmanLp_coe M hM F,
    forwardKoopmanLp_coe M hM (lpStar M F),
    hM.2.quasiMeasurePreserving.ae_eq_comp
      (lpStar_coe M F)] with x hleft hUF hUS hstarT
  rw [hleft, hUF, hUS]
  simpa only [Function.comp_apply] using hstarT.symm

lemma lpStar_iterate_koopman
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ) (n : ℕ) :
    lpStar M
        (((MultipleKhintchineKronecker.koopmanData M hM).U^[n]) F) =
      ((MultipleKhintchineKronecker.koopmanData M hM).U^[n]) (lpStar M F) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        lpStar_koopman, ih]

lemma almostPeriodic_lpStar
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : IsAlmostPeriodicVector
      (MultipleKhintchineKronecker.koopmanData M hM) F) :
    IsAlmostPeriodicVector
      (MultipleKhintchineKronecker.koopmanData M hM) (lpStar M F) := by
  intro ε hε
  obtain ⟨s, hs⟩ := hF ε hε
  refine ⟨s.image (lpStar M), ?_⟩
  intro n
  obtain ⟨Y, hYs, hdist⟩ := hs n
  refine ⟨lpStar M Y, Finset.mem_image.mpr ⟨Y, hYs, rfl⟩, ?_⟩
  rw [← lpStar_iterate_koopman M hM F n, ← lpStar_sub,
    norm_lpStar]
  exact hdist

/-- Representative-level realization of the forward almost-periodic Koopman
subspace.  The universal quantifier makes membership independent of the proof
used to construct `MemLp.toLp`. -/
def forwardAlmostPeriodicFunctions
    (M : System.{u}) (hM : IsErgodic M) : Set (M.X → ℂ) :=
  {f | M.lpMember 2 f ∧
    ∀ hf : M.lpMember 2 f,
      IsAlmostPeriodicVector
        (MultipleKhintchineKronecker.koopmanData M hM.1)
        (hf.toLp f)}

lemma forwardAlmostPeriodicFunctions_memLp
    (M : System.{u}) (hM : IsErgodic M)
    {f : M.X → ℂ}
    (hf : f ∈ forwardAlmostPeriodicFunctions M hM) :
    M.lpMember 2 f :=
  hf.1

lemma forwardAlmostPeriodicFunctions_toLp
    (M : System.{u}) (hM : IsErgodic M)
    {f : M.X → ℂ}
    (hf : f ∈ forwardAlmostPeriodicFunctions M hM)
    (hf2 : M.lpMember 2 f) :
    IsAlmostPeriodicVector
      (MultipleKhintchineKronecker.koopmanData M hM.1)
      (hf2.toLp f) :=
  hf.2 hf2

lemma forwardAlmostPeriodicFunctions_zero
    (M : System.{u}) (hM : IsErgodic M) :
    (fun _ : M.X ↦ (0 : ℂ)) ∈
      forwardAlmostPeriodicFunctions M hM := by
  refine ⟨MeasureTheory.MemLp.zero', ?_⟩
  intro hzero
  have hto :
      hzero.toLp (fun _ : M.X ↦ (0 : ℂ)) = 0 := by
    apply MeasureTheory.Lp.ext
    filter_upwards [hzero.coeFn_toLp,
      MeasureTheory.Lp.coeFn_zero ℂ 2 M.μ] with x hx hz
    rw [hx, hz]
    simp
  rw [hto]
  exact AlmostPeriodic.almostPeriodic_zero _

lemma forwardAlmostPeriodicFunctions_linear
    (M : System.{u}) (hM : IsErgodic M)
    (f g : M.X → ℂ)
    (hf : f ∈ forwardAlmostPeriodicFunctions M hM)
    (hg : g ∈ forwardAlmostPeriodicFunctions M hM)
    (a b : ℂ) :
    (fun x ↦ a * f x + b * g x) ∈
      forwardAlmostPeriodicFunctions M hM := by
  let haf := hf.1.const_mul a
  let hbg := hg.1.const_mul b
  let hab := haf.add hbg
  refine ⟨hab, ?_⟩
  intro hcomb
  have hfa := hf.2 hf.1
  have hga := hg.2 hg.1
  have hlin := AlmostPeriodic.almostPeriodic_linear
    (MultipleKhintchineKronecker.koopmanData M hM.1)
    (hf.1.toLp f) (hg.1.toLp g) hfa hga a b
  have heq :
      hcomb.toLp (fun x ↦ a * f x + b * g x) =
        a • hf.1.toLp f + b • hg.1.toLp g := by
    apply MeasureTheory.Lp.ext
    filter_upwards [hcomb.coeFn_toLp,
      MeasureTheory.Lp.coeFn_add
        (a • hf.1.toLp f) (b • hg.1.toLp g),
      MeasureTheory.Lp.coeFn_smul a (hf.1.toLp f),
      MeasureTheory.Lp.coeFn_smul b (hg.1.toLp g),
      hf.1.coeFn_toLp, hg.1.coeFn_toLp] with
        x hcombX haddX hafX hbgX hfX hgX
    rw [hcombX, haddX]
    simp only [Pi.add_apply]
    rw [hafX, hbgX]
    simp only [Pi.smul_apply]
    rw [hfX, hgX]
    rfl
  rw [heq]
  exact hlin

lemma forwardAlmostPeriodicFunctions_ae
    (M : System.{u}) (hM : IsErgodic M)
    (f : M.X → ℂ)
    (hf : f ∈ forwardAlmostPeriodicFunctions M hM)
    (g : M.X → ℂ) (hfg : f =ᵐ[M.μ] g) :
    g ∈ forwardAlmostPeriodicFunctions M hM := by
  have hg2 : M.lpMember 2 g := (memLp_congr_ae hfg).mp hf.1
  refine ⟨hg2, ?_⟩
  intro hg
  have heq : hg.toLp g = hf.1.toLp f := by
    apply MeasureTheory.Lp.ext
    filter_upwards [hg.coeFn_toLp, hf.1.coeFn_toLp, hfg] with
      x hgX hfX hfgX
    rw [hgX, hfX, ← hfgX]
  rw [heq]
  exact hf.2 hf.1

lemma forwardAlmostPeriodicFunctions_closed
    (M : System.{u}) (hM : IsErgodic M)
    (fseq : ℕ → M.X → ℂ)
    (hfseq : ∀ n, fseq n ∈ forwardAlmostPeriodicFunctions M hM)
    (f : M.X → ℂ) (hf : M.lpMember 2 f)
    (hconv : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ fseq n x - f x) 2 M.μ)
      atTop (nhds 0)) :
    f ∈ forwardAlmostPeriodicFunctions M hM := by
  let D := MultipleKhintchineKronecker.koopmanData M hM.1
  let X : ℕ → MeasureTheory.Lp ℂ 2 M.μ :=
    fun n ↦ (hfseq n).1.toLp (fseq n)
  let Y : MeasureTheory.Lp ℂ 2 M.μ := hf.toLp f
  have hXY : Tendsto X atTop (nhds Y) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hreal :=
      (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hconv
    convert hreal using 1
    funext n
    change ‖(hfseq n).1.toLp (fseq n) - hf.toLp f‖ =
      (eLpNorm (fun x ↦ fseq n x - f x) 2 M.μ).toReal
    change ‖(hfseq n).1.toLp (fseq n) - hf.toLp f‖ =
      (eLpNorm (fseq n - f) 2 M.μ).toReal
    rw [← MeasureTheory.Lp.norm_toLp _
      ((hfseq n).1.sub hf), MeasureTheory.MemLp.toLp_sub]
  have hclosed :=
    AlmostPeriodicIsometry.almostPeriodic_closed D
      (fun Z ↦
        (MeasureTheory.Lp.compMeasurePreservingₗᵢ
          ℂ M.T hM.1.2).norm_map Z)
  have hY :
      IsAlmostPeriodicVector D Y := by
    apply hclosed.isSeqClosed
    · intro n
      exact (hfseq n).2 (hfseq n).1
    · exact hXY
  refine ⟨hf, ?_⟩
  intro hf'
  have heq : hf'.toLp f = Y := by
    rfl
  rwa [heq]

theorem forwardAlmostPeriodicFunctions_isClosedL2
    (M : System.{u}) (hM : IsErgodic M) :
    IsClosedL2FunctionSubspace M
      (forwardAlmostPeriodicFunctions M hM) := by
  exact ⟨forwardAlmostPeriodicFunctions_zero M hM,
    fun _ hf ↦ hf.1,
    fun f hf g hg a b ↦
      forwardAlmostPeriodicFunctions_linear M hM f g hf hg a b,
    forwardAlmostPeriodicFunctions_ae M hM,
    forwardAlmostPeriodicFunctions_closed M hM⟩

lemma constantOne_mem
    (M : System.{u}) (hM : IsErgodic M) :
    (fun _ : M.X ↦ (1 : ℂ)) ∈
      forwardAlmostPeriodicFunctions M hM := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  let hOne : M.lpMember 2 (fun _ : M.X ↦ (1 : ℂ)) :=
    MeasureTheory.memLp_const 1
  refine ⟨hOne, ?_⟩
  intro hOne'
  let D := MultipleKhintchineKronecker.koopmanData M hM.1
  let One : MeasureTheory.Lp ℂ 2 M.μ :=
    hOne'.toLp (fun _ : M.X ↦ (1 : ℂ))
  have hfix : D.U One = One := by
    dsimp only [D, One]
    rw [MultipleKhintchineKronecker.koopmanData_apply_toLp]
    apply MeasureTheory.Lp.ext
    filter_upwards [
      (hOne'.comp_measurePreserving hM.1.2).coeFn_toLp,
      hOne'.coeFn_toLp] with x hcomp hone
    change
      ((hOne'.comp_measurePreserving hM.1.2).toLp
        (Chapter01.koopman M.T (fun _ : M.X ↦ (1 : ℂ)))) x = 1
      at hcomp
    rw [hcomp, hone]
  have hiter : ∀ n : ℕ, (D.U^[n]) One = One := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, hfix]
  intro ε hε
  refine ⟨{One}, ?_⟩
  intro n
  refine ⟨One, Finset.mem_singleton_self One, ?_⟩
  rw [hiter]
  simpa using hε

lemma star_mem
    (M : System.{u}) (hM : IsErgodic M)
    {f : M.X → ℂ}
    (hf : f ∈ forwardAlmostPeriodicFunctions M hM) :
    (fun x ↦ star (f x)) ∈
      forwardAlmostPeriodicFunctions M hM := by
  let F : MeasureTheory.Lp ℂ 2 M.μ := hf.1.toLp f
  have hstar2 : M.lpMember 2 (fun x ↦ star (f x)) :=
    memLp_pointwiseStar hf.1
  refine ⟨hstar2, ?_⟩
  intro hstar2'
  have heq :
      hstar2'.toLp (fun x ↦ star (f x)) = lpStar M F := by
    apply MeasureTheory.Lp.ext
    filter_upwards [hstar2'.coeFn_toLp, lpStar_coe M F,
      hf.1.coeFn_toLp] with x hraw hlp hfX
    rw [hraw, hlp, hfX]
  rw [heq]
  exact almostPeriodic_lpStar M hM.1 F (hf.2 hf.1)

/-- A bounded representative may multiply any forward almost-periodic
`L²` representative without leaving the forward almost-periodic subspace. -/
lemma bounded_mul_mem
    (M : System.{u}) (hM : IsErgodic M)
    {f g : M.X → ℂ}
    (hf : f ∈ forwardAlmostPeriodicFunctions M hM)
    (hg : g ∈ forwardAlmostPeriodicFunctions M hM)
    (hftop : M.lpMember ⊤ f)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂M.μ, ‖f x‖ ≤ C) :
    (fun x ↦ f x * g x) ∈
      forwardAlmostPeriodicFunctions M hM := by
  let F : MeasureTheory.Lp ℂ 2 M.μ := hf.1.toLp f
  let G : MeasureTheory.Lp ℂ 2 M.μ := hg.1.toLp g
  have hFraw : (fun x ↦ F x) =ᵐ[M.μ] f := hf.1.coeFn_toLp
  have hFtop : M.lpMember ⊤ (fun x ↦ F x) :=
    (memLp_congr_ae hFraw).mpr hftop
  have hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C := by
    filter_upwards [hFraw, hbound] with x hFx hx
    rwa [hFx]
  let P : MeasureTheory.Lp ℂ 2 M.μ :=
    MultipleKhintchineKronecker.lpPointwiseMul F G hFtop
  have hPAP :
      IsAlmostPeriodicVector
        (MultipleKhintchineKronecker.koopmanData M hM.1) P :=
    MultipleKhintchineKronecker.almostPeriodic_mul_of_bounded_left
      M hM G F (hg.2 hg.1) (hf.2 hf.1)
        hFtop C hC hFbound
  have hPraw :
      (fun x ↦ P x) =ᵐ[M.μ] (fun x ↦ f x * g x) := by
    filter_upwards [
      MultipleKhintchineKronecker.lpPointwiseMul_coe F G hFtop,
      hf.1.coeFn_toLp, hg.1.coeFn_toLp] with x hmul hfX hgX
    rw [hmul, hfX, hgX]
  have hprod2 : M.lpMember 2 (fun x ↦ f x * g x) :=
    (memLp_congr_ae hPraw).mp (MeasureTheory.Lp.memLp P)
  refine ⟨hprod2, ?_⟩
  intro hprod2'
  have heq : hprod2'.toLp (fun x ↦ f x * g x) = P := by
    apply MeasureTheory.Lp.ext
    filter_upwards [hprod2'.coeFn_toLp, hPraw] with x hraw hP
    rw [hraw, ← hP]
  rw [heq]
  exact hPAP

lemma bounded_pow_mem
    (M : System.{u}) (hM : IsErgodic M)
    {f : M.X → ℂ}
    (hf : f ∈ forwardAlmostPeriodicFunctions M hM)
    (hftop : M.lpMember ⊤ f) :
    ∀ n : ℕ,
      (fun x ↦ (f x) ^ n) ∈ forwardAlmostPeriodicFunctions M hM ∧
      M.lpMember ⊤ (fun x ↦ (f x) ^ n) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  intro n
  induction n with
  | zero =>
      constructor
      · simpa using constantOne_mem M hM
      · simpa using (MeasureTheory.memLp_const (μ := M.μ) (1 : ℂ))
  | succ n ih =>
      have hpowBound :
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ᵐ x ∂M.μ, ‖(f x) ^ n‖ ≤ C := by
        obtain ⟨C, hC⟩ :=
          eLpNormEssSup_lt_top_iff_isBoundedUnder.mp
            (by simpa only [eLpNorm_exponent_top] using ih.2.2)
        refine ⟨C, by positivity, ?_⟩
        filter_upwards [hC] with x hx
        exact_mod_cast hx
      obtain ⟨C, hCnonneg, hC⟩ := hpowBound
      constructor
      · simpa [pow_succ] using
          bounded_mul_mem M hM ih.1 hf ih.2 C hCnonneg hC
      · have hmulTop :
            M.lpMember ⊤ (fun x ↦ (f x) ^ n * f x) :=
          hftop.mul ih.2
        simpa [pow_succ] using hmulTop

lemma polynomial_eval_mem_bounded
    (M : System.{u}) (hM : IsErgodic M)
    {h : M.X → ℝ}
    (hh : (fun x ↦ (h x : ℂ)) ∈
      forwardAlmostPeriodicFunctions M hM)
    (hhtop : M.lpMember ⊤ (fun x ↦ (h x : ℂ)))
    (p : Polynomial ℝ) :
    (fun x ↦ Complex.ofReal (p.eval (h x))) ∈
      forwardAlmostPeriodicFunctions M hM := by
  let H := forwardAlmostPeriodicFunctions M hM
  have hterm : ∀ n ∈ p.support,
      (fun x ↦ ((p.coeff n : ℝ) : ℂ) * (h x : ℂ) ^ n) ∈ H := by
    intro n hn
    exact AlgebraSubSigma.mem_smul M H
      (forwardAlmostPeriodicFunctions_isClosedL2 M hM)
      (bounded_pow_mem M hM hh hhtop n).1 (p.coeff n : ℂ)
  have hsum := AlgebraSubSigma.mem_finset_sum M H
    (forwardAlmostPeriodicFunctions_isClosedL2 M hM) p.support
    (fun n x ↦ ((p.coeff n : ℝ) : ℂ) * (h x : ℂ) ^ n) hterm
  convert hsum using 1
  funext x
  rw [Polynomial.eval_eq_sum]
  simp only [Polynomial.sum, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow]

theorem continuous_real_function_mem_bounded
    (M : System.{u}) (hM : IsErgodic M)
    {h : M.X → ℝ} (hhmeas : Measurable h)
    (hh : (fun x ↦ (h x : ℂ)) ∈
      forwardAlmostPeriodicFunctions M hM)
    (hhtop : M.lpMember ⊤ (fun x ↦ (h x : ℂ)))
    (a b : ℝ) (hab : ∀ x, h x ∈ Set.Icc a b)
    (F : ℝ → ℝ) (hF : Continuous F)
    (C : ℝ) (hC : ∀ t ∈ Set.Icc a b, |F t| ≤ C) :
    (fun x ↦ Complex.ofReal (F (h x))) ∈
      forwardAlmostPeriodicFunctions M hM := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  choose p hp using fun n : ℕ ↦
    exists_polynomial_near_of_continuousOn a b F hF.continuousOn
      ((1 : ℝ) / (n + 1)) (by positivity)
  let q : ℕ → M.X → ℂ := fun n x ↦ Complex.ofReal ((p n).eval (h x))
  have hq : ∀ n, q n ∈ forwardAlmostPeriodicFunctions M hM :=
    fun n ↦ polynomial_eval_mem_bounded M hM hh hhtop (p n)
  apply (forwardAlmostPeriodicFunctions_isClosedL2 M hM).2.2.2.2
    q hq (fun x ↦ Complex.ofReal (F (h x)))
  · exact MemLp.of_bound
      (Complex.continuous_ofReal.measurable.comp
        (hF.measurable.comp hhmeas)).aestronglyMeasurable C
      (Eventually.of_forall fun x ↦ by
        simpa [Complex.norm_real, Real.norm_eq_abs] using hC (h x) (hab x))
  · have hu : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((1 : ℝ) / (n + 1)))
        atTop (nhds (0 : ENNReal)) := by
      simpa using ENNReal.tendsto_ofReal
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (nhds 0))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    · exact fun _ ↦ zero_le _
    · intro n
      calc
        eLpNorm (fun x ↦ q n x - Complex.ofReal (F (h x))) 2 M.μ
            ≤ eLpNorm (fun _ : M.X ↦
                Complex.ofReal ((1 : ℝ) / (n + 1))) 2 M.μ := by
              apply eLpNorm_mono
              intro x
              have hnear := hp n (h x) (hab x)
              have heps : 0 ≤ (1 : ℝ) / (n + 1) := by positivity
              change ‖Complex.ofReal ((p n).eval (h x)) -
                Complex.ofReal (F (h x))‖ ≤
                ‖Complex.ofReal ((1 : ℝ) / (n + 1))‖
              rw [← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
                Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg heps]
              exact hnear.le
        _ = ENNReal.ofReal ((1 : ℝ) / (n + 1)) := by
              have heps : 0 ≤ (1 : ℝ) / (n + 1) := by positivity
              rw [eLpNorm_const' (p := (2 : ENNReal)) _
                (by norm_num) (by norm_num)]
              rw [measure_univ, ENNReal.one_rpow, mul_one]
              rw [enorm_eq_nnnorm, ENNReal.ofReal_eq_coe_nnreal heps]
              norm_cast
              apply NNReal.eq
              simp [Real.norm_eq_abs]
              positivity

theorem upper_level_indicator_mem_bounded
    (M : System.{u}) (hM : IsErgodic M)
    {h : M.X → ℝ} (hhmeas : Measurable h)
    (hh : (fun x ↦ (h x : ℂ)) ∈
      forwardAlmostPeriodicFunctions M hM)
    (hhtop : M.lpMember ⊤ (fun x ↦ (h x : ℂ)))
    (a b : ℝ) (hab : ∀ x, h x ∈ Set.Icc a b) (c : ℝ) :
    AlgebraSubSigma.indicatorOne {x | c < h x} ∈
      forwardAlmostPeriodicFunctions M hM := by
  apply AlgebraSubSigma.upper_level_indicator_mem_of_ramps
    M (forwardAlmostPeriodicFunctions M hM) hM.1
    (forwardAlmostPeriodicFunctions_isClosedL2 M hM) hhmeas c
  intro n
  exact continuous_real_function_mem_bounded
    M hM hhmeas hh hhtop a b hab
    (AlgebraSubSigma.ramp c n)
    (AlgebraSubSigma.ramp_continuous c n) 1
    (fun t _ ↦ by
      rw [abs_of_nonneg (AlgebraSubSigma.ramp_mem_Icc c n t).1]
      exact (AlgebraSubSigma.ramp_mem_Icc c n t).2)

lemma finiteEigenCombination_function_mem_top
    (M : System.{u}) (hM : IsErgodic M)
    (s : Finset (MeasureTheory.Lp ℂ 2 M.μ))
    (hs : ∀ y ∈ s,
      IsEigenvector
        (MultipleKhintchineKronecker.koopmanData M hM.1) y)
    (c : MeasureTheory.Lp ℂ 2 M.μ → ℂ) :
    let f : M.X → ℂ := fun x ↦ ∑ y ∈ s, c y * y x
    f ∈ forwardAlmostPeriodicFunctions M hM ∧ M.lpMember ⊤ f := by
  let D := MultipleKhintchineKronecker.koopmanData M hM.1
  let Y : MeasureTheory.Lp ℂ 2 M.μ := ∑ y ∈ s, c y • y
  let f : M.X → ℂ := fun x ↦ ∑ y ∈ s, c y * y x
  have hYf : (fun x ↦ Y x) =ᵐ[M.μ] f :=
    coe_finset_linear_combination_ae s c
  have hf2 : M.lpMember 2 f :=
    (memLp_congr_ae hYf).mp (MeasureTheory.Lp.memLp Y)
  have hYap : IsAlmostPeriodicVector D Y :=
    AlmostPeriodicIsometry.finiteEigenCombination_almostPeriodic
      D (fun X ↦
        (MeasureTheory.Lp.compMeasurePreservingₗᵢ
          ℂ M.T hM.1.2).norm_map X) s hs c
  have hfH : f ∈ forwardAlmostPeriodicFunctions M hM := by
    refine ⟨hf2, ?_⟩
    intro hf2'
    have heq : hf2'.toLp f = Y := by
      apply MeasureTheory.Lp.ext
      filter_upwards [hf2'.coeFn_toLp, hYf] with x hraw hY
      rw [hraw, ← hY]
    rw [heq]
    exact hYap
  have hftop : M.lpMember ⊤ f := by
    exact memLp_top_finset_linear_combination s c
      (fun y hy ↦
        MultipleKhintchineKronecker.eigenvector_memLp_top
          M hM y (hs y hy))
  exact ⟨hfH, hftop⟩

lemma indicator_mul_mem
    (M : System.{u}) (hM : IsErgodic M)
    {A B : Set M.X}
    (hA : AlgebraSubSigma.indicatorOne A ∈
      forwardAlmostPeriodicFunctions M hM)
    (hB : AlgebraSubSigma.indicatorOne B ∈
      forwardAlmostPeriodicFunctions M hM) :
    (fun x ↦ AlgebraSubSigma.indicatorOne A x *
      AlgebraSubSigma.indicatorOne B x) ∈
        forwardAlmostPeriodicFunctions M hM := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  let fA := AlgebraSubSigma.indicatorOne A
  have hAtopRaw : M.lpMember ⊤ fA := by
    apply MeasureTheory.MemLp.of_bound hA.1.1 1
    filter_upwards [] with x
    by_cases hx : x ∈ A <;>
      simp [AlgebraSubSigma.indicatorOne, hx]
  have hAbound : ∀ᵐ x ∂M.μ, ‖fA x‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    by_cases hxA : x ∈ A <;>
      simp [fA, AlgebraSubSigma.indicatorOne, hxA]
  exact bounded_mul_mem M hM hA hB hAtopRaw 1 (by norm_num) hAbound

/-- Forward almost-periodicity is preserved by one Koopman step, without
requiring invertibility of the transformation. -/
lemma koopman_mem
    (M : System.{u}) (hM : IsErgodic M)
    {f : M.X → ℂ}
    (hf : f ∈ forwardAlmostPeriodicFunctions M hM) :
    (fun x ↦ f (M.T x)) ∈ forwardAlmostPeriodicFunctions M hM := by
  let D := MultipleKhintchineKronecker.koopmanData M hM.1
  have hcomp2 : M.lpMember 2 (fun x ↦ f (M.T x)) :=
    hf.1.comp_measurePreserving hM.1.2
  refine ⟨hcomp2, ?_⟩
  intro hcomp
  have hmap :
      IsAlmostPeriodicVector D (D.U (hf.1.toLp f)) :=
    (AlmostPeriodic.almostPeriodic_iff_map D (hf.1.toLp f)).mp
      (hf.2 hf.1)
  have hcanonical :
      D.U (hf.1.toLp f) =
        hcomp2.toLp (fun x ↦ f (M.T x)) := by
    exact MultipleKhintchineKronecker.koopmanData_apply_toLp
      M hM.1 f hf.1
  have hproof :
      hcomp.toLp (fun x ↦ f (M.T x)) =
        hcomp2.toLp (fun x ↦ f (M.T x)) := by
    apply MeasureTheory.Lp.ext
    exact hcomp.coeFn_toLp.trans hcomp2.coeFn_toLp.symm
  rwa [hproof, ← hcanonical]

/-- The forward Kronecker set family consists exactly of measurable sets whose
indicators are forward almost-periodic Koopman vectors. -/
def forwardKroneckerSets
    (M : System.{u}) (hM : IsErgodic M) : SetFamily M.X :=
  AlgebraSubSigma.indicatorFamily M
    (forwardAlmostPeriodicFunctions M hM)

theorem forwardKroneckerSets_isSigmaAlgebra
    (M : System.{u}) (hM : IsErgodic M) :
    Chapter00.IsSigmaAlgebraFamily (forwardKroneckerSets M hM) := by
  exact AlgebraSubSigma.indicatorFamily_isSigmaAlgebra_of_indicator_mul
    M (forwardAlmostPeriodicFunctions M hM) hM.1
    (forwardAlmostPeriodicFunctions_isClosedL2 M hM)
    (constantOne_mem M hM)
    (fun hA hB ↦ indicator_mul_mem M hM hA hB)

/-- The forward Kronecker set family is closed under transformation
preimages.  Only the forward direction is used, so no invertibility enters. -/
lemma forwardKroneckerSets_preimage
    (M : System.{u}) (hM : IsErgodic M)
    {A : Set M.X} (hA : A ∈ forwardKroneckerSets M hM) :
    M.T ⁻¹' A ∈ forwardKroneckerSets M hM := by
  refine ⟨hA.1.preimage hM.1.2.measurable, ?_⟩
  have hkoop := koopman_mem M hM hA.2
  convert hkoop using 1

/-- Every essentially bounded forward almost-periodic representative is
measurable, up to a.e. equality, for the forward Kronecker σ-algebra. -/
theorem bounded_member_has_forwardKronecker_measurable_representative
    (M : System.{u}) (hM : IsErgodic M)
    {f : M.X → ℂ}
    (hf : f ∈ forwardAlmostPeriodicFunctions M hM)
    (hftop : M.lpMember ⊤ f) :
    HasMeasurableRepresentativeForFamily
      M (forwardKroneckerSets M hM) f := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  let H := forwardAlmostPeriodicFunctions M hM
  obtain ⟨g, C, hgmeas, hfg, hgbound, hgH⟩ :=
    AlgebraSubSigma.exists_bounded_measurable_representative_of_memLp_top
      M H (forwardAlmostPeriodicFunctions_isClosedL2 M hM) hf hftop
  have hreH : (fun x ↦ ((g x).re : ℂ)) ∈ H :=
    AlgebraSubSigma.real_part_mem M H
      (forwardAlmostPeriodicFunctions_isClosedL2 M hM)
      (fun _ h ↦ star_mem M hM h) hgH
  have himH : (fun x ↦ ((g x).im : ℂ)) ∈ H :=
    AlgebraSubSigma.imag_part_mem M H
      (forwardAlmostPeriodicFunctions_isClosedL2 M hM)
      (fun _ h ↦ star_mem M hM h) hgH
  have hreBound : ∀ x, (g x).re ∈ Set.Icc (-|C|) |C| := by
    intro x
    have hx : |(g x).re| ≤ |C| :=
      (RCLike.abs_re_le_norm (g x)).trans
        ((hgbound x).trans (le_abs_self C))
    exact abs_le.mp hx
  have himBound : ∀ x, (g x).im ∈ Set.Icc (-|C|) |C| := by
    intro x
    have hx : |(g x).im| ≤ |C| :=
      (RCLike.abs_im_le_norm (g x)).trans
        ((hgbound x).trans (le_abs_self C))
    exact abs_le.mp hx
  have hreTop : M.lpMember ⊤ (fun x ↦ ((g x).re : ℂ)) := by
    apply MemLp.of_bound
      (Complex.continuous_ofReal.measurable.comp hgmeas.re).aestronglyMeasurable
      |C|
    filter_upwards [] with x
    simpa [Complex.norm_real, Real.norm_eq_abs] using
      (abs_le.mpr (hreBound x))
  have himTop : M.lpMember ⊤ (fun x ↦ ((g x).im : ℂ)) := by
    apply MemLp.of_bound
      (Complex.continuous_ofReal.measurable.comp hgmeas.im).aestronglyMeasurable
      |C|
    filter_upwards [] with x
    simpa [Complex.norm_real, Real.norm_eq_abs] using
      (abs_le.mpr (himBound x))
  let mK : MeasurableSpace M.X :=
    MeasurableSpace.generateFrom (forwardKroneckerSets M hM)
  have hreK : @Measurable M.X ℝ mK inferInstance (fun x ↦ (g x).re) := by
    apply measurable_of_Ioi
    intro c
    apply MeasurableSpace.measurableSet_generateFrom
    exact ⟨hgmeas.re measurableSet_Ioi,
      upper_level_indicator_mem_bounded M hM hgmeas.re hreH hreTop
        (-|C|) |C| hreBound c⟩
  have himK : @Measurable M.X ℝ mK inferInstance (fun x ↦ (g x).im) := by
    apply measurable_of_Ioi
    intro c
    apply MeasurableSpace.measurableSet_generateFrom
    exact ⟨hgmeas.im measurableSet_Ioi,
      upper_level_indicator_mem_bounded M hM hgmeas.im himH himTop
        (-|C|) |C| himBound c⟩
  refine ⟨g, ?_, hfg⟩
  have hreC : @Measurable M.X ℂ mK inferInstance
      (fun x ↦ ((g x).re : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hreK
  have himC : @Measurable M.X ℂ mK inferInstance
      (fun x ↦ ((g x).im : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp himK
  have hrec : @Measurable M.X ℂ mK inferInstance
      (fun x ↦ ((g x).re : ℂ) + Complex.I * ((g x).im : ℂ)) :=
    hreC.add (measurable_const.mul himC)
  convert hrec using 1
  funext x
  apply Complex.ext <;> simp

/-- The reverse half of the forward Kronecker `L²` identification: every
forward almost-periodic vector has a representative measurable for the
σ-algebra generated by forward-AP indicators. -/
theorem member_has_forwardKronecker_measurable_representative
    (M : System.{u}) (hM : IsErgodic M)
    {f : M.X → ℂ}
    (hf : f ∈ forwardAlmostPeriodicFunctions M hM) :
    HasMeasurableRepresentativeForFamily
      M (forwardKroneckerSets M hM) f := by
  let F : MeasureTheory.Lp ℂ 2 M.μ := hf.1.toLp f
  have hU : ∀ X : MeasureTheory.Lp ℂ 2 M.μ,
      ‖(MultipleKhintchineKronecker.koopmanData M hM.1).U X‖ = ‖X‖ :=
    fun X ↦
      (MeasureTheory.Lp.compMeasurePreservingₗᵢ
        ℂ M.T hM.1.2).norm_map X
  have hdisc : InDiscreteSpectralSubspace
      (MultipleKhintchineKronecker.koopmanData M hM.1) F :=
    AlmostPeriodicIsometry.almostPeriodic_implies_discrete
      (MultipleKhintchineKronecker.koopmanData M hM.1)
      hU F (hf.2 hf.1)
  have hdisc' : ∀ ε : ℝ, 0 < ε →
      ∃ s : Finset (MeasureTheory.Lp ℂ 2 M.μ),
        (∀ y ∈ s, IsEigenvector
          (MultipleKhintchineKronecker.koopmanData M hM.1) y) ∧
        ∃ c : MeasureTheory.Lp ℂ 2 M.μ → ℂ,
          ‖F - ∑ y ∈ s, c y • y‖ < ε :=
    hdisc
  choose s hs c happ using fun n : ℕ ↦
    hdisc' ((1 : ℝ) / (n + 1)) (by positivity)
  let Y : ℕ → MeasureTheory.Lp ℂ 2 M.μ :=
    fun n ↦ ∑ y ∈ s n, c n y • y
  let fn : ℕ → M.X → ℂ :=
    fun n x ↦ ∑ y ∈ s n, c n y * y x
  have hfnData : ∀ n,
      fn n ∈ forwardAlmostPeriodicFunctions M hM ∧
        M.lpMember ⊤ (fn n) := by
    intro n
    exact finiteEigenCombination_function_mem_top M hM
      (s n) (hs n) (c n)
  have hfnY : ∀ n, (fun x ↦ Y n x) =ᵐ[M.μ] fn n :=
    fun n ↦ coe_finset_linear_combination_ae (s n) (c n)
  have hfn2 : ∀ n, M.lpMember 2 (fn n) :=
    fun n ↦ (hfnData n).1.1
  have hfnK : ∀ n,
      HasMeasurableRepresentativeForFamily
        M (forwardKroneckerSets M hM) (fn n) :=
    fun n ↦
      bounded_member_has_forwardKronecker_measurable_representative
        M hM (hfnData n).1 (hfnData n).2
  have hYF : Tendsto Y atTop (nhds F) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (g := fun n : ℕ ↦ (1 : ℝ) / (n + 1))
    · exact Eventually.of_forall fun n ↦ norm_nonneg _
    · filter_upwards [] with n
      calc
        ‖Y n - F‖ = ‖F - Y n‖ := norm_sub_rev _ _
        _ ≤ (1 : ℝ) / (n + 1) := (happ n).le
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hnorm : Tendsto (fun n ↦ ‖Y n - F‖) atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hYF
  have hreal : Tendsto
      (fun n ↦
        (eLpNorm (fun x ↦ fn n x - f x) 2 M.μ).toReal)
      atTop (nhds 0) := by
    convert hnorm using 1
    funext n
    have hto : (hfn2 n).toLp (fn n) = Y n := by
      apply MeasureTheory.Lp.ext
      filter_upwards [(hfn2 n).coeFn_toLp, hfnY n] with x hraw hY
      rw [hraw, ← hY]
    let hsub : M.lpMember 2 (fn n - f) := (hfn2 n).sub hf.1
    calc
      (eLpNorm (fn n - f) 2 M.μ).toReal =
          ‖hsub.toLp (fn n - f)‖ :=
        (MeasureTheory.Lp.norm_toLp _ hsub).symm
      _ = ‖(hfn2 n).toLp (fn n) - hf.1.toLp f‖ := by
        rw [MeasureTheory.MemLp.toLp_sub]
      _ = ‖Y n - F‖ := by rw [hto]
  have hconv : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ fn n x - f x) 2 M.μ)
      atTop (nhds 0) := by
    apply (ENNReal.tendsto_toReal_zero_iff
      (fun n ↦ ne_of_lt ((hfn2 n).sub hf.1).2)).mp
    exact hreal
  exact AlgebraSubSigma.hasMeasurableRepresentativeForFamily_closed
    M (forwardKroneckerSets M hM) fn hfn2 hfnK f hf.1 hconv

/-- The easy half of the forward Kronecker `L²` identification: every
square-integrable function measurable for the indicator σ-algebra is an
almost-periodic Koopman vector. -/
theorem mem_of_forwardKronecker_measurable
    (M : System.{u}) (hM : IsErgodic M)
    {f : M.X → ℂ} (hf2 : M.lpMember 2 f)
    (hfmeas : HasMeasurableRepresentativeForFamily
      M (forwardKroneckerSets M hM) f) :
    f ∈ forwardAlmostPeriodicFunctions M hM := by
  exact
    AlgebraSubSigma.mem_of_indicatorFamily_measurable_representative_of_indicator_mul
        M (forwardAlmostPeriodicFunctions M hM) hM.1
        (forwardAlmostPeriodicFunctions_isClosedL2 M hM)
        (constantOne_mem M hM)
        (fun hA hB ↦ indicator_mul_mem M hM hA hB)
        hf2 hfmeas

/-- Exact `L²` identification of the forward Kronecker σ-algebra: a
square-integrable function is a forward almost-periodic Koopman vector if
and only if it has a representative measurable for the σ-algebra generated
by forward almost-periodic indicators. -/
theorem forwardAlmostPeriodic_iff_measurable
    (M : System.{u}) (hM : IsErgodic M)
    {f : M.X → ℂ} :
    f ∈ forwardAlmostPeriodicFunctions M hM ↔
      M.lpMember 2 f ∧
        HasMeasurableRepresentativeForFamily
          M (forwardKroneckerSets M hM) f := by
  constructor
  · intro hf
    exact
      ⟨hf.1,
        member_has_forwardKronecker_measurable_representative M hM hf⟩
  · rintro ⟨hf2, hfmeas⟩
    exact mem_of_forwardKronecker_measurable M hM hf2 hfmeas

/-- The measurable space generated by the forward Kronecker set family. -/
def forwardKroneckerMeasurableSpace
    (M : System.{u}) (hM : IsErgodic M) : MeasurableSpace M.X :=
  MeasurableSpace.generateFrom (forwardKroneckerSets M hM)

lemma forwardKroneckerMeasurableSpace_le
    (M : System.{u}) (hM : IsErgodic M) :
    forwardKroneckerMeasurableSpace M hM ≤ M.measurableSpace := by
  apply MeasurableSpace.generateFrom_le
  intro A hA
  exact hA.1

/-- The system transformation is measurable on the forward Kronecker
measurable space. -/
lemma measurable_forwardKronecker
    (M : System.{u}) (hM : IsErgodic M) :
    @Measurable M.X M.X
      (forwardKroneckerMeasurableSpace M hM)
      (forwardKroneckerMeasurableSpace M hM) M.T := by
  let mK := forwardKroneckerMeasurableSpace M hM
  change @Measurable M.X M.X mK mK M.T
  letI : MeasurableSpace M.X := mK
  apply measurable_generateFrom
  intro A hA
  exact MeasurableSpace.measurableSet_generateFrom
    (forwardKroneckerSets_preimage M hM hA)

/-- The conditional expectation of an indicator onto the forward Kronecker
space takes values in `[0,1]` almost everywhere. -/
lemma condExp_indicator_mem_Icc
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    ∀ᵐ x ∂M.μ,
      MeasureTheory.condExp
          (forwardKroneckerMeasurableSpace M hM) M.μ
          (A.indicator fun _ ↦ (1 : ℝ)) x ∈ Set.Icc (0 : ℝ) 1 := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  let f : M.X → ℝ := A.indicator fun _ ↦ 1
  have hfnonneg : (0 : M.X → ℝ) ≤ᵐ[M.μ] f := by
    filter_upwards [] with x
    by_cases hx : x ∈ A <;> simp [f, hx]
  have hfupper : f ≤ᵐ[M.μ] (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [] with x
    by_cases hx : x ∈ A <;> simp [f, hx]
  have hfint : MeasureTheory.Integrable f M.μ := by
    exact (MeasureTheory.integrable_const (1 : ℝ)).indicator hA
  have hnonneg :
      (0 : M.X → ℝ) ≤ᵐ[M.μ]
        MeasureTheory.condExp
          (forwardKroneckerMeasurableSpace M hM) M.μ f :=
    MeasureTheory.condExp_nonneg hfnonneg
  have hupper :
      MeasureTheory.condExp
          (forwardKroneckerMeasurableSpace M hM) M.μ f ≤ᵐ[M.μ]
        (fun _ ↦ (1 : ℝ)) := by
    have hmono := MeasureTheory.condExp_mono
      (m := forwardKroneckerMeasurableSpace M hM)
      hfint (MeasureTheory.integrable_const (1 : ℝ)) hfupper
    have hconst :=
      MeasureTheory.condExp_const
        (μ := M.μ)
        (forwardKroneckerMeasurableSpace_le M hM) (1 : ℝ)
    exact hmono.trans_eq
      (Eventually.of_forall fun x ↦ congrFun hconst x)
  filter_upwards [hnonneg, hupper] with x hx0 hx1
  exact ⟨hx0, hx1⟩

/-- The forward-Kronecker conditional expectation of an indicator preserves
its integral, hence its mean is the original set measure. -/
lemma integral_condExp_indicator
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    ∫ x,
        MeasureTheory.condExp
          (forwardKroneckerMeasurableSpace M hM) M.μ
          (A.indicator fun _ ↦ (1 : ℝ)) x ∂M.μ =
      realMeasure M A := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  let f : M.X → ℝ := A.indicator fun _ ↦ 1
  have hfint : MeasureTheory.Integrable f M.μ := by
    exact (MeasureTheory.integrable_const (1 : ℝ)).indicator hA
  calc
    ∫ x,
        MeasureTheory.condExp
          (forwardKroneckerMeasurableSpace M hM) M.μ f x ∂M.μ =
        ∫ x, f x ∂M.μ :=
      MeasureTheory.integral_condExp
        (forwardKroneckerMeasurableSpace_le M hM)
    _ = realMeasure M A := by
      rw [show f = A.indicator (fun _ ↦ (1 : ℝ)) by rfl,
        MeasureTheory.integral_indicator hA]
      simp [realMeasure, MeasureTheory.Measure.real]

/-- Jensen's cubic lower bound on a probability space, in the bounded
nonnegative form needed for the compact contribution. -/
lemma cube_integral_lower_bound_of_mem_Icc
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (g : M.X → ℝ) (hgint : MeasureTheory.Integrable g M.μ)
    (hgIcc : ∀ᵐ x ∂M.μ, g x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, g x ∂M.μ) ^ 3 ≤ ∫ x, (g x) ^ 3 ∂M.μ := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  have hg3int : MeasureTheory.Integrable (fun x ↦ (g x) ^ 3) M.μ := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrable_const (1 : ℝ))
      (hgint.aestronglyMeasurable.pow 3) ?_
    filter_upwards [hgIcc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.1 3)]
    have hsq : (g x) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
    rw [show (g x) ^ 3 = (g x) ^ 2 * g x by ring]
    nlinarith [mul_nonneg (sq_nonneg (g x)) hx.1,
      mul_le_mul_of_nonneg_right hsq hx.1]
  have hjensen :=
    (convexOn_pow 3 : ConvexOn ℝ (Set.Ici 0)
      (fun t : ℝ ↦ t ^ 3)).map_integral_le
      (continuousOn_pow 3) isClosed_Ici
      (hgIcc.mono fun _ hx ↦ hx.1) hgint
      (by simpa only [Function.comp_apply] using hg3int)
  simpa only [Function.comp_apply] using hjensen

/-- The cubic moment of the forward-Kronecker conditional expectation of an
indicator is at least the cube of the original set measure. -/
lemma cube_integral_condExp_indicator_lower_bound
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    (realMeasure M A) ^ 3 ≤
      ∫ x,
        (MeasureTheory.condExp
          (forwardKroneckerMeasurableSpace M hM) M.μ
          (A.indicator fun _ ↦ (1 : ℝ)) x) ^ 3 ∂M.μ := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  let f : M.X → ℝ := A.indicator fun _ ↦ 1
  let g : M.X → ℝ :=
    MeasureTheory.condExp
      (forwardKroneckerMeasurableSpace M hM) M.μ f
  have hfint : MeasureTheory.Integrable f M.μ := by
    exact (MeasureTheory.integrable_const (1 : ℝ)).indicator hA
  have hgint : MeasureTheory.Integrable g M.μ :=
    MeasureTheory.integrable_condExp
  have hJ :=
    cube_integral_lower_bound_of_mem_Icc M hM.1 g hgint
      (condExp_indicator_mem_Icc M hM A hA)
  rw [integral_condExp_indicator M hM A hA] at hJ
  exact hJ

/-- The real conditional expectation of an indicator, embedded in `ℂ`, is
an essentially bounded forward almost-periodic representative. -/
lemma condExp_indicator_complex_mem
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    let g : M.X → ℂ := fun x ↦
      ((MeasureTheory.condExp
        (forwardKroneckerMeasurableSpace M hM) M.μ
        (A.indicator fun _ ↦ (1 : ℝ)) x : ℝ) : ℂ)
    g ∈ forwardAlmostPeriodicFunctions M hM ∧ M.lpMember ⊤ g := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  let mK := forwardKroneckerMeasurableSpace M hM
  let f : M.X → ℝ := A.indicator fun _ ↦ 1
  let gR : M.X → ℝ := MeasureTheory.condExp mK M.μ f
  let g : M.X → ℂ := fun x ↦ (gR x : ℂ)
  have hgRmeas : @Measurable M.X ℝ mK inferInstance gR :=
    MeasureTheory.stronglyMeasurable_condExp.measurable
  have hgmeasK : @Measurable M.X ℂ mK inferInstance g :=
    Complex.continuous_ofReal.measurable.comp hgRmeas
  have hgIcc : ∀ᵐ x ∂M.μ, gR x ∈ Set.Icc (0 : ℝ) 1 :=
    condExp_indicator_mem_Icc M hM A hA
  have hgTop : M.lpMember ⊤ g := by
    apply MeasureTheory.MemLp.of_bound
      ((hgmeasK.mono (forwardKroneckerMeasurableSpace_le M hM)
        le_rfl).aestronglyMeasurable) 1
    filter_upwards [hgIcc] with x hx
    simpa [g, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hx.1] using hx.2
  have hg2 : M.lpMember 2 g :=
    hgTop.mono_exponent (by norm_num)
  have hgrep :
      HasMeasurableRepresentativeForFamily
        M (forwardKroneckerSets M hM) g :=
    ⟨g, hgmeasK, EventuallyEq.rfl⟩
  have hgmem : g ∈ forwardAlmostPeriodicFunctions M hM :=
    (forwardAlmostPeriodic_iff_measurable M hM (f := g)).2
      ⟨hg2, hgrep⟩
  simpa only [g, gR, f, mK] using And.intro hgmem hgTop

/-- Canonical complex representative of the forward-Kronecker conditional
expectation of an indicator. -/
noncomputable def forwardKroneckerIndicator
    (M : System.{u}) (hM : IsErgodic M) (A : Set M.X) : M.X → ℂ :=
  fun x ↦
    ((MeasureTheory.condExp
      (forwardKroneckerMeasurableSpace M hM) M.μ
      (A.indicator fun _ ↦ (1 : ℝ)) x : ℝ) : ℂ)

lemma forwardKroneckerIndicator_mem
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    forwardKroneckerIndicator M hM A ∈
        forwardAlmostPeriodicFunctions M hM ∧
      M.lpMember ⊤ (forwardKroneckerIndicator M hM A) := by
  simpa only [forwardKroneckerIndicator] using
    condExp_indicator_complex_mem M hM A hA

/-- `L²` vector represented by the forward-Kronecker conditional expectation
of an indicator. -/
noncomputable def forwardKroneckerIndicatorLp
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    MeasureTheory.Lp ℂ 2 M.μ :=
  ((forwardKroneckerIndicator_mem M hM A hA).1.1).toLp
    (forwardKroneckerIndicator M hM A)

/-- An everywhere `[0,1]`-valued representative of the real forward
Kronecker conditional expectation, embedded in `ℂ`.  The clipping changes
the raw conditional expectation only on a null set. -/
noncomputable def forwardKroneckerIndicatorClipped
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) : M.X → ℂ :=
  fun x ↦
    ((min 1 (max 0
      (MeasureTheory.condExp
        (forwardKroneckerMeasurableSpace M hM) M.μ
        (A.indicator fun _ ↦ (1 : ℝ)) x)) : ℝ) : ℂ)

lemma forwardKroneckerIndicator_ae_clipped
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    forwardKroneckerIndicator M hM A =ᵐ[M.μ]
      forwardKroneckerIndicatorClipped M hM A := by
  filter_upwards [condExp_indicator_mem_Icc M hM A hA] with x hx
  simp only [forwardKroneckerIndicator, forwardKroneckerIndicatorClipped]
  rw [max_eq_right hx.1, min_eq_right hx.2]

lemma forwardKroneckerIndicatorClipped_norm_le_one
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (x : M.X) :
    ‖forwardKroneckerIndicatorClipped M hM A x‖ ≤ 1 := by
  rw [forwardKroneckerIndicatorClipped, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg]
  · exact min_le_left _ _
  · exact le_min (by norm_num) (le_max_left _ _)

lemma forwardKroneckerIndicatorLp_coe_clipped
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    (fun x ↦ forwardKroneckerIndicatorLp M hM A hA x) =ᵐ[M.μ]
      forwardKroneckerIndicatorClipped M hM A := by
  exact
    ((forwardKroneckerIndicator_mem M hM A hA).1.1.coeFn_toLp).trans
      (forwardKroneckerIndicator_ae_clipped M hM A hA)

lemma forwardKroneckerIndicatorLp_iterate_coe_clipped
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) :
    (fun x ↦
      (show MeasureTheory.Lp ℂ 2 M.μ from
        ((MultipleKhintchineKronecker.koopmanData M hM.1).U^[n])
          (forwardKroneckerIndicatorLp M hM A hA)) x) =ᵐ[M.μ]
      (fun x ↦ forwardKroneckerIndicatorClipped M hM A ((M.T^[n]) x)) := by
  refine
    (MultipleKhintchineKronecker.koopmanData_iter_ae M hM.1 n
      (forwardKroneckerIndicatorLp M hM A hA)).trans ?_
  simpa only [Function.comp_apply] using
    (hM.1.2.iterate n).quasiMeasurePreserving.ae_eq
      (forwardKroneckerIndicatorLp_coe_clipped M hM A hA)

lemma forwardKroneckerIndicatorLp_iterate_norm_le_one
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) :
    ∀ᵐ x ∂M.μ,
      ‖(show MeasureTheory.Lp ℂ 2 M.μ from
        ((MultipleKhintchineKronecker.koopmanData M hM.1).U^[n])
          (forwardKroneckerIndicatorLp M hM A hA)) x‖ ≤ 1 := by
  filter_upwards [
    forwardKroneckerIndicatorLp_iterate_coe_clipped M hM A hA n]
      with x hx
  rw [hx]
  exact forwardKroneckerIndicatorClipped_norm_le_one M hM A _

lemma forwardKroneckerIndicatorLp_iterate_mem_top
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) :
    M.lpMember ⊤
      (fun x ↦
        (show MeasureTheory.Lp ℂ 2 M.μ from
          ((MultipleKhintchineKronecker.koopmanData M hM.1).U^[n])
            (forwardKroneckerIndicatorLp M hM A hA)) x) := by
  exact MeasureTheory.memLp_top_of_bound
    (MeasureTheory.Lp.memLp
      (show MeasureTheory.Lp ℂ 2 M.μ from
        ((MultipleKhintchineKronecker.koopmanData M hM.1).U^[n])
          (forwardKroneckerIndicatorLp M hM A hA))).1
    1
    (forwardKroneckerIndicatorLp_iterate_norm_le_one M hM A hA n)

/-- The self triple-product inner product of the compact indicator vector is
exactly the cubic moment of its real conditional expectation. -/
lemma re_inner_forwardKroneckerIndicatorLp_self_eq_cube_integral
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    let G := forwardKroneckerIndicatorLp M hM A hA
    let hGtop : M.lpMember ⊤ (fun x ↦ G x) :=
      MeasureTheory.memLp_top_of_bound
        (MeasureTheory.Lp.memLp G).1 1
        (by
          filter_upwards [
            forwardKroneckerIndicatorLp_coe_clipped M hM A hA]
              with x hx
          rw [hx]
          exact forwardKroneckerIndicatorClipped_norm_le_one M hM A x)
    (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
      G (MultipleKhintchineKronecker.lpPointwiseMul G G hGtop)).re =
      ∫ x,
        (MeasureTheory.condExp
          (forwardKroneckerMeasurableSpace M hM) M.μ
          (A.indicator fun _ ↦ (1 : ℝ)) x) ^ 3 ∂M.μ := by
  dsimp only
  let G := forwardKroneckerIndicatorLp M hM A hA
  have hGcoe :
      (fun x ↦ G x) =ᵐ[M.μ] forwardKroneckerIndicator M hM A := by
    exact (forwardKroneckerIndicator_mem M hM A hA).1.1.coeFn_toLp
  have hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ (1 : ℝ) := by
    filter_upwards [
      forwardKroneckerIndicatorLp_coe_clipped M hM A hA] with x hx
    rw [hx]
    exact forwardKroneckerIndicatorClipped_norm_le_one M hM A x
  let hGtop : M.lpMember ⊤ (fun x ↦ G x) :=
    MeasureTheory.memLp_top_of_bound
      (MeasureTheory.Lp.memLp G).1 1 hGbound
  have hprod :=
    MultipleKhintchineKronecker.lpPointwiseMul_coe G G hGtop
  rw [MeasureTheory.L2.inner_def]
  have hpoint :
      (fun x ↦
        @inner ℂ ℂ _ (G x)
          (MultipleKhintchineKronecker.lpPointwiseMul G G hGtop x)) =ᵐ[M.μ]
        (fun x ↦
          (((MeasureTheory.condExp
            (forwardKroneckerMeasurableSpace M hM) M.μ
            (A.indicator fun _ ↦ (1 : ℝ)) x) ^ 3 : ℝ) : ℂ)) := by
    filter_upwards [hGcoe, hprod] with x hxG hxprod
    simp only [forwardKroneckerIndicator] at hxG
    rw [hxprod, hxG]
    simp [RCLike.inner_apply]
    ring
  rw [MeasureTheory.integral_congr_ae hpoint,
    integral_complex_ofReal]
  rfl

lemma forwardKroneckerIndicatorLp_almostPeriodic
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    IsAlmostPeriodicVector
      (MultipleKhintchineKronecker.koopmanData M hM.1)
      (forwardKroneckerIndicatorLp M hM A hA) := by
  exact (forwardKroneckerIndicator_mem M hM A hA).1.2
    ((forwardKroneckerIndicator_mem M hM A hA).1.1)

/-- The compact conditional-expectation vector has syndetically many
simultaneous returns along every prescribed finite progression. -/
lemma forwardKroneckerIndicator_progression_returns_syndetic
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (ℓ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    IsSyndetic {n : ℕ |
      ∀ r : ℕ, 0 < r → r ≤ ℓ →
        ‖(show MeasureTheory.Lp ℂ 2 M.μ from
            ((MultipleKhintchineKronecker.koopmanData M hM.1).U^[r * n])
              (forwardKroneckerIndicatorLp M hM A hA)) -
          forwardKroneckerIndicatorLp M hM A hA‖ <
        (r : ℝ) * ε} := by
  exact
    AlmostPeriodicIsometry.almostPeriodic_progression_returns_syndetic
      (MultipleKhintchineKronecker.koopmanData M hM.1)
      (fun G ↦
        (MeasureTheory.Lp.compMeasurePreservingₗᵢ
          ℂ M.T hM.1.2).norm_map G)
      (forwardKroneckerIndicatorLp M hM A hA)
      (forwardKroneckerIndicatorLp_almostPeriodic M hM A hA)
      ℓ ε hε

/-- Triple correlation of the forward-Kronecker component, expressed in the
`L²` model. -/
noncomputable def forwardKroneckerTripleCorrelation
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) : ℝ :=
  let G := forwardKroneckerIndicatorLp M hM A hA
  let F : MeasureTheory.Lp ℂ 2 M.μ :=
    ((MultipleKhintchineKronecker.koopmanData M hM.1).U^[n]) G
  let H : MeasureTheory.Lp ℂ 2 M.μ :=
    ((MultipleKhintchineKronecker.koopmanData M hM.1).U^[2 * n]) G
  let hFtop : M.lpMember ⊤ (fun x ↦ F x) :=
    forwardKroneckerIndicatorLp_iterate_mem_top M hM A hA n
  (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
    G (MultipleKhintchineKronecker.lpPointwiseMul F H hFtop)).re

/-- The compact (forward-Kronecker) triple correlation exceeds the cubic
Khintchine threshold at syndetically many times. -/
theorem forwardKroneckerTripleCorrelation_syndetic
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (ε : ℝ) (hε : 0 < ε) :
    IsSyndetic {n : ℕ |
      forwardKroneckerTripleCorrelation M hM A hA n >
        (realMeasure M A) ^ 3 - ε} := by
  let G := forwardKroneckerIndicatorLp M hM A hA
  let C : ℝ := ‖G‖ + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let δ : ℝ := ε / (6 * C)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨N, hN, hret⟩ :=
    forwardKroneckerIndicator_progression_returns_syndetic
      M hM A hA 2 δ hδ
  refine ⟨N, hN, ?_⟩
  intro i
  obtain ⟨n, hn, hin, hnlt⟩ := hret i
  refine ⟨n, ?_, hin, hnlt⟩
  let F : MeasureTheory.Lp ℂ 2 M.μ :=
    ((MultipleKhintchineKronecker.koopmanData M hM.1).U^[n]) G
  let H : MeasureTheory.Lp ℂ 2 M.μ :=
    ((MultipleKhintchineKronecker.koopmanData M hM.1).U^[2 * n]) G
  have hFclose : ‖F - G‖ < δ := by
    simpa only [F, G, one_mul, Nat.cast_one] using
      hn 1 (by omega) (by omega)
  have hHclose : ‖H - G‖ < 2 * δ := by
    simpa only [H, G, Nat.cast_ofNat] using
      hn 2 (by omega) (by omega)
  have hsum : ‖H - G‖ + ‖F - G‖ < 3 * δ := by
    linarith
  have hsum_nonneg : 0 ≤ ‖H - G‖ + ‖F - G‖ := by positivity
  have hG_le_C : ‖G‖ ≤ C := by
    dsimp [C]
    linarith
  have herror :
      ‖G‖ * (‖H - G‖ + ‖F - G‖) < ε := by
    calc
      ‖G‖ * (‖H - G‖ + ‖F - G‖) ≤
          C * (‖H - G‖ + ‖F - G‖) :=
        mul_le_mul_of_nonneg_right hG_le_C hsum_nonneg
      _ < C * (3 * δ) :=
        mul_lt_mul_of_pos_left hsum hC
      _ = ε / 2 := by
        dsimp [δ]
        field_simp
        ring
      _ < ε := by linarith
  have hFtop : M.lpMember ⊤ (fun x ↦ F x) := by
    exact forwardKroneckerIndicatorLp_iterate_mem_top M hM A hA n
  have hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ (1 : ℝ) := by
    filter_upwards [
      forwardKroneckerIndicatorLp_coe_clipped M hM A hA] with x hx
    rw [show G x = forwardKroneckerIndicatorClipped M hM A x by
      simpa only [G] using hx]
    exact forwardKroneckerIndicatorClipped_norm_le_one M hM A x
  have hGtop : M.lpMember ⊤ (fun x ↦ G x) :=
    MeasureTheory.memLp_top_of_bound
      (MeasureTheory.Lp.memLp G).1 1 hGbound
  have hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ (1 : ℝ) := by
    simpa only [F, G] using
      forwardKroneckerIndicatorLp_iterate_norm_le_one M hM A hA n
  have hpert :=
    MultipleKhintchineKronecker.abs_re_inner_lpPointwiseMul_sub_self_le
      F G H hFtop hGtop hFbound hGbound
  have hpert_lt :
      |(@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          G (MultipleKhintchineKronecker.lpPointwiseMul F H hFtop)).re -
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          G (MultipleKhintchineKronecker.lpPointwiseMul G G hGtop)).re| <
        ε :=
    lt_of_le_of_lt hpert herror
  have hbase :
      (realMeasure M A) ^ 3 ≤
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          G (MultipleKhintchineKronecker.lpPointwiseMul G G hGtop)).re := by
    rw [re_inner_forwardKroneckerIndicatorLp_self_eq_cube_integral
      M hM A hA]
    exact cube_integral_condExp_indicator_lower_bound M hM A hA
  have hcompact :
      (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        G (MultipleKhintchineKronecker.lpPointwiseMul F H hFtop)).re >
        (realMeasure M A) ^ 3 - ε := by
    have hlower := (abs_lt.mp hpert_lt).1
    linarith
  simpa only [forwardKroneckerTripleCorrelation, G, F, H] using hcompact

/-- Hilbert-space form of the exact Kronecker identification: the closed
almost-periodic submodule is precisely the `L²` submodule measurable for the
forward Kronecker measurable space. -/
theorem almostPeriodicSubmodule_eq_lpMeas
    (M : System.{u}) (hM : IsErgodic M) :
    AlmostPeriodicIsometry.almostPeriodicSubmodule
        (MultipleKhintchineKronecker.koopmanData M hM.1) =
      MeasureTheory.lpMeas ℂ ℂ
        (forwardKroneckerMeasurableSpace M hM) 2 M.μ := by
  apply Submodule.ext
  intro (F : MeasureTheory.Lp ℂ 2 M.μ)
  constructor
  · intro hF
    rw [MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable]
    have hraw : (⇑F) ∈ forwardAlmostPeriodicFunctions M hM := by
      refine ⟨MeasureTheory.Lp.memLp F, ?_⟩
      intro hf
      have hto : hf.toLp (⇑F) = F := by
        apply MeasureTheory.Lp.ext
        exact hf.coeFn_toLp
      rwa [hto]
    obtain ⟨g, hgmeas, hFg⟩ :=
      member_has_forwardKronecker_measurable_representative M hM hraw
    exact hgmeas.aestronglyMeasurable.congr hFg.symm
  · intro hF
    rw [MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable] at hF
    have hrep :
        HasMeasurableRepresentativeForFamily
          M (forwardKroneckerSets M hM) (⇑F) := by
      refine ⟨hF.mk (⇑F), hF.measurable_mk, hF.ae_eq_mk⟩
    have hraw : (⇑F) ∈ forwardAlmostPeriodicFunctions M hM :=
      (forwardAlmostPeriodic_iff_measurable M hM).2
        ⟨MeasureTheory.Lp.memLp F, hrep⟩
    have hap := hraw.2 (MeasureTheory.Lp.memLp F)
    have hto :
        (MeasureTheory.Lp.memLp F).toLp (⇑F) = F := by
      apply MeasureTheory.Lp.ext
      exact (MeasureTheory.Lp.memLp F).coeFn_toLp
    rwa [hto] at hap

set_option synthInstance.maxHeartbeats 200000 in
/-- The orthogonal almost-periodic projection is exactly conditional
expectation onto the forward Kronecker measurable space. -/
theorem almostPeriodicProjection_eq_condExpL2
    (M : System.{u}) (hM : IsErgodic M)
    (F : MeasureTheory.Lp ℂ 2 M.μ) :
    AlmostPeriodicIsometry.almostPeriodicProjection
        (MultipleKhintchineKronecker.koopmanData M hM.1)
        (fun G ↦
          (MeasureTheory.Lp.compMeasurePreservingₗᵢ
            ℂ M.T hM.1.2).norm_map G)
        F =
      ((MeasureTheory.condExpL2
          (m := forwardKroneckerMeasurableSpace M hM)
          (m0 := M.measurableSpace) (μ := M.μ) ℂ ℂ
          (forwardKroneckerMeasurableSpace_le M hM)) F :
        MeasureTheory.Lp ℂ 2 M.μ) := by
  let S :=
    AlmostPeriodicIsometry.almostPeriodicSubmodule
      (MultipleKhintchineKronecker.koopmanData M hM.1)
  let K :=
    MeasureTheory.lpMeas ℂ ℂ
      (forwardKroneckerMeasurableSpace M hM) 2 M.μ
  have hSK : S = K := almostPeriodicSubmodule_eq_lpMeas M hM
  letI : Fact
      (forwardKroneckerMeasurableSpace M hM ≤ M.measurableSpace) :=
    ⟨forwardKroneckerMeasurableSpace_le M hM⟩
  letI : CompleteSpace S :=
    (AlmostPeriodicIsometry.almostPeriodic_closed
      (MultipleKhintchineKronecker.koopmanData M hM.1)
      (fun G ↦
        (MeasureTheory.Lp.compMeasurePreservingₗᵢ
          ℂ M.T hM.1.2).norm_map G)).completeSpace_coe
  letI : S.HasOrthogonalProjection := inferInstance
  letI : CompleteSpace K := inferInstance
  letI : K.HasOrthogonalProjection := inferInstance
  rw [MeasureTheory.condExpL2]
  change S.starProjection F = K.starProjection F
  apply S.eq_starProjection_of_mem_orthogonal
  · rw [hSK]
    exact K.starProjection_apply_mem F
  · rw [hSK]
    exact K.sub_starProjection_mem_orthogonal F

/-- Conditional expectation onto the forward Kronecker space commutes with
one Koopman step.  This is obtained from the corresponding orthogonal
projection identity and remains valid for a noninvertible isometry. -/
theorem condExpL2_forwardKronecker_map
    (M : System.{u}) (hM : IsErgodic M)
    (F : MeasureTheory.Lp ℂ 2 M.μ) :
    ((MeasureTheory.condExpL2
        (m := forwardKroneckerMeasurableSpace M hM)
        (m0 := M.measurableSpace) (μ := M.μ) ℂ ℂ
        (forwardKroneckerMeasurableSpace_le M hM))
        ((MultipleKhintchineKronecker.koopmanData M hM.1).U F) :
      MeasureTheory.Lp ℂ 2 M.μ) =
      (MultipleKhintchineKronecker.koopmanData M hM.1).U
        ((MeasureTheory.condExpL2
            (m := forwardKroneckerMeasurableSpace M hM)
            (m0 := M.measurableSpace) (μ := M.μ) ℂ ℂ
            (forwardKroneckerMeasurableSpace_le M hM)) F :
          MeasureTheory.Lp ℂ 2 M.μ) := by
  rw [← almostPeriodicProjection_eq_condExpL2 M hM,
    ← almostPeriodicProjection_eq_condExpL2 M hM]
  exact AlmostPeriodicIsometry.almostPeriodicProjection_map
    (MultipleKhintchineKronecker.koopmanData M hM.1)
    (fun G ↦
      (MeasureTheory.Lp.compMeasurePreservingₗᵢ
        ℂ M.T hM.1.2).norm_map G)
    F

/-- Removing the forward Kronecker conditional expectation leaves a
continuous-spectral Koopman vector. -/
theorem sub_condExpL2_forwardKronecker_continuous
    (M : System.{u}) (hM : IsErgodic M)
    (F : MeasureTheory.Lp ℂ 2 M.μ) :
    InContinuousSpectralSubspace
      (MultipleKhintchineKronecker.koopmanData M hM.1)
      (F -
        ((MeasureTheory.condExpL2
            (m := forwardKroneckerMeasurableSpace M hM)
            (m0 := M.measurableSpace) (μ := M.μ) ℂ ℂ
            (forwardKroneckerMeasurableSpace_le M hM)) F :
          MeasureTheory.Lp ℂ 2 M.μ)) := by
  rw [← almostPeriodicProjection_eq_condExpL2 M hM]
  exact
    AlmostPeriodicIsometry.sub_almostPeriodicProjection_continuous
      (MultipleKhintchineKronecker.koopmanData M hM.1)
      (fun G ↦
        (MeasureTheory.Lp.compMeasurePreservingₗᵢ
          ℂ M.T hM.1.2).norm_map G)
      F

end Chapter02.ForwardKroneckerFactor
