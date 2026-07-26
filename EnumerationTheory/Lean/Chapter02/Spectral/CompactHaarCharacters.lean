import Chapter02.Common
import share.Lean.NLFirst_Pfd28c3cf0fb145e58f2b0f19d4e83368_Chapter02
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section

open Classical Filter MeasureTheory
open scoped BigOperators

namespace Chapter02.CompactHaarCharacters

universe u

variable {G : Type u} [CommGroup G] [MetricSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

abbrev Character (G : Type u) [CommGroup G] [TopologicalSpace G] :=
  ContinuousMultiplicativeCircleCharacter G

lemma haarEndomorphism_measurePreserving
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (A : G →* G) (hAcont : Continuous A) (hAsurj : Function.Surjective A) :
    MeasurePreserving A m m :=
  A.measurePreserving hAcont hAsurj (by simp)

lemma character_memLp (m : Measure G) [IsProbabilityMeasure m]
    (χ : Character G) : MemLp χ.toFun 2 m := by
  apply (memLp_top_of_bound χ.continuous.aestronglyMeasurable 1 ?_).mono_exponent
    (by simp)
  exact .of_forall fun x => le_of_eq (χ.unit_norm x)

lemma character_ne_zero_ae (m : Measure G) [m.IsHaarMeasure] (χ : Character G) :
    ¬ χ.toFun =ᵐ[m] 0 := by
  intro h
  have hfun : χ.toFun = (fun _ : G => (0 : ℂ)) :=
    Measure.eq_of_ae_eq h χ.continuous continuous_zero
  have hzero : χ.toFun 1 = 0 := congrFun hfun 1
  simpa [χ.map_one] using hzero

lemma integral_character_eq_zero_of_nontrivial
    (m : Measure G) [m.IsHaarMeasure] (χ : Character G)
    (hχ : ¬ ∀ x, χ.toFun x = 1) :
    ∫ x, χ.toFun x ∂m = 0 := by
  push_neg at hχ
  obtain ⟨g, hg⟩ := hχ
  let I : ℂ := ∫ x, χ.toFun x ∂m
  have htranslate : I = χ.toFun g * I := by
    calc
      I = ∫ x, χ.toFun (g * x) ∂m :=
        (integral_mul_left_eq_self χ.toFun g).symm
      _ = ∫ x, χ.toFun g * χ.toFun x ∂m := by
        apply integral_congr_ae
        exact .of_forall fun x => χ.map_mul g x
      _ = χ.toFun g * I := by
        exact integral_const_mul (χ.toFun g) χ.toFun
  have hprod : (χ.toFun g - 1) * I = 0 := by
    rw [sub_mul, one_mul, ← htranslate, sub_self]
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hg)

def characterConj (χ : Character G) : Character G where
  toFun x := star (χ.toFun x)
  map_one := by simp [χ.map_one]
  map_mul x y := by simp [χ.map_mul, mul_comm]
  continuous := χ.continuous.star
  unit_norm x := by simp [χ.unit_norm x]

def characterMul (χ ψ : Character G) : Character G where
  toFun x := χ.toFun x * ψ.toFun x
  map_one := by simp [χ.map_one, ψ.map_one]
  map_mul x y := by
    rw [χ.map_mul, ψ.map_mul]
    ring
  continuous := χ.continuous.mul ψ.continuous
  unit_norm x := by simp [norm_mul, χ.unit_norm x, ψ.unit_norm x]

def characterQuotient (χ ψ : Character G) : Character G :=
  characterMul (characterConj χ) ψ

private lemma star_mul_self_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    star z * z = 1 := by
  rw [Complex.star_def]
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]
  norm_num

private lemma self_mul_star_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    z * star z = 1 := by
  rw [mul_comm]
  exact star_mul_self_of_norm_eq_one hz

lemma characterQuotient_trivial_iff (χ ψ : Character G) :
    (∀ x, (characterQuotient χ ψ).toFun x = 1) ↔ χ.toFun = ψ.toFun := by
  constructor
  · intro h
    funext x
    have hx := h x
    change star (χ.toFun x) * ψ.toFun x = 1 at hx
    calc
      χ.toFun x = χ.toFun x * 1 := by simp
      _ = χ.toFun x * (star (χ.toFun x) * ψ.toFun x) := by rw [hx]
      _ = (χ.toFun x * star (χ.toFun x)) * ψ.toFun x := by ring
      _ = ψ.toFun x := by
        rw [self_mul_star_of_norm_eq_one (χ.unit_norm x), one_mul]
  · intro h x
    have hx := congrFun h x
    change star (χ.toFun x) * ψ.toFun x = 1
    rw [← hx]
    exact star_mul_self_of_norm_eq_one (χ.unit_norm x)

lemma character_orthogonal_integral
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (χ ψ : Character G) (hne : χ.toFun ≠ ψ.toFun) :
    ∫ x, star (χ.toFun x) * ψ.toFun x ∂m = 0 := by
  change ∫ x, (characterQuotient χ ψ).toFun x ∂m = 0
  apply integral_character_eq_zero_of_nontrivial m
  exact fun htriv => hne ((characterQuotient_trivial_iff χ ψ).mp htriv)

private lemma iterate_monoidHom_map_one (A : G →* G) (n : ℕ) :
    (A : G → G)^[n] 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, A.map_one, ih]

private lemma iterate_monoidHom_map_mul (A : G →* G) (n : ℕ) (x y : G) :
    (A : G → G)^[n] (x * y) =
      (A : G → G)^[n] x * (A : G → G)^[n] y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, A.map_mul]
      exact ih (A x) (A y)

def characterCompIterate (A : G →* G) (hA : Continuous A)
    (ψ : Character G) (n : ℕ) : Character G where
  toFun x := ψ.toFun ((A : G → G)^[n] x)
  map_one := by rw [iterate_monoidHom_map_one, ψ.map_one]
  map_mul x y := by rw [iterate_monoidHom_map_mul, ψ.map_mul]
  continuous := ψ.continuous.comp (hA.iterate n)
  unit_norm x := ψ.unit_norm _

lemma character_correlation_integral
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (A : G →* G) (hA : Continuous A) (χ ψ : Character G) (n : ℕ) :
    (∫ x, star (χ.toFun x) * ψ.toFun ((A : G → G)^[n] x) ∂m) =
      if χ.toFun = (characterCompIterate A hA ψ n).toFun then 1 else 0 := by
  split_ifs with h
  · have hpoint : ∀ x,
        star (χ.toFun x) * ψ.toFun ((A : G → G)^[n] x) = 1 := by
      intro x
      have hx := congrFun h x
      change χ.toFun x =
        ψ.toFun ((A : G → G)^[n] x) at hx
      rw [← hx]
      exact star_mul_self_of_norm_eq_one (χ.unit_norm x)
    calc
      (∫ x, star (χ.toFun x) *
          ψ.toFun ((A : G → G)^[n] x) ∂m) =
          ∫ _x : G, (1 : ℂ) ∂m := integral_congr_ae (.of_forall hpoint)
      _ = 1 := by simp
  · exact character_orthogonal_integral m χ (characterCompIterate A hA ψ n) h

abbrev characterLp (m : Measure G) [IsProbabilityMeasure m]
    (χ : Character G) : Lp ℂ 2 m :=
  MathCopilotPrior.compactAbelianCharacterLp m χ

lemma characterLp_coeFn (m : Measure G) [IsProbabilityMeasure m]
    (χ : Character G) :
    (fun x => characterLp m χ x) =ᵐ[m] χ.toFun := by
  unfold characterLp MathCopilotPrior.compactAbelianCharacterLp
  exact MemLp.coeFn_toLp _

lemma orthonormal_character_family
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    {ι : Type*} (χ : ι → Character G)
    (hinj : Function.Injective fun i => (χ i).toFun) :
    Orthonormal ℂ (fun i => characterLp m (χ i)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [L2.inner_def]
  have hcoe_i := characterLp_coeFn m (χ i)
  have hcoe_j := characterLp_coeFn m (χ j)
  have hintegral :
      (∫ x, @inner ℂ ℂ _ (characterLp m (χ i) x)
          (characterLp m (χ j) x) ∂m) =
        ∫ x, star ((χ i).toFun x) * (χ j).toFun x ∂m := by
    apply integral_congr_ae
    filter_upwards [hcoe_i, hcoe_j] with x hi hj
    rw [hi, hj, RCLike.inner_apply]
    simpa only [starRingEnd_apply] using
      (mul_comm ((χ j).toFun x) (star ((χ i).toFun x)))
  rw [hintegral]
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    calc
      (∫ x, star ((χ i).toFun x) * (χ i).toFun x ∂m) =
          ∫ _x : G, (1 : ℂ) ∂m := by
        apply integral_congr_ae
        exact .of_forall fun x =>
          star_mul_self_of_norm_eq_one ((χ i).unit_norm x)
      _ = 1 := by simp
  · rw [if_neg hij]
    exact character_orthogonal_integral m (χ i) (χ j)
      (fun h => hij (hinj h))

def trivialCharacter : Character G where
  toFun _ := 1
  map_one := rfl
  map_mul _ _ := by simp
  continuous := continuous_const
  unit_norm _ := by simp

lemma characterLp_eq_of_toFun_eq
    (m : Measure G) [IsProbabilityMeasure m] {χ ψ : Character G}
    (h : χ.toFun = ψ.toFun) :
    characterLp m χ = characterLp m ψ := by
  apply Lp.ext
  filter_upwards [characterLp_coeFn m χ, characterLp_coeFn m ψ] with x hχ hψ
  rw [hχ, hψ, congrFun h x]

lemma characterLp_inner_eq
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (χ ψ : Character G) :
    @inner ℂ (Lp ℂ 2 m) _ (characterLp m χ) (characterLp m ψ) =
      if χ.toFun = ψ.toFun then 1 else 0 := by
  rw [L2.inner_def]
  have hχcoe := characterLp_coeFn m χ
  have hψcoe := characterLp_coeFn m ψ
  have hintegral :
      (∫ x, @inner ℂ ℂ _ (characterLp m χ x)
          (characterLp m ψ x) ∂m) =
        ∫ x, star (χ.toFun x) * ψ.toFun x ∂m := by
    apply integral_congr_ae
    filter_upwards [hχcoe, hψcoe] with x hχ hψ
    rw [hχ, hψ, RCLike.inner_apply]
    simp only [starRingEnd_apply, mul_comm]
  rw [hintegral]
  split_ifs with h
  · have hp : ∀ x, star (χ.toFun x) * ψ.toFun x = 1 := by
      intro x
      rw [← congrFun h x]
      exact star_mul_self_of_norm_eq_one (χ.unit_norm x)
    calc
      (∫ x, star (χ.toFun x) * ψ.toFun x ∂m) =
          ∫ _x : G, (1 : ℂ) ∂m := integral_congr_ae (.of_forall hp)
      _ = 1 := by simp
  · exact character_orthogonal_integral m χ ψ h

lemma characterOrbit_toFun_injective
    (A : G →* G) (hA : Continuous A) (hAsurj : Function.Surjective A)
    (χ : Character G) (hχnontrivial : ¬ ∀ x, χ.toFun x = 1)
    (haperiodic : ∀ ψ : Character G,
      (∃ n : ℕ, 0 < n ∧
        (fun x => ψ.toFun ((A : G → G)^[n] x)) = ψ.toFun) →
      ∀ x, ψ.toFun x = 1) :
    Function.Injective fun n => (characterCompIterate A hA χ n).toFun := by
  have forward {i j : ℕ} (hijle : i ≤ j)
      (hij : (characterCompIterate A hA χ i).toFun =
        (characterCompIterate A hA χ j).toFun) : i = j := by
    by_contra hne
    have hilt : i < j := lt_of_le_of_ne hijle hne
    let k := j - i
    have hk : 0 < k := Nat.sub_pos_of_lt hilt
    have hperiod :
        (fun x => χ.toFun ((A : G → G)^[k] x)) = χ.toFun := by
      funext y
      obtain ⟨x, rfl⟩ := hAsurj.iterate i y
      have heq := congrFun hij x
      change χ.toFun ((A : G → G)^[i] x) =
        χ.toFun ((A : G → G)^[j] x) at heq
      have hj : j = k + i := by
        dsimp [k]
        omega
      rw [hj, Function.iterate_add_apply] at heq
      exact heq.symm
    exact hχnontrivial (haperiodic χ ⟨k, hk, hperiod⟩)
  intro i j hij
  rcases le_total i j with hijle | hjile
  · exact forward hijle hij
  · exact (forward hjile hij.symm).symm

private lemma integral_comp_measurePreserving
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

private lemma invariant_iterate_ae
    (m : Measure G) (A : G →* G) (hmp : MeasurePreserving A m m)
    (f : G → ℂ)
    (hinv : Chapter01.koopman (A : G → G) f =ᵐ[m] f) :
    ∀ n : ℕ, (fun x => f ((A : G → G)^[n] x)) =ᵐ[m] f := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hpre := hmp.quasiMeasurePreserving.ae_eq_comp ih
      simpa only [Function.comp_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply'] using hpre.trans hinv

lemma invariant_character_inner_orbit_eq
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (A : G →* G) (hA : Continuous A) (hAsurj : Function.Surjective A)
    (f : G → ℂ) (hf : MemLp f 2 m)
    (hinv : Chapter01.koopman (A : G → G) f =ᵐ[m] f)
    (χ : Character G) (n : ℕ) :
    @inner ℂ (Lp ℂ 2 m) _ (characterLp m (characterCompIterate A hA χ n))
      (hf.toLp f) =
    @inner ℂ (Lp ℂ 2 m) _ (characterLp m χ) (hf.toLp f) := by
  let hmp : MeasurePreserving A m m :=
    haarEndomorphism_measurePreserving m A hA hAsurj
  have hmpn : MeasurePreserving ((A : G → G)^[n]) m m := hmp.iterate n
  have hfinv := invariant_iterate_ae m A hmp f hinv n
  have hχcoe := characterLp_coeFn m (characterCompIterate A hA χ n)
  have hχ0coe := characterLp_coeFn m χ
  have hfcoe := hf.coeFn_toLp
  rw [L2.inner_def, L2.inner_def]
  have hleft :
      (∫ x, @inner ℂ ℂ _ (characterLp m
          (characterCompIterate A hA χ n) x) ((hf.toLp f) x) ∂m) =
        ∫ x, star (χ.toFun ((A : G → G)^[n] x)) * f x ∂m := by
    apply integral_congr_ae
    filter_upwards [hχcoe, hfcoe] with x hχx hfx
    rw [hχx, hfx, RCLike.inner_apply]
    simp only [starRingEnd_apply, mul_comm, characterCompIterate]
  have hright :
      (∫ x, @inner ℂ ℂ _ (characterLp m χ x) ((hf.toLp f) x) ∂m) =
        ∫ x, star (χ.toFun x) * f x ∂m := by
    apply integral_congr_ae
    filter_upwards [hχ0coe, hfcoe] with x hχx hfx
    rw [hχx, hfx, RCLike.inner_apply]
    simp only [starRingEnd_apply, mul_comm]
  rw [hleft, hright]
  calc
    (∫ x, star (χ.toFun ((A : G → G)^[n] x)) * f x ∂m) =
        ∫ x, star (χ.toFun ((A : G → G)^[n] x)) *
          f ((A : G → G)^[n] x) ∂m := by
      apply integral_congr_ae
      filter_upwards [hfinv] with x hx
      rw [hx]
    _ = ∫ x, star (χ.toFun x) * f x ∂m := by
      let g : G → ℂ := fun x => star (χ.toFun x) * f x
      apply integral_comp_measurePreserving ((A : G → G)^[n]) hmpn g
      exact χ.continuous.star.aestronglyMeasurable.mul hf.1

lemma invariant_nontrivial_character_inner_eq_zero
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (A : G →* G) (hA : Continuous A) (hAsurj : Function.Surjective A)
    (f : G → ℂ) (hf : MemLp f 2 m)
    (hinv : Chapter01.koopman (A : G → G) f =ᵐ[m] f)
    (haperiodic : ∀ ψ : Character G,
      (∃ n : ℕ, 0 < n ∧
        (fun x => ψ.toFun ((A : G → G)^[n] x)) = ψ.toFun) →
      ∀ x, ψ.toFun x = 1)
    (χ : Character G) (hχnontrivial : ¬ ∀ x, χ.toFun x = 1) :
    @inner ℂ (Lp ℂ 2 m) _ (characterLp m χ) (hf.toLp f) = 0 := by
  let v : ℕ → Lp ℂ 2 m :=
    fun n => characterLp m (characterCompIterate A hA χ n)
  have hinj := characterOrbit_toFun_injective A hA hAsurj χ
    hχnontrivial haperiodic
  have hv : Orthonormal ℂ v :=
    orthonormal_character_family m
      (fun n => characterCompIterate A hA χ n) hinj
  let c : ℂ := @inner ℂ (Lp ℂ 2 m) _ (characterLp m χ) (hf.toLp f)
  have hcoeff : ∀ n, @inner ℂ (Lp ℂ 2 m) _ (v n) (hf.toLp f) = c := by
    intro n
    exact invariant_character_inner_orbit_eq m A hA hAsurj f hf hinv χ n
  have hsummable := hv.inner_products_summable (hf.toLp f)
  have hconst :
      (fun n => ‖@inner ℂ (Lp ℂ 2 m) _ (v n) (hf.toLp f)‖ ^ 2) =
        fun _n : ℕ => ‖c‖ ^ 2 := by
    funext n
    rw [hcoeff n]
  rw [hconst] at hsummable
  have hnormsq : ‖c‖ ^ 2 = 0 := by
    simpa only [summable_const_iff] using hsummable
  have hnorm : ‖c‖ = 0 := by nlinarith [norm_nonneg c]
  exact norm_eq_zero.mp hnorm

lemma eq_zero_of_inner_characterLp_eq_zero
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (F : Lp ℂ 2 m)
    (hF : ∀ χ : Character G,
      @inner ℂ (Lp ℂ 2 m) _ (characterLp m χ) F = 0) :
    F = 0 := by
  let S : Submodule ℂ (Lp ℂ 2 m) :=
    Submodule.span ℂ (Set.range (characterLp m))
  let K : Submodule ℂ (Lp ℂ 2 m) := (innerSL ℂ F).ker
  have hSK : S ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨χ, rfl⟩
    change @inner ℂ (Lp ℂ 2 m) _ F (characterLp m χ) = 0
    exact inner_eq_zero_symm.mpr (hF χ)
  have hSdense : Dense (S : Set (Lp ℂ 2 m)) := by
    exact MathCopilotPrior.compactAbelian_character_span_dense m
  have hclosure : S.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hSdense
  have htopK : (⊤ : Submodule ℂ (Lp ℂ 2 m)) ≤ K := by
    rw [← hclosure]
    exact Submodule.topologicalClosure_minimal S hSK
      (ContinuousLinearMap.isClosed_ker (innerSL ℂ F))
  have hmem : F ∈ K := htopK (by simp)
  change @inner ℂ (Lp ℂ 2 m) _ F F = 0 at hmem
  exact inner_self_eq_zero.mp hmem

lemma invariant_function_ae_constant_of_aperiodic_characters
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (A : G →* G) (hA : Continuous A) (hAsurj : Function.Surjective A)
    (haperiodic : ∀ ψ : Character G,
      (∃ n : ℕ, 0 < n ∧
        (fun x => ψ.toFun ((A : G → G)^[n] x)) = ψ.toFun) →
      ∀ x, ψ.toFun x = 1)
    (f : G → ℂ) (hf : MemLp f 2 m)
    (hinv : Chapter01.koopman (A : G → G) f =ᵐ[m] f) :
    ∃ c : ℂ, f =ᵐ[m] fun _ => c := by
  let e : Lp ℂ 2 m := characterLp m (trivialCharacter (G := G))
  let F : Lp ℂ 2 m := hf.toLp f
  let c : ℂ := @inner ℂ (Lp ℂ 2 m) _ e F
  let Y : Lp ℂ 2 m := F - c • e
  have hYchar : ∀ χ : Character G,
      @inner ℂ (Lp ℂ 2 m) _ (characterLp m χ) Y = 0 := by
    intro χ
    dsimp only [Y]
    rw [inner_sub_right, inner_smul_right]
    by_cases hχtriv : ∀ x, χ.toFun x = 1
    · have hfun : χ.toFun = (trivialCharacter (G := G)).toFun := by
        funext x
        exact hχtriv x
      have hLp : characterLp m χ = e := by
        exact characterLp_eq_of_toFun_eq m hfun
      rw [hLp]
      change c - c * @inner ℂ (Lp ℂ 2 m) _ e e = 0
      have heinner :
          @inner ℂ (Lp ℂ 2 m) _ e e = 1 := by
        dsimp only [e]
        simpa using characterLp_inner_eq m
          (trivialCharacter (G := G)) (trivialCharacter (G := G))
      rw [heinner, mul_one, sub_self]
    · have hzero := invariant_nontrivial_character_inner_eq_zero
        m A hA hAsurj f hf hinv haperiodic χ hχtriv
      have horth :
          @inner ℂ (Lp ℂ 2 m) _ (characterLp m χ) e = 0 := by
        dsimp only [e]
        rw [characterLp_inner_eq]
        rw [if_neg]
        intro hfun
        apply hχtriv
        intro x
        exact congrFun hfun x
      rw [hzero, horth, mul_zero, sub_zero]
  have hYzero := eq_zero_of_inner_characterLp_eq_zero m Y hYchar
  have hFEq : F = c • e := sub_eq_zero.mp hYzero
  refine ⟨c, ?_⟩
  have hfunEq : (fun x => F x) =ᵐ[m] fun x => (c • e) x := by
    rw [hFEq]
  filter_upwards [hf.coeFn_toLp, hfunEq, Lp.coeFn_smul c e,
    characterLp_coeFn m (trivialCharacter (G := G))] with x hfcoe hEq hsmul he
  rw [← hfcoe, hEq, hsmul]
  change c * e x = c
  have heone : e x = 1 := by
    dsimp only [e]
    rw [he]
    rfl
  rw [heone, mul_one]

def orbitSum (A : G →* G) (χ : Character G) (n : ℕ) : G → ℂ :=
  fun x => ∑ j ∈ Finset.range n, χ.toFun ((A : G → G)^[j] x)

lemma continuous_orbitSum (A : G →* G) (hA : Continuous A)
    (χ : Character G) (n : ℕ) :
    Continuous (orbitSum A χ n) := by
  apply continuous_finset_sum
  intro j _
  exact χ.continuous.comp (hA.iterate j)

lemma orbitSum_one (A : G →* G) (χ : Character G) (n : ℕ) :
    orbitSum A χ n 1 = n := by
  simp [orbitSum, χ.map_one]

lemma orbitSum_memLp (m : Measure G) [IsProbabilityMeasure m]
    (A : G →* G) (hA : Continuous A) (χ : Character G) (n : ℕ) :
    MemLp (orbitSum A χ n) 2 m := by
  apply (memLp_top_of_bound
    (continuous_orbitSum A hA χ n).aestronglyMeasurable n ?_).mono_exponent
    (by simp)
  filter_upwards with x
  calc
    ‖orbitSum A χ n x‖ ≤
        ∑ j ∈ Finset.range n, ‖χ.toFun ((A : G → G)^[j] x)‖ := norm_sum_le _ _
    _ = n := by simp [χ.unit_norm]

private lemma complex_eq_one_of_norm_eq_one_of_re_eq_one
    {z : ℂ} (hnorm : ‖z‖ = 1) (hre : z.re = 1) : z = 1 := by
  apply Complex.ext
  · simpa using hre
  · have hsquare : z.im ^ 2 = 0 := by
      have hnormsq := Complex.sq_norm z
      rw [hnorm, Complex.normSq_apply, hre] at hnormsq
      nlinarith
    exact sq_eq_zero_iff.mp hsquare

private lemma first_eq_one_of_unit_norm_sum_eq
    {n : ℕ} (hn : 0 < n) (z : ℕ → ℂ)
    (hz : ∀ j < n, ‖z j‖ = 1)
    (hsum : ∑ j ∈ Finset.range n, z j = n) :
    z 0 = 1 := by
  have hre_le (j : ℕ) (hj : j < n) : (z j).re ≤ 1 := by
    calc
      (z j).re ≤ ‖z j‖ := Complex.re_le_norm _
      _ = 1 := hz j hj
  have hresum :
      ∑ j ∈ Finset.range n, (z j).re = n := by
    have := congrArg Complex.re hsum
    simpa using this
  have hrest_le :
      ∑ j ∈ (Finset.range n).erase 0, (z j).re ≤
        ∑ _j ∈ (Finset.range n).erase 0, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hre_le j (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))
  have h0mem : 0 ∈ Finset.range n := Finset.mem_range.mpr hn
  have hre0 : (z 0).re = 1 := by
    rw [← Finset.sum_erase_add _ _ h0mem] at hresum
    have hcard : ((Finset.range n).erase 0).card = n - 1 := by
      rw [Finset.card_erase_of_mem h0mem, Finset.card_range]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard] at hrest_le
    have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hnreal : (n : ℝ) = (n - 1 : ℕ) + 1 := by
      exact_mod_cast hnsub.symm
    have hre0le := hre_le 0 hn
    linarith
  exact complex_eq_one_of_norm_eq_one_of_re_eq_one (hz 0 hn) hre0

lemma orbitSum_constant_implies_character_trivial
    (A : G →* G) (χ : Character G) {n : ℕ} (hn : 0 < n)
    (hconst : ∃ c : ℂ, orbitSum A χ n = fun _ => c) :
    ∀ x, χ.toFun x = 1 := by
  obtain ⟨c, hc⟩ := hconst
  have hcval : c = n := by
    have := congrFun hc 1
    simpa [orbitSum_one] using this.symm
  intro x
  apply first_eq_one_of_unit_norm_sum_eq hn
    (fun j => χ.toFun ((A : G → G)^[j] x))
  · intro j hj
    exact χ.unit_norm _
  · have := congrFun hc x
    simpa [orbitSum, hcval] using this

lemma orbitSum_ae_constant_implies_character_trivial
    (m : Measure G) [m.IsHaarMeasure]
    (A : G →* G) (hA : Continuous A) (χ : Character G)
    {n : ℕ} (hn : 0 < n)
    (hconst : ∃ c : ℂ, orbitSum A χ n =ᵐ[m] fun _ => c) :
    ∀ x, χ.toFun x = 1 := by
  obtain ⟨c, hc⟩ := hconst
  apply orbitSum_constant_implies_character_trivial A χ hn
  refine ⟨c, ?_⟩
  exact Measure.eq_of_ae_eq hc (continuous_orbitSum A hA χ n) continuous_const

lemma orbitSum_invariant_of_periodic
    (A : G →* G) (χ : Character G) {n : ℕ} (hn : 0 < n)
    (hperiodic :
      (fun x => χ.toFun ((A : G → G)^[n] x)) = χ.toFun) :
    Chapter01.koopman (A : G → G) (orbitSum A χ n) =
      orbitSum A χ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  funext x
  simp only [Chapter01.koopman, Function.comp_apply, orbitSum]
  simp_rw [← Function.iterate_succ_apply]
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have hp := congrFun hperiodic x
  rw [hp]
  ac_rfl

end Chapter02.CompactHaarCharacters
