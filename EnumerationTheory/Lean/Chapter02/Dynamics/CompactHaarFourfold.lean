import Chapter02.Spectral.CompactHaarCharacters

noncomputable section

open Classical MeasureTheory

namespace Chapter02.CompactHaarFourfold

universe u

open CompactHaarCharacters

variable {G : Type u} [CommGroup G] [MetricSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- The project's concrete continuous characters are extensional in their
underlying functions. -/
lemma character_ext (χ ψ : Character G) (h : χ.toFun = ψ.toFun) : χ = ψ := by
  cases χ
  cases ψ
  simp_all

lemma character_toFun_injective :
    Function.Injective (fun χ : Character G ↦ χ.toFun) :=
  fun χ ψ h ↦ character_ext χ ψ h

lemma self_mul_star_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) :
    z * star z = 1 := by
  rw [mul_comm, Complex.star_def]
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]
  norm_num

lemma character_map_inv (χ : Character G) (x : G) :
    χ.toFun x⁻¹ = star (χ.toFun x) := by
  have hinv := χ.map_mul x⁻¹ x
  have hinv' : χ.toFun x⁻¹ * χ.toFun x = 1 := by
    simpa [χ.map_one] using hinv.symm
  calc
    χ.toFun x⁻¹ = χ.toFun x⁻¹ * 1 := by simp
    _ = χ.toFun x⁻¹ * (χ.toFun x * star (χ.toFun x)) := by
      rw [self_mul_star_of_norm_one (χ.unit_norm x)]
    _ = (χ.toFun x⁻¹ * χ.toFun x) * star (χ.toFun x) := by ring
    _ = star (χ.toFun x) := by rw [hinv', one_mul]

/-- The continuous characters form a Hilbert basis of `L²` for Haar
probability on a compact metrizable abelian group. -/
def characterHilbertBasis
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure] :
    HilbertBasis (Character G) ℂ (Lp ℂ 2 m) := by
  apply HilbertBasis.mk
    (CompactHaarCharacters.orthonormal_character_family
      m (fun χ : Character G ↦ χ) character_toFun_injective)
  let S : Submodule ℂ (Lp ℂ 2 m) :=
    Submodule.span ℂ (Set.range (CompactHaarCharacters.characterLp m))
  have hSdense : Dense (S : Set (Lp ℂ 2 m)) := by
    exact MathCopilotPrior.compactAbelian_character_span_dense m
  have hclosure : S.topologicalClosure = ⊤ := by
    ext x
    constructor
    · intro hx
      trivial
    · intro hx
      change x ∈ closure (S : Set (Lp ℂ 2 m))
      rw [hSdense.closure_eq]
      trivial
  change ⊤ ≤ S.topologicalClosure
  rw [hclosure]

@[simp]
lemma characterHilbertBasis_apply
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (χ : Character G) :
    characterHilbertBasis m χ = characterLp m χ := by
  unfold characterHilbertBasis
  rw [HilbertBasis.coe_mk]

/-- The cubing endomorphism of a commutative multiplicative group. -/
def cubeHom : G →* G :=
  MonoidHom.mk' (fun x : G ↦ x ^ 3) (by
    intro x y
    change (x * y) ^ 3 = x ^ 3 * y ^ 3
    rw [mul_pow])

lemma cubeHom_continuous : Continuous (cubeHom : G → G) := by
  change Continuous (fun x : G ↦ x ^ 3)
  fun_prop

/-- Pullback of a character along the cubing endomorphism. -/
def characterCube (χ : Character G) : Character G where
  toFun x := χ.toFun (x ^ 3)
  map_one := by simp [χ.map_one]
  map_mul x y := by rw [mul_pow, χ.map_mul]
  continuous := χ.continuous.comp cubeHom_continuous
  unit_norm x := χ.unit_norm _

lemma characterCube_toFun (χ : Character G) (x : G) :
    (characterCube χ).toFun x = χ.toFun (x ^ 3) :=
  rfl

lemma characterCube_injective
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3)) :
    Function.Injective (characterCube : Character G → Character G) := by
  intro χ ψ hχψ
  apply character_ext
  funext x
  obtain ⟨y, rfl⟩ := hcube x
  exact congrFun (congrArg
    (fun η : Character G ↦ η.toFun) hχψ) y

lemma cubeHom_measurePreserving
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3)) :
    MeasurePreserving (cubeHom : G → G) m m :=
  CompactHaarCharacters.haarEndomorphism_measurePreserving
    m cubeHom cubeHom_continuous hcube

/-- On the character basis, pullback by cubing is exactly cubing of the
character. -/
lemma compCube_characterLp
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    (χ : Character G) :
    Lp.compMeasurePreserving (cubeHom : G → G)
        (cubeHom_measurePreserving m hcube) (characterLp m χ) =
      characterLp m (characterCube χ) := by
  apply Lp.ext
  filter_upwards
    [Lp.coeFn_compMeasurePreserving (characterLp m χ)
      (cubeHom_measurePreserving m hcube),
     characterLp_coeFn m χ,
     characterLp_coeFn m (characterCube χ),
     (cubeHom_measurePreserving m hcube).quasiMeasurePreserving.ae_eq_comp
       (characterLp_coeFn m χ)] with x hcomp hχ hχcube hχcomp
  rw [hcomp, hχcube]
  exact hχcomp

/-- Applying a linear isometry to a Hilbert expansion and then pairing
against a second vector.  This is the operator form of Parseval used below. -/
lemma hasSum_inner_linearIsometry_hilbertBasis
    {ι : Type*} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (b : HilbertBasis ι ℂ E) (U : E →ₗᵢ[ℂ] E) (x y : E) :
    HasSum
      (fun i ↦ inner ℂ x (b i) * inner ℂ (U (b i)) y)
      (inner ℂ (U x) y) := by
  have hU := (b.hasSum_repr x).map U U.continuous
  have hinner := hU.map ((innerSLFlip ℂ) y)
    (((innerSLFlip ℂ) y).continuous)
  simpa [Function.comp_def, innerSLFlip_apply_apply, inner_smul_left,
    HilbertBasis.repr_apply_apply, inner_conj_symm] using hinner

/-- Parseval after pullback by cubing, with the character injection made
explicit. -/
lemma hasSum_inner_compCube
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    (F H : Lp ℂ 2 m) :
    HasSum
      (fun χ : Character G ↦
        inner ℂ F (characterLp m χ) *
          inner ℂ (characterLp m (characterCube χ)) H)
      (inner ℂ
        (Lp.compMeasurePreserving (cubeHom : G → G)
          (cubeHom_measurePreserving m hcube) F) H) := by
  let b := characterHilbertBasis m
  let U : Lp ℂ 2 m →ₗᵢ[ℂ] Lp ℂ 2 m :=
    Lp.compMeasurePreservingₗᵢ ℂ (cubeHom : G → G)
      (cubeHom_measurePreserving m hcube)
  have hsum := hasSum_inner_linearIsometry_hilbertBasis b U F H
  simpa only [b, U, characterHilbertBasis_apply,
    compCube_characterLp] using hsum

/-- Haar autocorrelation of a continuous function. -/
noncomputable def autocorrelationContinuousMap
    (m : Measure G) [IsProbabilityMeasure m]
    (a : C(G, ℂ)) : C(G, ℂ) where
  toFun w := ∫ g, star (a g) * a (g * w) ∂m
  continuous_toFun := by
    rw [← continuousOn_univ]
    apply continuousOn_integral_of_compact_support
      (k := (Set.univ : Set G)) isCompact_univ
    · apply Continuous.continuousOn
      fun_prop
    · intro w g hw hg
      exact (hg (Set.mem_univ g)).elim

@[simp]
lemma autocorrelationContinuousMap_apply
    (m : Measure G) [IsProbabilityMeasure m]
    (a : C(G, ℂ)) (w : G) :
    autocorrelationContinuousMap m a w =
      ∫ g, star (a g) * a (g * w) ∂m :=
  rfl

/-- Fourier characters factor out of a Haar-translated integral. -/
lemma character_weighted_translate_integral
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (χ : Character G) (a : C(G, ℂ)) (g : G) :
    (∫ w, star (χ.toFun w) * a (g * w) ∂m) =
      χ.toFun g * ∫ z, star (χ.toFun z) * a z ∂m := by
  calc
    (∫ w, star (χ.toFun w) * a (g * w) ∂m) =
        ∫ w, star (χ.toFun (g⁻¹ * (g * w))) * a (g * w) ∂m := by
      apply integral_congr_ae
      exact .of_forall fun w ↦ by simp
    _ = ∫ z, star (χ.toFun (g⁻¹ * z)) * a z ∂m := by
      exact integral_mul_left_eq_self
        (fun z ↦ star (χ.toFun (g⁻¹ * z)) * a z) g
    _ = ∫ z, χ.toFun g * (star (χ.toFun z) * a z) ∂m := by
      apply integral_congr_ae
      exact .of_forall fun z ↦ by
        change star (χ.toFun (g⁻¹ * z)) * a z =
          χ.toFun g * (star (χ.toFun z) * a z)
        rw [χ.map_mul, character_map_inv]
        change (starRingEnd ℂ)
            ((starRingEnd ℂ) (χ.toFun g) * χ.toFun z) * a z =
          χ.toFun g * ((starRingEnd ℂ) (χ.toFun z) * a z)
        rw [map_mul (starRingEnd ℂ)]
        have hstarstar :
            (starRingEnd ℂ) ((starRingEnd ℂ) (χ.toFun g)) =
              χ.toFun g := by
          change star (star (χ.toFun g)) = χ.toFun g
          exact star_star _
        rw [hstarstar]
        ring
    _ = χ.toFun g * ∫ z, star (χ.toFun z) * a z ∂m :=
      integral_const_mul _ _

/-- The Fourier coefficient of Haar autocorrelation is the squared modulus
of the corresponding Fourier coefficient. -/
lemma integral_character_autocorrelation
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (χ : Character G) (a : C(G, ℂ)) :
    (∫ w, star (χ.toFun w) * autocorrelationContinuousMap m a w ∂m) =
      (Complex.normSq
        (∫ z, star (χ.toFun z) * a z ∂m) : ℂ) := by
  let c : ℂ := ∫ z, star (χ.toFun z) * a z ∂m
  let F : G × G → ℂ := fun p ↦
    star (χ.toFun p.2) * (star (a p.1) * a (p.1 * p.2))
  have hFcont : Continuous F := by
    dsimp only [F]
    exact (χ.continuous.comp continuous_snd).star.mul
      ((a.continuous.comp continuous_fst).star.mul
        (a.continuous.comp (continuous_fst.mul continuous_snd)))
  have hF : Integrable F (m.prod m) :=
    hFcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hconj :
      (∫ g, star (a g) * χ.toFun g ∂m) = star c := by
    rw [show star c =
        ∫ g, star (star (χ.toFun g) * a g) ∂m by
      exact (integral_conj (μ := m)).symm]
    apply integral_congr_ae
    exact .of_forall fun g ↦ by
      change star (a g) * χ.toFun g =
        star (star (χ.toFun g) * a g)
      change (starRingEnd ℂ) (a g) * χ.toFun g =
        (starRingEnd ℂ) ((starRingEnd ℂ) (χ.toFun g) * a g)
      rw [map_mul (starRingEnd ℂ)]
      have hstarstar :
          (starRingEnd ℂ) ((starRingEnd ℂ) (χ.toFun g)) =
            χ.toFun g := by
        change star (star (χ.toFun g)) = χ.toFun g
        exact star_star _
      rw [hstarstar]
      ring
  calc
    (∫ w, star (χ.toFun w) * autocorrelationContinuousMap m a w ∂m) =
        ∫ w, ∫ g, F (g, w) ∂m ∂m := by
      apply integral_congr_ae
      exact .of_forall fun w ↦ by
        change star (χ.toFun w) * autocorrelationContinuousMap m a w =
          ∫ g, F (g, w) ∂m
        rw [autocorrelationContinuousMap_apply,
          ← integral_const_mul]
    _ = ∫ p, F p ∂(m.prod m) :=
      (integral_prod_symm F hF).symm
    _ = ∫ g, ∫ w, F (g, w) ∂m ∂m :=
      integral_prod F hF
    _ = ∫ g, star (a g) *
          (∫ w, star (χ.toFun w) * a (g * w) ∂m) ∂m := by
      apply integral_congr_ae
      exact .of_forall fun g ↦ by
        change (∫ w, F (g, w) ∂m) =
          star (a g) *
            (∫ w, star (χ.toFun w) * a (g * w) ∂m)
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact .of_forall fun w ↦ by
          dsimp only [F]
          ring
    _ = ∫ g, star (a g) * (χ.toFun g * c) ∂m := by
      apply integral_congr_ae
      exact .of_forall fun g ↦ by
        change star (a g) *
            (∫ w, star (χ.toFun w) * a (g * w) ∂m) =
          star (a g) * (χ.toFun g * c)
        rw [character_weighted_translate_integral]
    _ = ∫ g, (star (a g) * χ.toFun g) * c ∂m := by
      apply integral_congr_ae
      exact .of_forall fun g ↦ by ring
    _ = (∫ g, star (a g) * χ.toFun g ∂m) * c :=
      integral_mul_const _ _
    _ = star c * c := by rw [hconj]
    _ = (Complex.normSq c : ℂ) := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

lemma inner_characterLp_autocorrelation
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (χ : Character G) (a : C(G, ℂ)) :
    inner ℂ (characterLp m χ)
        (ContinuousMap.toLp 2 m ℂ (autocorrelationContinuousMap m a)) =
      (Complex.normSq
        (∫ z, star (χ.toFun z) * a z ∂m) : ℂ) := by
  rw [L2.inner_def]
  have hχ := characterLp_coeFn m χ
  have hD := ContinuousMap.coeFn_toLp
    (p := (2 : ENNReal)) (𝕜 := ℂ) m (autocorrelationContinuousMap m a)
  calc
    (∫ x, @inner ℂ ℂ _
        (characterLp m χ x)
        (ContinuousMap.toLp 2 m ℂ
          (autocorrelationContinuousMap m a) x) ∂m) =
        ∫ x, star (χ.toFun x) *
          autocorrelationContinuousMap m a x ∂m := by
      apply integral_congr_ae
      filter_upwards [hχ, hD] with x hxχ hxD
      rw [hxχ, hxD, RCLike.inner_apply]
      simp only [starRingEnd_apply, mul_comm]
    _ = (Complex.normSq
        (∫ z, star (χ.toFun z) * a z ∂m) : ℂ) :=
      integral_character_autocorrelation m χ a

lemma inner_autocorrelation_characterLp
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (χ : Character G) (a : C(G, ℂ)) :
    inner ℂ
        (ContinuousMap.toLp 2 m ℂ (autocorrelationContinuousMap m a))
        (characterLp m χ) =
      (Complex.normSq
        (∫ z, star (χ.toFun z) * a z ∂m) : ℂ) := by
  calc
    inner ℂ
        (ContinuousMap.toLp 2 m ℂ (autocorrelationContinuousMap m a))
        (characterLp m χ) =
        star (inner ℂ (characterLp m χ)
          (ContinuousMap.toLp 2 m ℂ
            (autocorrelationContinuousMap m a))) := by
      exact (inner_conj_symm _ _).symm
    _ = star
        (Complex.normSq
          (∫ z, star (χ.toFun z) * a z ∂m) : ℂ) := by
      rw [inner_characterLp_autocorrelation]
    _ = (Complex.normSq
        (∫ z, star (χ.toFun z) * a z ∂m) : ℂ) := by
      simp

lemma characterCube_trivial :
    characterCube (trivialCharacter : Character G) =
      (trivialCharacter : Character G) := by
  apply character_ext
  funext x
  rfl

/-- The compact-abelian Fourier core of the sharp fourfold estimate:
the cubed autocorrelation pairing dominates its trivial Fourier mode. -/
lemma autocorrelation_cube_inner_lower_bound
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    (a : C(G, ℂ)) :
    (Complex.normSq (∫ x, a x ∂m)) ^ 2 ≤
      (inner ℂ
        (Lp.compMeasurePreserving (cubeHom : G → G)
          (cubeHom_measurePreserving m hcube)
          (ContinuousMap.toLp 2 m ℂ
            (autocorrelationContinuousMap m a)))
        (ContinuousMap.toLp 2 m ℂ
          (autocorrelationContinuousMap m a))).re := by
  let D : Lp ℂ 2 m :=
    ContinuousMap.toLp 2 m ℂ (autocorrelationContinuousMap m a)
  let q : Character G → ℝ := fun χ ↦
    Complex.normSq (∫ z, star (χ.toFun z) * a z ∂m)
  have hsumComplex :
      HasSum
        (fun χ : Character G ↦
          (q χ : ℂ) * (q (characterCube χ) : ℂ))
        (inner ℂ
          (Lp.compMeasurePreserving (cubeHom : G → G)
            (cubeHom_measurePreserving m hcube) D) D) := by
    simpa only [D, q, inner_autocorrelation_characterLp,
      inner_characterLp_autocorrelation] using
      (hasSum_inner_compCube m hcube D D)
  have hsumReal :
      HasSum
        (fun χ : Character G ↦ q χ * q (characterCube χ))
        (inner ℂ
          (Lp.compMeasurePreserving (cubeHom : G → G)
            (cubeHom_measurePreserving m hcube) D) D).re := by
    simpa only [Complex.reCLM_apply, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
      hsumComplex.mapL Complex.reCLM
  have hnonneg (χ : Character G) :
      0 ≤ q χ * q (characterCube χ) :=
    mul_nonneg (Complex.normSq_nonneg _)
      (Complex.normSq_nonneg _)
  have hsingle :
      q (trivialCharacter : Character G) *
          q (characterCube (trivialCharacter : Character G)) ≤
        (inner ℂ
          (Lp.compMeasurePreserving (cubeHom : G → G)
            (cubeHom_measurePreserving m hcube) D) D).re := by
    rw [← hsumReal.tsum_eq]
    simpa using hsumReal.summable.sum_le_tsum
      ({(trivialCharacter : Character G)} : Finset (Character G))
      (by
        intro χ hχ
        exact hnonneg χ)
  rw [characterCube_trivial] at hsingle
  simpa only [D, q, trivialCharacter, one_mul, star_one, pow_two] using
    hsingle

/-- The `L²` pairing with cubing is the expected Haar integral for a
continuous representative. -/
lemma inner_compCube_continuousMap
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    (f : C(G, ℂ)) :
    inner ℂ
        (Lp.compMeasurePreserving (cubeHom : G → G)
          (cubeHom_measurePreserving m hcube)
          (ContinuousMap.toLp 2 m ℂ f))
        (ContinuousMap.toLp 2 m ℂ f) =
      ∫ w, star (f (w ^ 3)) * f w ∂m := by
  rw [L2.inner_def]
  have hf := ContinuousMap.coeFn_toLp
    (p := (2 : ENNReal)) (𝕜 := ℂ) m f
  have hcomp := Lp.coeFn_compMeasurePreserving
    (ContinuousMap.toLp 2 m ℂ f)
    (cubeHom_measurePreserving m hcube)
  have hfpull :=
    (cubeHom_measurePreserving m hcube).quasiMeasurePreserving.ae_eq_comp hf
  apply integral_congr_ae
  filter_upwards [hcomp, hf, hfpull] with w hwcomp hwf hwfpull
  rw [RCLike.inner_apply, hwcomp, hwf, hwfpull]
  change f w * star (f (w ^ 3)) = star (f (w ^ 3)) * f w
  ring

/-- A real-valued continuous function viewed as complex-valued. -/
def ofRealContinuousMap (f : C(G, ℝ)) : C(G, ℂ) where
  toFun x := (f x : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous

/-- Real Haar autocorrelation. -/
noncomputable def realAutocorrelation
    (m : Measure G) (f : C(G, ℝ)) (w : G) : ℝ :=
  ∫ g, f g * f (g * w) ∂m

lemma autocorrelation_ofRealContinuousMap
    (m : Measure G) [IsProbabilityMeasure m]
    (f : C(G, ℝ)) (w : G) :
    autocorrelationContinuousMap m (ofRealContinuousMap f) w =
      (realAutocorrelation m f w : ℂ) := by
  change (∫ g, star (f g : ℂ) * (f (g * w) : ℂ) ∂m) =
    ((∫ g, f g * f (g * w) ∂m : ℝ) : ℂ)
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  exact .of_forall fun g ↦ by
    change star (f g : ℂ) * (f (g * w) : ℂ) =
      ((f g * f (g * w) : ℝ) : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]

/-- The cubed `L²` autocorrelation pairing of a real function is the
ordinary real autocorrelation integral. -/
lemma inner_compCube_autocorrelation_ofReal_re
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    (f : C(G, ℝ)) :
    (inner ℂ
      (Lp.compMeasurePreserving (cubeHom : G → G)
        (cubeHom_measurePreserving m hcube)
        (ContinuousMap.toLp 2 m ℂ
          (autocorrelationContinuousMap m (ofRealContinuousMap f))))
      (ContinuousMap.toLp 2 m ℂ
        (autocorrelationContinuousMap m (ofRealContinuousMap f)))).re =
      ∫ w, realAutocorrelation m f (w ^ 3) *
        realAutocorrelation m f w ∂m := by
  rw [inner_compCube_continuousMap m hcube]
  have hcomplex :
      (∫ w, star
          (autocorrelationContinuousMap m (ofRealContinuousMap f) (w ^ 3)) *
          autocorrelationContinuousMap m (ofRealContinuousMap f) w ∂m) =
        ((∫ w, realAutocorrelation m f (w ^ 3) *
          realAutocorrelation m f w ∂m : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact .of_forall fun w ↦ by
      change star
          (autocorrelationContinuousMap m (ofRealContinuousMap f) (w ^ 3)) *
          autocorrelationContinuousMap m (ofRealContinuousMap f) w =
        (realAutocorrelation m f (w ^ 3) *
          realAutocorrelation m f w : ℝ)
      rw [autocorrelation_ofRealContinuousMap,
        autocorrelation_ofRealContinuousMap]
      rw [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
  rw [hcomplex, Complex.ofReal_re]

/-- Sharp compact-abelian Haar inequality in real autocorrelation form. -/
theorem realAutocorrelation_cube_lower_bound
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    (f : C(G, ℝ)) :
    (∫ x, f x ∂m) ^ 4 ≤
      ∫ w, realAutocorrelation m f (w ^ 3) *
        realAutocorrelation m f w ∂m := by
  have h := autocorrelation_cube_inner_lower_bound
    m hcube (ofRealContinuousMap f)
  rw [inner_compCube_autocorrelation_ofReal_re m hcube f] at h
  have hint :
      (∫ x, ofRealContinuousMap f x ∂m) =
        ((∫ x, f x ∂m : ℝ) : ℂ) := by
    exact integral_complex_ofReal
  rw [hint, Complex.normSq_ofReal] at h
  convert h using 1 <;> ring

/-- The same sharp estimate with both autocorrelations expanded. -/
theorem compactAbelian_fourfold_lower_bound
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hcube : Function.Surjective (fun x : G ↦ x ^ 3))
    (f : C(G, ℝ)) :
    (∫ x, f x ∂m) ^ 4 ≤
      ∫ w, ∫ g, ∫ h,
        f g * f h * f (h * w) * f (g * w ^ 3) ∂m ∂m ∂m := by
  refine (realAutocorrelation_cube_lower_bound m hcube f).trans_eq ?_
  apply integral_congr_ae
  exact .of_forall fun w ↦ by
    change
      (∫ g, f g * f (g * w ^ 3) ∂m) *
          (∫ h, f h * f (h * w) ∂m) =
        ∫ g, ∫ h,
          f g * f h * f (h * w) * f (g * w ^ 3) ∂m ∂m
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact .of_forall fun g ↦ by
      change
        (f g * f (g * w ^ 3)) *
            (∫ h, f h * f (h * w) ∂m) =
          ∫ h, f g * f h * f (h * w) * f (g * w ^ 3) ∂m
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact .of_forall fun h ↦ by ring

end Chapter02.CompactHaarFourfold
