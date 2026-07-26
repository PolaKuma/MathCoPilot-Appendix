import Chapter02.Spectral.CompactHaarCharacters
import Chapter02.Ergodic.CorrelationMean

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter02
namespace CompactHaarMixing

universe u

abbrev Character (G : Type u) [CommGroup G] [TopologicalSpace G] :=
  ContinuousMultiplicativeCircleCharacter G

variable {G : Type u} [CommGroup G] [MetricSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private lemma characterLp_koopman_inner_eq
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (A : G →* G) (hA : Continuous A) (hAsurj : Function.Surjective A)
    (χ ψ : Character G) (n : ℕ) :
    let M := compactGroupHaarEndomorphismSystem m A
    @inner ℂ (Lp ℂ 2 m) _
      (CompactHaarCharacters.characterLp m χ)
      (CorrelationMean.koopmanIterLp M
        ⟨(inferInstance : IsProbabilityMeasure m),
          CompactHaarCharacters.haarEndomorphism_measurePreserving
            m A hA hAsurj⟩ n
        (CompactHaarCharacters.characterLp m ψ)) =
      if χ.toFun =
          (CompactHaarCharacters.characterCompIterate A hA ψ n).toFun
        then 1 else 0 := by
  dsimp only
  let hM : Chapter01.IsMeasurePreservingSystem
      (compactGroupHaarEndomorphismSystem m A) :=
    ⟨(inferInstance : IsProbabilityMeasure m),
      CompactHaarCharacters.haarEndomorphism_measurePreserving
        m A hA hAsurj⟩
  have hχ := CompactHaarCharacters.characterLp_coeFn m χ
  have hψ := CompactHaarCharacters.characterLp_coeFn m ψ
  have hcomp := Lp.coeFn_compMeasurePreserving
    (CompactHaarCharacters.characterLp m ψ)
    (hM.2.iterate n)
  calc
    @inner ℂ (Lp ℂ 2 m) _
        (CompactHaarCharacters.characterLp m χ)
        (CorrelationMean.koopmanIterLp
          (compactGroupHaarEndomorphismSystem m A) hM n
          (CompactHaarCharacters.characterLp m ψ)) =
        ∫ x, star (χ.toFun x) *
          ψ.toFun ((A : G → G)^[n] x) ∂m := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hχ, hcomp,
        (hM.2.iterate n).quasiMeasurePreserving.ae_eq_comp hψ] with
          x hχx hUx hψx
      rw [hχx]
      change @inner ℂ ℂ _ (χ.toFun x)
        (((Lp.compMeasurePreservingₗᵢ ℂ ((A : G → G)^[n])
          (hM.2.iterate n)) (CompactHaarCharacters.characterLp m ψ)) x) =
        _
      change
        (((Lp.compMeasurePreservingₗᵢ ℂ ((A : G → G)^[n])
          (hM.2.iterate n)) (CompactHaarCharacters.characterLp m ψ)) x) =
          ((CompactHaarCharacters.characterLp m ψ : G → ℂ) ∘
            ((A : G → G)^[n])) x at hUx
      rw [hUx]
      change
        (CompactHaarCharacters.characterLp m ψ)
            ((A : G → G)^[n] x) =
          ψ.toFun ((A : G → G)^[n] x) at hψx
      change @inner ℂ ℂ _ (χ.toFun x)
          ((CompactHaarCharacters.characterLp m ψ)
            ((A : G → G)^[n] x)) =
        star (χ.toFun x) * ψ.toFun ((A : G → G)^[n] x)
      rw [hψx, RCLike.inner_apply]
      simp only [starRingEnd_apply, mul_comm]
    _ = _ := CompactHaarCharacters.character_correlation_integral
      m A hA χ ψ n

lemma character_pair_correlation_tendsto
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (A : G →* G) (hA : Continuous A) (hAsurj : Function.Surjective A)
    (haperiodic : ∀ ψ : Character G,
      (∃ n : ℕ, 0 < n ∧
        (fun x => ψ.toFun ((A : G → G)^[n] x)) = ψ.toFun) →
      ∀ x, ψ.toFun x = 1)
    (χ ψ : Character G) :
    let M := compactGroupHaarEndomorphismSystem m A
    let hM : Chapter01.IsMeasurePreservingSystem M :=
      ⟨(inferInstance : IsProbabilityMeasure m),
        CompactHaarCharacters.haarEndomorphism_measurePreserving
          m A hA hAsurj⟩
    let e := CompactHaarCharacters.characterLp m
      (CompactHaarCharacters.trivialCharacter (G := G))
    Tendsto
      (fun n => @inner ℂ (Lp ℂ 2 m) _
        (CompactHaarCharacters.characterLp m χ)
        (CorrelationMean.koopmanIterLp M hM n
          (CompactHaarCharacters.characterLp m ψ)))
      atTop
      (nhds (@inner ℂ (Lp ℂ 2 m) _ e
          (CompactHaarCharacters.characterLp m ψ) *
        star (@inner ℂ (Lp ℂ 2 m) _ e
          (CompactHaarCharacters.characterLp m χ)))) := by
  dsimp only
  have hformula (n : ℕ) :=
    characterLp_koopman_inner_eq m A hA hAsurj χ ψ n
  by_cases hψtriv : ∀ x, ψ.toFun x = 1
  · have hψfun :
        ψ.toFun =
          (CompactHaarCharacters.trivialCharacter (G := G)).toFun := by
      funext x
      exact hψtriv x
    have hψLp :
        CompactHaarCharacters.characterLp m ψ =
          CompactHaarCharacters.characterLp m
            (CompactHaarCharacters.trivialCharacter (G := G)) :=
      CompactHaarCharacters.characterLp_eq_of_toFun_eq m hψfun
    by_cases hχtriv : ∀ x, χ.toFun x = 1
    · have hχfun :
          χ.toFun =
            (CompactHaarCharacters.trivialCharacter (G := G)).toFun := by
        funext x
        exact hχtriv x
      have hχLp :
          CompactHaarCharacters.characterLp m χ =
            CompactHaarCharacters.characterLp m
              (CompactHaarCharacters.trivialCharacter (G := G)) :=
        CompactHaarCharacters.characterLp_eq_of_toFun_eq m hχfun
      simp only [hχLp, hψLp]
      have heinner :
          @inner ℂ (Lp ℂ 2 m) _
              (CompactHaarCharacters.characterLp m
                (CompactHaarCharacters.trivialCharacter (G := G)))
              (CompactHaarCharacters.characterLp m
                (CompactHaarCharacters.trivialCharacter (G := G))) = 1 := by
        simpa using CompactHaarCharacters.characterLp_inner_eq m
          (CompactHaarCharacters.trivialCharacter (G := G))
          (CompactHaarCharacters.trivialCharacter (G := G))
      have hleft : ∀ n : ℕ,
          @inner ℂ (Lp ℂ 2 m) _
            (CompactHaarCharacters.characterLp m
              (CompactHaarCharacters.trivialCharacter (G := G)))
            (CorrelationMean.koopmanIterLp
              (compactGroupHaarEndomorphismSystem m A)
              ⟨(inferInstance : IsProbabilityMeasure m),
                CompactHaarCharacters.haarEndomorphism_measurePreserving
                  m A hA hAsurj⟩ n
              (CompactHaarCharacters.characterLp m
                (CompactHaarCharacters.trivialCharacter (G := G)))) = 1 := by
        intro n
        rw [characterLp_koopman_inner_eq m A hA hAsurj]
        simp [CompactHaarCharacters.characterCompIterate,
          CompactHaarCharacters.trivialCharacter]
      have htarget :
          @inner ℂ (Lp ℂ 2 m) _
              (CompactHaarCharacters.characterLp m
                (CompactHaarCharacters.trivialCharacter (G := G)))
              (CompactHaarCharacters.characterLp m
                (CompactHaarCharacters.trivialCharacter (G := G))) *
            star (@inner ℂ (Lp ℂ 2 m) _
              (CompactHaarCharacters.characterLp m
                (CompactHaarCharacters.trivialCharacter (G := G)))
              (CompactHaarCharacters.characterLp m
                (CompactHaarCharacters.trivialCharacter (G := G)))) = 1 := by
        rw [heinner, star_one, mul_one]
      rw [htarget]
      convert
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1)) using 1
      funext n
      exact hleft n
    · have hχne :
          χ.toFun ≠
            (CompactHaarCharacters.trivialCharacter (G := G)).toFun := by
        intro h
        apply hχtriv
        intro x
        exact congrFun h x
      have hleft : ∀ n : ℕ,
          @inner ℂ (Lp ℂ 2 m) _
            (CompactHaarCharacters.characterLp m χ)
            (CorrelationMean.koopmanIterLp
              (compactGroupHaarEndomorphismSystem m A)
              ⟨(inferInstance : IsProbabilityMeasure m),
                CompactHaarCharacters.haarEndomorphism_measurePreserving
                  m A hA hAsurj⟩ n
              (CompactHaarCharacters.characterLp m ψ)) = 0 := by
        intro n
        rw [hformula]
        rw [if_neg]
        simpa [CompactHaarCharacters.characterCompIterate, hψfun]
      have heχ := CompactHaarCharacters.characterLp_inner_eq m
        (CompactHaarCharacters.trivialCharacter (G := G)) χ
      have hee := CompactHaarCharacters.characterLp_inner_eq m
        (CompactHaarCharacters.trivialCharacter (G := G))
        (CompactHaarCharacters.trivialCharacter (G := G))
      simp only [hχne.symm, if_false] at heχ
      rw [if_pos rfl] at hee
      have htarget :
          @inner ℂ (Lp ℂ 2 m) _
              (CompactHaarCharacters.characterLp m
                (CompactHaarCharacters.trivialCharacter (G := G)))
              (CompactHaarCharacters.characterLp m ψ) *
            star (@inner ℂ (Lp ℂ 2 m) _
              (CompactHaarCharacters.characterLp m
                (CompactHaarCharacters.trivialCharacter (G := G)))
              (CompactHaarCharacters.characterLp m χ)) = 0 := by
        rw [hψLp, hee, heχ, star_zero, mul_zero]
      rw [htarget]
      convert
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0)) using 1
      funext n
      exact hleft n
  · have horbitinj :=
      CompactHaarCharacters.characterOrbit_toFun_injective
        A hA hAsurj ψ hψtriv haperiodic
    have heψ := CompactHaarCharacters.characterLp_inner_eq m
      (CompactHaarCharacters.trivialCharacter (G := G)) ψ
    have htrivψ :
        (CompactHaarCharacters.trivialCharacter (G := G)).toFun ≠
          ψ.toFun := by
      intro h
      apply hψtriv
      intro x
      exact (congrFun h x).symm
    rw [if_neg htrivψ] at heψ
    have htarget :
        @inner ℂ (Lp ℂ 2 m) _
            (CompactHaarCharacters.characterLp m
              (CompactHaarCharacters.trivialCharacter (G := G)))
            (CompactHaarCharacters.characterLp m ψ) *
          star (@inner ℂ (Lp ℂ 2 m) _
            (CompactHaarCharacters.characterLp m
              (CompactHaarCharacters.trivialCharacter (G := G)))
            (CompactHaarCharacters.characterLp m χ)) = 0 := by
      rw [heψ, zero_mul]
    rw [htarget]
    by_cases hex : ∃ n : ℕ, χ.toFun =
        (CompactHaarCharacters.characterCompIterate A hA ψ n).toFun
    · obtain ⟨N, hN⟩ := hex
      apply tendsto_atTop_of_eventually_const (i₀ := N + 1)
      intro n hn
      rw [hformula, if_neg]
      intro h
      have := horbitinj (hN.symm.trans h)
      omega
    · have hall : ∀ n : ℕ,
          @inner ℂ (Lp ℂ 2 m) _
            (CompactHaarCharacters.characterLp m χ)
            (CorrelationMean.koopmanIterLp
              (compactGroupHaarEndomorphismSystem m A)
              ⟨(inferInstance : IsProbabilityMeasure m),
                CompactHaarCharacters.haarEndomorphism_measurePreserving
                  m A hA hAsurj⟩ n
              (CompactHaarCharacters.characterLp m ψ)) = 0 := by
        intro n
        rw [hformula, if_neg]
        exact fun h => hex ⟨n, h⟩
      simp [hall]

/-- Character convergence extends, by the Peter--Weyl dense span and the
uniform isometry bound for Koopman iterates, to every pair of `L²` vectors. -/
lemma lp_correlation_tendsto_of_aperiodic_characters
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (A : G →* G) (hA : Continuous A) (hAsurj : Function.Surjective A)
    (haperiodic : ∀ ψ : Character G,
      (∃ n : ℕ, 0 < n ∧
        (fun x => ψ.toFun ((A : G → G)^[n] x)) = ψ.toFun) →
      ∀ x, ψ.toFun x = 1) :
    let M := compactGroupHaarEndomorphismSystem m A
    let hM : Chapter01.IsMeasurePreservingSystem M :=
      ⟨(inferInstance : IsProbabilityMeasure m),
        CompactHaarCharacters.haarEndomorphism_measurePreserving
          m A hA hAsurj⟩
    let e := CompactHaarCharacters.characterLp m
      (CompactHaarCharacters.trivialCharacter (G := G))
    ∀ F H : Lp ℂ 2 m,
      Tendsto
        (fun n => @inner ℂ (Lp ℂ 2 m) _ H
          (CorrelationMean.koopmanIterLp M hM n F))
        atTop
        (nhds (@inner ℂ (Lp ℂ 2 m) _ e F *
          star (@inner ℂ (Lp ℂ 2 m) _ e H))) := by
  dsimp only
  let M := compactGroupHaarEndomorphismSystem m A
  let hM : Chapter01.IsMeasurePreservingSystem M :=
    ⟨(inferInstance : IsProbabilityMeasure m),
      CompactHaarCharacters.haarEndomorphism_measurePreserving
        m A hA hAsurj⟩
  let H := Lp ℂ 2 m
  let e : H := CompactHaarCharacters.characterLp m
    (CompactHaarCharacters.trivialCharacter (G := G))
  let S : Submodule ℂ H :=
    Submodule.span ℂ
      (Set.range (CompactHaarCharacters.characterLp m))
  have hdense : Dense (S : Set H) := by
    exact MathCopilotPrior.compactAbelian_character_span_dense m
  have hfirstGenerator (χ : Character G) :
      ∀ F ∈ S,
        Tendsto
          (fun n => @inner ℂ H _
            (CompactHaarCharacters.characterLp m χ)
            (CorrelationMean.koopmanIterLp M hM n F))
          atTop
          (nhds (@inner ℂ H _ e F *
            star (@inner ℂ H _ e
              (CompactHaarCharacters.characterLp m χ)))) := by
    intro F hF
    change F ∈ Submodule.span ℂ
      (Set.range (CompactHaarCharacters.characterLp m)) at hF
    induction hF using Submodule.span_induction with
    | mem F hF =>
        obtain ⟨ψ, rfl⟩ := hF
        simpa [M, hM, e, H] using
          character_pair_correlation_tendsto
            m A hA hAsurj haperiodic χ ψ
    | zero =>
        convert
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0)) using 1
        · funext n
          rw [map_zero, inner_zero_right]
        · rw [inner_zero_right, zero_mul]
    | add X Y hX hY ihX ihY =>
        have hadd := ihX.add ihY
        convert hadd using 1
        · funext n
          rw [map_add, inner_add_right]
        · rw [inner_add_right, add_mul]
    | smul c X hX ih =>
        have hscaled := ih.const_mul c
        convert hscaled using 1
        · funext n
          rw [map_smul, inner_smul_right]
        · rw [inner_smul_right]
          ring_nf
  have hspan :
      ∀ F ∈ S, ∀ K ∈ S,
        Tendsto
          (fun n => @inner ℂ H _ K
            (CorrelationMean.koopmanIterLp M hM n F))
          atTop
          (nhds (@inner ℂ H _ e F *
            star (@inner ℂ H _ e K))) := by
    intro F hF K hK
    change K ∈ Submodule.span ℂ
      (Set.range (CompactHaarCharacters.characterLp m)) at hK
    induction hK using Submodule.span_induction with
    | mem K hK =>
        obtain ⟨χ, rfl⟩ := hK
        exact hfirstGenerator χ F hF
    | zero =>
        convert
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0)) using 1
        · funext n
          rw [inner_zero_left]
        · rw [inner_zero_right, star_zero, mul_zero]
    | add X Y hX hY ihX ihY =>
        have hadd := ihX.add ihY
        convert hadd using 1
        · funext n
          rw [inner_add_left]
        · congr 1
          rw [inner_add_right, star_add]
          ring
    | smul c X hX ih =>
        have hscaled := ih.const_mul (star c)
        convert hscaled using 1
        · funext n
          rw [inner_smul_left]
          simp only [starRingEnd_apply]
        · congr 1
          rw [inner_smul_right, star_mul]
          ring
  have hfirst (K : H) (hK : K ∈ S) :
      ∀ F : H,
        Tendsto
          (fun n => @inner ℂ H _ K
            (CorrelationMean.koopmanIterLp M hM n F))
          atTop
          (nhds (@inner ℂ H _ e F *
            star (@inner ℂ H _ e K))) := by
    let C : ℝ := ‖K‖ + ‖e‖ ^ 2 * ‖K‖
    apply CorrelationMean.tendsto_of_dense_of_uniform_dist hdense
      (fun n F => @inner ℂ H _ K
        (CorrelationMean.koopmanIterLp M hM n F))
      (fun F => @inner ℂ H _ e F * star (@inner ℂ H _ e K)) C
    · dsimp [C]
      positivity
    · intro n X Y
      rw [dist_eq_norm, dist_eq_norm]
      have hinner :
          @inner ℂ H _ K
              (CorrelationMean.koopmanIterLp M hM n X) -
            @inner ℂ H _ K
              (CorrelationMean.koopmanIterLp M hM n Y) =
          @inner ℂ H _ K
            (CorrelationMean.koopmanIterLp M hM n (X - Y)) := by
        rw [map_sub]
        exact (inner_sub_right K _ _).symm
      rw [hinner]
      calc
        ‖@inner ℂ H _ K
            (CorrelationMean.koopmanIterLp M hM n (X - Y))‖ ≤
            ‖K‖ * ‖CorrelationMean.koopmanIterLp M hM n (X - Y)‖ :=
          norm_inner_le_norm _ _
        _ = ‖K‖ * ‖X - Y‖ := by rw [LinearIsometry.norm_map]
        _ ≤ C * ‖X - Y‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          dsimp [C]
          exact le_add_of_nonneg_right
            (mul_nonneg (sq_nonneg _) (norm_nonneg _))
    · intro X Y
      rw [dist_eq_norm, dist_eq_norm]
      have hone : ‖@inner ℂ H _ e (X - Y)‖ ≤ ‖e‖ * ‖X - Y‖ :=
        norm_inner_le_norm e (X - Y)
      have hKinner : ‖@inner ℂ H _ e K‖ ≤ ‖e‖ * ‖K‖ :=
        norm_inner_le_norm e K
      calc
        ‖@inner ℂ H _ e X * star (@inner ℂ H _ e K) -
            @inner ℂ H _ e Y * star (@inner ℂ H _ e K)‖ =
            ‖@inner ℂ H _ e (X - Y)‖ * ‖@inner ℂ H _ e K‖ := by
              rw [← sub_mul, inner_sub_right, norm_mul, norm_star]
        _ ≤ (‖e‖ * ‖X - Y‖) * (‖e‖ * ‖K‖) :=
          mul_le_mul hone hKinner (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ C * ‖X - Y‖ := by
          dsimp [C]
          nlinarith [norm_nonneg K, norm_nonneg e, norm_nonneg (X - Y)]
    · intro F hFS
      exact hspan F hFS K hK
  intro F
  let C : ℝ := ‖F‖ + ‖e‖ ^ 2 * ‖F‖
  apply CorrelationMean.tendsto_of_dense_of_uniform_dist hdense
    (fun n K => @inner ℂ H _ K
      (CorrelationMean.koopmanIterLp M hM n F))
    (fun K => @inner ℂ H _ e F * star (@inner ℂ H _ e K)) C
  · dsimp [C]
    positivity
  · intro n X Y
    rw [dist_eq_norm, dist_eq_norm]
    have hinner :
        @inner ℂ H _ X
            (CorrelationMean.koopmanIterLp M hM n F) -
          @inner ℂ H _ Y
            (CorrelationMean.koopmanIterLp M hM n F) =
        @inner ℂ H _ (X - Y)
          (CorrelationMean.koopmanIterLp M hM n F) :=
      (inner_sub_left X Y _).symm
    rw [hinner]
    calc
      ‖@inner ℂ H _ (X - Y)
          (CorrelationMean.koopmanIterLp M hM n F)‖ ≤
          ‖X - Y‖ * ‖CorrelationMean.koopmanIterLp M hM n F‖ :=
        norm_inner_le_norm _ _
      _ = ‖X - Y‖ * ‖F‖ := by rw [LinearIsometry.norm_map]
      _ ≤ C * ‖X - Y‖ := by
        rw [mul_comm]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        dsimp [C]
        exact le_add_of_nonneg_right
          (mul_nonneg (sq_nonneg _) (norm_nonneg _))
  · intro X Y
    rw [dist_eq_norm, dist_eq_norm]
    have hFinner : ‖@inner ℂ H _ e F‖ ≤ ‖e‖ * ‖F‖ :=
      norm_inner_le_norm e F
    have hone : ‖@inner ℂ H _ e (X - Y)‖ ≤ ‖e‖ * ‖X - Y‖ :=
      norm_inner_le_norm e (X - Y)
    calc
      ‖@inner ℂ H _ e F * star (@inner ℂ H _ e X) -
          @inner ℂ H _ e F * star (@inner ℂ H _ e Y)‖ =
          ‖@inner ℂ H _ e F‖ * ‖@inner ℂ H _ e (X - Y)‖ := by
            rw [← mul_sub, norm_mul]
            congr 1
            calc
              ‖star (@inner ℂ H _ e X) - star (@inner ℂ H _ e Y)‖ =
                  ‖@inner ℂ H _ e X - @inner ℂ H _ e Y‖ := by
                rw [← star_sub, norm_star]
              _ = ‖@inner ℂ H _ e (X - Y)‖ := by
                rw [inner_sub_right]
      _ ≤ (‖e‖ * ‖F‖) * (‖e‖ * ‖X - Y‖) :=
        mul_le_mul hFinner hone (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ C * ‖X - Y‖ := by
        dsimp [C]
        nlinarith [norm_nonneg F, norm_nonneg e, norm_nonneg (X - Y)]
  · intro K hK
    exact hfirst K hK F

/-- The character criterion implies strong mixing for a surjective
endomorphism of a compact metrizable abelian group with normalized Haar
measure. -/
theorem strongMixing_of_aperiodic_characters
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (A : G →* G) (hA : Continuous A) (hAsurj : Function.Surjective A)
    (haperiodic : ∀ ψ : Character G,
      (∃ n : ℕ, 0 < n ∧
        (fun x => ψ.toFun ((A : G → G)^[n] x)) = ψ.toFun) →
      ∀ x, ψ.toFun x = 1) :
    IsStrongMixing (compactGroupHaarEndomorphismSystem m A) := by
  let M := compactGroupHaarEndomorphismSystem m A
  let hM : Chapter01.IsMeasurePreservingSystem M :=
    ⟨(inferInstance : IsProbabilityMeasure m),
      CompactHaarCharacters.haarEndomorphism_measurePreserving
        m A hA hAsurj⟩
  rw [CorrelationMean.strongMixing_iff_functionCorrelations M hM]
  intro f g hf hg
  let F : Lp ℂ 2 m := hf.toLp f
  let K : Lp ℂ 2 m := hg.toLp g
  let e : Lp ℂ 2 m := CompactHaarCharacters.characterLp m
    (CompactHaarCharacters.trivialCharacter (G := G))
  have heq : e = CorrelationMean.oneLp M hM := by
    apply Lp.ext
    have hecoe := CompactHaarCharacters.characterLp_coeFn m
      (CompactHaarCharacters.trivialCharacter (G := G))
    have hone :
        (CorrelationMean.oneLp M hM : G → ℂ) =ᵐ[m] fun _ => 1 := by
      exact (memLp_const (p := (2 : ENNReal)) (c := (1 : ℂ))).coeFn_toLp
    filter_upwards [hecoe, hone] with x hex honex
    change (e : G → ℂ) x =
      (CorrelationMean.oneLp M hM : G → ℂ) x
    rw [hex, honex]
    rfl
  have hLp :=
    lp_correlation_tendsto_of_aperiodic_characters
      m A hA hAsurj haperiodic F K
  have hseq (n : ℕ) :
      @inner ℂ (Lp ℂ 2 m) _ K
          (CorrelationMean.koopmanIterLp M hM n F) =
        functionCorrelation M f g n := by
    dsimp only [F, K]
    rw [CorrelationMean.koopmanIterLp_apply_toLp]
    exact (CorrelationMean.functionCorrelation_eq_innerLp
      M hM f g hf hg n).symm
  have hfint :
      (∫ x, (F : G → ℂ) x ∂m) = ∫ x, f x ∂m := by
    exact integral_congr_ae hf.coeFn_toLp
  have hgint :
      (∫ x, (K : G → ℂ) x ∂m) = ∫ x, g x ∂m := by
    exact integral_congr_ae hg.coeFn_toLp
  have htarget :
      @inner ℂ (Lp ℂ 2 m) _ e F *
          star (@inner ℂ (Lp ℂ 2 m) _ e K) =
        productOfMeans M f g := by
    rw [heq, ← CorrelationMean.integral_eq_inner_oneLp,
      ← CorrelationMean.integral_eq_inner_oneLp]
    change (∫ x : G, (F : G → ℂ) x ∂m) *
        star (∫ x : G, (K : G → ℂ) x ∂m) =
      (∫ x : G, f x ∂m) * star (∫ x : G, g x ∂m)
    rw [hfint, hgint]
  convert hLp using 1
  · funext n
    exact (hseq n).symm
  · rw [htarget]

end CompactHaarMixing
end Chapter02
