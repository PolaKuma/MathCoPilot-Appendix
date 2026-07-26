import Chapter04.Descriptive.DynamicsSpatial

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter04.LtwoPullback

universe u v

def pullback {M : System.{u}} {N : System.{v}}
    (φ : M.X → N.X) (f : N.X → ℂ) : M.X → ℂ :=
  fun x => f (φ x)

/-- A global measure-preserving conjugacy induces, by pullback, the same
operator required in both halves of an algebraic spectral isomorphism. -/
theorem isAlgebraicSpectralIsomorphism_of_global_realizers
    (M : System.{u}) (N : System.{v})
    (φ : M.X → N.X) (ψ : N.X → M.X)
    (hφmp : MeasurePreserving φ M.μ N.μ)
    (hψmp : MeasurePreserving ψ N.μ M.μ)
    (hψφ : (fun x => ψ (φ x)) =ᵐ[M.μ] id)
    (hφψ : (fun y => φ (ψ y)) =ᵐ[N.μ] id)
    (hint : (fun x => φ (M.T x)) =ᵐ[M.μ] fun x => N.T (φ x)) :
    IsAlgebraicSpectralIsomorphism M N := by
  let W : (N.X → ℂ) → (M.X → ℂ) := pullback φ
  have hae (f g : N.X → ℂ) (hfg : f =ᵐ[N.μ] g) :
      W f =ᵐ[M.μ] W g := by
    exact hφmp.quasiMeasurePreserving.ae_eq_comp hfg
  have hmem (p : ENNReal) (f : N.X → ℂ) (hf : MemLp f p N.μ) :
      MemLp (W f) p M.μ := by
    exact hf.comp_measurePreserving hφmp
  have hnorm (p : ENNReal) (f : N.X → ℂ) (hf : MemLp f p N.μ) :
      eLpNorm (W f) p M.μ = eLpNorm f p N.μ := by
    exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hφmp
  have hdense (h : M.X → ℂ) (hh : MemLp h 2 M.μ)
      (ε : ℝ) (hε : 0 < ε) :
      ∃ f : N.X → ℂ, MemLp f 2 N.μ ∧
        eLpNorm (fun x => h x - W f x) 2 M.μ < ENNReal.ofReal ε := by
    refine ⟨fun y => h (ψ y), hh.comp_measurePreserving hψmp, ?_⟩
    have hz : (fun x => h x - W (fun y => h (ψ y)) x) =ᵐ[M.μ]
        fun _ => (0 : ℂ) := by
      filter_upwards [hψφ] with x hx
      simp [W, pullback, hx]
    rw [eLpNorm_congr_ae hz]
    simpa using ENNReal.ofReal_pos.mpr hε
  have htopSurj (h : M.X → ℂ) (hh : MemLp h ⊤ M.μ) :
      ∃ f : N.X → ℂ, MemLp f ⊤ N.μ ∧ W f =ᵐ[M.μ] h := by
    refine ⟨fun y => h (ψ y), hh.comp_measurePreserving hψmp, ?_⟩
    filter_upwards [hψφ] with x hx
    simp [W, pullback, hx]
  refine ⟨W, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro f g _hf _hg hfg
      exact hae f g hfg
    · intro f g _hf _hg
      exact Filter.Eventually.of_forall fun _ => rfl
    · intro c f _hf
      exact Filter.Eventually.of_forall fun _ => rfl
    · intro f hf
      exact ⟨hmem 2 f hf, hnorm 2 f hf⟩
    · exact hdense
    · intro f _hf
      filter_upwards [hint] with x hx
      simp [W, pullback, Chapter01.koopman, hx]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro f g _hf _hg hfg
      exact hae f g hfg
    · intro f g _hf _hg
      exact Filter.Eventually.of_forall fun _ => rfl
    · intro c f _hf
      exact Filter.Eventually.of_forall fun _ => rfl
    · intro f hf
      exact ⟨hmem 2 f hf, hnorm 2 f hf⟩
    · exact hdense
    · intro f hf
      exact hmem ⊤ f hf
    · exact htopSurj
    · exact Filter.Eventually.of_forall fun _ => rfl
    · intro f g _hf _hg
      exact Filter.Eventually.of_forall fun _ => rfl

/-- On Lebesgue probability systems, an abstract measure-algebra conjugacy has
global spatial realizers, so its pullback is an algebraic spectral
isomorphism. -/
theorem of_lebesgue_system_conjugacy
    (M : System.{u}) (N : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (hMLeb : IsLebesgueProbabilitySpace M.toProbabilitySpace)
    (hNLeb : IsLebesgueProbabilitySpace N.toProbabilitySpace)
    (hconj : IsSystemConjugate M N) :
    IsAlgebraicSpectralIsomorphism M N := by
  obtain ⟨φ, ψ, _hφm, _hψm, hφmp, hψmp, hψφ, hφψ, hint⟩ :=
    DynamicsSpatial.global_realizers_of_system_conjugacy
      M N hM hN hMLeb hNLeb hconj
  exact isAlgebraicSpectralIsomorphism_of_global_realizers
    M N φ ψ hφmp hψmp hψφ hφψ hint

end Chapter04.LtwoPullback
