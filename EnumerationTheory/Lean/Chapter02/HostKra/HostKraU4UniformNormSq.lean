import Chapter02.HostKra.HostKraU3NonergodicFourTerm
import Chapter02.HostKra.HostKraU4CartesianProduct

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HostKraU4UniformNormSq

universe u

open HostKraCubeSeminorm

/-- An ergodic base-system `U⁴`-null last slot forces translated-uniform
mean-square decay of every bounded four-term scalar progression.  The
Cartesian product itself is not assumed ergodic. -/
theorem uniform_norm_sq_of_hasZeroHostKraU4
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (hf₀ : MemLp f₀ ⊤ M.μ)
    (hf₁ : MemLp f₁ ⊤ M.μ)
    (hf₂ : MemLp f₂ ⊤ M.μ)
    (hf₃ : MemLp f₃ ⊤ M.μ)
    (hzero : HasZeroHostKraU4 M hM f₃ hf₃) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        cesaroAverage
          (fun n ↦
            ‖∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
              f₀ f₁ f₂ f₃ (i + n) x ∂M.μ‖ ^ 2) N < ε := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let P := MultipleKhintchineCartesian.productSystem M M
  let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
  let sq : (M.X → ℂ) → (M.X × M.X → ℂ) :=
    MultipleKhintchineCartesian.cartesianSquare
  have hsq (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
      MemLp (sq f) ⊤ P.μ := by
    simpa only [P, sq, MultipleKhintchineCartesian.productSystem,
      MultipleKhintchineCartesian.cartesianSquare] using
      (hf.star.comp_snd M.μ).mul (r := ⊤) (hf.comp_fst M.μ)
  letI : StandardBorelSpace P.X := by
    dsimp only [P, MultipleKhintchineCartesian.productSystem]
    infer_instance
  have hzeroP :
      HasZeroHostKraU3 P hP (sq f₃) (hsq f₃ hf₃) := by
    exact
      Chapter02.HostKraU4CartesianProduct.cartesianSquare_hasZeroHostKraU3_on_product_of_hasZeroHostKraU4
        M hM hErg f₃ hf₃ hzero
  have hdecay :=
    Chapter02.HostKraU3NonergodicFourTerm.hasUniformFourTermIntegralDecay_of_hasZeroHostKraU3
      P hP (sq f₀) (sq f₁) (sq f₂) (sq f₃)
      (hsq f₀ hf₀) (hsq f₁ hf₁) (hsq f₂ hf₂) (hsq f₃ hf₃) hzeroP
  intro ε hε
  filter_upwards [hdecay ε hε] with N hN
  intro i
  rw [show cesaroAverage
      (fun n ↦
        ‖∫ x, MultipleKhintchineCartesian.quadrupleIntegrand M
          f₀ f₁ f₂ f₃ (i + n) x ∂M.μ‖ ^ 2) N =
      cesaroAverage
        (fun n ↦
          (∫ p, MultipleKhintchineCartesian.quadrupleIntegrand P
            (sq f₀) (sq f₁) (sq f₂) (sq f₃) (i + n) p ∂P.μ).re) N by
    unfold cesaroAverage
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    simpa only [P, sq] using
      MultipleKhintchineCartesian.norm_integral_quadrupleIntegrand_sq
        M hM f₀ f₁ f₂ f₃ (i + n)]
  let z : ℂ := (((N + 1 : ℕ) : ℂ)⁻¹) *
    ∑ n ∈ Finset.range (N + 1),
      ∫ p, MultipleKhintchineCartesian.quadrupleIntegrand P
        (sq f₀) (sq f₁) (sq f₂) (sq f₃) (i + n) p ∂P.μ
  calc
    cesaroAverage
        (fun n ↦
          (∫ p, MultipleKhintchineCartesian.quadrupleIntegrand P
            (sq f₀) (sq f₁) (sq f₂) (sq f₃) (i + n) p ∂P.μ).re) N =
      z.re := by
        unfold cesaroAverage z
        simp only [Complex.mul_re, Complex.inv_re, Complex.inv_im]
        simp only [Complex.natCast_re, Complex.natCast_im,
          Complex.normSq_natCast, zero_div, neg_zero, zero_mul, sub_zero]
        have hsum_re :
            (∑ n ∈ Finset.range (N + 1),
              ∫ p, MultipleKhintchineCartesian.quadrupleIntegrand P
                (sq f₀) (sq f₁) (sq f₂) (sq f₃)
                (i + n) p ∂P.μ).re =
              ∑ n ∈ Finset.range (N + 1),
                (∫ p, MultipleKhintchineCartesian.quadrupleIntegrand P
                  (sq f₀) (sq f₁) (sq f₂) (sq f₃)
                  (i + n) p ∂P.μ).re := by
          change Complex.reAddGroupHom
            (∑ n ∈ Finset.range (N + 1),
              ∫ p, MultipleKhintchineCartesian.quadrupleIntegrand P
                (sq f₀) (sq f₁) (sq f₂) (sq f₃)
                (i + n) p ∂P.μ) = _
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro n hn
          rfl
        rw [hsum_re]
        have hNR : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
        field_simp
    _ ≤ ‖z‖ := Complex.re_le_norm z
    _ < ε := hN i

end Chapter02.HostKraU4UniformNormSq
