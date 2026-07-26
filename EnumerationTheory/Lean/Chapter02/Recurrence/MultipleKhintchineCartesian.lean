import Chapter02.Common
import Chapter02.Recurrence.MultipleKhintchineSyndetic
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open Classical MeasureTheory

namespace Chapter02.MultipleKhintchineCartesian

universe u v

/-- The product probability system used in BHK's Cartesian-square
mean-square argument.  It is kept in a low-dependency module so that no
unfinished Chapter09 theorem enters the proof closure. -/
def productSystem (M : System.{u}) (N : System.{v}) : System where
  X := M.X × N.X
  measurableSpace := inferInstance
  μ := M.μ.prod N.μ
  T := fun p ↦ (M.T p.1, N.T p.2)

lemma productSystem_mps
    (M : System.{u}) (N : System.{v})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N) :
    Chapter01.IsMeasurePreservingSystem (productSystem M N) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : IsProbabilityMeasure N.μ := hN.1
  constructor
  · change IsProbabilityMeasure (M.μ.prod N.μ)
    infer_instance
  · simpa [productSystem, Prod.map] using hM.2.prod hN.2

lemma product_iter
    (M : System.{u}) (N : System.{v}) (n : ℕ) (p : M.X × N.X) :
    (((productSystem M N).T^[n]) p) =
      ((M.T^[n]) p.1, (N.T^[n]) p.2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih]
      rfl

/-- Tensor with the conjugate copy, so its integral is the squared modulus
of the original integral. -/
def cartesianSquare (f : M → ℂ) : M × M → ℂ :=
  fun p ↦ f p.1 * (starRingEnd ℂ) (f p.2)

lemma integral_cartesianSquare
    {M : Type u} [MeasurableSpace M]
    (μ : Measure M) [SFinite μ] (f : M → ℂ) :
    ∫ p, cartesianSquare f p ∂μ.prod μ =
      (∫ x, f x ∂μ) * (starRingEnd ℂ) (∫ x, f x ∂μ) := by
  have hprod :=
    integral_prod_mul (μ := μ) (ν := μ)
      f (fun y ↦ (starRingEnd ℂ) (f y))
  rw [show (fun p ↦ cartesianSquare f p) =
      (fun p : M × M ↦
        f p.1 * (fun y ↦ (starRingEnd ℂ) (f y)) p.2) by rfl]
  rw [hprod]
  rw [integral_conj]

lemma re_integral_cartesianSquare_eq_norm_sq
    {M : Type u} [MeasurableSpace M]
    (μ : Measure M) [SFinite μ] (f : M → ℂ) :
    (∫ p, cartesianSquare f p ∂μ.prod μ).re =
      ‖∫ x, f x ∂μ‖ ^ 2 := by
  rw [integral_cartesianSquare]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact Complex.ofReal_re _

/-- The three-term progression integrand before integration. -/
def tripleIntegrand
    (M : System.{u}) (f₀ f₁ f₂ : M.X → ℂ) (n : ℕ) (x : M.X) : ℂ :=
  f₀ x * f₁ ((M.T^[n]) x) * f₂ ((M.T^[2 * n]) x)

/-- Cartesian squaring turns a scalar triple progression into the same
triple progression on the product system, with tensor-squared functions.
This is the algebraic heart of BHK's mean-square reduction. -/
lemma cartesianSquare_tripleIntegrand
    (M : System.{u}) (f₀ f₁ f₂ : M.X → ℂ) (n : ℕ)
    (p : M.X × M.X) :
    cartesianSquare (tripleIntegrand M f₀ f₁ f₂ n) p =
      tripleIntegrand (productSystem M M)
        (cartesianSquare f₀) (cartesianSquare f₁) (cartesianSquare f₂) n p := by
  simp only [cartesianSquare, tripleIntegrand, product_iter, map_mul]
  ring

/-- The squared modulus of a triple-correlation integral is the real part
of the corresponding product-system triple integral. -/
lemma norm_integral_tripleIntegrand_sq
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f₀ f₁ f₂ : M.X → ℂ) (n : ℕ) :
    ‖∫ x, tripleIntegrand M f₀ f₁ f₂ n x ∂M.μ‖ ^ 2 =
      (∫ p,
        tripleIntegrand (productSystem M M)
          (cartesianSquare f₀) (cartesianSquare f₁)
          (cartesianSquare f₂) n p ∂(productSystem M M).μ).re := by
  letI : IsProbabilityMeasure M.μ := hM.1
  rw [← re_integral_cartesianSquare_eq_norm_sq M.μ
    (tripleIntegrand M f₀ f₁ f₂ n)]
  apply congrArg Complex.re
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (cartesianSquare_tripleIntegrand M f₀ f₁ f₂ n)

/-- The exact product-system cancellation obligation produced by the
Cartesian-square reduction. -/
def CartesianTripleUniformZero
    (M : System.{u}) (f₀ f₁ f₂ : M.X → ℂ) : Prop :=
  ∀ ε > 0, ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ℕ,
    cesaroAverage
      (fun n ↦
        (∫ p,
          tripleIntegrand (productSystem M M)
            (cartesianSquare f₀) (cartesianSquare f₁)
            (cartesianSquare f₂) (i + n) p
          ∂(productSystem M M).μ).re) N < ε

/-- If the Cartesian-square triple correlations tend uniformly to zero on
translated intervals, then the real parts of the original triple
correlations are zero in BHK uniform density. -/
theorem uniformDensity_re_integral_triple_of_cartesian_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f₀ f₁ f₂ : M.X → ℂ)
    (hzero :
      ∀ ε > 0, ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ℕ,
        cesaroAverage
          (fun n ↦
            (∫ p,
              tripleIntegrand (productSystem M M)
                (cartesianSquare f₀) (cartesianSquare f₁)
                (cartesianSquare f₂) (i + n) p
              ∂(productSystem M M).μ).re) N < ε) :
    MultipleKhintchineSyndetic.TendsToZeroInUniformDensity
      (fun n ↦ (∫ x, tripleIntegrand M f₀ f₁ f₂ n x ∂M.μ).re) := by
  apply MultipleKhintchineSyndetic.tendsToZeroInUniformDensity_of_meanSquare
  intro ε hε
  filter_upwards [hzero ε hε] with N hN
  intro i
  have hterm (n : ℕ) :
      ((∫ x, tripleIntegrand M f₀ f₁ f₂ (i + n) x ∂M.μ).re) ^ 2 ≤
        (∫ p,
          tripleIntegrand (productSystem M M)
            (cartesianSquare f₀) (cartesianSquare f₁)
            (cartesianSquare f₂) (i + n) p
          ∂(productSystem M M).μ).re := by
    calc
      ((∫ x, tripleIntegrand M f₀ f₁ f₂ (i + n) x ∂M.μ).re) ^ 2 ≤
          ‖∫ x, tripleIntegrand M f₀ f₁ f₂ (i + n) x ∂M.μ‖ ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _)
            (norm_nonneg _)).2 (Complex.abs_re_le_norm _)
      _ = (∫ p,
          tripleIntegrand (productSystem M M)
            (cartesianSquare f₀) (cartesianSquare f₁)
            (cartesianSquare f₂) (i + n) p
          ∂(productSystem M M).μ).re :=
        norm_integral_tripleIntegrand_sq M hM f₀ f₁ f₂ (i + n)
  have havg :
      cesaroAverage
          (fun n ↦
            ((∫ x, tripleIntegrand M f₀ f₁ f₂ (i + n) x ∂M.μ).re) ^ 2) N ≤
        cesaroAverage
          (fun n ↦
            (∫ p,
              tripleIntegrand (productSystem M M)
                (cartesianSquare f₀) (cartesianSquare f₁)
                (cartesianSquare f₂) (i + n) p
              ∂(productSystem M M).μ).re) N := by
    unfold cesaroAverage
    gcongr with n hn
    exact hterm n
  exact lt_of_le_of_lt havg (hN i)

/-- The four-term progression integrand before integration. -/
def quadrupleIntegrand
    (M : System.{u}) (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (n : ℕ) (x : M.X) : ℂ :=
  f₀ x * f₁ ((M.T^[n]) x) * f₂ ((M.T^[2 * n]) x) *
    f₃ ((M.T^[3 * n]) x)

lemma cartesianSquare_quadrupleIntegrand
    (M : System.{u}) (f₀ f₁ f₂ f₃ : M.X → ℂ) (n : ℕ)
    (p : M.X × M.X) :
    cartesianSquare (quadrupleIntegrand M f₀ f₁ f₂ f₃ n) p =
      quadrupleIntegrand (productSystem M M)
        (cartesianSquare f₀) (cartesianSquare f₁)
        (cartesianSquare f₂) (cartesianSquare f₃) n p := by
  simp only [cartesianSquare, quadrupleIntegrand, product_iter, map_mul]
  ring

/-- The squared modulus of a four-term scalar correlation is the real part
of the corresponding four-term correlation on the Cartesian square. -/
lemma norm_integral_quadrupleIntegrand_sq
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f₀ f₁ f₂ f₃ : M.X → ℂ) (n : ℕ) :
    ‖∫ x, quadrupleIntegrand M f₀ f₁ f₂ f₃ n x ∂M.μ‖ ^ 2 =
      (∫ p,
        quadrupleIntegrand (productSystem M M)
          (cartesianSquare f₀) (cartesianSquare f₁)
          (cartesianSquare f₂) (cartesianSquare f₃) n p
        ∂(productSystem M M).μ).re := by
  letI : IsProbabilityMeasure M.μ := hM.1
  rw [← re_integral_cartesianSquare_eq_norm_sq M.μ
    (quadrupleIntegrand M f₀ f₁ f₂ f₃ n)]
  apply congrArg Complex.re
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (cartesianSquare_quadrupleIntegrand M f₀ f₁ f₂ f₃ n)

/-- The product-system cancellation obligation for a four-term
progression. -/
def CartesianQuadrupleUniformZero
    (M : System.{u}) (f₀ f₁ f₂ f₃ : M.X → ℂ) : Prop :=
  ∀ ε > 0, ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ℕ,
    cesaroAverage
      (fun n ↦
        (∫ p,
          quadrupleIntegrand (productSystem M M)
            (cartesianSquare f₀) (cartesianSquare f₁)
            (cartesianSquare f₂) (cartesianSquare f₃) (i + n) p
          ∂(productSystem M M).μ).re) N < ε

/-- Cartesian-square cancellation implies BHK uniform-density cancellation
for a four-term scalar progression. -/
theorem uniformDensity_re_integral_quadruple_of_cartesian_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (hzero : CartesianQuadrupleUniformZero M f₀ f₁ f₂ f₃) :
    MultipleKhintchineSyndetic.TendsToZeroInUniformDensity
      (fun n ↦
        (∫ x, quadrupleIntegrand M f₀ f₁ f₂ f₃ n x ∂M.μ).re) := by
  apply MultipleKhintchineSyndetic.tendsToZeroInUniformDensity_of_meanSquare
  intro ε hε
  filter_upwards [hzero ε hε] with N hN
  intro i
  have hterm (n : ℕ) :
      ((∫ x,
        quadrupleIntegrand M f₀ f₁ f₂ f₃ (i + n) x ∂M.μ).re) ^ 2 ≤
        (∫ p,
          quadrupleIntegrand (productSystem M M)
            (cartesianSquare f₀) (cartesianSquare f₁)
            (cartesianSquare f₂) (cartesianSquare f₃) (i + n) p
          ∂(productSystem M M).μ).re := by
    calc
      ((∫ x,
        quadrupleIntegrand M f₀ f₁ f₂ f₃ (i + n) x ∂M.μ).re) ^ 2 ≤
          ‖∫ x,
            quadrupleIntegrand M f₀ f₁ f₂ f₃ (i + n) x ∂M.μ‖ ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2
            (Complex.abs_re_le_norm _)
      _ = (∫ p,
          quadrupleIntegrand (productSystem M M)
            (cartesianSquare f₀) (cartesianSquare f₁)
            (cartesianSquare f₂) (cartesianSquare f₃) (i + n) p
          ∂(productSystem M M).μ).re :=
        norm_integral_quadrupleIntegrand_sq
          M hM f₀ f₁ f₂ f₃ (i + n)
  have havg :
      cesaroAverage
          (fun n ↦
            ((∫ x,
              quadrupleIntegrand M f₀ f₁ f₂ f₃
                (i + n) x ∂M.μ).re) ^ 2) N ≤
        cesaroAverage
          (fun n ↦
            (∫ p,
              quadrupleIntegrand (productSystem M M)
                (cartesianSquare f₀) (cartesianSquare f₁)
                (cartesianSquare f₂) (cartesianSquare f₃) (i + n) p
              ∂(productSystem M M).μ).re) N := by
    unfold cesaroAverage
    gcongr with n hn
    exact hterm n
  exact lt_of_le_of_lt havg (hN i)

end Chapter02.MultipleKhintchineCartesian
