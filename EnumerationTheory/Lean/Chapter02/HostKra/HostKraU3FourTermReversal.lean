import Chapter02.HostKra.HostKraU4Characteristic

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraU3FourTermReversal

universe u

open MultipleKhintchineCartesian

/-- `U³`-nullity is preserved by every forward iterate. -/
theorem hasZeroHostKraU3_comp_iter
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : HostKraCubeSeminorm.HasZeroHostKraU3 M hM f hf)
    (n : ℕ) :
    let hfn : MemLp (f ∘ (M.T^[n])) ⊤ M.μ :=
      hf.comp_measurePreserving (hM.2.iterate n)
    HostKraCubeSeminorm.HasZeroHostKraU3
      M hM (f ∘ (M.T^[n])) hfn := by
  dsimp only
  unfold HostKraCubeSeminorm.HasZeroHostKraU3
  rw [HostKraU4ProgressionDecay.hostKraU3Power_iter M hM f hf n]
  exact hzero

/-- Forward reflection of a four-term progression around the endpoint
`q = r + m`.  Only nonnegative iterates occur: composing the term at
time `r` with `T^[3*m]` reverses the four coefficient slots, at the cost
of fixed forward shifts depending on `q`. -/
lemma quadrupleIntegrand_comp_three_mul_eq_reversed
    (M : System.{u}) (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (r m : ℕ) :
    quadrupleIntegrand M f₀ f₁ f₂ f₃ r ∘ (M.T^[3 * m]) =
      quadrupleIntegrand M
        (f₃ ∘ (M.T^[3 * (r + m)]))
        (f₂ ∘ (M.T^[2 * (r + m)]))
        (f₁ ∘ (M.T^[r + m]))
        f₀ m := by
  funext x
  simp only [quadrupleIntegrand, Function.comp_apply,
    ← Function.iterate_add_apply]
  have h₁ : r + 3 * m = r + m + 2 * m := by omega
  have h₂ : 2 * r + 3 * m = 2 * (r + m) + m := by omega
  have h₃ : 3 * r + 3 * m = 3 * (r + m) := by omega
  rw [h₁, h₂, h₃]
  ring

/-- Integral form of forward reflection.  Measure preservation replaces
the unavailable inverse iterate: the integral at `r` equals the reversed
integral at the forward distance `m` from the right endpoint. -/
theorem integral_quadruple_reversal
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (hf₀ : MemLp f₀ ⊤ M.μ)
    (hf₁ : MemLp f₁ ⊤ M.μ)
    (hf₂ : MemLp f₂ ⊤ M.μ)
    (hf₃ : MemLp f₃ ⊤ M.μ)
    (r m : ℕ) :
    (∫ x, quadrupleIntegrand M f₀ f₁ f₂ f₃ r x ∂M.μ) =
      ∫ x, quadrupleIntegrand M
        (f₃ ∘ (M.T^[3 * (r + m)]))
        (f₂ ∘ (M.T^[2 * (r + m)]))
        (f₁ ∘ (M.T^[r + m]))
        f₀ m x ∂M.μ := by
  let F := quadrupleIntegrand M f₀ f₁ f₂ f₃ r
  have hF : AEStronglyMeasurable F M.μ := by
    exact
      (((hf₀.aestronglyMeasurable.mul
        (hf₁.comp_measurePreserving (hM.2.iterate r)).aestronglyMeasurable).mul
        (hf₂.comp_measurePreserving
          (hM.2.iterate (2 * r))).aestronglyMeasurable).mul
        (hf₃.comp_measurePreserving
          (hM.2.iterate (3 * r))).aestronglyMeasurable)
  calc
    (∫ x, quadrupleIntegrand M f₀ f₁ f₂ f₃ r x ∂M.μ) =
        ∫ x, F ((M.T^[3 * m]) x) ∂M.μ := by
      symm
      exact
        HilbertSchmidtInvariant.integral_comp_measurePreserving
          (M.T^[3 * m]) (hM.2.iterate (3 * m)) F hF
    _ = ∫ x, quadrupleIntegrand M
        (f₃ ∘ (M.T^[3 * (r + m)]))
        (f₂ ∘ (M.T^[2 * (r + m)]))
        (f₁ ∘ (M.T^[r + m]))
        f₀ m x ∂M.μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun x ↦ congrFun
          (quadrupleIntegrand_comp_three_mul_eq_reversed
            M f₀ f₁ f₂ f₃ r m) x)

/-- A whole translated block can be reflected using only forward
iterates.  All fixed shifts on the reversed side depend on the common
right endpoint `i + N`, not on the summation variable. -/
theorem sum_range_integral_quadruple_reversal
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (hf₀ : MemLp f₀ ⊤ M.μ)
    (hf₁ : MemLp f₁ ⊤ M.μ)
    (hf₂ : MemLp f₂ ⊤ M.μ)
    (hf₃ : MemLp f₃ ⊤ M.μ)
    (i N : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
      ∫ x, quadrupleIntegrand M f₀ f₁ f₂ f₃ (i + n) x ∂M.μ) =
      ∑ m ∈ Finset.range (N + 1),
        ∫ x, quadrupleIntegrand M
          (f₃ ∘ (M.T^[3 * (i + N)]))
          (f₂ ∘ (M.T^[2 * (i + N)]))
          (f₁ ∘ (M.T^[i + N]))
          f₀ m x ∂M.μ := by
  rw [← Finset.sum_range_reflect
    (fun n ↦
      ∫ x, quadrupleIntegrand M f₀ f₁ f₂ f₃ (i + n) x ∂M.μ)
    (N + 1)]
  apply Finset.sum_congr rfl
  intro m hm
  have hmN : m ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  have hreflect :=
    integral_quadruple_reversal M hM f₀ f₁ f₂ f₃
      hf₀ hf₁ hf₂ hf₃ (i + (N - m)) m
  simpa only [Nat.add_sub_cancel, Nat.add_assoc,
    Nat.sub_add_cancel hmN] using hreflect

/-- Cesàro form of `sum_range_integral_quadruple_reversal`. -/
theorem cesaroAverage_integral_quadruple_reversal
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (hf₀ : MemLp f₀ ⊤ M.μ)
    (hf₁ : MemLp f₁ ⊤ M.μ)
    (hf₂ : MemLp f₂ ⊤ M.μ)
    (hf₃ : MemLp f₃ ⊤ M.μ)
    (i N : ℕ) :
    (((N + 1 : ℕ) : ℂ)⁻¹) *
        ∑ n ∈ Finset.range (N + 1),
          ∫ x, quadrupleIntegrand M f₀ f₁ f₂ f₃ (i + n) x ∂M.μ =
      (((N + 1 : ℕ) : ℂ)⁻¹) *
        ∑ m ∈ Finset.range (N + 1),
          ∫ x, quadrupleIntegrand M
            (f₃ ∘ (M.T^[3 * (i + N)]))
            (f₂ ∘ (M.T^[2 * (i + N)]))
            (f₁ ∘ (M.T^[i + N]))
            f₀ m x ∂M.μ := by
  rw [sum_range_integral_quadruple_reversal
    M hM f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂ hf₃ i N]

/-- Translated-uniform complex cancellation of a four-term scalar
progression. -/
def HasUniformFourTermIntegralDecay
    (M : System.{u}) (f₀ f₁ f₂ f₃ : M.X → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ℕ,
      ‖(((N + 1 : ℕ) : ℂ)⁻¹) *
        ∑ n ∈ Finset.range (N + 1),
          ∫ x, quadrupleIntegrand M f₀ f₁ f₂ f₃
            (i + n) x ∂M.μ‖ < ε

/-- Endpoint-orbit form of four-term cancellation.  The first slot is
the triply shifted former last slot, and the remaining coefficients are
reversed.  The condition `N ≤ q` says that `q` is the right endpoint of
some translated block of length `N + 1`. -/
def HasUniformReversedOrbitFourTermIntegralDecay
    (M : System.{u}) (f₀ f₁ f₂ f₃ : M.X → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in Filter.atTop, ∀ q : ℕ, N ≤ q →
      ‖(((N + 1 : ℕ) : ℂ)⁻¹) *
        ∑ m ∈ Finset.range (N + 1),
          ∫ x, quadrupleIntegrand M
            (f₃ ∘ (M.T^[3 * q]))
            (f₂ ∘ (M.T^[2 * q]))
            (f₁ ∘ (M.T^[q]))
            f₀ m x ∂M.μ‖ < ε

/-- Forward block reflection is an exact equivalence between ordinary
translated-uniform cancellation and the endpoint-orbit formulation.
This is the noninvertible replacement for reversing an interval with
negative powers of `T`. -/
theorem hasUniformFourTermIntegralDecay_iff_reversedOrbit
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f₀ f₁ f₂ f₃ : M.X → ℂ)
    (hf₀ : MemLp f₀ ⊤ M.μ)
    (hf₁ : MemLp f₁ ⊤ M.μ)
    (hf₂ : MemLp f₂ ⊤ M.μ)
    (hf₃ : MemLp f₃ ⊤ M.μ) :
    HasUniformFourTermIntegralDecay M f₀ f₁ f₂ f₃ ↔
      HasUniformReversedOrbitFourTermIntegralDecay
        M f₀ f₁ f₂ f₃ := by
  constructor
  · intro h ε hε
    filter_upwards [h ε hε] with N hN
    intro q hNq
    let i := q - N
    have hi := hN i
    have hreflect :=
      cesaroAverage_integral_quadruple_reversal
        M hM f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂ hf₃ i N
    rw [hreflect] at hi
    simpa only [i, Nat.sub_add_cancel hNq] using hi
  · intro h ε hε
    filter_upwards [h ε hε] with N hN
    intro i
    have hright := hN (i + N) (Nat.le_add_left N i)
    have hreflect :=
      cesaroAverage_integral_quadruple_reversal
        M hM f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂ hf₃ i N
    rw [hreflect]
    exact hright

end Chapter02.HostKraU3FourTermReversal
