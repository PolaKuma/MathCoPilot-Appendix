import Chapter02.Spectral.TorusDualMatrixBridge

open Classical

noncomputable section

namespace Chapter02.MultiplicativeTorusCharacter

open Chapter02.TorusDualMatrixBridge

variable {n : ℕ}

/-- Coordinatewise passage from the additive unit torus to the
multiplicative circle torus. -/
def toMultiplicativeTorus
    (x : Chapter01.Torus n) : Fin n → Circle :=
  fun i => AddCircle.homeomorphCircle one_ne_zero (x i)

lemma continuous_toMultiplicativeTorus :
    Continuous (toMultiplicativeTorus :
      Chapter01.Torus n → Fin n → Circle) := by
  rw [continuous_pi_iff]
  intro i
  exact (AddCircle.homeomorphCircle one_ne_zero).continuous.comp
    (continuous_apply i)

lemma toMultiplicativeTorus_add
    (x y : Chapter01.Torus n) :
    toMultiplicativeTorus (x + y) =
      toMultiplicativeTorus x * toMultiplicativeTorus y := by
  funext i
  simpa [toMultiplicativeTorus, AddCircle.homeomorphCircle_apply] using
    AddCircle.toCircle_add (x i) (y i)

/-- A multiplicative torus character pulled back to the additive unit
torus. -/
def toAdditiveCharacter
    (χ : Chapter02.ContinuousMultiplicativeCircleCharacter
      (Fin n → Circle)) :
    Chapter02.ContinuousCircleCharacter (Chapter01.Torus n) where
  toFun x := χ.toFun (toMultiplicativeTorus x)
  map_zero := by
    rw [show toMultiplicativeTorus (0 : Chapter01.Torus n) = 1 by
      funext i
      simp [toMultiplicativeTorus, AddCircle.homeomorphCircle_apply]]
    exact χ.map_one
  map_add x y := by
    rw [toMultiplicativeTorus_add, χ.map_mul]
  continuous := χ.continuous.comp continuous_toMultiplicativeTorus
  unit_norm x := χ.unit_norm (toMultiplicativeTorus x)

/-- Every continuous character of a finite multiplicative torus is an
integer Fourier monomial, expressed through the canonical additive-circle
coordinates. -/
theorem exists_frequency
    (χ : Chapter02.ContinuousMultiplicativeCircleCharacter
      (Fin n → Circle)) :
    ∃ k : Fin n → ℤ,
      ∀ z : Fin n → Circle,
        χ.toFun z =
          UnitAddTorus.mFourier k
            (fun i =>
              (AddCircle.homeomorphCircle one_ne_zero).symm (z i)) := by
  obtain ⟨k, hk⟩ :=
    character_eq_fourierCharacter (toAdditiveCharacter χ)
  refine ⟨k, fun z ↦ ?_⟩
  let x : Chapter01.Torus n :=
    fun i => (AddCircle.homeomorphCircle one_ne_zero).symm (z i)
  have hx : toMultiplicativeTorus x = z := by
    funext i
    exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply (z i)
  have hvalue := congrFun hk x
  change χ.toFun (toMultiplicativeTorus x) =
    UnitAddTorus.mFourier k x at hvalue
  rw [hx] at hvalue
  exact hvalue

/-- A nontrivial multiplicative torus character has a nonzero integer
frequency. -/
theorem exists_nonzero_frequency
    (χ : Chapter02.ContinuousMultiplicativeCircleCharacter
      (Fin n → Circle))
    (hχ : ∃ z, χ.toFun z ≠ 1) :
    ∃ k : Fin n → ℤ, k ≠ 0 ∧
      ∀ z : Fin n → Circle,
        χ.toFun z =
          UnitAddTorus.mFourier k
            (fun i =>
              (AddCircle.homeomorphCircle one_ne_zero).symm (z i)) := by
  obtain ⟨k, hk⟩ := exists_frequency χ
  refine ⟨k, ?_, hk⟩
  obtain ⟨z, hz⟩ := hχ
  intro hkzero
  apply hz
  rw [hk z, hkzero]
  simp [UnitAddTorus.mFourier]

end Chapter02.MultiplicativeTorusCharacter
