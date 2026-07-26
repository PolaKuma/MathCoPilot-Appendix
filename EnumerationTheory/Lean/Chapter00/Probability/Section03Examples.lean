import Chapter00.Probability.Section03ConditionalMeasure

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter00.Section03

theorem conditionalExpectationExamplesAux (P : BasicProbabilitySpaceData)
    (A : Set P.X) (hA : MeasurableSet A) (hμA : 0 < P.μ A)
    (hμAc : 0 < P.μ Aᶜ)
    (Etriv : ConditionalExpectationData P {∅, Set.univ})
    (Epart : ConditionalExpectationData P {∅, A, Aᶜ, Set.univ})
    (hEtriv : IsConditionalExpectation P {∅, Set.univ} Etriv)
    (hEpart : IsConditionalExpectation P {∅, A, Aᶜ, Set.univ} Epart) :
    (∀ f : P.X → ℂ, Integrable f P.μ →
      Etriv.op f =ᵐ[P.μ] fun _ => ∫ x, f x ∂P.μ) ∧
    (∀ f : P.X → ℂ, Integrable f P.μ →
      Epart.op f =ᵐ[P.μ] fun x =>
        if x ∈ A then (P.μ A).toReal⁻¹ • ∫ y in A, f y ∂P.μ
        else (P.μ Aᶜ).toReal⁻¹ • ∫ y in Aᶜ, f y ∂P.μ) := by
  constructor
  · intro f hf
    obtain ⟨hmeas, _, hsets⟩ := hEtriv f hf
    letI : Nonempty P.X := nonempty_of_isProbabilityMeasure P.μ
    let x₀ : P.X := Classical.choice (inferInstance : Nonempty P.X)
    have hconst : ∀ x, Etriv.op f x = Etriv.op f x₀ := by
      intro x
      let H : Set P.X := (Etriv.op f) ⁻¹' {Etriv.op f x₀}
      have hHF : H ∈ ({∅, Set.univ} : SetFamily P.X) :=
        hmeas {Etriv.op f x₀} isClosed_singleton
      have hx₀H : x₀ ∈ H := by simp [H]
      have hHuniv : H = Set.univ := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hHF
        rcases hHF with h | h
        · exfalso
          rw [h] at hx₀H
          exact hx₀H
        · exact h
      have hxH : x ∈ H := hHuniv.symm ▸ Set.mem_univ x
      simpa [H] using hxH
    have hc : Etriv.op f x₀ = ∫ x, f x ∂P.μ := by
      have hset := hsets Set.univ (by simp)
      calc
        Etriv.op f x₀ = ∫ x, Etriv.op f x₀ ∂P.μ := by simp
        _ = ∫ x, Etriv.op f x ∂P.μ :=
          integral_congr_ae (Eventually.of_forall fun x => (hconst x).symm)
        _ = ∫ x, f x ∂P.μ := by simpa using hset
    exact Eventually.of_forall fun x => (hconst x).trans hc
  · intro f hf
    obtain ⟨hmeas, _, hsets⟩ := hEpart f hf
    have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr fun h => by
      subst A
      simpa using hμA.ne'
    have hAcne : Aᶜ.Nonempty := Set.nonempty_iff_ne_empty.mpr fun h => by
      rw [h] at hμAc
      simpa using hμAc.ne'
    let xA : P.X := Classical.choose hAne
    let xAc : P.X := Classical.choose hAcne
    have hxA : xA ∈ A := Classical.choose_spec hAne
    have hxAc : xAc ∈ Aᶜ := Classical.choose_spec hAcne
    have sameOn (x y : P.X) (hxy : (x ∈ A ∧ y ∈ A) ∨ (x ∈ Aᶜ ∧ y ∈ Aᶜ)) :
        Epart.op f x = Epart.op f y := by
      let H : Set P.X := (Epart.op f) ⁻¹' {Epart.op f x}
      have hHF : H ∈ ({∅, A, Aᶜ, Set.univ} : SetFamily P.X) :=
        hmeas {Epart.op f x} isClosed_singleton
      have hxH : x ∈ H := by simp [H]
      have hyH : y ∈ H := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hHF
        rcases hHF with h | h | h | h
        · rw [h] at hxH
          exact hxH.elim
        · rw [h] at hxH ⊢
          rcases hxy with ⟨_, hy⟩ | ⟨hx, _⟩
          · exact hy
          · exact (hx hxH).elim
        · rw [h] at hxH ⊢
          rcases hxy with ⟨hx, _⟩ | ⟨_, hy⟩
          · exact (hxH hx).elim
          · exact hy
        · rw [h]
          exact Set.mem_univ y
      exact (show Epart.op f y = Epart.op f x by simpa [H] using hyH).symm
    have hrealA : 0 < (P.μ A).toReal :=
      ENNReal.toReal_pos hμA.ne' (measure_ne_top _ _)
    have hrealAc : 0 < (P.μ Aᶜ).toReal :=
      ENNReal.toReal_pos hμAc.ne' (measure_ne_top _ _)
    have hcA : Epart.op f xA =
        (P.μ A).toReal⁻¹ • ∫ y in A, f y ∂P.μ := by
      have hset := hsets A (by simp)
      have hi : ∫ x in A, Epart.op f x ∂P.μ =
          ∫ x in A, Epart.op f xA ∂P.μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hA] with x hx
        exact sameOn x xA (Or.inl ⟨hx, hxA⟩)
      rw [hi, setIntegral_const] at hset
      simp only [Measure.real_def] at hset
      rw [← hset, smul_smul, inv_mul_cancel₀ hrealA.ne', one_smul]
    have hcAc : Epart.op f xAc =
        (P.μ Aᶜ).toReal⁻¹ • ∫ y in Aᶜ, f y ∂P.μ := by
      have hset := hsets Aᶜ (by simp)
      have hi : ∫ x in Aᶜ, Epart.op f x ∂P.μ =
          ∫ x in Aᶜ, Epart.op f xAc ∂P.μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hA.compl] with x hx
        exact sameOn x xAc (Or.inr ⟨hx, hxAc⟩)
      rw [hi, setIntegral_const] at hset
      simp only [Measure.real_def] at hset
      rw [← hset, smul_smul, inv_mul_cancel₀ hrealAc.ne', one_smul]
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ A
      · dsimp
        rw [if_pos hx]
        simpa [smul_eq_mul] using
          (sameOn x xA (Or.inl ⟨hx, hxA⟩)).trans hcA
      · dsimp
        rw [if_neg hx]
        simpa [smul_eq_mul] using
          (sameOn x xAc (Or.inr ⟨by simpa, hxAc⟩)).trans hcAc

end Chapter00.Section03
