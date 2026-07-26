import Chapter04.Section02
import Chapter04.Spectral.LebesgueSpectrumStrongMixing
import Chapter04.Spectral.LebesgueSpectralIsomorphism
import Chapter04.Spectral.BernoulliKolmogorov
import share.Lean.NLFirst_Pfd28c3cf0fb145e58f2b0f19d4e83368

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter04

universe u v

namespace Section03

/--
Source: Definition 4.3.1, Chapter 4, Section 3.
A Kolmogorov system is a nontrivial invertible Lebesgue system admitting a
sub-sigma-algebra whose forward iterates generate the whole sigma algebra and
whose backward tail is trivial.
-/
def kolmogorovSystem (M : System.{u}) : Prop :=
  IsKolmogorovSystem M

/--
Source: Definition 4.3.2, Chapter 4, Section 3.
A Bernoulli system is the two-sided product shift over a probability base.
-/
def bernoulliSystem (M : System.{u}) : Prop :=
  IsBernoulliSystem M

/--
Source: Remark 4.3.3, Chapter 4, Section 3.
Finite-alphabet symbolic Bernoulli shifts are Bernoulli systems, and products
of Bernoulli systems are Bernoulli.
-/
def bernoulliCoordinateFiltrationRemark : Prop :=
  (∀ M : System.{u}, ∀ k : ℕ, ∀ p : Fin k -> ℝ,
    (∀ i, 0 ≤ p i) -> (∑ i, p i) = 1 ->
    Chapter01.IsTwoSidedBernoulliShiftWith M k p -> IsBernoulliSystem M) ∧
  ∀ M : System.{u}, ∀ N : System.{v},
    IsBernoulliSystem M -> IsBernoulliSystem N ->
      IsBernoulliSystem (measureProductSystem M N)

/--
Source: Theorem 4.3.4, Chapter 4, Section 3.
Every Bernoulli system is a Kolmogorov system.
-/
theorem bernoulliSystemIsKolmogorov (M : System.{u}) :
    IsBernoulliSystem M -> IsKolmogorovSystem M := by
  rintro ⟨hLeb, hM, hinv, Ω, mΩ, ρ, hρ,
    ⟨C, hC, hCpos, hClt⟩, ν, hν, e, inv, he, hinvmeas,
    hinv_e, he_inv, hmap, hinter, hcyl⟩
  letI : MeasureTheory.IsProbabilityMeasure ρ := hρ
  letI : MeasureTheory.IsProbabilityMeasure ν := hν
  have hinter' :
      (fun x => e (M.T x)) =ᵐ[M.μ]
        fun x => BernoulliKolmogorov.leftShift (e x) := by
    filter_upwards [hinter] with x hx
    funext n
    exact hx n
  exact BernoulliKolmogorov.bernoulliData_isKolmogorov
    M hLeb hM hinv ρ C hC hCpos hClt ν e inv he hinvmeas
      hinv_e he_inv hmap hinter' hcyl

/--
Source: Theorem 4.3.5, Chapter 4, Section 3.
Kalikow constructed a Kolmogorov system that is not Bernoulli.
-/
theorem kalikowKolmogorovNotBernoulliExample :
    ∃ M : System.{0}, IsKolmogorovSystem M ∧ ¬ IsBernoulliSystem M := by
  exact MathCopilotPrior.chapter04_results.{0}.kalikow

/--
Source: Definition 4.3.6, Chapter 4, Section 3.
A system has countable Lebesgue spectrum when the Koopman representation has a
countable Lebesgue spectral model.
-/
def countableLebesgueSpectrum (M : System.{u}) : Prop :=
  HasCountableLebesgueSpectrum M

/--
Source: Proposition 4.3.7, Chapter 4, Section 3.
An invertible measure-preserving system with countable Lebesgue spectrum is
strong mixing.
-/
theorem countableLebesgueSpectrumStrongMixing (M : System.{u}) :
    HasCountableLebesgueSpectrum M -> Chapter02.IsStrongMixing M := by
  exact Chapter04.LebesgueSpectrum.countableLebesgueSpectrum_strongMixing M

/--
Source: Proposition 4.3.8, Chapter 4, Section 3.
Any two systems with countable Lebesgue spectrum are spectrally isomorphic.
-/
theorem countableLebesgueSpectrumSystemsSpectrallyIsomorphic
    (M N : System.{u}) :
    HasCountableLebesgueSpectrum M -> HasCountableLebesgueSpectrum N ->
      IsSpectrallyIsomorphic M N := by
  exact Chapter04.LebesgueSpectrum.countableLebesgueSpectrum_spectrallyIsomorphic M N

/--
Source: Theorem 4.3.9, Chapter 4, Section 3.
Rohlin's theorem: every Kolmogorov system has countable Lebesgue spectrum.
-/
theorem kolmogorovSystemHasCountableLebesgueSpectrum (M : System.{u}) :
    IsKolmogorovSystem M -> HasCountableLebesgueSpectrum M := by
  exact
    MathCopilotPrior.chapter04_results.kolmogorov_has_countable_lebesgue_spectrum M

/--
Source: Theorem 4.3.10, Chapter 4, Section 3.
A system is Kolmogorov exactly when it is uniformly mixing in the sense of the
chapter.
-/
theorem kolmogorovIffUniformMixing (M : System.{u}) :
    IsKolmogorovAmbientSystem M ->
      (IsKolmogorovSystem M ↔ Chapter02.IsUniformMixing M) := by
  exact MathCopilotPrior.chapter04_results.kolmogorov_iff_uniform_mixing M

end Section03
end Chapter04
