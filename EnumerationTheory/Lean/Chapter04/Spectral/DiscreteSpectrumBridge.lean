import Chapter04.Common

noncomputable section

namespace Chapter04.DiscreteSpectrumBridge

universe u

/-- The orthogonal-basis formulation of discrete spectrum used in Chapter 4
implies the finite-eigenfunction approximation formulation developed in
Chapter 2. -/
theorem chapter02_discreteSpectrum_of_chapter04
    (M : System.{u}) (hdisc : HasDiscreteSpectrum M) :
    Chapter02.HasDiscreteSpectrum M := by
  rcases hdisc with ⟨basis, heigen, _horthogonal, hdense⟩
  intro h hh ε hε
  obtain ⟨s, hs, c, happ⟩ := hdense h hh ε hε
  refine ⟨s, ?_, c, happ⟩
  intro f hf
  exact heigen f (hs hf)

end Chapter04.DiscreteSpectrumBridge
