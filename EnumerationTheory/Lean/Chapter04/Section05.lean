import Chapter04.Ergodic.Exhaustion
import Chapter04.Ergodic.ErgodicFactor
import share.Lean.NLFirst_Pfd28c3cf0fb145e58f2b0f19d4e83368

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter04

universe u v

namespace Section05

/--
Source: Definition 4.5.1, Chapter 4, Section 5.
A group extension is obtained from a compact subgroup of the automorphism group
by passing to the invariant sigma algebra; skew products and cocycles provide
the corresponding concrete model.
-/
def groupExtension (extension factor : System.{u}) : Prop :=
  IsGroupExtension extension factor

/--
Source: Definition 4.5.1, Chapter 4, Section 5.
The skew-product form of a group extension is represented by a base system, a
fiber group, and a measurable cocycle acting on the fiber.
-/
def skewProductCocycleExtension (extension factor : System.{u}) : Prop :=
  IsSkewProductExtension extension factor

/--
Source: Lemma 4.5.2, Chapter 4, Section 5.
Exhaustion lemma: a hereditary family in a probability space admits a disjoint
sequence whose union is maximal up to saturation.
-/
theorem exhaustionLemma
    (P : ProbabilitySpace.{u}) (𝓗 : Set (Set P.X)) :
    Chapter01.IsProbabilitySpace P ->
      IsHereditaryFamily 𝓗 ->
      (∀ A ∈ 𝓗, MeasurableSet A) ->
      ∃ U : Set P.X, HasMeasurableUnion 𝓗 P.𝓧 P.μ U := by
  exact exists_measurableUnion_of_hereditary P 𝓗

/--
Source: Corollary 4.5.3, Chapter 4, Section 5.
A hereditary family that saturates a sigma algebra has a countable disjoint
measurable union saturating the same sigma algebra.
-/
theorem saturatedHereditaryFamilyPartition
    (P : ProbabilitySpace.{u}) (𝓗 : Set (Set P.X)) :
    Chapter01.IsProbabilitySpace P -> IsHereditaryFamily 𝓗 ->
      (∀ A ∈ 𝓗, MeasurableSet A) -> Saturates 𝓗 P.𝓧 P.μ ->
      ∃ U : Set P.X, HasMeasurableUnion 𝓗 P.𝓧 P.μ U ∧ P.μ U = 1 := by
  intro hprob hher hmeas hsat
  obtain ⟨U, hU⟩ := exhaustionLemma P 𝓗 hprob hher hmeas
  refine ⟨U, hU, ?_⟩
  have hcompl : P.μ Uᶜ = 0 := by
    by_contra hne
    have hpos : 0 < P.μ Uᶜ := bot_lt_iff_ne_bot.2 hne
    obtain ⟨B, hBH, hBU, hBpos⟩ := hsat Uᶜ hU.1.compl hpos
    have hzero := hU.2.choose_spec.2.2.2 B hBH
    have hdiff : B \ U = B := by
      ext x
      constructor
      · exact fun hx => hx.1
      · intro hxB
        exact ⟨hxB, fun hxU => hBU hxB hxU⟩
    rw [hdiff] at hzero
    exact (ne_of_gt hBpos) hzero
  calc
    P.μ U = P.μ Set.univ :=
      MeasureTheory.measure_congr (MeasureTheory.ae_eq_univ.mpr hcompl)
    _ = 1 := hprob.measure_univ

/--
Source: Theorem 4.5.4, Chapter 4, Section 5.
Local inversion theorem: a measurable map with countable fibers can be
partitioned into countably many measurable pieces on which the map is injective.
-/
theorem localInversionTheorem : LocalInversionForCountableFibers := by
  exact MathCopilotPrior.chapter04_results.local_inversion

/--
Source: Theorem 4.5.5, Chapter 4, Section 5.
Rohlin's skew-product theorem: an ergodic extension of an ergodic system is
isomorphic to a skew product.
-/
theorem rohlinSkewProductTheorem : RohlinSkewProductTheoremStatement := by
  exact MathCopilotPrior.chapter04_results.rohlin_skew_product

/--
Source: Theorem 4.5.6, Chapter 4, Section 5.
An ergodic compact-group extension of an ergodic system is represented by a
group skew product.
-/
theorem compactGroupExtensionIsGroupSkewProduct : GroupSkewProductRepresentationStatement := by
  intro extension factor hext hLebExt hLebFactor hinvExt hinvFactor hgroup
  rcases hgroup with
    ⟨K, groupK, topologyK, topGroupK, compactK, π, act, hfactor, hrest⟩
  apply rohlinSkewProductTheorem extension factor
  · exact ⟨π, hfactor⟩
  · exact hLebExt
  · exact hLebFactor
  · exact hinvExt
  · exact hinvFactor
  · exact hext
  · exact ErgodicFactor.of_factor_map extension factor π hext hfactor

end Section05
end Chapter04
