import Chapter00.Section03
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

noncomputable section

open Classical Filter Set Function Metric List
open scoped BigOperators NNReal Pointwise SetRel Topology Uniformity

namespace Chapter00
namespace Section04

universe u v

/-- The book's convention: a Haar measure is a nonzero invariant Radon
measure.  Mathlib's `IsHaarMeasure` supplies invariance, local finiteness and
positivity on nonempty open sets; `Regular` supplies exactly the Radon
regularity required in Definition 0.4.2. -/
def IsRadonHaarMeasure
    {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (μ : MeasureTheory.Measure G) : Prop :=
  μ.IsHaarMeasure ∧ μ.Regular

/-- Source: Definition 0.4.2. A right Haar measure is a measure whose inverse
pushforward is a left Haar measure. -/
def rightHaarMeasureDefinition (G : Type u) [Group G] [TopologicalSpace G]
    [T2Space G] [MeasurableSpace G] (μ : MeasureTheory.Measure G) : Prop :=
  IsRadonHaarMeasure
    (MeasureTheory.Measure.map (fun g : G => g⁻¹) μ)

/-- Pushing a measure forward by inversion twice gives the original measure. -/
private theorem inverseMap_inverseMap
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) :
    MeasureTheory.Measure.map (fun g : G => g⁻¹)
      (MeasureTheory.Measure.map (fun g : G => g⁻¹) μ) = μ := by
  rw [MeasureTheory.Measure.map_map measurable_inv measurable_inv]
  have hinv : (Inv.inv ∘ Inv.inv : G → G) = id := by
    funext g
    simp
  rw [hinv]
  convert (MeasureTheory.Measure.map_id (μ := μ)) using 1

/-- A reusable existence lemma: a compact neighborhood of the identity gives
the positive compact needed by Mathlib's Haar-measure construction. -/
theorem existsHaarMeasureFromLocalCompact
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    ∃ μ : MeasureTheory.Measure G, IsRadonHaarMeasure μ := by
  obtain ⟨K, hKcompact, hKnhds⟩ :=
    WeaklyLocallyCompactSpace.exists_compact_mem_nhds (1 : G)
  let P : TopologicalSpace.PositiveCompacts G :=
    { toCompacts := ⟨K, hKcompact⟩
      interior_nonempty' := by
        refine ⟨1, ?_⟩
        exact mem_interior_iff_mem_nhds.mpr hKnhds }
  exact ⟨MeasureTheory.Measure.haarMeasure P,
    MeasureTheory.Measure.isHaarMeasure_haarMeasure P,
    MeasureTheory.Measure.regular_haarMeasure⟩

/-- A right Haar measure is obtained by transporting a left Haar measure
through inversion. -/
theorem existsRightHaarMeasure
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    ∃ μr : MeasureTheory.Measure G, rightHaarMeasureDefinition G μr := by
  obtain ⟨μl, hμl⟩ := existsHaarMeasureFromLocalCompact G
  letI : MeasureTheory.Measure.IsHaarMeasure μl := hμl.1
  letI : μl.Regular := hμl.2
  refine ⟨MeasureTheory.Measure.map (fun g : G => g⁻¹) μl, ?_⟩
  rw [rightHaarMeasureDefinition, inverseMap_inverseMap]
  exact hμl

/-- Counting measure is a Haar measure on every discrete topological group. -/
theorem countMeasureIsHaarOnDiscreteGroup
    (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G]
    [MeasurableSpace G] [BorelSpace G] :
    (MeasureTheory.Measure.count : MeasureTheory.Measure G).IsHaarMeasure := by
  letI : MeasureTheory.IsFiniteMeasureOnCompacts
      (MeasureTheory.Measure.count : MeasureTheory.Measure G) :=
    ⟨by
      intro K hK
      have hfinite : K.Finite := isCompact_iff_finite.mp hK
      rw [MeasureTheory.Measure.count_apply_finite K hfinite]
      exact ENNReal.coe_lt_top⟩
  letI : MeasureTheory.Measure.IsMulLeftInvariant
      (MeasureTheory.Measure.count : MeasureTheory.Measure G) :=
    ⟨fun g => by
      ext A hA
      rw [MeasureTheory.Measure.map_apply
        (MeasurableMul.measurable_const_mul g) hA]
      rw [MeasureTheory.Measure.count_apply
        ((MeasurableMul.measurable_const_mul g) hA),
        MeasureTheory.Measure.count_apply hA]
      have he := Set.encard_preimage_of_bijective
        (Homeomorph.mulLeft g).bijective A
      change ((fun x : G => g * x) ⁻¹' A).encard = A.encard at he
      exact congrArg (fun e : ENat => (e : ENNReal)) he⟩
  letI : MeasureTheory.Measure.IsOpenPosMeasure
      (MeasureTheory.Measure.count : MeasureTheory.Measure G) :=
    ⟨by
      intro U hU hUne
      obtain ⟨x, hx⟩ := hUne
      have hmono : MeasureTheory.Measure.count ({x} : Set G) ≤
          MeasureTheory.Measure.count U :=
        MeasureTheory.measure_mono (Set.singleton_subset_iff.mpr hx)
      have hone : MeasureTheory.Measure.count ({x} : Set G) = 1 := by simp
      rw [hone] at hmono
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hmono)⟩
  exact MeasureTheory.Measure.IsHaarMeasure.mk

/-- Normalized counting measure is Haar probability measure on a nontrivial
finite cyclic group. -/
theorem normalizedCountMeasureOnZModIsProbabilityHaar
    (n : ℕ) [NeZero n]
    [MeasurableSpace (Multiplicative (ZMod n))]
    [BorelSpace (Multiplicative (ZMod n))] :
    let μn : MeasureTheory.Measure (Multiplicative (ZMod n)) :=
      (n : ENNReal)⁻¹ • MeasureTheory.Measure.count
    MeasureTheory.IsProbabilityMeasure μn ∧ μn.IsHaarMeasure := by
  dsimp
  have hcount := countMeasureIsHaarOnDiscreteGroup
    (Multiplicative (ZMod n))
  letI : MeasureTheory.Measure.IsHaarMeasure
      (MeasureTheory.Measure.count :
        MeasureTheory.Measure (Multiplicative (ZMod n))) := hcount
  constructor
  · apply MeasureTheory.IsProbabilityMeasure.mk
    let huniv : (Set.univ : Set (Multiplicative (ZMod n))).Finite :=
      Set.finite_univ
    rw [MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.count_apply_finite Set.univ huniv]
    simp only [Set.Finite.toFinset_univ, smul_eq_mul]
    have hcard : (Finset.univ :
        Finset (Multiplicative (ZMod n))).card = n := by simp
    rw [hcard]
    have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast (NeZero.ne n)
    exact ENNReal.inv_mul_cancel hn0 ENNReal.coe_ne_top
  · apply MeasureTheory.Measure.IsHaarMeasure.smul
      MeasureTheory.Measure.count
    · exact ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
    · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast (NeZero.ne n))

/-- Lebesgue measure, transported from additive to multiplicative notation, is
a Haar measure. -/
theorem additiveRealVolumeIsHaarInMultiplicativeNotation
    [MeasurableSpace (Multiplicative ℝ)] [BorelSpace (Multiplicative ℝ)] :
    (MeasureTheory.Measure.map Multiplicative.ofAdd
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)).IsHaarMeasure := by
  let e : ℝ ≃ₜ Multiplicative ℝ :=
    { Multiplicative.ofAdd with
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }
  let m : MeasureTheory.Measure (Multiplicative ℝ) :=
    MeasureTheory.Measure.map Multiplicative.ofAdd
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)
  have hefun : (e : ℝ → Multiplicative ℝ) = Multiplicative.ofAdd := rfl
  letI : MeasureTheory.IsFiniteMeasureOnCompacts m :=
    ⟨by
      intro K hK
      change MeasureTheory.Measure.map Multiplicative.ofAdd
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) K < ⊤
      rw [← hefun, MeasureTheory.Measure.map_apply e.measurable
        hK.measurableSet]
      exact MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact
        ((e.isCompact_preimage).mpr hK)⟩
  letI : MeasureTheory.Measure.IsMulLeftInvariant m :=
    ⟨fun g => by
      ext A hA
      change MeasureTheory.Measure.map
        (fun x : Multiplicative ℝ => g * x) m A = m A
      rw [MeasureTheory.Measure.map_apply
        (MeasurableMul.measurable_const_mul g) hA]
      change MeasureTheory.Measure.map Multiplicative.ofAdd
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)
          ((fun x : Multiplicative ℝ => g * x) ⁻¹' A) =
        MeasureTheory.Measure.map Multiplicative.ofAdd
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) A
      rw [← hefun, MeasureTheory.Measure.map_apply e.measurable
          ((MeasurableMul.measurable_const_mul g) hA),
        MeasureTheory.Measure.map_apply e.measurable hA]
      have hmap :=
        MeasureTheory.Measure.IsAddLeftInvariant.map_add_left_eq_self
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) g.toAdd
      have hval := congrArg
        (fun ν : MeasureTheory.Measure ℝ => ν (e ⁻¹' A)) hmap
      change MeasureTheory.Measure.map (fun x : ℝ => g.toAdd + x)
          MeasureTheory.volume (e ⁻¹' A) =
        MeasureTheory.volume (e ⁻¹' A) at hval
      rw [MeasureTheory.Measure.map_apply (measurable_const_add g.toAdd)
        (e.measurable hA)] at hval
      exact hval⟩
  letI : MeasureTheory.Measure.IsOpenPosMeasure m :=
    ⟨by
      intro U hU hUne
      change MeasureTheory.Measure.map Multiplicative.ofAdd
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) U ≠ 0
      rw [← hefun, MeasureTheory.Measure.map_apply e.measurable
        hU.measurableSet]
      apply MeasureTheory.Measure.IsOpenPosMeasure.open_pos
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (e ⁻¹' U)
      · exact (e.isOpen_preimage).mpr hU
      · obtain ⟨y, hy⟩ := hUne
        exact ⟨e.symm y, by simpa using hy⟩⟩
  exact MeasureTheory.Measure.IsHaarMeasure.mk

/-- Every compact Hausdorff topological group has a normalized Haar measure. -/
theorem existsHaarProbabilityOnCompactGroup
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    ∃ m : MeasureTheory.Measure G,
      MeasureTheory.IsProbabilityMeasure m ∧ m.IsHaarMeasure := by
  obtain ⟨μ, hμ⟩ := existsHaarMeasureFromLocalCompact G
  letI : MeasureTheory.Measure.IsHaarMeasure μ := hμ.1
  have hfinite : μ Set.univ < ⊤ :=
    MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact isCompact_univ
  have hpos : μ Set.univ ≠ 0 :=
    MeasureTheory.Measure.IsOpenPosMeasure.open_pos
      Set.univ isOpen_univ Set.univ_nonempty
  let m : MeasureTheory.Measure G := (μ Set.univ)⁻¹ • μ
  refine ⟨m, ?_, ?_⟩
  · apply MeasureTheory.IsProbabilityMeasure.mk
    change ((μ Set.univ)⁻¹ • μ) Set.univ = 1
    rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hpos (ne_of_lt hfinite)
  · change ((μ Set.univ)⁻¹ • μ).IsHaarMeasure
    apply MeasureTheory.Measure.IsHaarMeasure.smul μ
    · exact ENNReal.inv_ne_zero.mpr (ne_of_lt hfinite)
    · exact ENNReal.inv_ne_top.mpr hpos

/-- A fixed positive compact set, used only to normalize Haar products. -/
private noncomputable def chosenPositiveCompact
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] : TopologicalSpace.PositiveCompacts G := by
  let e := WeaklyLocallyCompactSpace.exists_compact_mem_nhds (1 : G)
  let K := Classical.choose e
  have hK := Classical.choose_spec e
  exact
    { toCompacts := ⟨K, hK.1⟩
      interior_nonempty' :=
        ⟨1, mem_interior_iff_mem_nhds.mpr hK.2⟩ }

/-- The product of two positive compact sets is positive compact. -/
private def positiveCompactsProd
    {G H : Type*} [TopologicalSpace G] [TopologicalSpace H]
    (P : TopologicalSpace.PositiveCompacts G)
    (Q : TopologicalSpace.PositiveCompacts H) :
    TopologicalSpace.PositiveCompacts (G × H) :=
  { toCompacts := ⟨P.1 ×ˢ Q.1, P.1.2.prod Q.1.2⟩
    interior_nonempty' := by
      rw [interior_prod_eq]
      exact P.2.prod Q.2 }

/-- The Radon-Haar product valid without any σ-compactness assumption.

Mathlib's generic `Measure.prod` has its expected rectangle laws only under
an `SFinite` hypothesis, which a Haar measure on a non-σ-compact locally
compact group need not satisfy.  We therefore form the product in the Haar
category: take the regular Haar measure associated to the product positive
compact and multiply it by the two normalization factors of the inputs. -/
noncomputable def radonHaarProductMeasure
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (H : Type v) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (μ : MeasureTheory.Measure G) (ν : MeasureTheory.Measure H)
    (hμ : IsRadonHaarMeasure μ) (hν : IsRadonHaarMeasure ν) :
    @MeasureTheory.Measure (G × H) (borel (G × H)) := by
  letI : MeasurableSpace (G × H) := borel (G × H)
  letI : BorelSpace (G × H) := ⟨rfl⟩
  letI : MeasureTheory.Measure.IsHaarMeasure μ := hμ.1
  letI : MeasureTheory.Measure.IsHaarMeasure ν := hν.1
  let PG := chosenPositiveCompact G
  let PH := chosenPositiveCompact H
  let μ₀ := MeasureTheory.Measure.haarMeasure PG
  let ν₀ := MeasureTheory.Measure.haarMeasure PH
  let cμ := MeasureTheory.Measure.haarScalarFactor μ μ₀
  let cν := MeasureTheory.Measure.haarScalarFactor ν ν₀
  exact (cμ * cν) •
    MeasureTheory.Measure.haarMeasure (positiveCompactsProd PG PH)

/--
Source: Theorem 0.4.3, Chapter 0, Section 4.
Existence and uniqueness up to a finite positive scalar of left Haar measure
on a locally compact Hausdorff topological group, together with right and
binary product Haar measures.
-/
theorem haarMeasureExistenceUniquenessAndProducts
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (H : Type v) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] :
    (∃ μ : MeasureTheory.Measure G, IsRadonHaarMeasure μ) ∧
      (∀ μ ν : MeasureTheory.Measure G,
        IsRadonHaarMeasure μ -> IsRadonHaarMeasure ν ->
        ∃ c : ENNReal, c ≠ 0 ∧ c < ⊤ ∧ μ = c • ν) ∧
      (∃ μr : MeasureTheory.Measure G, ∃ μl : MeasureTheory.Measure G,
        IsRadonHaarMeasure μl ∧
          μr = MeasureTheory.Measure.map (fun g : G => g⁻¹) μl) ∧
      (∀ μ ν : MeasureTheory.Measure G,
        rightHaarMeasureDefinition G μ -> rightHaarMeasureDefinition G ν ->
        ∃ c : ENNReal, c ≠ 0 ∧ c < ⊤ ∧ μ = c • ν) ∧
      ∀ μ : MeasureTheory.Measure G, ∀ ν : MeasureTheory.Measure H,
        ∀ hμ : IsRadonHaarMeasure μ, ∀ hν : IsRadonHaarMeasure ν,
          letI : MeasurableSpace (G × H) := borel (G × H)
          IsRadonHaarMeasure (radonHaarProductMeasure G H μ ν hμ hν) := by
  refine ⟨existsHaarMeasureFromLocalCompact G, ?_⟩
  constructor
  · intro μ ν hμ hν
    letI : MeasureTheory.Measure.IsHaarMeasure μ := hμ.1
    letI : MeasureTheory.Measure.IsHaarMeasure ν := hν.1
    letI : μ.Regular := hμ.2
    letI : ν.Regular := hν.2
    let c : ENNReal :=
      (MeasureTheory.Measure.haarScalarFactor μ ν : NNReal)
    refine ⟨c, ?_, ?_, ?_⟩
    · change ((MeasureTheory.Measure.haarScalarFactor μ ν : NNReal) : ENNReal) ≠ 0
      exact ENNReal.coe_ne_zero.mpr
        (MeasureTheory.Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν).ne'
    · exact ENNReal.coe_lt_top
    · simpa [c] using
        (MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_regular μ ν)
  constructor
  · obtain ⟨μl, hμl⟩ := existsHaarMeasureFromLocalCompact G
    exact ⟨MeasureTheory.Measure.map (fun g : G => g⁻¹) μl,
      μl, hμl, rfl⟩
  constructor
  · intro μ ν hμ hν
    let μi := MeasureTheory.Measure.map (fun g : G => g⁻¹) μ
    let νi := MeasureTheory.Measure.map (fun g : G => g⁻¹) ν
    change IsRadonHaarMeasure μi at hμ
    change IsRadonHaarMeasure νi at hν
    letI : MeasureTheory.Measure.IsHaarMeasure μi := hμ.1
    letI : MeasureTheory.Measure.IsHaarMeasure νi := hν.1
    letI : μi.Regular := hμ.2
    letI : νi.Regular := hν.2
    let c : ENNReal :=
      (MeasureTheory.Measure.haarScalarFactor μi νi : NNReal)
    refine ⟨c, ?_, ?_, ?_⟩
    · change ((MeasureTheory.Measure.haarScalarFactor μi νi : NNReal) : ENNReal) ≠ 0
      exact ENNReal.coe_ne_zero.mpr
        (MeasureTheory.Measure.haarScalarFactor_pos_of_isHaarMeasure μi νi).ne'
    · exact ENNReal.coe_lt_top
    · have heq : μi = c • νi := by
        simpa [c] using
          (MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_regular μi νi)
      have heq' := congrArg
        (MeasureTheory.Measure.map (fun g : G => g⁻¹)) heq
      dsimp only [μi, νi] at heq'
      rw [MeasureTheory.Measure.map_smul, inverseMap_inverseMap,
        inverseMap_inverseMap] at heq'
      exact heq'
  · intro μ ν hμ hν
    letI : MeasurableSpace (G × H) := borel (G × H)
    letI : BorelSpace (G × H) := ⟨rfl⟩
    letI : MeasureTheory.Measure.IsHaarMeasure μ := hμ.1
    letI : MeasureTheory.Measure.IsHaarMeasure ν := hν.1
    let PG := chosenPositiveCompact G
    let PH := chosenPositiveCompact H
    let μ₀ := MeasureTheory.Measure.haarMeasure PG
    let ν₀ := MeasureTheory.Measure.haarMeasure PH
    let ρ₀ := MeasureTheory.Measure.haarMeasure (positiveCompactsProd PG PH)
    let cμ := MeasureTheory.Measure.haarScalarFactor μ μ₀
    let cν := MeasureTheory.Measure.haarScalarFactor ν ν₀
    rw [radonHaarProductMeasure]
    change IsRadonHaarMeasure ((cμ * cν) • ρ₀)
    letI : MeasureTheory.Measure.IsHaarMeasure μ₀ := by
      dsimp only [μ₀]
      infer_instance
    letI : MeasureTheory.Measure.IsHaarMeasure ν₀ := by
      dsimp only [ν₀]
      infer_instance
    letI : MeasureTheory.Measure.IsHaarMeasure ρ₀ := by
      dsimp only [ρ₀]
      infer_instance
    letI : ρ₀.Regular := by
      dsimp only [ρ₀]
      infer_instance
    have hcμ : cμ ≠ 0 :=
      by simpa [cμ] using
        (MeasureTheory.Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₀).ne'
    have hcν : cν ≠ 0 :=
      by simpa [cν] using
        (MeasureTheory.Measure.haarScalarFactor_pos_of_isHaarMeasure ν ν₀).ne'
    constructor
    · exact MeasureTheory.Measure.IsHaarMeasure.nnreal_smul ρ₀
        (mul_ne_zero hcμ hcν)
    · infer_instance

private theorem symmetric_fast_basis
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [FirstCountableTopology G] :
    ∃ V : ℕ → Set G,
      (𝓝 (1 : G)).HasAntitoneBasis V ∧
      (∀ n, (fun x : G => x⁻¹) ⁻¹' V n = V n) ∧
      ∀ ⦃m n⦄, m < n → V n * (V n * V n) ⊆ V m := by
  obtain ⟨u, hu, husq⟩ := IsTopologicalGroup.exists_antitone_basis_nhds_one G
  let V : ℕ → Set G := fun n =>
    u (2 * n) ∩ (fun x : G => x⁻¹) ⁻¹' u (2 * n)
  have hVbasis : (𝓝 (1 : G)).HasAntitoneBasis V := by
    refine ⟨?_, ?_⟩
    · apply hu.toHasBasis.to_hasBasis
      · intro n _
        refine ⟨n, trivial, ?_⟩
        intro x hx
        exact hu.antitone (Nat.le_mul_of_pos_left n (by omega)) hx.1
      · intro n _
        have hun : u (2 * n) ∈ 𝓝 (1 : G) :=
          hu.mem_iff.mpr ⟨2 * n, Set.Subset.rfl⟩
        have huinv : (fun x : G => x⁻¹) ⁻¹' u (2 * n) ∈ 𝓝 (1 : G) := by
          have ht : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1) := by
            have ht0 : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 ((1 : G)⁻¹)) :=
              continuous_inv.continuousAt
            rw [inv_one] at ht0
            exact ht0
          exact ht hun
        have hVmem : V n ∈ 𝓝 (1 : G) := inter_mem hun huinv
        obtain ⟨k, hk⟩ := hu.mem_iff.mp hVmem
        exact ⟨k, trivial, hk⟩
    · intro m n hmn
      intro x hx
      exact ⟨hu.antitone (Nat.mul_le_mul_left 2 hmn) hx.1,
        hu.antitone (Nat.mul_le_mul_left 2 hmn) hx.2⟩
  have hVinv (n : ℕ) : (fun x : G => x⁻¹) ⁻¹' V n = V n := by
    ext x
    simp only [V, Set.mem_preimage, Set.mem_inter_iff]
    constructor <;> rintro ⟨h₁, h₂⟩
    · exact ⟨by simpa using h₂, h₁⟩
    · exact ⟨h₂, by simpa using h₁⟩
  refine ⟨V, hVbasis, hVinv, ?_⟩
  intro m n hmn
  have h2 : 2 * m + 2 ≤ 2 * n := by omega
  have hsub : V n * (V n * V n) ⊆ u (2 * m) := by
    intro x hx
    rcases hx with ⟨a, ha, bc, hbc, rfl⟩
    rcases hbc with ⟨b, hb, c, hc, rfl⟩
    have hab : a * b ∈ u (2 * m + 1) :=
      husq (2 * m + 1) ⟨a, hu.antitone h2 ha.1,
        b, hu.antitone h2 hb.1, rfl⟩
    have hc' : c ∈ u (2 * m + 1) :=
      hu.antitone (by omega) (hu.antitone h2 hc.1)
    change a * (b * c) ∈ u (2 * m)
    rw [← mul_assoc]
    exact husq (2 * m) ⟨a * b, hab, c, hc', rfl⟩
  intro x hx
  refine ⟨hsub hx, ?_⟩
  have hxinv : x⁻¹ ∈ V n * (V n * V n) := by
    rcases hx with ⟨a, ha, bc, hbc, rfl⟩
    rcases hbc with ⟨b, hb, c, hc, rfl⟩
    refine ⟨c⁻¹, ?_, b⁻¹ * a⁻¹, ?_, by group⟩
    · simpa [← Set.mem_preimage, hVinv n] using hc
    · refine ⟨b⁻¹, ?_, a⁻¹, ?_, rfl⟩
      · simpa [← Set.mem_preimage, hVinv n] using hb
      · simpa [← Set.mem_preimage, hVinv n] using ha
  exact hsub hxinv

private def leftUniformSpace
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    UniformSpace G where
  uniformity := comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1)
  symm :=
    have h : Tendsto (fun p : G × G => (p.1⁻¹ * p.2)⁻¹)
        (comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1)) (𝓝 1⁻¹) :=
      tendsto_id.inv.comp tendsto_comap
    by simpa [tendsto_comap_iff] using h
  comp := Tendsto.le_comap fun W hW => by
    rcases exists_nhds_one_split hW with ⟨V, hV, hVV⟩
    refine mem_map.2 (mem_of_superset (mem_lift' <| preimage_mem_comap hV) ?_)
    rintro ⟨x, y⟩ ⟨z, hxz, hzy⟩
    change x⁻¹ * y ∈ W
    change x⁻¹ * z ∈ V at hxz
    change z⁻¹ * y ∈ V at hzy
    convert hVV _ hxz _ hzy using 1 <;> group
  nhds_eq_comap_uniformity x := by
    simp only [comap_comap, Function.comp_def]
    symm
    exact ((Homeomorph.mulLeft x⁻¹).comap_nhds_eq 1).trans
      (show 𝓝 (x⁻¹⁻¹ * 1) = 𝓝 x by simp)

private theorem left_uniform_relation_basis
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [FirstCountableTopology G] :
    letI : UniformSpace G := leftUniformSpace G
    ∃ U : ℕ → Set (G × G),
      (∀ n, SetRel.IsSymm (U n)) ∧
      (∀ ⦃m n⦄, m < n → (U n ○ (U n ○ U n)) ⊆ U m) ∧
      (∀ n z x y, (x, y) ∈ U n ↔ (z * x, z * y) ∈ U n) ∧
      (𝓤 G).HasAntitoneBasis U := by
  letI : UniformSpace G := leftUniformSpace G
  obtain ⟨V, hVbasis, hVinv, hVcomp⟩ := symmetric_fast_basis G
  let U : ℕ → Set (G × G) := fun n =>
    {p | p.1⁻¹ * p.2 ∈ V n}
  have hUsymm (n : ℕ) : SetRel.IsSymm (U n) := by
    refine ⟨?_⟩
    intro x y hxy
    change y⁻¹ * x ∈ V n
    have hinv : (x⁻¹ * y)⁻¹ ∈ V n := by
      have : (x⁻¹ * y)⁻¹ ∈ (fun g : G => g⁻¹) ⁻¹' V n := by
        simpa using hxy
      simpa [hVinv n] using this
    simpa using hinv
  have hUcomp : ∀ ⦃m n⦄, m < n → U n ○ (U n ○ U n) ⊆ U m := by
    intro m n hmn p hp
    rcases hp with ⟨x₂, hx12, x₃, hx23, hx34⟩
    change p.1⁻¹ * p.2 ∈ V m
    apply hVcomp hmn
    refine ⟨p.1⁻¹ * x₂, hx12, x₂⁻¹ * x₃ * (x₃⁻¹ * p.2), ?_, ?_⟩
    · exact ⟨x₂⁻¹ * x₃, hx23, x₃⁻¹ * p.2, hx34, rfl⟩
    · group
  have hUleft (n : ℕ) (z x y : G) :
      (x, y) ∈ U n ↔ (z * x, z * y) ∈ U n := by
    change x⁻¹ * y ∈ V n ↔ (z * x)⁻¹ * (z * y) ∈ V n
    group
  have hUbasis : (𝓤 G).HasAntitoneBasis U := by
    change (comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1)).HasAntitoneBasis U
    exact hVbasis.comap _
  exact ⟨U, hUsymm, hUcomp, hUleft, hUbasis⟩

/--
Source: Theorem 0.4.4, Chapter 0, Section 4.
Birkhoff-Kakutani theorem: a locally compact metrizable topological group has
a left-invariant metric.
-/
theorem birkhoffKakutaniLeftInvariantMetric
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TopologicalSpace.MetrizableSpace G] :
    ∃ m : MetricSpace G,
      m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace G) ∧
      ∀ z x y : G, @dist G m.toDist (z * x) (z * y) =
        @dist G m.toDist x y := by
  let originalTopology : TopologicalSpace G := inferInstance
  let originalT2 : @T2Space G originalTopology := inferInstance
  let originalT0 : @T0Space G originalTopology := inferInstance
  letI : UniformSpace G := leftUniformSpace G
  letI : T2Space G := originalT2
  letI : T0Space G := originalT0
  obtain ⟨U, hU_symm, hU_comp, hU_left, hB⟩ :=
    left_uniform_relation_basis G
  set d : G → G → ℝ≥0 := fun x y =>
    if h : ∃ n, (x, y) ∉ U n then (1 / 2) ^ Nat.find h else 0
  have hd₀ : ∀ {x y}, d x y = 0 ↔ Inseparable x y := by
    intro x y
    refine Iff.trans ?_ hB.inseparable_iff_uniformity.symm
    simp only [d, true_imp_iff]
    split_ifs with h
    · simp [h, pow_eq_zero_iff']
    · simpa only [not_exists, Classical.not_not, eq_self_iff_true, true_iff] using h
  have find_eq_of_iff (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q]
      (hpq : ∀ n, p n ↔ q n)
      (hp : ∃ n, p n) (hq : ∃ n, q n) : Nat.find hp = Nat.find hq := by
    apply Nat.le_antisymm
    · exact Nat.find_min' hp (hpq (Nat.find hq) |>.mpr (Nat.find_spec hq))
    · exact Nat.find_min' hq (hpq (Nat.find hp) |>.mp (Nat.find_spec hp))
  have hd_symm x y : d x y = d y x := by
    have he (n : ℕ) : (x, y) ∉ U n ↔ (y, x) ∉ U n :=
      not_congr ⟨(hU_symm n).symm x y, (hU_symm n).symm y x⟩
    by_cases hx : ∃ n, (x, y) ∉ U n
    · have hy : ∃ n, (y, x) ∉ U n := (exists_congr he).mp hx
      dsimp only [d]
      rw [dif_pos hx, dif_pos hy]
      congr 1
      exact find_eq_of_iff _ _ he hx hy
    · have hy : ¬ ∃ n, (y, x) ∉ U n := fun h => hx ((exists_congr he).mpr h)
      dsimp only [d]
      rw [dif_neg hx, dif_neg hy]
  have hd_left (z x y : G) : d (z * x) (z * y) = d x y := by
    have he (n : ℕ) : (z * x, z * y) ∉ U n ↔ (x, y) ∉ U n :=
      not_congr (hU_left n z x y).symm
    by_cases hz : ∃ n, (z * x, z * y) ∉ U n
    · have hxy : ∃ n, (x, y) ∉ U n := (exists_congr he).mp hz
      dsimp only [d]
      rw [dif_pos hz, dif_pos hxy]
      congr 1
      exact find_eq_of_iff _ _ he hz hxy
    · have hxy : ¬ ∃ n, (x, y) ∉ U n := fun h => hz ((exists_congr he).mpr h)
      dsimp only [d]
      rw [dif_neg hz, dif_neg hxy]
  have hr : (1 / 2 : ℝ≥0) ∈ Set.Ioo (0 : ℝ≥0) 1 :=
    ⟨half_pos one_pos, NNReal.half_lt_self one_ne_zero⟩
  let P := PseudoMetricSpace.ofPreNNDist d (fun x => hd₀.2 rfl) hd_symm
  have hdist_le : ∀ x y, @dist G P.toDist x y ≤ d x y :=
    PseudoMetricSpace.dist_ofPreNNDist_le _ _ _
  have hle_d : ∀ {x y : G} {n : ℕ}, (1 / 2) ^ n ≤ d x y ↔ (x, y) ∉ U n := by
    intro x y n
    dsimp only [d]
    split_ifs with h
    · rw [(pow_right_strictAnti₀ hr.1 hr.2).le_iff_ge, Nat.find_le_iff]
      exact ⟨fun ⟨m, hmn, hm⟩ hn => hm (hB.antitone hmn hn),
        fun hn => ⟨n, le_rfl, hn⟩⟩
    · push Not at h
      simp only [h, not_true, (pow_pos hr.1 _).not_ge]
  have hd_le : ∀ x y, ↑(d x y) ≤ 2 * @dist G P.toDist x y := by
    refine PseudoMetricSpace.le_two_mul_dist_ofPreNNDist _ _ _
      (fun x₁ x₂ x₃ x₄ => ?_) 
    by_cases H : ∃ n, (x₁, x₄) ∉ U n
    · refine (dif_pos H).trans_le ?_
      rw [← div_le_iff₀' zero_lt_two, ← mul_one_div (_ ^ _), ← pow_succ]
      simp only [le_max_iff, hle_d, ← not_and_or]
      rintro ⟨h₁₂, h₂₃, h₃₄⟩
      refine Nat.find_spec H (hU_comp (lt_add_one (Nat.find H)) ?_)
      exact ⟨x₂, h₁₂, x₃, h₂₃, h₃₄⟩
    · exact (dif_neg H).trans_le (by positivity)
  rw [Set.mem_Ioo, ← NNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at hr
  have hPunif : P.toUniformSpace = (inferInstance : UniformSpace G) := by
    apply UniformSpace.ext
    refine (uniformity_basis_dist_pow hr.1 hr.2).ext hB.toHasBasis ?_ ?_
    · intro n hn
      refine ⟨n, hn, fun x hx => (hdist_le _ _).trans_lt ?_⟩
      rwa [← NNReal.coe_pow, NNReal.coe_lt_coe, ← not_le, hle_d, Classical.not_not]
    · intro n _
      refine ⟨n + 1, trivial, fun x hx => ?_⟩
      change @dist G P.toDist x.1 x.2 < (1 / 2 : ℝ) ^ (n + 1) at hx
      contrapose! hx
      refine le_trans ?_ ((div_le_iff₀' zero_lt_two).2 (hd_le x.1 x.2))
      have hbase : (1 / 2 : ℝ≥0) ^ n ≤ d x.1 x.2 := hle_d.mpr hx
      have hnn : (1 / 2 : ℝ≥0) ^ (n + 1) ≤ d x.1 x.2 / 2 := by
        simpa [pow_succ, div_eq_mul_inv, mul_assoc] using
          mul_le_mul_right' hbase (1 / 2 : ℝ≥0)
      exact_mod_cast hnn
  let m : MetricSpace G :=
    { P with
      eq_of_dist_eq_zero := by
        intro x y hxy
        have hdzero : d x y = 0 := by
          have hd := hd_le x y
          rw [hxy, mul_zero] at hd
          exact NNReal.coe_eq_zero.mp (le_antisymm hd (NNReal.zero_le_coe))
        exact inseparable_iff_eq.mp (hd₀.mp hdzero) }
  refine ⟨m, ?_, ?_⟩
  · change P.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace G)
    rw [hPunif]
    rfl
  · intro z x y
    change @dist G P.toDist (z * x) (z * y) = @dist G P.toDist x y
    rw [PseudoMetricSpace.dist_ofPreNNDist, PseudoMetricSpace.dist_ofPreNNDist]
    rw [NNReal.coe_inj]
    apply le_antisymm
    · refine le_ciInf fun l => ?_
      refine ciInf_le_of_le (OrderBot.bddBelow _)
        (l.map fun a => z * a) ?_
      induction l generalizing x y with
      | nil => simp [hd_left]
      | cons a l ih =>
          simp only [List.map_cons]
          simp [hd_left, ih]
    · refine le_ciInf fun l => ?_
      refine ciInf_le_of_le (OrderBot.bddBelow _)
        (l.map fun a => z⁻¹ * a) ?_
      induction l generalizing x y with
      | nil => simp [hd_left]
      | cons a l ih =>
          simp only [List.map_cons]
          apply add_le_add
          · exact le_of_eq (by simpa using (hd_left z x (z⁻¹ * a)).symm)
          · simpa using ih (z⁻¹ * a) y

/-- A metric neighborhood basis at `1` in the circle, chosen so that the
no-small-subgroups squaring criterion holds. -/
private def circleNSSBasis (n : ℕ) : Set Circle :=
  Metric.ball 1 ((1 / 2 : ℝ) * (3 / 4 : ℝ) ^ n)

private theorem circleNSSBasis_square {n : ℕ} {x : Circle}
    (hx : x ∈ circleNSSBasis n) (hx2 : x * x ∈ circleNSSBasis n) :
    x ∈ circleNSSBasis (n + 1) := by
  let r : ℝ := (1 / 2 : ℝ) * (3 / 4 : ℝ) ^ n
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  have hrle : r ≤ 1 / 2 := by
    dsimp [r]
    have hp : (3 / 4 : ℝ) ^ n ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hx' : ‖(x : ℂ) - 1‖ < r := by
    simpa [circleNSSBasis, r, Metric.mem_ball, Complex.dist_eq] using hx
  have hx2' : ‖(x : ℂ) * x - 1‖ < r := by
    simpa [circleNSSBasis, r, Metric.mem_ball, Complex.dist_eq] using hx2
  have hfac : ((x : ℂ) * x - 1) =
      ((x : ℂ) - 1) * ((x : ℂ) + 1) := by ring
  have hprod : ‖(x : ℂ) - 1‖ * ‖(x : ℂ) + 1‖ < r := by
    rw [← Complex.norm_mul, ← hfac]
    exact hx2'
  have htri := norm_add_le ((x : ℂ) + 1) (1 - (x : ℂ))
  have hsum : ((x : ℂ) + 1) + (1 - (x : ℂ)) = (2 : ℂ) := by ring
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hrev : ‖1 - (x : ℂ)‖ = ‖(x : ℂ) - 1‖ := norm_sub_rev _ _
  rw [hsum, hnorm2, hrev] at htri
  have hlarge : 3 / 2 < ‖(x : ℂ) + 1‖ := by nlinarith
  have hnonneg : 0 ≤ ‖(x : ℂ) - 1‖ := norm_nonneg _
  have hsmall : ‖(x : ℂ) - 1‖ < (3 / 4 : ℝ) * r := by
    nlinarith [mul_lt_mul_of_pos_left hlarge hrpos]
  change dist x 1 < (1 / 2 : ℝ) * (3 / 4 : ℝ) ^ (n + 1)
  rw [pow_succ]
  change ‖(x : ℂ) - 1‖ <
    (1 / 2 : ℝ) * ((3 / 4 : ℝ) ^ n * (3 / 4 : ℝ))
  convert hsmall using 1 <;> ring

private theorem circleNSSBasis_hasBasis :
    (nhds (1 : Circle)).HasBasis (fun _ : ℕ => True) circleNSSBasis := by
  apply Metric.nhds_basis_ball.to_hasBasis
  · intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (show 0 < (2 : ℝ) * ε by positivity)
      (show (3 / 4 : ℝ) < 1 by norm_num)
    refine ⟨n, trivial, Metric.ball_subset_ball ?_⟩
    dsimp [circleNSSBasis]
    nlinarith
  · intro n hn
    refine ⟨(1 / 2 : ℝ) * (3 / 4 : ℝ) ^ n, by positivity, ?_⟩
    exact Set.Subset.rfl

/--
Source: Theorem 0.4.9, Chapter 0, Section 4.
The character group is an abelian group under pointwise multiplication, and
with the compact-open topology it is a locally compact abelian topological
group.
-/
theorem characterGroupLocallyCompactAbelian
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] :
    Nonempty (CommGroup (CharacterGroup G)) ∧ IsTopologicalGroup (CharacterGroup G) ∧
      LocallyCompactSpace (CharacterGroup G) := by
  refine ⟨⟨inferInstance⟩, inferInstance, ?_⟩
  exact ContinuousMonoidHom.locallyCompactSpace_of_hasBasis
    circleNSSBasis circleNSSBasis_square circleNSSBasis_hasBasis

private noncomputable def circleAddEquiv :
    AddCircle (2 * Real.pi) ≃+ Additive Circle := by
  let hT : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  let e := AddCircle.homeomorphCircle hT
  refine
    { toFun := fun x => Additive.ofMul (e x)
      invFun := fun y => e.symm (Additive.toMul y)
      left_inv := by intro x; simp
      right_inv := by intro y; simp
      map_add' := ?_ }
  intro x y
  apply Additive.ofMul.injective
  change e (x + y) = e x * e y
  rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply,
    AddCircle.homeomorphCircle_apply, ← AddCircle.toCircle_add]

private noncomputable def circleAddHomeomorph :
    AddCircle (2 * Real.pi) ≃ₜ+ Additive Circle where
  toAddEquiv := circleAddEquiv
  continuous_toFun := by
    let hT : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact (AddCircle.homeomorphCircle hT).continuous
  continuous_invFun := by
    let hT : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact (AddCircle.homeomorphCircle hT).symm.continuous

private def subgroupToAddSubgroup (H : Subgroup Circle) :
    AddSubgroup (Additive Circle) where
  carrier := {x | Additive.toMul x ∈ H}
  zero_mem' := H.one_mem
  add_mem' := by intro x y hx hy; exact H.mul_mem hx hy
  neg_mem' := by intro x hx; exact H.inv_mem hx

private noncomputable def circleUnitsEquiv : Circle ≃* Circleˣ where
  toFun z :=
    { val := z
      inv := z⁻¹
      val_inv := by simp
      inv_val := by simp }
  invFun u := u.val
  left_inv z := rfl
  right_inv u := by ext; rfl
  map_mul' _ _ := by ext <;> simp

private noncomputable def circleRootsEquiv (p : ℕ) :
    {z : Circle // z ^ p = 1} ≃ rootsOfUnity p Circle := by
  let e := circleUnitsEquiv
  refine
    { toFun := fun z => ⟨e z.1, ?_⟩
      invFun := fun u => ⟨e.symm u.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change (e z.1) ^ p = 1
    simpa using congrArg e z.2
  · change (e.symm u.1) ^ p = 1
    have hu := u.2
    simpa using congrArg e.symm hu
  · intro z; rfl
  · intro u; ext; rfl

private theorem circleClosedSubgroup_cyclic_branch
    (H : Subgroup Circle) (_hH : IsClosed (H : Set Circle))
    (S : AddSubgroup (AddCircle (2 * Real.pi)))
    (hS : S = (subgroupToAddSubgroup H).comap circleAddHomeomorph.toAddMonoidHom)
    (a : AddCircle (2 * Real.pi)) (ha : addOrderOf a ≠ 0)
    (hcyclic : S = AddSubgroup.zmultiples a) :
    ∃ p : ℕ, 0 < p ∧ (H : Set Circle) = {z : Circle | z ^ p = 1} := by
  let p := addOrderOf a
  have hp : 0 < p := Nat.pos_of_ne_zero ha
  refine ⟨p, hp, ?_⟩
  letI : NeZero p := ⟨ha⟩
  have hcardRoots : Nat.card {z : Circle // z ^ p = 1} = p := by
    rw [Nat.card_congr (circleRootsEquiv p)]
    exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Circle p
  let eH : H ≃ S :=
    { toFun := fun z => ⟨circleAddHomeomorph.symm (Additive.ofMul z), by
          rw [hS]
          change Additive.toMul (circleAddHomeomorph
            (circleAddHomeomorph.symm (Additive.ofMul z))) ∈ H
          simpa using z.2⟩
      invFun := fun x => ⟨Additive.toMul (circleAddHomeomorph x), by
          have hx' : (x : AddCircle (2 * Real.pi)) ∈
              (subgroupToAddSubgroup H).comap
                circleAddHomeomorph.toAddMonoidHom := by
            rw [← hS]
            exact x.property
          exact hx'⟩
      left_inv := by intro z; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp }
  have hcardH : Nat.card H = p := by
    rw [Nat.card_congr eH, hcyclic, Nat.card_zmultiples]
  have hsub : (H : Set Circle) ⊆ {z : Circle | z ^ p = 1} := by
    intro z hz
    let x := circleAddHomeomorph.symm (Additive.ofMul z)
    have hxS : x ∈ S := by
      rw [hS]
      change Additive.toMul (circleAddHomeomorph x) ∈ H
      simpa [x] using hz
    rw [hcyclic] at hxS
    obtain ⟨n, hn⟩ := hxS
    have hpa : p • a = 0 := addOrderOf_nsmul_eq_zero a
    have hpaZ : (p : ℤ) • a = 0 := by simpa using hpa
    have hxp : p • x = 0 := by
      calc
        p • x = (p : ℤ) • x := by simp
        _ = (p : ℤ) • (n • a) :=
          congrArg (fun y => (p : ℤ) • y) hn.symm
        _ = ((p : ℤ) * n) • a := by rw [smul_smul]
        _ = (n * (p : ℤ)) • a :=
          congrArg (fun k : ℤ => k • a) (Int.mul_comm (p : ℤ) n)
        _ = n • ((p : ℤ) • a) := by rw [smul_smul]
        _ = 0 := by rw [hpaZ, smul_zero]
    have hzto : AddCircle.toCircle x = z := by
      have h := circleAddHomeomorph.apply_symm_apply (Additive.ofMul z)
      have hm := congrArg Additive.toMul h
      change Additive.toMul (circleAddHomeomorph x) = z at hm
      have hforward : Additive.toMul (circleAddHomeomorph x) =
          AddCircle.toCircle x := by
        change (AddCircle.homeomorphCircle _ x) = AddCircle.toCircle x
        rw [AddCircle.homeomorphCircle_apply]
      exact hforward.symm.trans hm
    change z ^ p = 1
    rw [← hzto, ← AddCircle.toCircle_nsmul, hxp]
    simp
  letI : Finite (rootsOfUnity p Circle) :=
    HasEnoughRootsOfUnity.finite_rootsOfUnity Circle p
  have ht : ({z : Circle | z ^ p = 1} : Set Circle).Finite := by
    change Finite {z : Circle // z ^ p = 1}
    exact Finite.of_injective (circleRootsEquiv p)
      (circleRootsEquiv p).injective
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (ht := ht)
  change Nat.card {z : Circle // z ^ p = 1} ≤ Nat.card H
  rw [hcardRoots, hcardH]

private theorem circleClosedSubgroup_dense_branch
    (H : Subgroup Circle) (hH : IsClosed (H : Set Circle))
    (S : AddSubgroup (AddCircle (2 * Real.pi)))
    (hS : S = (subgroupToAddSubgroup H).comap circleAddHomeomorph.toAddMonoidHom)
    (hDense : Dense (S : Set (AddCircle (2 * Real.pi)))) :
    H = ⊤ := by
  have hsubset : (S : Set (AddCircle (2 * Real.pi))) ⊆
      circleAddHomeomorph ⁻¹' (H : Set Circle) := by
    intro x hx
    rw [hS] at hx
    exact hx
  have hall : (Set.univ : Set (AddCircle (2 * Real.pi))) ⊆
      circleAddHomeomorph ⁻¹' (H : Set Circle) := by
    have hclosedPre : IsClosed (circleAddHomeomorph ⁻¹' (H : Set Circle)) :=
      hH.preimage circleAddHomeomorph.continuous
    have hc : closure (S : Set (AddCircle (2 * Real.pi))) ⊆
        circleAddHomeomorph ⁻¹' (H : Set Circle) :=
      (hclosedPre.closure_subset_iff).2 hsubset
    rw [hDense.closure_eq] at hc
    exact hc
  apply Subgroup.ext
  intro z
  have hz : z ∈ H := by
    obtain ⟨x, rfl⟩ := circleAddHomeomorph.surjective z
    exact hall (Set.mem_univ x)
  exact ⟨fun _ => trivial, fun _ => hz⟩

private theorem circleClosedSubgroupsClassification :
    IsCircleClosedSubgroupClassification := by
  letI : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩
  intro H hH
  let S : AddSubgroup (AddCircle (2 * Real.pi)) :=
    (subgroupToAddSubgroup H).comap circleAddHomeomorph.toAddMonoidHom
  by_cases hd : Dense (S : Set (AddCircle (2 * Real.pi)))
  · exact Or.inl (circleClosedSubgroup_dense_branch H hH S rfl hd)
  · right
    have hnotall :
        ¬ ∀ a, addOrderOf a ≠ 0 → S ≠ AddSubgroup.zmultiples a := by
      intro hall
      exact hd (AddCircle.dense_addSubgroup_iff_ne_zmultiples.mpr hall)
    push_neg at hnotall
    obtain ⟨a, ha, hEq⟩ := hnotall
    exact circleClosedSubgroup_cyclic_branch H hH S rfl a ha hEq

private theorem circleCharacterClassification
    (χ : CharacterGroup Circle) :
    ∃ m : ℤ, ∀ z : Circle, χ z = z ^ m := by
  let f : C(ℝ, Circle) :=
    ⟨fun t => χ (Circle.exp t), χ.continuous.comp Circle.exp.continuous⟩
  have he : Circle.exp 0 = f 0 := by simp [f]
  obtain ⟨F, hF, huniq⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0 he
  rcases hF with ⟨hF0, hFexp⟩
  have hFadd : ∀ x y : ℝ, F (x + y) = F x + F y := by
    intro x y
    let L : C(ℝ, ℝ) :=
      ⟨fun t => F (x + t) - F x,
        (F.continuous.comp (continuous_const.add continuous_id)).sub
          continuous_const⟩
    have hL0 : L 0 = 0 := by simp [L]
    have hLexp : Circle.exp ∘ L = f := by
      funext t
      have hx := congrFun hFexp x
      have hxt := congrFun hFexp (x + t)
      change Circle.exp (F x) = f x at hx
      change Circle.exp (F (x + t)) = f (x + t) at hxt
      change Circle.exp (F (x + t) - F x) = f t
      rw [Circle.exp_sub, hxt, hx]
      change χ (Circle.exp (x + t)) / χ (Circle.exp x) = χ (Circle.exp t)
      rw [Circle.exp_add, map_mul]
      simp
    have hLF : L = F := huniq L ⟨hL0, hLexp⟩
    have hpoint := DFunLike.congr_fun hLF y
    change F (x + y) - F x = F y at hpoint
    linarith
  let Fhom : ℝ →+ ℝ :=
    { toFun := F
      map_zero' := hF0
      map_add' := hFadd }
  have hFlinear : ∀ t : ℝ, F t = t * F 1 := by
    intro t
    have hm := (Fhom.toRealLinearMap F.continuous).map_smul t (1 : ℝ)
    simpa [Fhom, smul_eq_mul] using hm
  have hperiod : Circle.exp (F (2 * Real.pi)) = 1 := by
    have h := congrFun hFexp (2 * Real.pi)
    change Circle.exp (F (2 * Real.pi)) = f (2 * Real.pi) at h
    simpa [f] using h
  obtain ⟨m : ℤ, hmperiod⟩ := Circle.exp_eq_one.mp hperiod
  have hFone : F 1 = (m : ℝ) := by
    have hlin := hFlinear (2 * Real.pi)
    have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hne
    calc
      (2 * Real.pi) * F 1 = F (2 * Real.pi) := hlin.symm
      _ = (m : ℝ) * (2 * Real.pi) := hmperiod
      _ = (2 * Real.pi) * (m : ℝ) := by ring
  refine ⟨m, ?_⟩
  intro z
  let t := z.val.arg
  have hz : Circle.exp t = z := Circle.exp_arg z
  rw [← hz]
  have ht := congrFun hFexp t
  change Circle.exp (F t) = f t at ht
  have ht' : Circle.exp (F t) = χ (Circle.exp t) := by
    simpa [f] using ht
  rw [← ht', hFlinear, hFone]
  simpa [zsmul_eq_mul, mul_comm] using Circle.expHom.map_zsmul t m

private theorem circle_zpow_function_injective :
    Function.Injective (fun m : ℤ => fun z : Circle => z ^ m) := by
  intro m k hmk
  by_contra hne
  have hdne : m - k ≠ 0 := sub_ne_zero.mpr hne
  let p : ℕ := (m - k).natAbs + 1
  have hp : 0 < p := by simp [p]
  letI : NeZero p := ⟨hp.ne'⟩
  obtain ⟨ζ : Circle, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Circle p
  have heval : ζ ^ m = ζ ^ k := congrFun hmk ζ
  have hpow : ζ ^ (m - k) = 1 := by
    rw [zpow_sub, heval]
    simp
  have hdvd : (p : ℤ) ∣ m - k := (hζ.zpow_eq_one_iff_dvd (m - k)).mp hpow
  have hnatdvd : p ∣ (m - k).natAbs := by
    have h := (Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := m - k)).mpr hdvd
    simpa using h
  have hle : p ≤ (m - k).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hdne) hnatdvd
  omega

private theorem circleAutomorphismClassification
    (χ : ContinuousMonoidHom Circle Circle) (hχ : Function.Bijective χ) :
    (∀ z : Circle, χ z = z) ∨ (∀ z : Circle, χ z = z⁻¹) := by
  obtain ⟨m, hm⟩ := circleCharacterClassification χ
  let e : Circle ≃* Circle := MulEquiv.ofBijective χ.toMonoidHom hχ
  have hecont : Continuous e.symm := by
    rw [continuous_iff_isClosed]
    intro s hs
    have hset : e.symm ⁻¹' s = e '' s := by
      ext y
      constructor
      · intro hy
        exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
    rw [hset]
    exact χ.continuous.isClosedMap s hs
  let χinv : CharacterGroup Circle :=
    { toMonoidHom := e.symm.toMonoidHom
      continuous_toFun := hecont }
  obtain ⟨k, hk⟩ := circleCharacterClassification χinv
  have hmkfun : (fun z : Circle => z ^ (m * k)) = fun z => z ^ (1 : ℤ) := by
    funext z
    have hinv : χinv (χ z) = z := e.symm_apply_apply z
    rw [hm z] at hinv
    rw [hk (z ^ m)] at hinv
    simpa [zpow_mul] using hinv
  have hmkeq : m * k = 1 := circle_zpow_function_injective hmkfun
  have hdvd : m ∣ 1 := ⟨k, hmkeq.symm⟩
  have habsdvd : m.natAbs ∣ (1 : ℤ).natAbs :=
    (Int.natAbs_dvd_natAbs (a := m) (b := 1)).mpr hdvd
  have hmabs : m.natAbs = 1 := Nat.eq_one_of_dvd_one (by simpa using habsdvd)
  have hmunit : m = 1 ∨ m = -1 := by
    cases m with
    | ofNat a => left; simp_all
    | negSucc a => right; simp_all
  rcases hmunit with rfl | rfl
  · left
    intro z
    simpa using hm z
  · right
    intro z
    simpa using hm z

private noncomputable def circleCoordinateHom (i : Fin n) :
    ContinuousMonoidHom Circle (Fin n → Circle) where
  toFun z j := if j = i then z else 1
  map_one' := by
    funext j
    split_ifs <;> rfl
  map_mul' x y := by
    funext j
    by_cases h : j = i <;> simp [h]
  continuous_toFun := by
    apply continuous_pi
    intro j
    by_cases h : j = i
    · subst j
      simpa using (continuous_id : Continuous (fun z : Circle => z))
    · simpa [h] using (continuous_const : Continuous (fun _ : Circle => (1 : Circle)))

private theorem torusCharacterClassification
    (n : ℕ) (φ : CharacterGroup (Fin n → Circle)) :
    ∃ m : Fin n → ℤ, ∀ z : Fin n → Circle,
      φ z = Finset.univ.prod fun i : Fin n => z i ^ m i := by
  have hi : ∀ i : Fin n, ∃ m : ℤ, ∀ z : Circle,
      φ (circleCoordinateHom i z) = z ^ m := by
    intro i
    exact circleCharacterClassification (φ.comp (circleCoordinateHom i))
  choose m hm using hi
  refine ⟨m, ?_⟩
  intro z
  have hz : z = Finset.univ.prod fun i : Fin n => circleCoordinateHom i (z i) := by
    funext j
    simp only [Finset.prod_apply]
    change z j = Finset.univ.prod fun i : Fin n => if j = i then z i else 1
    simp
  calc
    φ z = φ (Finset.univ.prod fun i : Fin n => circleCoordinateHom i (z i)) :=
      congrArg φ hz
    _ = Finset.univ.prod (fun i : Fin n => φ (circleCoordinateHom i (z i))) :=
      map_prod φ _ _
    _ = Finset.univ.prod (fun i : Fin n => z i ^ m i) :=
      Finset.prod_congr rfl fun i _ => hm i (z i)

/--
Source: Theorem 0.4.11, Chapter 0, Section 4.
Closed subgroups and continuous automorphisms of the circle; characters of the
circle and finite tori are monomials with integer exponents.
-/
theorem circleClosedSubgroupsAutomorphismsAndCharacters :
    IsCircleClosedSubgroupClassification ∧
      (∀ χ : ContinuousMonoidHom Circle Circle, Function.Bijective χ ->
        (∀ z : Circle, χ z = z) ∨ (∀ z : Circle, χ z = z⁻¹)) ∧
      (∀ χ : CharacterGroup Circle,
        ∃ m : ℤ, ∀ z : Circle, χ z = z ^ m) ∧
      ∀ n : ℕ, ∀ φ : CharacterGroup (Fin n -> Circle),
        ∃ m : Fin n -> ℤ, ∀ z : Fin n -> Circle,
          φ z = Finset.univ.prod fun i : Fin n => z i ^ m i := by
  exact ⟨circleClosedSubgroupsClassification, circleAutomorphismClassification,
    circleCharacterClassification, torusCharacterClassification⟩

private def torusCharacter (m : Fin n → ℤ) :
    CharacterGroup (Fin n → Circle) :=
  { toMonoidHom :=
      { toFun := fun z => Finset.univ.prod fun i : Fin n => z i ^ m i
        map_one' := by simp
        map_mul' := by
          intro x y
          simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib] }
    continuous_toFun := by
      fun_prop }

private def torusCharacterHom (n : ℕ) :
    (Fin n → Multiplicative ℤ) →* CharacterGroup (Fin n → Circle) where
  toFun m := torusCharacter (fun i => (m i).toAdd)
  map_one' := by
    apply ContinuousMonoidHom.ext
    intro z
    change Finset.univ.prod (fun i : Fin n => z i ^ (0 : ℤ)) = 1
    simp
  map_mul' m k := by
    apply ContinuousMonoidHom.ext
    intro z
    change Finset.univ.prod (fun i : Fin n =>
      z i ^ ((m i).toAdd + (k i).toAdd)) =
      (Finset.univ.prod (fun i : Fin n => z i ^ (m i).toAdd)) *
        (Finset.univ.prod (fun i : Fin n => z i ^ (k i).toAdd))
    rw [← Finset.prod_mul_distrib]
    congr 1
    funext i
    rw [zpow_add]

private theorem torusCharacterHom_injective (n : ℕ) :
    Function.Injective (torusCharacterHom n) := by
  intro m k hmk
  funext i
  apply Multiplicative.toAdd.injective
  apply circle_zpow_function_injective
  funext z
  have heval := DFunLike.congr_fun hmk (fun j => if j = i then z else 1)
  dsimp [torusCharacterHom, torusCharacter] at heval
  change torusCharacter (fun j => (m j).toAdd) (fun j => if j = i then z else 1) =
    torusCharacter (fun j => (k j).toAdd) (fun j => if j = i then z else 1) at heval
  dsimp [torusCharacter] at heval
  change (Finset.univ.prod (fun j : Fin n =>
      (if j = i then z else 1) ^ (m j).toAdd)) =
    Finset.univ.prod (fun j : Fin n =>
      (if j = i then z else 1) ^ (k j).toAdd) at heval
  simpa [Finset.prod_ite_eq'] using heval

private theorem torusCharacterHom_surjective (n : ℕ) :
    Function.Surjective (torusCharacterHom n) := by
  intro φ
  obtain ⟨m, hm⟩ := (circleClosedSubgroupsAutomorphismsAndCharacters.2.2.2 n φ)
  refine ⟨fun i => Multiplicative.ofAdd (m i), ?_⟩
  apply ContinuousMonoidHom.ext
  intro z
  simpa [torusCharacterHom, torusCharacter] using (hm z).symm

/--
Source: Corollary 0.4.12, Chapter 0, Section 4.
The dual group of the `n`-torus is naturally isomorphic to `ℤ^n`.
-/
theorem torusDualIsIntegerLattice (n : ℕ) :
    Nonempty (CharacterGroup (Fin n -> Circle) ≃* (Fin n -> Multiplicative ℤ)) := by
  exact ⟨(MulEquiv.ofBijective (torusCharacterHom n)
    ⟨torusCharacterHom_injective n, torusCharacterHom_surjective n⟩).symm⟩

private def matrixTorusMap {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    ContinuousMonoidHom (Fin n → Circle) (Fin n → Circle) where
  toFun z i := Finset.univ.prod fun j : Fin n => z j ^ M i j
  map_one' := by funext i; simp
  map_mul' x y := by
    funext i
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
  continuous_toFun := by fun_prop

private theorem matrixTorusMap_injective {n : ℕ} :
    Function.Injective (matrixTorusMap (n := n)) := by
  intro M N hMN
  funext i j
  apply circle_zpow_function_injective
  funext z
  have h := DFunLike.congr_fun hMN (fun k => if k = j then z else 1)
  have hi := congrFun h i
  change (∏ k : Fin n, (if k = j then z else 1) ^ M i k) =
    ∏ k : Fin n, (if k = j then z else 1) ^ N i k at hi
  simpa [Finset.prod_ite_eq'] using hi

private theorem matrixTorusMap_mul {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℤ) :
    (matrixTorusMap M).comp (matrixTorusMap N) =
      matrixTorusMap (M * N) := by
  apply ContinuousMonoidHom.ext
  intro z
  funext i
  change (∏ j : Fin n, (∏ k : Fin n, z k ^ N j k) ^ M i j) =
    ∏ k : Fin n, z k ^ (∑ j : Fin n, M i j * N j k)
  have zpow_finset_sum (w : Circle) (s : Finset (Fin n)) (f : Fin n → ℤ) :
      w ^ (∑ j ∈ s, f j) = ∏ j ∈ s, w ^ f j := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [ha, zpow_add, ih]
  calc
    (∏ j : Fin n, (∏ k : Fin n, z k ^ N j k) ^ M i j) =
        ∏ j : Fin n, ∏ k : Fin n, (z k ^ N j k) ^ M i j := by
          apply Finset.prod_congr rfl
          intro j _
          simpa using
            (Finset.prod_zpow (fun k : Fin n => z k ^ N j k)
              Finset.univ (M i j)).symm
    _ = ∏ k : Fin n, ∏ j : Fin n, (z k ^ N j k) ^ M i j :=
      Finset.prod_comm
    _ = ∏ k : Fin n, z k ^ (∑ j : Fin n, M i j * N j k) := by
      apply Finset.prod_congr rfl
      intro k _
      rw [zpow_finset_sum]
      apply Finset.prod_congr rfl
      intro j _
      rw [← zpow_mul]
      congr 1
      exact mul_comm _ _

private theorem matrixTorusMap_one {n : ℕ} :
    matrixTorusMap (1 : Matrix (Fin n) (Fin n) ℤ) =
      ContinuousMonoidHom.id (Fin n → Circle) := by
  apply ContinuousMonoidHom.ext
  intro z
  funext i
  change (∏ j : Fin n, z j ^ (1 : Matrix (Fin n) (Fin n) ℤ) i j) = z i
  simp [Matrix.one_apply]

private theorem matrixTorusMap_smul_one {n : ℕ} (d : ℤ)
    (z : Fin n → Circle) :
    matrixTorusMap (d • (1 : Matrix (Fin n) (Fin n) ℤ)) z =
      fun i => z i ^ d := by
  funext i
  change (∏ j : Fin n,
    z j ^ (d • (1 : Matrix (Fin n) (Fin n) ℤ)) i j) = z i ^ d
  simp [Matrix.one_apply]

private theorem matrixTorusMap_surjective_of_det_ne_zero {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ) (hdet : M.det ≠ 0) :
    Function.Surjective (matrixTorusMap M) := by
  letI : NeZero M.det := ⟨hdet⟩
  have hpowsurj : Function.Surjective (fun w : Circle => w ^ M.det) :=
    (Circle.isQuotientCoveringMap_zpow M.det).surjective
  intro y
  choose w hw using fun i : Fin n => hpowsurj (y i)
  refine ⟨matrixTorusMap M.adjugate w, ?_⟩
  have hcomp := DFunLike.congr_fun (matrixTorusMap_mul M M.adjugate) w
  change matrixTorusMap M (matrixTorusMap M.adjugate w) =
    matrixTorusMap (M * M.adjugate) w at hcomp
  change matrixTorusMap M (matrixTorusMap M.adjugate w) = y
  rw [hcomp]
  rw [Matrix.mul_adjugate]
  rw [matrixTorusMap_smul_one]
  funext i
  exact hw i

private theorem matrixTorusMap_character_of_vecMul_eq_zero {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ)
    (hv : Matrix.vecMul v M = 0) (z : Fin n → Circle) :
    (Finset.univ.prod fun i : Fin n => (matrixTorusMap M z i) ^ v i) = 1 := by
  change (∏ i : Fin n, (∏ j : Fin n, z j ^ M i j) ^ v i) = 1
  have zpow_finset_sum (w : Circle) (s : Finset (Fin n)) (f : Fin n → ℤ) :
      w ^ (∑ i ∈ s, f i) = ∏ i ∈ s, w ^ f i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [ha, zpow_add, ih]
  calc
    (∏ i : Fin n, (∏ j : Fin n, z j ^ M i j) ^ v i) =
        ∏ i : Fin n, ∏ j : Fin n, (z j ^ M i j) ^ v i := by
          apply Finset.prod_congr rfl
          intro i _
          simpa using
            (Finset.prod_zpow (fun j : Fin n => z j ^ M i j)
              Finset.univ (v i)).symm
    _ = ∏ j : Fin n, ∏ i : Fin n, (z j ^ M i j) ^ v i :=
      Finset.prod_comm
    _ = ∏ j : Fin n, z j ^ (∑ i : Fin n, v i * M i j) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [zpow_finset_sum]
      apply Finset.prod_congr rfl
      intro i _
      rw [← zpow_mul]
      congr 1
      exact mul_comm _ _
    _ = 1 := by
      have hvj : ∀ j : Fin n, (∑ i : Fin n, v i * M i j) = 0 := by
        intro j
        have h := congrFun hv j
        simpa [Matrix.vecMul, dotProduct] using h
      simp [hvj]

private theorem matrixTorusMap_det_ne_zero_of_surjective {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ)
    (hsurj : Function.Surjective (matrixTorusMap M)) : M.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hvne, hvM⟩ :=
    (Matrix.exists_vecMul_eq_zero_iff (M := M)).mpr hdet
  have hchar : ∀ y : Fin n → Circle,
      (Finset.univ.prod fun i : Fin n => y i ^ v i) = 1 := by
    intro y
    obtain ⟨z, rfl⟩ := hsurj y
    exact matrixTorusMap_character_of_vecMul_eq_zero M v hvM z
  have hvzero : v = 0 := by
    funext i
    apply circle_zpow_function_injective
    funext z
    have h := hchar (fun j => if j = i then z else 1)
    simpa [Finset.prod_ite_eq'] using h
  exact hvne hvzero

private theorem matrixTorusMap_exists_matrix {n : ℕ}
    (A : ContinuousMonoidHom (Fin n → Circle) (Fin n → Circle)) :
    ∃ M : Matrix (Fin n) (Fin n) ℤ, A = matrixTorusMap M := by
  let χ : Fin n → CharacterGroup (Fin n → Circle) := fun i =>
    { toFun := fun z => A z i
      map_one' := by simp
      map_mul' := by intro x y; simp
      continuous_toFun := (continuous_apply i).comp A.continuous }
  have hi : ∀ i : Fin n, ∃ m : Fin n → ℤ, ∀ z : Fin n → Circle,
      χ i z = Finset.univ.prod fun j : Fin n => z j ^ m j := by
    intro i
    exact circleClosedSubgroupsAutomorphismsAndCharacters.2.2.2 n (χ i)
  choose m hm using hi
  refine ⟨fun i j => m i j, ?_⟩
  apply ContinuousMonoidHom.ext
  intro z
  funext i
  exact hm i z

private theorem matrixTorusMap_bijective_of_isUnit_det {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ) (hunit : IsUnit M.det) :
    Function.Bijective (matrixTorusMap M) := by
  have hMunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr hunit
  obtain ⟨u, hu⟩ := hMunit
  let N : Matrix (Fin n) (Fin n) ℤ := (↑u⁻¹ : Matrix (Fin n) (Fin n) ℤ)
  have hMN : M * N = 1 := by
    rw [← hu]
    simp [N]
  have hNM : N * M = 1 := by
    rw [← hu]
    simp [N]
  let e : (Fin n → Circle) ≃ (Fin n → Circle) :=
    { toFun := matrixTorusMap M
      invFun := matrixTorusMap N
      left_inv := by
        intro z
        have h := DFunLike.congr_fun (matrixTorusMap_mul N M) z
        change matrixTorusMap N (matrixTorusMap M z) =
          matrixTorusMap (N * M) z at h
        rw [hNM] at h
        have h1 := DFunLike.congr_fun matrixTorusMap_one z
        exact h.trans h1
      right_inv := by
        intro z
        have h := DFunLike.congr_fun (matrixTorusMap_mul M N) z
        change matrixTorusMap M (matrixTorusMap N z) =
          matrixTorusMap (M * N) z at h
        rw [hMN] at h
        have h1 := DFunLike.congr_fun matrixTorusMap_one z
        exact h.trans h1 }
  exact e.bijective

private theorem matrixTorusMap_det_eq_one_or_neg_one_of_bijective {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ)
    (hbij : Function.Bijective (matrixTorusMap M)) :
    M.det = 1 ∨ M.det = -1 := by
  let e : (Fin n → Circle) ≃* (Fin n → Circle) :=
    MulEquiv.ofBijective (matrixTorusMap M).toMonoidHom hbij
  have hecont : Continuous e.symm := by
    rw [continuous_iff_isClosed]
    intro s hs
    have hset : e.symm ⁻¹' s = e '' s := by
      ext y
      constructor
      · intro hy
        exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
    rw [hset]
    exact (matrixTorusMap M).continuous.isClosedMap s hs
  let Ainv : ContinuousMonoidHom (Fin n → Circle) (Fin n → Circle) :=
    { toMonoidHom := e.symm.toMonoidHom
      continuous_toFun := hecont }
  obtain ⟨N, hN⟩ := matrixTorusMap_exists_matrix Ainv
  have hcomp : (matrixTorusMap M).comp (matrixTorusMap N) =
      ContinuousMonoidHom.id (Fin n → Circle) := by
    rw [← hN]
    apply ContinuousMonoidHom.ext
    intro z
    exact e.apply_symm_apply z
  have hMN : M * N = 1 := by
    apply matrixTorusMap_injective
    rw [← matrixTorusMap_mul, matrixTorusMap_one]
    exact hcomp
  have hunit : IsUnit M.det := Matrix.isUnit_det_of_right_inverse hMN
  simpa [Int.isUnit_iff] using hunit

/--
Source: Theorem 0.4.13, Chapter 0, Section 4.
Endomorphisms of the `n`-torus are represented by integer matrices; such an
endomorphism is surjective iff the determinant is nonzero and an automorphism
iff the determinant is `±1`.
-/
theorem torusEndomorphismsAreIntegerMatrices (n : ℕ) :
    ∀ A : ContinuousMonoidHom (Fin n -> Circle) (Fin n -> Circle),
      ∃! M : Matrix (Fin n) (Fin n) ℤ,
        (∀ z : Fin n -> Circle, ∀ i : Fin n,
          A z i = Finset.univ.prod fun j : Fin n => z j ^ M i j) ∧
        (Function.Surjective A ↔ M.det ≠ 0) ∧
        (Function.Bijective A ↔ M.det = 1 ∨ M.det = -1) := by
  intro A
  obtain ⟨M, hA⟩ := matrixTorusMap_exists_matrix A
  refine ⟨M, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro z i
      have hz := DFunLike.congr_fun hA z
      have hi := congrFun hz i
      simpa [matrixTorusMap] using hi
    · rw [hA]
      exact ⟨matrixTorusMap_det_ne_zero_of_surjective M,
        matrixTorusMap_surjective_of_det_ne_zero M⟩
    · rw [hA]
      constructor
      · exact matrixTorusMap_det_eq_one_or_neg_one_of_bijective M
      · intro hdet
        apply matrixTorusMap_bijective_of_isUnit_det M
        simpa [Int.isUnit_iff] using hdet
  · intro N hN
    apply matrixTorusMap_injective
    have hAN : A = matrixTorusMap N := by
      apply ContinuousMonoidHom.ext
      intro z
      funext i
      simpa [matrixTorusMap] using hN.1 z i
    exact hAN.symm.trans hA

/--
Source: Definition 0.4.1, Chapter 0, Section 4.
A topological group is a group with a topology for which multiplication and
inversion are continuous.
-/
def topologicalGroupDefinition
    (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  T2Space G ∧ IsTopologicalGroup G

/--
Source: Definition 0.4.2, Chapter 0, Section 4.
Left and right Haar measures on a topological group.
-/
def haarMeasureDefinition (G : Type u) [Group G] [TopologicalSpace G]
    [T2Space G] [MeasurableSpace G] (μ : MeasureTheory.Measure G) : Prop :=
  IsRadonHaarMeasure μ

/-- Source: discussion following Theorem 0.4.3. On a locally compact abelian
group, every left Haar measure is also right invariant. -/
theorem commutativeHaarMeasureIsRightInvariant
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) (hμ : IsRadonHaarMeasure μ) :
    rightHaarMeasureDefinition G μ ∧
      ∀ x : G, ∀ A : Set G, MeasurableSet A ->
        μ ((fun y : G => y * x) ⁻¹' A) = μ A := by
  letI : MeasureTheory.Measure.IsHaarMeasure μ := hμ.1
  letI : μ.Regular := hμ.2
  let f : G →ₜ* G :=
    { toMonoidHom :=
        { toFun := fun y => y⁻¹
          map_one' := inv_one
          map_mul' := by intro a b; simp [mul_comm] }
      continuous_toFun := continuous_inv }
  have hf : Function.Surjective (f : G → G) := by
    intro y; exact ⟨y⁻¹, by change (y⁻¹)⁻¹ = y; simp⟩
  have hc : Filter.Tendsto (f : G → G) (cocompact G) (cocompact G) := by
    change Filter.Tendsto (fun y : G => y⁻¹) (cocompact G) (cocompact G)
    have ht := Filter.tendsto_map (f := fun y : G => y⁻¹) (x := cocompact G)
    have hm := Homeomorph.map_cocompact (Homeomorph.inv G)
    change Filter.map (fun y : G => y⁻¹) (cocompact G) = cocompact G at hm
    simpa [hm] using ht
  constructor
  · refine ⟨MeasureTheory.Measure.isHaarMeasure_map μ f.toMonoidHom
      f.continuous hf hc, ?_⟩
    simpa [f] using
      (MeasureTheory.Measure.Regular.map (μ := μ) (Homeomorph.inv G))
  · intro x A hA
    letI : MeasureTheory.Measure.IsMulRightInvariant μ := ⟨fun g => by
      simpa [mul_comm] using
        (MeasureTheory.Measure.IsMulLeftInvariant.map_mul_left_eq_self (μ := μ) g)⟩
    have hmap : MeasureTheory.Measure.map (fun y : G => y * x) μ = μ :=
      MeasureTheory.Measure.IsMulRightInvariant.map_mul_right_eq_self x
    have hval := congrArg (fun ν : MeasureTheory.Measure G => ν A) hmap
    change MeasureTheory.Measure.map (fun y : G => y * x) μ A = μ A at hval
    rw [MeasureTheory.Measure.map_apply
      (MeasurableMul.measurable_mul_const x) hA] at hval
    exact hval

/--
Source: Remark 0.4.5, Chapter 0, Section 4.
Construction of a compatible left-invariant metric from a countable decreasing
base at the identity.
-/
theorem leftInvariantMetricConstructionRemark
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (m : MeasureTheory.Measure G)
    (hm : IsRadonHaarMeasure m) (V : ℕ -> Set G)
    (hVopen : ∀ n, IsOpen (V n)) (hVid : ∀ n, 1 ∈ V n)
    (hbase : ∀ U : Set G, IsOpen U -> 1 ∈ U ->
      ∃ n, V n ⊆ U) (hcompact : IsCompact (V 0))
    (hmono : Antitone V) :
    ∃ d : G -> G -> ℝ,
      (∀ x y, d x y = sSup (Set.range fun n =>
        ENNReal.toReal (m (symmDiff ((fun g => x * g) '' V n)
          ((fun g => y * g) '' V n))))) ∧
      (∀ x, d x x = 0) ∧
      (∀ x y, 0 ≤ d x y) ∧
      (∀ x y, d x y = 0 ↔ x = y) ∧
      (∀ x y, d x y = d y x) ∧
      (∀ x y z, d x z ≤ d x y + d y z) ∧
      (∀ z x y, d (z * x) (z * y) = d x y) ∧
      ∀ U : Set G, IsOpen U ↔
        ∀ x ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∀ y, d x y < ε -> y ∈ U := by
  letI : MeasureTheory.Measure.IsHaarMeasure m := hm.1
  letI : m.Regular := hm.2
  let A : ℕ → G → Set G := fun n x => (fun g : G => x * g) '' V n
  let δ : ℕ → G → G → ℝ := fun n x y =>
    ENNReal.toReal (m (symmDiff (A n x) (A n y)))
  let d : G → G → ℝ := fun x y => sSup (Set.range fun n => δ n x y)
  have hVmeas (n : ℕ) : MeasurableSet (V n) := (hVopen n).measurableSet
  have hVsub (n : ℕ) : V n ⊆ V 0 := hmono (Nat.zero_le n)
  have hVfin (n : ℕ) : m (V n) ≠ ⊤ := by
    exact ne_top_of_le_ne_top hcompact.measure_lt_top.ne
      (MeasureTheory.measure_mono (hVsub n))
  have hAmeas (n : ℕ) (x : G) : MeasurableSet (A n x) := by
    exact ((Homeomorph.mulLeft x).isOpenMap (V n) (hVopen n)).measurableSet
  have hAmeasure (n : ℕ) (x : G) : m (A n x) = m (V n) := by
    change m (x • V n) = m (V n)
    exact MeasureTheory.measure_smul m x (V n)
  have hAfin (n : ℕ) (x : G) : m (A n x) ≠ ⊤ := by
    rw [hAmeasure]
    exact hVfin n
  have hδfin (n : ℕ) (x y : G) :
      m (symmDiff (A n x) (A n y)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hAfin n x, hAfin n y⟩) ?_
    calc
      m (symmDiff (A n x) (A n y)) ≤ m (A n x ∪ A n y) := by
        apply MeasureTheory.measure_mono
        rintro g (hg | hg) <;> simp_all
      _ ≤ m (A n x) + m (A n y) := MeasureTheory.measure_union_le _ _
  have hδnonneg (n : ℕ) (x y : G) : 0 ≤ δ n x y := ENNReal.toReal_nonneg
  have hδbound (n : ℕ) (x y : G) :
      δ n x y ≤ 2 * ENNReal.toReal (m (V 0)) := by
    have hle : m (symmDiff (A n x) (A n y)) ≤ m (V 0) + m (V 0) := by
      calc
        m (symmDiff (A n x) (A n y)) ≤ m (A n x) + m (A n y) := by
          calc
            m (symmDiff (A n x) (A n y)) ≤ m (A n x ∪ A n y) := by
              apply MeasureTheory.measure_mono
              rintro g (hg | hg) <;> simp_all
            _ ≤ m (A n x) + m (A n y) := MeasureTheory.measure_union_le _ _
        _ = m (V n) + m (V n) := by rw [hAmeasure, hAmeasure]
        _ ≤ m (V 0) + m (V 0) := add_le_add
          (MeasureTheory.measure_mono (hVsub n))
          (MeasureTheory.measure_mono (hVsub n))
    change (m (symmDiff (A n x) (A n y))).toReal ≤ _
    calc
      _ ≤ (m (V 0) + m (V 0)).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hVfin 0, hVfin 0⟩) hle
      _ = (m (V 0)).toReal + (m (V 0)).toReal :=
        ENNReal.toReal_add (hVfin 0) (hVfin 0)
      _ = 2 * (m (V 0)).toReal := (two_mul _).symm
  have hBdd (x y : G) : BddAbove (Set.range fun n => δ n x y) :=
    ⟨2 * ENNReal.toReal (m (V 0)), by rintro _ ⟨n, rfl⟩; exact hδbound n x y⟩
  have hδle (n : ℕ) (x y : G) : δ n x y ≤ d x y :=
    le_csSup (hBdd x y) ⟨n, rfl⟩
  have hInter : (⋂ n, V n) = ({1} : Set G) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_singleton_iff]
    constructor
    · intro hg
      by_contra hgne
      have hopen : IsOpen ({g}ᶜ : Set G) := isClosed_singleton.isOpen_compl
      have h1 : (1 : G) ∈ ({g}ᶜ : Set G) := by simpa [eq_comm]
      obtain ⟨n, hn⟩ := hbase {g}ᶜ hopen h1
      exact (hn (hg n)) (by simp)
    · rintro rfl n
      exact hVid n
  let F : C(G, C(G, G)) :=
    (ContinuousMap.mk (fun p : G × G => p.1⁻¹ * p.2)
      ((continuous_inv.comp continuous_fst).mul continuous_snd)).curry
  have hFpres (z : G) : MeasureTheory.MeasurePreserving (F z) m m := by
    simpa [F] using MeasureTheory.measurePreserving_mul_left m z⁻¹
  have hsymm (S T : Set G) :
      symmDiff S T = _root_.symmDiff S T := rfl
  have hcoord (n : ℕ) (x : G) :
      Tendsto (fun y => δ n x y) (𝓝 x) (𝓝 0) := by
    have ht := MeasureTheory.tendsto_measure_symmDiff_preimage_nhds_zero
      (μ := m) (ν := m) (f := fun y => F y) (g := F x) (s := V n)
      F.continuous.continuousAt (Filter.Eventually.of_forall hFpres) (hFpres x)
      (hVmeas n).nullMeasurableSet (hVfin n)
    have htr := (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp ht
    convert htr using 1
    · funext y
      apply congrArg ENNReal.toReal
      apply congrArg m
      rw [hsymm]
      ext g
      simp [A, F, Set.mem_symmDiff, or_comm, and_comm]
  have hdself (x : G) : d x x = 0 := by
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨n, rfl⟩
      change (m (symmDiff (A n x) (A n x))).toReal ≤ 0
      have he : symmDiff (A n x) (A n x) = ∅ := by
        ext g
        simp [symmDiff]
      simp [he]
    · exact (hδnonneg 0 x x).trans (hδle 0 x x)
  have hdnonneg (x y : G) : 0 ≤ d x y :=
    (hδnonneg 0 x y).trans (hδle 0 x y)
  have hδboundAt (n : ℕ) (x y : G) :
      δ n x y ≤ 2 * ENNReal.toReal (m (V n)) := by
    have hle : m (symmDiff (A n x) (A n y)) ≤ m (V n) + m (V n) := by
      calc
        m (symmDiff (A n x) (A n y)) ≤ m (A n x ∪ A n y) := by
          apply MeasureTheory.measure_mono
          rintro g (hg | hg) <;> simp_all
        _ ≤ m (A n x) + m (A n y) := MeasureTheory.measure_union_le _ _
        _ = m (V n) + m (V n) := by rw [hAmeasure, hAmeasure]
    change (m (symmDiff (A n x) (A n y))).toReal ≤ _
    calc
      _ ≤ (m (V n) + m (V n)).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hVfin n, hVfin n⟩) hle
      _ = (m (V n)).toReal + (m (V n)).toReal :=
        ENNReal.toReal_add (hVfin n) (hVfin n)
      _ = 2 * (m (V n)).toReal := (two_mul _).symm
  have hdtendsto (x : G) : Tendsto (fun y => d x y) (𝓝 x) (𝓝 0) := by
    by_cases hatom : m ({1} : Set G) = 0
    · have htV := MeasureTheory.tendsto_measure_iInter_atTop
        (μ := m) (fun n => (hVmeas n).nullMeasurableSet) hmono ⟨0, hVfin 0⟩
      rw [hInter, hatom] at htV
      have htR := (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp htV
      have htTail : Tendsto (fun n => 2 * ENNReal.toReal (m (V n)))
          atTop (𝓝 0) := by
        convert htR.const_mul 2 using 1 <;> simp [Function.comp_def]
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hhalf : 0 < ε / 2 := half_pos hε
      have hevTail := htTail.eventually (Iio_mem_nhds hhalf)
      obtain ⟨N, hN⟩ := eventually_atTop.1 hevTail
      have hevFinite : ∀ᶠ y in 𝓝 x,
          ∀ n ∈ Finset.range N, δ n x y < ε / 2 := by
        rw [Finset.eventually_all]
        intro n hn
        exact (hcoord n x).eventually (Iio_mem_nhds hhalf)
      filter_upwards [hevFinite] with y hy
      have hdle : d x y ≤ ε / 2 := by
        apply csSup_le (Set.range_nonempty _)
        rintro _ ⟨n, rfl⟩
        by_cases hn : n < N
        · exact (hy n (Finset.mem_range.mpr hn)).le
        · have hVN : m (V n) ≤ m (V N) :=
            MeasureTheory.measure_mono (hmono (Nat.le_of_not_gt hn))
          have hreal : ENNReal.toReal (m (V n)) ≤ ENNReal.toReal (m (V N)) :=
            ENNReal.toReal_mono (hVfin N) hVN
          exact (hδboundAt n x y).trans <|
            (mul_le_mul_of_nonneg_left hreal (by positivity)).trans
              (hN N le_rfl).le
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hdnonneg x y)]
      exact hdle.trans_lt (half_lt_self hε)
    · have hpos : 0 < m ({1} : Set G) := pos_iff_ne_zero.mpr hatom
      have hfin : m ({1} : Set G) ≠ ⊤ :=
        MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact
          (isCompact_singleton : IsCompact ({1} : Set G)) |>.ne
      have hsnh : ({1} : Set G) ∈ 𝓝 (1 : G) := by
        simpa using MeasureTheory.Measure.div_mem_nhds_one_of_haar_pos_ne_top
          m ({1} : Set G) (MeasurableSet.singleton (1 : G)) hpos hfin
      obtain ⟨O, hOsub, hOo, h1O⟩ := mem_nhds_iff.mp hsnh
      have hOeq : O = ({1} : Set G) := by
        apply Set.Subset.antisymm hOsub
        simpa using h1O
      have hsopen : IsOpen ({1} : Set G) := by simpa [hOeq] using hOo
      have hxopen : IsOpen ({x} : Set G) := by
        simpa using (Homeomorph.mulLeft x).isOpenMap {1} hsopen
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hxopen.mem_nhds (by simp)] with y hy
      have hyx : y = x := by simpa using hy
      subst y
      simp [hdself x, hε]
  refine ⟨d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    rfl
  · intro x
    exact hdself x
  · intro x y
    exact hdnonneg x y
  · intro x y
    constructor
    · intro hd
      by_contra hxy
      obtain ⟨U, W, hUo, hWo, hxU, hyW, hUW⟩ := t2_separation hxy
      have hNx : (fun g : G => x * g) ⁻¹' U ∈ 𝓝 (1 : G) := by
        have hopen := hUo.preimage (continuous_mul_left x)
        exact hopen.mem_nhds (by simpa using hxU)
      have hNy : (fun g : G => y * g) ⁻¹' W ∈ 𝓝 (1 : G) := by
        have hopen := hWo.preimage (continuous_mul_left y)
        exact hopen.mem_nhds (by simpa using hyW)
      obtain ⟨O, hOsub, hOo, h1O⟩ :=
        mem_nhds_iff.mp (inter_mem hNx hNy)
      obtain ⟨n, hn⟩ := hbase O hOo h1O
      have hAx : A n x ⊆ U := by
        rintro _ ⟨g, hg, rfl⟩
        exact (hOsub (hn hg)).1
      have hAy : A n y ⊆ W := by
        rintro _ ⟨g, hg, rfl⟩
        exact (hOsub (hn hg)).2
      have hdisj : Disjoint (A n x) (A n y) := hUW.mono hAx hAy
      have hposV : 0 < m (V n) :=
        (hVopen n).measure_pos m ⟨1, hVid n⟩
      have hmonoA : m (A n x) ≤ m (symmDiff (A n x) (A n y)) := by
        apply MeasureTheory.measure_mono
        intro g hg
        exact Or.inl ⟨hg, (Set.disjoint_left.mp hdisj hg)⟩
      have hposδ : 0 < δ n x y := by
        apply ENNReal.toReal_pos
        · exact ne_of_gt (hposV.trans_le (by rwa [hAmeasure] at hmonoA))
        · exact hδfin n x y
      have : δ n x y ≤ 0 := by simpa [hd] using hδle n x y
      exact (not_lt_of_ge this) hposδ
    · rintro rfl
      exact hdself x
  · intro x y
    simp only [d, δ]
    congr 2 with n
    apply congrArg ENNReal.toReal
    apply congrArg m
    ext g
    simp [symmDiff, or_comm, and_comm]
  · intro x y z
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨n, rfl⟩
    have hle := MeasureTheory.measure_symmDiff_le (μ := m) (A n x) (A n y) (A n z)
    have hreal : δ n x z ≤ δ n x y + δ n y z := by
      simp only [δ]
      rw [← ENNReal.toReal_add (hδfin n x y) (hδfin n y z)]
      exact ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨hδfin n x y, hδfin n y z⟩) hle
    exact hreal.trans (add_le_add (hδle n x y) (hδle n y z))
  · intro z x y
    have hAz (n : ℕ) (w : G) : A n (z * w) = z • A n w := by
      ext g
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨w * v, ⟨v, hv, rfl⟩, by simp [mul_assoc]⟩
      · rintro ⟨q, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨v, hv, by simp [mul_assoc]⟩
    simp only [d, δ]
    congr 3 with n
    rw [hAz, hAz]
    apply congrArg ENNReal.toReal
    have he : symmDiff (z • A n x) (z • A n y) =
        z • symmDiff (A n x) (A n y) := by
      exact (Set.image_symmDiff (Homeomorph.mulLeft z).injective _ _).symm
    rw [he, MeasureTheory.measure_smul]
  · intro U
    constructor
    · intro hU x hx
      let N : Set G := (fun q : G => x * q) ⁻¹' U
      have hNo : IsOpen N := hU.preimage (continuous_mul_left x)
      have h1N : (1 : G) ∈ N := by simpa [N] using hx
      let q : G × G → G := fun p => p.1 * p.2⁻¹
      have hqo : IsOpen (q ⁻¹' N) :=
        hNo.preimage (continuous_fst.mul (continuous_inv.comp continuous_snd))
      have hqq : ((1 : G), (1 : G)) ∈ q ⁻¹' N := by simpa [q] using h1N
      obtain ⟨R, S, hRo, hSo, h1R, h1S, hRS⟩ :=
        isOpen_prod_iff.mp hqo 1 1 hqq
      let W : Set G := R ∩ S
      have hWo : IsOpen W := hRo.inter hSo
      have h1W : (1 : G) ∈ W := ⟨h1R, h1S⟩
      obtain ⟨n, hn⟩ := hbase W hWo h1W
      have hposV : 0 < m (V n) :=
        (hVopen n).measure_pos m ⟨1, hVid n⟩
      let ε : ℝ := ENNReal.toReal (m (V n))
      have hε : 0 < ε := ENNReal.toReal_pos hposV.ne' (hVfin n)
      refine ⟨ε, hε, ?_⟩
      intro y hdy
      have hδlt : δ n x y < ε := (hδle n x y).trans_lt hdy
      have hnotdisj : ¬ Disjoint (A n x) (A n y) := by
        intro hdisj
        have hmonoA : m (A n x) ≤ m (symmDiff (A n x) (A n y)) := by
          apply MeasureTheory.measure_mono
          intro g hg
          exact Or.inl ⟨hg, Set.disjoint_left.mp hdisj hg⟩
        have hreal : ε ≤ δ n x y := by
          change (m (V n)).toReal ≤
            (m (symmDiff (A n x) (A n y))).toReal
          apply ENNReal.toReal_mono (hδfin n x y)
          rwa [hAmeasure] at hmonoA
        exact (not_lt_of_ge hreal) hδlt
      obtain ⟨g, hgx, hgy⟩ := Set.not_disjoint_iff.mp hnotdisj
      rcases hgx with ⟨a, ha, hga⟩
      rcases hgy with ⟨b, hb, hgb⟩
      have hab : a * b⁻¹ ∈ N := by
        have hp := hRS (show (a, b) ∈ R ×ˢ S from ⟨(hn ha).1, (hn hb).2⟩)
        simpa [q] using hp
      have hy : y = x * (a * b⁻¹) := by
        calc
          y = (y * b) * b⁻¹ := by simp
          _ = (x * a) * b⁻¹ :=
            congrArg (fun t : G => t * b⁻¹) (hgb.trans hga.symm)
          _ = x * (a * b⁻¹) := by simp [mul_assoc]
      rw [hy]
      exact hab
    · intro hmetric
      rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨ε, hε, hball⟩ := hmetric x hx
      have hb : (fun y => d x y) ⁻¹' Set.Iio ε ∈ 𝓝 x :=
        hdtendsto x (Iio_mem_nhds hε)
      exact Filter.mem_of_superset hb fun y hy => hball y hy

/-- A normalized left Haar measure on a compact group is right invariant.
The proof follows the book: right translation produces another left Haar
probability measure, which equals the original one by uniqueness. -/
private theorem haarProbability_isRightInvariant
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (m : MeasureTheory.Measure G)
    (hmprob : MeasureTheory.IsProbabilityMeasure m) (hmhaar : m.IsHaarMeasure) :
    ∀ x : G, ∀ A : Set G, MeasurableSet A ->
      m ((fun y : G => y * x) ⁻¹' A) = m A := by
  letI : MeasureTheory.IsProbabilityMeasure m := hmprob
  letI : MeasureTheory.Measure.IsHaarMeasure m := hmhaar
  intro x
  let r : G → G := fun y => y * x
  let mr : MeasureTheory.Measure G := MeasureTheory.Measure.map r m
  have hrmeas : Measurable r := MeasurableMul.measurable_mul_const x
  letI : MeasureTheory.IsFiniteMeasureOnCompacts mr :=
    ⟨by
      intro K hK
      change MeasureTheory.Measure.map r m K < ⊤
      rw [MeasureTheory.Measure.map_apply hrmeas hK.measurableSet]
      exact MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact
        ((Homeomorph.mulRight x).isCompact_preimage.mpr hK)⟩
  letI : MeasureTheory.Measure.IsOpenPosMeasure mr :=
    ⟨by
      intro U hU hUne
      change MeasureTheory.Measure.map r m U ≠ 0
      rw [MeasureTheory.Measure.map_apply hrmeas hU.measurableSet]
      apply MeasureTheory.Measure.IsOpenPosMeasure.open_pos
      · exact (Homeomorph.mulRight x).isOpen_preimage.mpr hU
      · obtain ⟨u, hu⟩ := hUne
        refine ⟨u * x⁻¹, ?_⟩
        simpa [r] using hu⟩
  letI : MeasureTheory.Measure.IsMulLeftInvariant mr :=
    ⟨fun g => by
      ext A hA
      change MeasureTheory.Measure.map (fun y : G => g * y) mr A = mr A
      rw [MeasureTheory.Measure.map_apply
        (MeasurableMul.measurable_const_mul g) hA]
      change MeasureTheory.Measure.map r m
          ((fun y : G => g * y) ⁻¹' A) = MeasureTheory.Measure.map r m A
      rw [MeasureTheory.Measure.map_apply hrmeas
          ((MeasurableMul.measurable_const_mul g) hA),
        MeasureTheory.Measure.map_apply hrmeas hA]
      have hleft := congrArg (fun μ : MeasureTheory.Measure G => μ (r ⁻¹' A))
        (MeasureTheory.Measure.IsMulLeftInvariant.map_mul_left_eq_self (μ := m) g)
      change (MeasureTheory.Measure.map (fun y : G => g * y) m) (r ⁻¹' A) =
        m (r ⁻¹' A) at hleft
      rw [MeasureTheory.Measure.map_apply
        (MeasurableMul.measurable_const_mul g) (hrmeas hA)] at hleft
      have hsets : r ⁻¹' ((fun y : G => g * y) ⁻¹' A) =
          (fun y : G => g * y) ⁻¹' (r ⁻¹' A) := by
        ext y
        simp only [Set.mem_preimage]
        change g * (y * x) ∈ A ↔ (g * y) * x ∈ A
        rw [mul_assoc]
      rw [hsets]
      exact hleft⟩
  have hmrhaar : mr.IsHaarMeasure := MeasureTheory.Measure.IsHaarMeasure.mk
  letI : MeasureTheory.Measure.IsHaarMeasure mr := hmrhaar
  letI : MeasureTheory.IsProbabilityMeasure mr :=
    ⟨by
      change MeasureTheory.Measure.map r m Set.univ = 1
      rw [MeasureTheory.Measure.map_apply hrmeas MeasurableSet.univ]
      simp⟩
  have heq : mr = m :=
    MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure mr m
  intro A hA
  have hval := congrArg (fun μ : MeasureTheory.Measure G => μ A) heq
  change MeasureTheory.Measure.map r m A = m A at hval
  rw [MeasureTheory.Measure.map_apply hrmeas hA] at hval
  exact hval

/-- A compact metrizable group admits a compatible bi-invariant metric.
Embed the group into the continuous real-valued functions on `G × G` by
`x ↦ ((a,b) ↦ dist (a*x*b) 1)` and use the uniform metric. -/
private theorem compactBiInvariantMetric
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    (hmet : TopologicalSpace.MetrizableSpace G) :
    ∃ d : MetricSpace G,
      d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace G) ∧
      ∀ z x y : G,
        @dist G d.toDist (x * z) (y * z) = @dist G d.toDist x y ∧
        @dist G d.toDist (z * x) (z * y) = @dist G d.toDist x y := by
  letI : TopologicalSpace.MetrizableSpace G := hmet
  let d0 : MetricSpace G := TopologicalSpace.metrizableSpaceMetric G
  letI : MetricSpace G := d0
  let Φ : G → C(G × G, ℝ) := fun x =>
    ⟨fun p => dist (p.1 * x * p.2) 1, by fun_prop⟩
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    have h := DFunLike.congr_fun hxy ((1 : G), x⁻¹)
    dsimp [Φ] at h
    have hy : y * x⁻¹ = 1 := by
      apply dist_eq_zero.mp
      simpa using h.symm
    calc
      x = 1 * x := by simp
      _ = (y * x⁻¹) * x := by rw [hy]
      _ = y := by group
  have hΦcont : Continuous Φ := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : G × (G × G) =>
      dist (p.2.1 * p.1 * p.2.2) 1)
    fun_prop
  have hright : ∀ z x y : G,
      dist (Φ (x * z)) (Φ (y * z)) = dist (Φ x) (Φ y) := by
    intro z x y
    simp only [ContinuousMap.dist_eq_iSup]
    change (⨆ p : G × G, (dist ((Φ (x * z)) p) ((Φ (y * z)) p) : ℝ)) =
      ⨆ p : G × G, (dist ((Φ x) p) ((Φ y) p) : ℝ)
    apply le_antisymm
    · refine ciSup_le fun p : G × G => ?_
      have hb : BddAbove (Set.range (fun q : G × G =>
          (dist ((Φ x) q) ((Φ y) q) : ℝ))) :=
        ⟨dist (Φ x) (Φ y), by
          rintro _ ⟨q, rfl⟩
          exact ContinuousMap.dist_apply_le_dist q⟩
      have hle := le_ciSup hb (p.1, z * p.2)
      simpa only [Φ, ContinuousMap.coe_mk, mul_assoc] using hle
    · refine ciSup_le fun q : G × G => ?_
      have hb : BddAbove (Set.range (fun p : G × G =>
          (dist ((Φ (x * z)) p) ((Φ (y * z)) p) : ℝ))) :=
        ⟨dist (Φ (x * z)) (Φ (y * z)), by
          rintro _ ⟨p, rfl⟩
          exact ContinuousMap.dist_apply_le_dist p⟩
      have hle := le_ciSup hb (q.1, z⁻¹ * q.2)
      simpa [Φ, mul_assoc] using hle
  have hleft : ∀ z x y : G,
      dist (Φ (z * x)) (Φ (z * y)) = dist (Φ x) (Φ y) := by
    intro z x y
    simp only [ContinuousMap.dist_eq_iSup]
    change (⨆ p : G × G, (dist ((Φ (z * x)) p) ((Φ (z * y)) p) : ℝ)) =
      ⨆ p : G × G, (dist ((Φ x) p) ((Φ y) p) : ℝ)
    apply le_antisymm
    · refine ciSup_le fun p : G × G => ?_
      have hb : BddAbove (Set.range (fun q : G × G =>
          (dist ((Φ x) q) ((Φ y) q) : ℝ))) :=
        ⟨dist (Φ x) (Φ y), by
          rintro _ ⟨q, rfl⟩
          exact ContinuousMap.dist_apply_le_dist q⟩
      have hle := le_ciSup hb (p.1 * z, p.2)
      simpa only [Φ, ContinuousMap.coe_mk, mul_assoc] using hle
    · refine ciSup_le fun q : G × G => ?_
      have hb : BddAbove (Set.range (fun p : G × G =>
          (dist ((Φ (z * x)) p) ((Φ (z * y)) p) : ℝ))) :=
        ⟨dist (Φ (z * x)) (Φ (z * y)), by
          rintro _ ⟨p, rfl⟩
          exact ContinuousMap.dist_apply_le_dist p⟩
      have hle := le_ciSup hb (q.1 * z⁻¹, q.2)
      simpa [Φ, mul_assoc] using hle
  let d : MetricSpace G := MetricSpace.induced Φ hΦinj inferInstance
  refine ⟨d, ?_, ?_⟩
  · change TopologicalSpace.induced Φ inferInstance =
      (inferInstance : TopologicalSpace G)
    have hEmb : Topology.IsEmbedding Φ :=
      (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
        hΦcont hΦinj hΦcont.isClosedMap).toIsEmbedding
    exact hEmb.toIsInducing.eq_induced.symm
  · intro z x y
    constructor
    · change dist (Φ (x * z)) (Φ (y * z)) = dist (Φ x) (Φ y)
      exact hright z x y
    · change dist (Φ (z * x)) (Φ (z * y)) = dist (Φ x) (Φ y)
      exact hleft z x y

/--
Source: Remark 0.4.6, Chapter 0, Section 4.
Normalization and invariance properties of Haar probability measure on compact
groups.
-/
theorem compactGroupHaarProbabilityRemark
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    (∃! m : MeasureTheory.Measure G,
      MeasureTheory.IsProbabilityMeasure m ∧ m.IsHaarMeasure) ∧
    (∀ m : MeasureTheory.Measure G, MeasureTheory.IsProbabilityMeasure m ->
      m.IsHaarMeasure -> ∀ x : G, ∀ A : Set G, MeasurableSet A ->
        m ((fun y => y * x) ⁻¹' A) = m A) ∧
    (∀ m : MeasureTheory.Measure G, m.IsHaarMeasure ->
      ∀ U : Set G, IsOpen U -> U.Nonempty -> 0 < m U) ∧
    (TopologicalSpace.MetrizableSpace G ->
      ∃ d : MetricSpace G,
        d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace G) ∧
        ∀ z x y : G,
          @dist G d.toDist (x * z) (y * z) =
            @dist G d.toDist x y ∧
            @dist G d.toDist (z * x) (z * y) =
            @dist G d.toDist x y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨m, hmprob, hmhaar⟩ := existsHaarProbabilityOnCompactGroup G
    refine ⟨m, ⟨hmprob, hmhaar⟩, ?_⟩
    intro m' hm'pair
    rcases hm'pair with ⟨hm'prob, hm'haar⟩
    letI : MeasureTheory.IsProbabilityMeasure m := hmprob
    letI : MeasureTheory.IsProbabilityMeasure m' := hm'prob
    letI : MeasureTheory.Measure.IsHaarMeasure m := hmhaar
    letI : MeasureTheory.Measure.IsHaarMeasure m' := hm'haar
    exact MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure m' m
  · intro m hmprob hmhaar x A hA
    exact haarProbability_isRightInvariant G m hmprob hmhaar x A hA
  · intro m hm U hU hUne
    letI : MeasureTheory.Measure.IsHaarMeasure m := hm
    exact pos_iff_ne_zero.mpr
      (MeasureTheory.Measure.IsOpenPosMeasure.open_pos U hU hUne)
  · intro hmet
    exact compactBiInvariantMetric G hmet

/--
Source: Example 0.4.7, Chapter 0, Section 4.
Examples of Haar measures on finite cyclic groups, tori, and products.
-/
theorem haarMeasureExamples (n : ℕ) [NeZero n]
    [MeasurableSpace (Multiplicative (ZMod n))]
    [BorelSpace (Multiplicative (ZMod n))]
    [MeasurableSpace (Multiplicative ℤ)] [BorelSpace (Multiplicative ℤ)]
    [MeasurableSpace (Multiplicative ℝ)] [BorelSpace (Multiplicative ℝ)]
    [MeasurableSpace Circle] [BorelSpace Circle] :
    let μn : MeasureTheory.Measure (Multiplicative (ZMod n)) :=
      (n : ENNReal)⁻¹ • MeasureTheory.Measure.count
    (MeasureTheory.IsProbabilityMeasure μn ∧ μn.IsHaarMeasure) ∧
      (MeasureTheory.Measure.count : MeasureTheory.Measure (Multiplicative ℤ)).IsHaarMeasure ∧
      (MeasureTheory.Measure.map Multiplicative.ofAdd
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)).IsHaarMeasure ∧
      ∃ m : MeasureTheory.Measure Circle,
        MeasureTheory.IsProbabilityMeasure m ∧ m.IsHaarMeasure := by
  dsimp
  exact ⟨normalizedCountMeasureOnZModIsProbabilityHaar n,
    countMeasureIsHaarOnDiscreteGroup (Multiplicative ℤ),
    additiveRealVolumeIsHaarInMultiplicativeNotation,
    existsHaarProbabilityOnCompactGroup Circle⟩

/--
Source: Definition 0.4.8, Chapter 0, Section 4.
A character of a locally compact abelian group is a continuous homomorphism
into the circle group.
-/
def characterDefinition (G : Type u) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] : Type u :=
  CharacterGroup G

/-- The character determined by the image of the additive generator of `ℤ`. -/
private def integerCharacter (z : Circle) :
    CharacterGroup (Multiplicative ℤ) :=
  { toMonoidHom :=
      { toFun := fun k => z ^ k.toAdd
        map_one' := by simp
        map_mul' := by intro a b; exact zpow_add z a.toAdd b.toAdd }
    continuous_toFun := continuous_of_discreteTopology }

private def integerCharacterEval :
    CharacterGroup (Multiplicative ℤ) →* Circle where
  toFun χ := χ (Multiplicative.ofAdd 1)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem integerCharacter_eval_inverse (z : Circle) :
    integerCharacterEval (integerCharacter z) = z := by
  change z ^ (1 : ℤ) = z
  exact zpow_one z

private theorem integerCharacter_inverse_eval
    (χ : CharacterGroup (Multiplicative ℤ)) :
    integerCharacter (integerCharacterEval χ) = χ := by
  apply ContinuousMonoidHom.ext
  intro k
  change χ (Multiplicative.ofAdd 1) ^ k.toAdd = χ k
  have hk : k = (Multiplicative.ofAdd 1) ^ k.toAdd := by
    apply Multiplicative.toAdd.injective
    simp
  calc
    χ (Multiplicative.ofAdd 1) ^ k.toAdd =
        χ ((Multiplicative.ofAdd 1) ^ k.toAdd) :=
      (map_zpow χ (Multiplicative.ofAdd 1) k.toAdd).symm
    _ = χ k := congrArg χ hk.symm

/-- Evaluation at the generator identifies the dual of discrete `ℤ` with
the circle. -/
def integerCharacterMulEquiv :
    CharacterGroup (Multiplicative ℤ) ≃* Circle where
  toFun := integerCharacterEval
  invFun := integerCharacter
  left_inv := integerCharacter_inverse_eval
  right_inv := integerCharacter_eval_inverse
  map_mul' := map_mul integerCharacterEval

private def zmodCircleAddEquiv (n : ℕ) [NeZero n] :
    ZMod n ≃+ AddChar (ZMod n) Circle :=
  (AddChar.zmodAddEquiv (n := n)).trans AddChar.circleEquivComplex.symm

private def addCharToCharacter (n : ℕ) [NeZero n]
    (ψ : AddChar (ZMod n) Circle) :
      CharacterGroup (Multiplicative (ZMod n)) :=
  { toMonoidHom := AddChar.toMonoidHomEquiv ψ
    continuous_toFun := continuous_of_discreteTopology }

private def characterToAddChar (n : ℕ) [NeZero n]
    (χ : CharacterGroup (Multiplicative (ZMod n))) :
      AddChar (ZMod n) Circle :=
  (AddChar.toMonoidHomEquiv (A := ZMod n) (M := Circle)).symm χ.toMonoidHom

private theorem characterToAddChar_addCharToCharacter (n : ℕ) [NeZero n]
    (ψ : AddChar (ZMod n) Circle) :
    characterToAddChar n (addCharToCharacter n ψ) = ψ := by
  ext x
  rfl

private theorem addCharToCharacter_characterToAddChar (n : ℕ) [NeZero n]
    (χ : CharacterGroup (Multiplicative (ZMod n))) :
    addCharToCharacter n (characterToAddChar n χ) = χ := by
  apply ContinuousMonoidHom.ext
  intro x
  rfl

private def cyclicCharacterMulEquiv (n : ℕ) [NeZero n] :
    CharacterGroup (Multiplicative (ZMod n)) ≃* Multiplicative (ZMod n) := by
  let e : AddChar (ZMod n) Circle ≃* CharacterGroup (Multiplicative (ZMod n)) :=
    { toFun := addCharToCharacter n
      invFun := characterToAddChar n
      left_inv := characterToAddChar_addCharToCharacter n
      right_inv := addCharToCharacter_characterToAddChar n
      map_mul' := by
        intro a b
        apply ContinuousMonoidHom.ext
        intro x
        change (a * b) x = a x * b x
        rfl }
  exact ((zmodCircleAddEquiv n).toMultiplicative.trans e).symm

/-- Evaluation at the unique coordinate identifies the one-dimensional torus
with the circle as a topological group. -/
private def circlePiOneEquiv : (Fin 1 → Circle) ≃ₜ* Circle where
  toFun z := z 0
  invFun z := fun _ => z
  left_inv z := by funext i; exact Fin.eq_zero i ▸ rfl
  right_inv z := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_apply 0
  continuous_invFun := continuous_pi fun _ => continuous_id

private def characterCirclePiOneEquiv :
    CharacterGroup Circle ≃* CharacterGroup (Fin 1 → Circle) where
  toFun χ := χ.comp
    { toMonoidHom := circlePiOneEquiv.toMulEquiv.toMonoidHom
      continuous_toFun := circlePiOneEquiv.continuous }
  invFun ψ := ψ.comp
    { toMonoidHom := circlePiOneEquiv.symm.toMulEquiv.toMonoidHom
      continuous_toFun := circlePiOneEquiv.symm.continuous }
  left_inv χ := by
    apply ContinuousMonoidHom.ext
    intro z
    rfl
  right_inv ψ := by
    apply ContinuousMonoidHom.ext
    intro z
    change ψ (fun _ => z 0) = ψ z
    congr 1
    funext i
    exact Fin.eq_zero i ▸ rfl
  map_mul' _ _ := rfl

private def piOneIntegerEquiv :
    (Fin 1 → Multiplicative ℤ) ≃* Multiplicative ℤ where
  toFun m := m 0
  invFun z := fun _ => z
  left_inv m := by funext i; exact Fin.eq_zero i ▸ rfl
  right_inv z := rfl
  map_mul' _ _ := rfl

private theorem circleDualFromTorusOne :
    Nonempty (CharacterGroup Circle ≃* Multiplicative ℤ) := by
  obtain ⟨e⟩ := torusDualIsIntegerLattice 1
  exact ⟨characterCirclePiOneEquiv.trans (e.trans piOneIntegerEquiv)⟩

private noncomputable def realCharacter (a : Multiplicative ℝ) :
    CharacterGroup (Multiplicative ℝ) where
  toFun x := Circle.exp (a.toAdd * x.toAdd)
  map_one' := by simp
  map_mul' x y := by
    change Circle.exp (a.toAdd * (x.toAdd + y.toAdd)) =
      Circle.exp (a.toAdd * x.toAdd) * Circle.exp (a.toAdd * y.toAdd)
    rw [mul_add, Circle.exp_add]
  continuous_toFun := by
    apply Circle.exp.continuous.comp
    change Continuous (fun x : ℝ => a.toAdd * x)
    fun_prop

private theorem realCharacterClassification
    (χ : CharacterGroup (Multiplicative ℝ)) :
    ∃ a : ℝ, ∀ x : Multiplicative ℝ,
      χ x = Circle.exp (a * x.toAdd) := by
  let f : C(ℝ, Circle) :=
    ⟨fun t => χ (Multiplicative.ofAdd t), by
      change Continuous (fun t : Multiplicative ℝ => χ t)
      exact χ.continuous⟩
  have he : Circle.exp 0 = f 0 := by simp [f]
  obtain ⟨F, hF, huniq⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0 he
  rcases hF with ⟨hF0, hFexp⟩
  have hFadd : ∀ x y : ℝ, F (x + y) = F x + F y := by
    intro x y
    let L : C(ℝ, ℝ) :=
      ⟨fun t => F (x + t) - F x,
        (F.continuous.comp (continuous_const.add continuous_id)).sub
          continuous_const⟩
    have hL0 : L 0 = 0 := by simp [L]
    have hLexp : Circle.exp ∘ L = f := by
      funext t
      have hx := congrFun hFexp x
      have hxt := congrFun hFexp (x + t)
      change Circle.exp (F x) = f x at hx
      change Circle.exp (F (x + t)) = f (x + t) at hxt
      change Circle.exp (F (x + t) - F x) = f t
      rw [Circle.exp_sub, hxt, hx]
      change χ (Multiplicative.ofAdd (x + t)) /
        χ (Multiplicative.ofAdd x) = χ (Multiplicative.ofAdd t)
      rw [show Multiplicative.ofAdd (x + t) =
          Multiplicative.ofAdd x * Multiplicative.ofAdd t by rfl, map_mul]
      simp
    have hLF : L = F := huniq L ⟨hL0, hLexp⟩
    have hpoint := DFunLike.congr_fun hLF y
    change F (x + y) - F x = F y at hpoint
    linarith
  let Fhom : ℝ →+ ℝ :=
    { toFun := F
      map_zero' := hF0
      map_add' := hFadd }
  have hFlinear : ∀ t : ℝ, F t = F 1 * t := by
    intro t
    have hm := (Fhom.toRealLinearMap F.continuous).map_smul t (1 : ℝ)
    simpa [Fhom, smul_eq_mul, mul_comm] using hm
  refine ⟨F 1, ?_⟩
  intro x
  have ht := congrFun hFexp x.toAdd
  change Circle.exp (F x.toAdd) = f x.toAdd at ht
  change Circle.exp (F x.toAdd) = χ x at ht
  rw [hFlinear x.toAdd] at ht
  exact ht.symm

private theorem realCharacter_injective : Function.Injective realCharacter := by
  intro a b hab
  have hfun : ∀ t : ℝ, Circle.exp (a.toAdd * t) =
      Circle.exp (b.toAdd * t) := by
    intro t
    exact DFunLike.congr_fun hab (Multiplicative.ofAdd t)
  let f : C(ℝ, Circle) :=
    ⟨fun t => Circle.exp (a.toAdd * t), by fun_prop⟩
  let A : C(ℝ, ℝ) := ⟨fun t => a.toAdd * t, by fun_prop⟩
  let B : C(ℝ, ℝ) := ⟨fun t => b.toAdd * t, by fun_prop⟩
  have he : Circle.exp 0 = f 0 := by simp [f]
  obtain ⟨F, _hF, huniq⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0 he
  have hA : A = F := by
    apply huniq A
    constructor
    · simp [A]
    · funext t
      rfl
  have hB : B = F := by
    apply huniq B
    constructor
    · simp [B]
    · funext t
      change Circle.exp (b.toAdd * t) = Circle.exp (a.toAdd * t)
      exact (hfun t).symm
  apply Multiplicative.toAdd.injective
  have hAB : A = B := hA.trans hB.symm
  have h1 := DFunLike.congr_fun hAB 1
  simpa [A, B] using h1

private noncomputable def realCharacterHom :
    Multiplicative ℝ →* CharacterGroup (Multiplicative ℝ) where
  toFun := realCharacter
  map_one' := by
    apply ContinuousMonoidHom.ext
    intro x
    change Circle.exp ((0 : ℝ) * x.toAdd) = 1
    simp
  map_mul' a b := by
    apply ContinuousMonoidHom.ext
    intro x
    change Circle.exp ((a.toAdd + b.toAdd) * x.toAdd) =
      Circle.exp (a.toAdd * x.toAdd) * Circle.exp (b.toAdd * x.toAdd)
    rw [add_mul, Circle.exp_add]

private theorem realCharacterHom_surjective : Function.Surjective realCharacterHom := by
  intro χ
  obtain ⟨a, ha⟩ := realCharacterClassification χ
  refine ⟨Multiplicative.ofAdd a, ?_⟩
  apply ContinuousMonoidHom.ext
  intro x
  exact (ha x).symm

private theorem realDual :
    Nonempty (CharacterGroup (Multiplicative ℝ) ≃* Multiplicative ℝ) := by
  exact ⟨(MulEquiv.ofBijective realCharacterHom
    ⟨realCharacter_injective, realCharacterHom_surjective⟩).symm⟩

/--
Source: Example 0.4.10, Chapter 0, Section 4.
Examples of dual groups for finite cyclic groups, integers, real numbers, and
tori.
-/
theorem dualGroupExamples (n : ℕ) [NeZero n] :
    Nonempty (CharacterGroup (Multiplicative (ZMod n)) ≃* Multiplicative (ZMod n)) ∧
      Nonempty (CharacterGroup Circle ≃* Multiplicative ℤ) ∧
      Nonempty (CharacterGroup (Multiplicative ℤ) ≃* Circle) ∧
      Nonempty (CharacterGroup (Multiplicative ℝ) ≃* Multiplicative ℝ) := by
  refine ⟨⟨cyclicCharacterMulEquiv n⟩, ?_, ⟨integerCharacterMulEquiv⟩, ?_⟩
  · exact circleDualFromTorusOne
  · exact realDual

end Section04
end Chapter00
