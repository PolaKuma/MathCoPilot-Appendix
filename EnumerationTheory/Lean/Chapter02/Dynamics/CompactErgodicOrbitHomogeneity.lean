import Chapter02.Ergodic.CorrelationMean
import Chapter02.Ergodic.ErgodicBirkhoffBridge
import Chapter02.HostKra.HostKraStructuredRecurrence

open Classical Filter MeasureTheory Set

noncomputable section

namespace Chapter02.CompactErgodicOrbitHomogeneity

universe u

/-- The forward orbit of a point under a self-map. -/
def forwardOrbit {X : Type u} (T : X → X) (x : X) : Set X :=
  Set.range fun n : ℕ ↦ (T^[n]) x

/-- Orbit closures are homogeneous when every point inside one has the
same forward orbit closure.  Distal minimal extensions and nilsystems
satisfy this property; unlike global minimality, it is stable pointwise. -/
def OrbitClosureHomogeneous
    {X : Type u} [TopologicalSpace X] (T : X → X) : Prop :=
  ∀ x y : X, y ∈ closure (forwardOrbit T x) →
    closure (forwardOrbit T y) = closure (forwardOrbit T x)

/-- A dense orbit together with homogeneous orbit closures forces every
orbit to meet every nonempty open set. -/
theorem everyOrbitHitsOpen_of_denseOrbit_of_orbitClosureHomogeneous
    {X : Type u} [TopologicalSpace X]
    (T : X → X)
    (hhom : OrbitClosureHomogeneous T)
    (x₀ : X) (hx₀ : DenseRange fun n : ℕ ↦ (T^[n]) x₀) :
    Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen T := by
  intro x U hU hUne
  have hxmem : x ∈ closure (forwardOrbit T x₀) := by
    rw [show closure (forwardOrbit T x₀) = Set.univ by
      exact hx₀.closure_eq]
    exact Set.mem_univ x
  have hxdense : Dense (forwardOrbit T x) := by
    rw [dense_iff_closure_eq]
    rw [hhom x₀ x hxmem]
    exact hx₀.closure_eq
  obtain ⟨z, hzU, ⟨n, hzn⟩⟩ :=
    (dense_iff_inter_open.mp hxdense) U hU hUne
  refine ⟨n, ?_⟩
  change (T^[n]) x = z at hzn
  rw [hzn]
  exact hzU

/-- In a second-countable ergodic probability system with full-support
measure, almost every point has dense forward orbit. -/
theorem exists_dense_forwardOrbit
    (M : System.{u})
    [TopologicalSpace M.X] [SecondCountableTopology M.X]
    [BorelSpace M.X] [M.μ.IsOpenPosMeasure]
    (hM : IsErgodic M) :
    ∃ x : M.X, DenseRange fun n : ℕ ↦ (M.T^[n]) x := by
  letI : IsProbabilityMeasure M.μ := hM.1.1
  obtain ⟨B, hBcount, hBempty, hBbasis⟩ :=
    TopologicalSpace.exists_countable_basis M.X
  letI : Countable B := Set.countable_coe_iff.mpr hBcount
  have hlimit (U : B) :
      ∀ᵐ x ∂M.μ,
        Tendsto
          (fun n ↦ ergodicAverage M
            (CorrelationMean.indicatorComplex U.1) n x)
          atTop (nhds ((realMeasure M U.1 : ℂ))) := by
    have hUopen : IsOpen U.1 := hBbasis.isOpen U.2
    have hUmeas : MeasurableSet U.1 := hUopen.measurableSet
    have hmem :=
      CorrelationMean.indicatorComplex_memLp M hM.1 U.1 hUmeas 1
    simpa only [CorrelationMean.integral_indicatorComplex M U.1 hUmeas] using
      ErgodicBirkhoffBridge.ergodicTimeAverage_tendsto_integral
        M hM (CorrelationMean.indicatorComplex U.1) hmem
  have hall :
      ∀ᵐ x ∂M.μ, ∀ U : B,
        Tendsto
          (fun n ↦ ergodicAverage M
            (CorrelationMean.indicatorComplex U.1) n x)
          atTop (nhds ((realMeasure M U.1 : ℂ))) :=
    ae_all_iff.mpr hlimit
  obtain ⟨x, hx⟩ := hall.exists
  refine ⟨x, ?_⟩
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨y, hyU⟩ := hUne
  obtain ⟨V, hVB, hyV, hVU⟩ :=
    hBbasis.exists_subset_of_mem_open hyU hU
  let Vb : B := ⟨V, hVB⟩
  have hVopen : IsOpen V := hBbasis.isOpen hVB
  have hVne : V.Nonempty := ⟨y, hyV⟩
  have hVpos : 0 < M.μ V :=
    pos_iff_ne_zero.mpr
      (Measure.IsOpenPosMeasure.open_pos V hVopen hVne)
  have hVreal : 0 < realMeasure M V := by
    exact ENNReal.toReal_pos hVpos.ne' (measure_ne_top M.μ V)
  have htarget : (realMeasure M V : ℂ) ≠ 0 := by
    exact_mod_cast hVreal.ne'
  have hnhds : {0}ᶜ ∈ nhds (realMeasure M V : ℂ) :=
    isOpen_compl_singleton.mem_nhds htarget
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        ergodicAverage M
          (CorrelationMean.indicatorComplex V) n x ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (hx Vb).eventually hnhds
  obtain ⟨N, hN⟩ := hevent.exists
  have hNzero : N ≠ 0 := by
    intro h
    subst N
    simp [ergodicAverage] at hN
  have hsum :
      ∑ j ∈ Finset.range N,
          CorrelationMean.indicatorComplex V ((M.T^[j]) x) ≠ 0 := by
    unfold ergodicAverage at hN
    rw [if_neg hNzero] at hN
    intro hzero
    rw [hzero, mul_zero] at hN
    exact hN rfl
  have hex :
      ∃ j ∈ Finset.range N,
        CorrelationMean.indicatorComplex V ((M.T^[j]) x) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hsum
    exact Finset.sum_eq_zero fun j hj ↦ h j hj
  obtain ⟨j, hjN, hj⟩ := hex
  have hjV : (M.T^[j]) x ∈ V := by
    by_contra hnot
    apply hj
    simp [CorrelationMean.indicatorComplex, Set.indicator, hnot]
  exact ⟨(M.T^[j]) x, hVU hjV, ⟨j, rfl⟩⟩

/-- Ergodicity, full support, and orbit-closure homogeneity imply the
topological minimality interface used by structured recurrence. -/
theorem everyOrbitHitsOpen_of_ergodic_fullSupport
    (M : System.{u})
    [TopologicalSpace M.X] [SecondCountableTopology M.X]
    [BorelSpace M.X] [M.μ.IsOpenPosMeasure]
    (hM : IsErgodic M)
    (hhom : OrbitClosureHomogeneous M.T) :
    Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen M.T := by
  obtain ⟨x₀, hx₀⟩ := exists_dense_forwardOrbit M hM
  exact
    everyOrbitHitsOpen_of_denseOrbit_of_orbitClosureHomogeneous
      M.T hhom x₀ hx₀

end Chapter02.CompactErgodicOrbitHomogeneity
