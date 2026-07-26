import Chapter02.Ergodic.AlgebraSubSigma
import Chapter02.HostKra.HostKraErgodicRelativeJoining
import Chapter02.HostKra.HostKraStandardRelativeJoining
import Chapter00.Probability.Section03ConditionalMeasure

open Classical Filter Set MeasureTheory ProbabilityTheory

noncomputable section

namespace Chapter02.HostKraErgodicDecomposition

universe u

/-- The `L²` indicator vectors of sets invariant modulo the ambient
probability measure.  This subtype is used only to choose a countable dense
family; it does not assert that the exact invariant sigma-algebra is
countably generated. -/
def invariantIndicatorLpSet
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    Set (Lp ℂ 2 M.μ) :=
  {F | ∃ A : Set M.X, ∃ hA : MeasurableSet A,
    M.μ (Chapter00.symmDiff (M.T ⁻¹' A) A) = 0 ∧
      F = MultipleKhintchineCharacteristic.indicatorLp M hM A hA}

abbrev InvariantIndicatorLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :=
  invariantIndicatorLpSet M hM

private theorem invariantIndicatorLp_nonempty
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    Nonempty (InvariantIndicatorLp M hM) := by
  let F :=
    MultipleKhintchineCharacteristic.indicatorLp
      M hM Set.univ MeasurableSet.univ
  refine ⟨⟨F, Set.mem_setOf.mpr ?_⟩⟩
  refine ⟨Set.univ, MeasurableSet.univ, ?_, rfl⟩
  simp [Chapter00.symmDiff]

private theorem invariantIndicatorLp_secondCountable
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    SecondCountableTopology (InvariantIndicatorLp M hM) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  letI : IsSeparable M.μ := inferInstance
  letI : SecondCountableTopology (Lp ℂ 2 M.μ) := inferInstance
  infer_instance

/-- A countable dense set of invariant indicator vectors. -/
noncomputable def denseInvariantIndicators
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Set (InvariantIndicatorLp M hM) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  letI : IsSeparable M.μ := inferInstance
  letI : SecondCountableTopology (InvariantIndicatorLp M hM) :=
    invariantIndicatorLp_secondCountable M hM
  exact Classical.choose
    (TopologicalSpace.exists_countable_dense
      (InvariantIndicatorLp M hM))

theorem denseInvariantIndicators_countable
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    (denseInvariantIndicators M hM).Countable := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  letI : IsSeparable M.μ := inferInstance
  letI : SecondCountableTopology (InvariantIndicatorLp M hM) :=
    invariantIndicatorLp_secondCountable M hM
  exact (Classical.choose_spec
    (TopologicalSpace.exists_countable_dense
      (InvariantIndicatorLp M hM))).1

theorem denseInvariantIndicators_dense
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Dense (denseInvariantIndicators M hM) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  letI : IsSeparable M.μ := inferInstance
  letI : SecondCountableTopology (InvariantIndicatorLp M hM) :=
    invariantIndicatorLp_secondCountable M hM
  exact (Classical.choose_spec
    (TopologicalSpace.exists_countable_dense
      (InvariantIndicatorLp M hM))).2

abbrev DenseInvariantIndicator
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :=
  denseInvariantIndicators M hM

/-- A measurable invariant set representing one selected dense indicator
vector. -/
noncomputable def denseInvariantIndicatorSet
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (d : DenseInvariantIndicator M hM) : Set M.X :=
  Classical.choose d.1.2

theorem denseInvariantIndicatorSet_measurable
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (d : DenseInvariantIndicator M hM) :
    MeasurableSet (denseInvariantIndicatorSet M hM d) :=
  (Classical.choose_spec d.1.2).choose

theorem denseInvariantIndicatorSet_invariant
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (d : DenseInvariantIndicator M hM) :
    M.μ (Chapter00.symmDiff
      (M.T ⁻¹' denseInvariantIndicatorSet M hM d)
      (denseInvariantIndicatorSet M hM d)) = 0 :=
  (Classical.choose_spec
    (Classical.choose_spec d.1.2)).1

theorem denseInvariantIndicatorSet_toLp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (d : DenseInvariantIndicator M hM) :
    d.1.1 =
      MultipleKhintchineCharacteristic.indicatorLp M hM
        (denseInvariantIndicatorSet M hM d)
        (denseInvariantIndicatorSet_measurable M hM d) :=
  (Classical.choose_spec
    (Classical.choose_spec d.1.2)).2

/-- The countable family of invariant sets selected from the dense
indicator vectors. -/
def invariantCountableCore
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    SetFamily M.X :=
  Set.range (denseInvariantIndicatorSet M hM)

theorem invariantCountableCore_countable
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    (invariantCountableCore M hM).Countable := by
  letI : Countable (DenseInvariantIndicator M hM) :=
    (denseInvariantIndicators_countable M hM).to_subtype
  exact Set.countable_range _

theorem invariantCountableCore_measurable
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {A : Set M.X} (hA : A ∈ invariantCountableCore M hM) :
    MeasurableSet A := by
  rcases hA with ⟨d, rfl⟩
  exact denseInvariantIndicatorSet_measurable M hM d

theorem invariantCountableCore_invariant
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {A : Set M.X} (hA : A ∈ invariantCountableCore M hM) :
    M.μ (Chapter00.symmDiff (M.T ⁻¹' A) A) = 0 := by
  rcases hA with ⟨d, rfl⟩
  exact denseInvariantIndicatorSet_invariant M hM d

/-- Every measurable invariant set is, modulo the ambient measure, measurable
for the sigma-algebra generated by the countable invariant core. -/
theorem invariantSet_exists_core_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hInv : M.μ (Chapter00.symmDiff (M.T ⁻¹' A) A) = 0) :
    ∃ B : Set M.X,
      @MeasurableSet M.X
        (MeasurableSpace.generateFrom (invariantCountableCore M hM)) B ∧
      A =ᵐ[M.μ] B := by
  let F : Lp ℂ 2 M.μ :=
    MultipleKhintchineCharacteristic.indicatorLp M hM A hA
  let Fs : InvariantIndicatorLp M hM :=
    ⟨F, ⟨A, hA, hInv, rfl⟩⟩
  have hFclosure :
      Fs ∈ closure (denseInvariantIndicators M hM) := by
    rw [(denseInvariantIndicators_dense M hM).closure_eq]
    trivial
  obtain ⟨Qseq, hQmem, hQlim⟩ :=
    mem_closure_iff_seq_limit.mp hFclosure
  let d : ℕ → DenseInvariantIndicator M hM :=
    fun n ↦ ⟨Qseq n, hQmem n⟩
  let Aseq : ℕ → Set M.X :=
    fun n ↦ denseInvariantIndicatorSet M hM (d n)
  let fseq : ℕ → M.X → ℂ :=
    fun n ↦ CorrelationMean.indicatorComplex (Aseq n)
  have hLpLim : Tendsto (fun n ↦ (Qseq n).1) atTop (nhds F) := by
    simpa [Fs, F] using
      (continuous_subtype_val.tendsto Fs).comp hQlim
  have hconvLp :
      Tendsto
        (fun n ↦ MultipleKhintchineCharacteristic.indicatorLp M hM
          (Aseq n) (denseInvariantIndicatorSet_measurable M hM (d n)))
        atTop (nhds F) := by
    apply hLpLim.congr'
    filter_upwards with n
    exact denseInvariantIndicatorSet_toLp M hM (d n)
  have hconv :
      Tendsto
        (fun n ↦ eLpNorm
          (fun x ↦ fseq n x - CorrelationMean.indicatorComplex A x)
          2 M.μ)
        atTop (nhds 0) := by
    have hnorm :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
        (fun n ↦ MultipleKhintchineCharacteristic.indicatorLp M hM
          (Aseq n) (denseInvariantIndicatorSet_measurable M hM (d n)))
        F).mp hconvLp
    apply hnorm.congr'
    filter_upwards with n
    apply eLpNorm_congr_ae
    filter_upwards [
      MultipleKhintchineCharacteristic.indicatorLp_coe M hM
        (Aseq n) (denseInvariantIndicatorSet_measurable M hM (d n)),
      MultipleKhintchineCharacteristic.indicatorLp_coe M hM A hA
    ] with x hxn hx
    simp only [Pi.sub_apply]
    rw [hxn, hx]
  have hfseq2 :
      ∀ n, M.lpMember 2 (fseq n) := by
    intro n
    exact CorrelationMean.indicatorComplex_memLp M hM
      (Aseq n) (denseInvariantIndicatorSet_measurable M hM (d n)) 2
  have hfseqCore :
      ∀ n, HasMeasurableRepresentativeForFamily M
        (invariantCountableCore M hM) (fseq n) := by
    intro n
    refine ⟨fseq n, ?_, EventuallyEq.rfl⟩
    exact measurable_const.indicator
      (MeasurableSpace.measurableSet_generateFrom ⟨d n, rfl⟩)
  obtain ⟨g, hg, hAg⟩ :=
    AlgebraSubSigma.hasMeasurableRepresentativeForFamily_closed
      M (invariantCountableCore M hM) fseq hfseq2 hfseqCore
      (CorrelationMean.indicatorComplex A)
      (CorrelationMean.indicatorComplex_memLp M hM A hA 2) hconv
  let B : Set M.X := g ⁻¹' ({1} : Set ℂ)
  refine ⟨B, hg (measurableSet_singleton (1 : ℂ)), ?_⟩
  filter_upwards [hAg] with x hx
  change (x ∈ A) = (g x = 1)
  by_cases hxin : x ∈ A
  · simpa [CorrelationMean.indicatorComplex, Set.indicator, hxin] using hx.symm
  · have hxg : g x = 0 := by
      simpa [CorrelationMean.indicatorComplex, Set.indicator, hxin] using hx.symm
    simp [hxin, hxg]

/-- The actual sigma-algebra generated by the selected countable core. -/
def invariantCoreSigmaAlgebra
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) : SetFamily M.X :=
  Chapter00.generatedSigmaAlgebra (invariantCountableCore M hM)

def invariantCoreMeasurableSpace
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) : MeasurableSpace M.X :=
  MeasurableSpace.generateFrom (invariantCountableCore M hM)

def invariantBaseProbabilitySpace
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter00.BasicProbabilitySpaceData where
  X := M.X
  measurableSpace := M.measurableSpace
  μ := M.μ
  isProbability := hM.1

/-- Every set measurable for the generated invariant sigma-algebra has an
almost-everywhere equal representative in the countable invariant core. -/
theorem invariantGeneratedSet_exists_core_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (B : Set M.X)
    (hB : @MeasurableSet M.X
      (MeasurableSpace.generateFrom (invariantSigmaAlgebra M)) B) :
    ∃ C : Set M.X,
      @MeasurableSet M.X (invariantCoreMeasurableSpace M hM) C ∧
      B =ᵐ[M.μ] C := by
  exact MeasurableSpace.generateFrom_induction
    (invariantSigmaAlgebra M)
    (fun C _ ↦ ∃ D : Set M.X,
      @MeasurableSet M.X (invariantCoreMeasurableSpace M hM) D ∧
      C =ᵐ[M.μ] D)
    (by
      intro C hC _
      exact invariantSet_exists_core_ae M hM C hC.1 hC.2)
    (by
      refine ⟨∅, ?_, EventuallyEq.rfl⟩
      exact @MeasurableSet.empty M.X
        (invariantCoreMeasurableSpace M hM))
    (by
      intro C _ hC
      rcases hC with ⟨D, hD, hCD⟩
      exact ⟨Dᶜ, hD.compl, hCD.compl⟩)
    (by
      intro C _ hC
      choose D hD hCD using hC
      refine ⟨⋃ n, D n, MeasurableSet.iUnion hD, ?_⟩
      have hall : ∀ᵐ x ∂M.μ, ∀ n, x ∈ C n ↔ x ∈ D n :=
        ae_all_iff.mpr fun n ↦ by
          filter_upwards [hCD n] with x hx
          exact iff_of_eq hx
      filter_upwards [hall] with x hx
      change (x ∈ ⋃ n, C n) = (x ∈ ⋃ n, D n)
      apply propext
      simp only [Set.mem_iUnion]
      exact exists_congr fun n ↦ hx n)
    B hB

theorem invariantCoreSigmaAlgebra_isSigma
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter00.IsSigmaAlgebraFamily (invariantCoreSigmaAlgebra M hM) := by
  letI : MeasurableSpace M.X :=
    MeasurableSpace.generateFrom (invariantCountableCore M hM)
  change Chapter00.IsSigmaAlgebraFamily
    {A : Set M.X | @MeasurableSet M.X
      (MeasurableSpace.generateFrom (invariantCountableCore M hM)) A}
  constructor
  · change MeasurableSet (Set.univ : Set M.X)
    exact MeasurableSet.univ
  constructor
  · intro A hA
    change MeasurableSet A at hA
    change MeasurableSet Aᶜ
    exact hA.compl
  · intro A hA
    change ∀ n, MeasurableSet (A n) at hA
    change MeasurableSet (⋃ n, A n)
    exact MeasurableSet.iUnion hA

theorem invariantCoreSigmaAlgebra_le_ambient
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    invariantCoreSigmaAlgebra M hM ⊆ M.𝓧 := by
  intro A hA
  exact (MeasurableSpace.generateFrom_le
    (fun _ h ↦ invariantCountableCore_measurable M hM h)) A hA

theorem invariantCoreMeasurableSpace_le
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    invariantCoreMeasurableSpace M hM ≤ M.measurableSpace :=
  MeasurableSpace.generateFrom_le
    (fun _ h ↦ invariantCountableCore_measurable M hM h)

theorem invariantCoreSigmaAlgebra_invariant
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {A : Set M.X} (hA : A ∈ invariantCoreSigmaAlgebra M hM) :
    M.T ⁻¹' A =ᵐ[M.μ] A := by
  exact MeasurableSpace.generateFrom_induction
    (invariantCountableCore M hM)
    (fun B _ ↦ M.T ⁻¹' B =ᵐ[M.μ] B)
    (by
      intro B hB _
      rw [← measure_symmDiff_eq_zero_iff]
      simpa [Chapter00.symmDiff, Set.symmDiff_def] using
        invariantCountableCore_invariant M hM hB)
    (by simp)
    (by
      intro B _ hBinv
      simpa only [Set.preimage_compl] using hBinv.compl)
    (by
      intro B _ hBinv
      have hall : ∀ᵐ x ∂M.μ, ∀ n, (M.T ⁻¹' B n) x = (B n) x :=
        ae_all_iff.mpr hBinv
      filter_upwards [hall] with x hx
      change (x ∈ M.T ⁻¹' ⋃ n, B n) = (x ∈ ⋃ n, B n)
      simp only [Set.mem_preimage, Set.mem_iUnion]
      exact propext ⟨
        fun ⟨n, hn⟩ ↦ ⟨n, (hx n).mp hn⟩,
        fun ⟨n, hn⟩ ↦ ⟨n, (hx n).mpr hn⟩⟩)
    A hA

theorem invariantCountableCore_nonempty
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    (invariantCountableCore M hM).Nonempty := by
  letI : Nonempty (InvariantIndicatorLp M hM) :=
    invariantIndicatorLp_nonempty M hM
  obtain ⟨d, hd⟩ := (denseInvariantIndicators_dense M hM).nonempty
  exact ⟨denseInvariantIndicatorSet M hM ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩⟩

theorem invariantCoreSigmaAlgebra_countablyGenerated
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter00.CountablyGeneratedFamily (invariantCoreSigmaAlgebra M hM) := by
  obtain ⟨G, hG⟩ :=
    (invariantCountableCore_countable M hM).exists_eq_range
      (invariantCountableCore_nonempty M hM)
  exact ⟨G, by simp only [invariantCoreSigmaAlgebra, hG]⟩

/-- A fixed sequence generating the countable invariant core. -/
def invariantCoreGenerator
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) : ℕ → Set M.X :=
  Classical.choose (invariantCoreSigmaAlgebra_countablyGenerated M hM)

theorem invariantCoreGenerator_generates
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter00.generatedSigmaAlgebra
        (Set.range (invariantCoreGenerator M hM)) =
      invariantCoreSigmaAlgebra M hM :=
  Classical.choose_spec (invariantCoreSigmaAlgebra_countablyGenerated M hM)

theorem invariantCoreGenerator_mem
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) (n : ℕ) :
    invariantCoreGenerator M hM n ∈
      invariantCoreSigmaAlgebra M hM := by
  rw [← invariantCoreGenerator_generates M hM]
  exact MeasurableSpace.measurableSet_generateFrom ⟨n, rfl⟩

/-- The atom of the countable invariant core containing a point. -/
def invariantCoreAtom
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) (x : M.X) : Set M.X :=
  ⋂₀ {B : Set M.X |
    B ∈ invariantCoreSigmaAlgebra M hM ∧ x ∈ B}

private theorem invariantCore_membership_iff_of_generator_iff
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (x y : M.X)
    (hxy : ∀ n, x ∈ invariantCoreGenerator M hM n ↔
      y ∈ invariantCoreGenerator M hM n)
    {B : Set M.X} (hB : B ∈ invariantCoreSigmaAlgebra M hM) :
    x ∈ B ↔ y ∈ B := by
  have hB' : B ∈ Chapter00.generatedSigmaAlgebra
      (Set.range (invariantCoreGenerator M hM)) := by
    rw [invariantCoreGenerator_generates M hM]
    exact hB
  exact MeasurableSpace.generateFrom_induction
    (Set.range (invariantCoreGenerator M hM))
    (fun C _ ↦ x ∈ C ↔ y ∈ C)
    (by
      intro C hC
      rcases hC with ⟨n, rfl⟩
      intro _
      exact hxy n)
    (by simp)
    (by
      intro C _ hC
      exact not_congr hC)
    (by
      intro C _ hC
      simp only [Set.mem_iUnion]
      exact exists_congr fun n ↦ hC n)
    B hB'

theorem invariantCoreAtom_eq_iInter
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) (x : M.X) :
    invariantCoreAtom M hM x =
      ⋂ n, if x ∈ invariantCoreGenerator M hM n then
        invariantCoreGenerator M hM n
      else (invariantCoreGenerator M hM n)ᶜ := by
  ext y
  constructor
  · intro hy
    apply Set.mem_iInter.mpr
    intro n
    by_cases hx : x ∈ invariantCoreGenerator M hM n
    · simpa [hx] using
        hy (invariantCoreGenerator M hM n)
          ⟨invariantCoreGenerator_mem M hM n, hx⟩
    · have hcomp :
          (invariantCoreGenerator M hM n)ᶜ ∈
            invariantCoreSigmaAlgebra M hM :=
        (invariantCoreSigmaAlgebra_isSigma M hM).2.1 _
          (invariantCoreGenerator_mem M hM n)
      simpa [hx] using hy (invariantCoreGenerator M hM n)ᶜ
        ⟨hcomp, hx⟩
  · intro hy
    have hxy : ∀ n, x ∈ invariantCoreGenerator M hM n ↔
        y ∈ invariantCoreGenerator M hM n := by
      intro n
      have hyn := Set.mem_iInter.mp hy n
      by_cases hx : x ∈ invariantCoreGenerator M hM n
      · simp only [if_pos hx] at hyn
        exact ⟨fun _ ↦ hyn, fun _ ↦ hx⟩
      · simp only [if_neg hx, Set.mem_compl_iff] at hyn
        exact ⟨fun h ↦ (hx h).elim, fun h ↦ (hyn h).elim⟩
    intro B hB
    exact (invariantCore_membership_iff_of_generator_iff
      M hM x y hxy hB.1).mp hB.2

theorem invariantCoreAtom_mem
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) (x : M.X) :
    invariantCoreAtom M hM x ∈
      invariantCoreSigmaAlgebra M hM := by
  rw [invariantCoreAtom_eq_iInter M hM x]
  change @MeasurableSet M.X (invariantCoreMeasurableSpace M hM)
    (⋂ n, if x ∈ invariantCoreGenerator M hM n then
      invariantCoreGenerator M hM n
    else (invariantCoreGenerator M hM n)ᶜ)
  apply MeasurableSet.iInter
  intro n
  have hgen :
      @MeasurableSet M.X (invariantCoreMeasurableSpace M hM)
        (invariantCoreGenerator M hM n) := by
    exact invariantCoreGenerator_mem M hM n
  by_cases hx : x ∈ invariantCoreGenerator M hM n
  · simpa only [if_pos hx] using hgen
  · simpa only [if_neg hx] using hgen.compl

theorem invariantCoreAtom_subset
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (x : M.X) {B : Set M.X}
    (hB : B ∈ invariantCoreSigmaAlgebra M hM) (hx : x ∈ B) :
    invariantCoreAtom M hM x ⊆ B := by
  intro y hy
  exact hy B ⟨hB, hx⟩

theorem invariantCoreAtom_eq_of_mem
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (x y : M.X) (hy : y ∈ invariantCoreAtom M hM x) :
    invariantCoreAtom M hM y = invariantCoreAtom M hM x := by
  have hxy : ∀ B : Set M.X, B ∈ invariantCoreSigmaAlgebra M hM →
      (x ∈ B ↔ y ∈ B) := by
    intro B hB
    constructor
    · intro hx
      exact hy B ⟨hB, hx⟩
    · intro hyB
      by_contra hxB
      have hBc : Bᶜ ∈ invariantCoreSigmaAlgebra M hM :=
        (invariantCoreSigmaAlgebra_isSigma M hM).2.1 B hB
      have hyBc := hy Bᶜ ⟨hBc, hxB⟩
      exact hyBc hyB
  ext z
  constructor
  · intro hz B hB
    exact hz B ⟨hB.1, (hxy B hB.1).mp hB.2⟩
  · intro hz B hB
    exact hz B ⟨hB.1, (hxy B hB.1).mpr hB.2⟩

/-- On a proper component, every point in the supporting core atom indexes
the same conditional measure. -/
theorem coreConditionalMeasure_eq_of_mem_atom
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (hsame : ∀ x ∈ D.fullSet, ∀ y ∈ D.fullSet,
      invariantCoreAtom M hM x = invariantCoreAtom M hM y →
        D.measureAt x = D.measureAt y)
    (x : M.X) (hx : x ∈ D.fullSet)
    (y : M.X) (hy : y ∈ invariantCoreAtom M hM x) :
    D.measureAt y = D.measureAt x := by
  have hyfull : y ∈ D.fullSet :=
    invariantCoreAtom_subset M hM x hD.1 hx hy
  exact hsame y hyfull x hx
    (invariantCoreAtom_eq_of_mem M hM x y hy)

/-- The component kernel is almost surely constant when sampled inside one
proper invariant-core atom. -/
theorem coreConditionalMeasure_ae_eq_on_atom
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (hproper : ∀ x ∈ D.fullSet,
      D.measureAt x (invariantCoreAtom M hM x) = 1)
    (hsame : ∀ x ∈ D.fullSet, ∀ y ∈ D.fullSet,
      invariantCoreAtom M hM x = invariantCoreAtom M hM y →
        D.measureAt x = D.measureAt y)
    (x : M.X) (hx : x ∈ D.fullSet) :
    ∀ᵐ y ∂(D.measureAt x), D.measureAt y = D.measureAt x := by
  letI : IsProbabilityMeasure (D.measureAt x) := hD.2.2.1 x hx
  have hatomMeas : MeasurableSet (invariantCoreAtom M hM x) :=
    invariantCoreSigmaAlgebra_le_ambient M hM
      (invariantCoreAtom_mem M hM x)
  have haeAtom :
      ∀ᵐ y ∂(D.measureAt x), y ∈ invariantCoreAtom M hM x := by
    rw [ae_iff]
    calc
      D.measureAt x (invariantCoreAtom M hM x)ᶜ =
          D.measureAt x Set.univ -
            D.measureAt x (invariantCoreAtom M hM x) :=
        measure_compl hatomMeas (measure_ne_top _ _)
      _ = 0 := by rw [hproper x hx, measure_univ]; simp
  filter_upwards [haeAtom] with y hy
  exact coreConditionalMeasure_eq_of_mem_atom
    M hM E D hD hsame x hx y hy

/-- A regular conditional probability over the countable invariant core,
with the properness conclusion supplied by the countable-generation part of
the conditional-measure theorem. -/
theorem invariantCoreConditionalMeasure_exists
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    let P : Chapter00.BasicProbabilitySpaceData :=
      { X := M.X
        measurableSpace := M.measurableSpace
        μ := M.μ
        isProbability := hM.1 }
    ∃ E : Chapter00.ConditionalExpectationData P
        (invariantCoreSigmaAlgebra M hM),
      ∃ D : Chapter00.ConditionalMeasureFamily P
          (invariantCoreSigmaAlgebra M hM),
        Chapter00.IsConditionalExpectation P
            (invariantCoreSigmaAlgebra M hM) E ∧
        Chapter00.IsConditionalMeasureFamily P
            (invariantCoreSigmaAlgebra M hM) E D ∧
        ((∀ x ∈ D.fullSet,
            D.measureAt x
              (⋂₀ {B : Set M.X |
                B ∈ invariantCoreSigmaAlgebra M hM ∧ x ∈ B}) = 1) ∧
          ∀ x ∈ D.fullSet, ∀ y ∈ D.fullSet,
            (⋂₀ {B : Set M.X |
                B ∈ invariantCoreSigmaAlgebra M hM ∧ x ∈ B}) =
              (⋂₀ {B : Set M.X |
                B ∈ invariantCoreSigmaAlgebra M hM ∧ y ∈ B}) →
            D.measureAt x = D.measureAt y) := by
  dsimp
  obtain ⟨E, D, hE, hD, hproper, _⟩ :=
    Chapter00.Section03.conditionalMeasureFamilyAux
      ({ X := M.X
         measurableSpace := M.measurableSpace
         μ := M.μ
         isProbability := hM.1 } :
        Chapter00.BasicProbabilitySpaceData)
      (invariantCoreSigmaAlgebra M hM)
      (invariantCoreSigmaAlgebra_isSigma M hM)
      (invariantCoreSigmaAlgebra_le_ambient M hM)
  exact ⟨E, D, hE, hD,
    hproper (invariantCoreSigmaAlgebra_countablyGenerated M hM)⟩

/-- Conditional expectation onto the countable invariant core commutes with
one Koopman step. -/
theorem coreCondExp_comp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : Integrable f M.μ) :
    condExp (invariantCoreMeasurableSpace M hM) M.μ
        (fun x ↦ f (M.T x)) =ᵐ[M.μ]
      condExp (invariantCoreMeasurableSpace M hM) M.μ f := by
  have hcomp : Integrable (fun x ↦ f (M.T x)) M.μ :=
    (hM.2.integrable_comp hf.aestronglyMeasurable).2 hf
  let mCore := invariantCoreMeasurableSpace M hM
  let hm : mCore ≤ M.measurableSpace :=
    invariantCoreMeasurableSpace_le M hM
  letI : IsProbabilityMeasure M.μ := hM.1
  have hinv : ∀ s : Set M.X, @MeasurableSet M.X mCore s →
      M.T ⁻¹' s =ᵐ[M.μ] s := by
    intro s hs
    exact invariantCoreSigmaAlgebra_invariant M hM hs
  have hsetIntegral : ∀ s : Set M.X, @MeasurableSet M.X mCore s →
      (∫ x in s, condExp mCore M.μ (fun y ↦ f (M.T y)) x ∂M.μ) =
        ∫ x in s, f x ∂M.μ := by
    intro s hs
    letI : MeasurableSpace M.X := M.measurableSpace
    have hs0 : @MeasurableSet M.X M.measurableSpace s := hm s hs
    have hsetinv := hinv s hs
    have hmap_eq : Measure.map M.T M.μ = M.μ := hM.2.map_eq
    have hgsm : AEStronglyMeasurable (s.indicator f)
        (Measure.map M.T M.μ) := by
      rw [hmap_eq]
      exact (hf.indicator hs0).aestronglyMeasurable
    have hmap := integral_map (μ := M.μ) (φ := M.T)
      (f := s.indicator f) hM.2.measurable.aemeasurable hgsm
    rw [hmap_eq] at hmap
    calc
      (∫ x in s, condExp mCore M.μ (fun y ↦ f (M.T y)) x ∂M.μ) =
          ∫ x in s, f (M.T x) ∂M.μ :=
        setIntegral_condExp hm hcomp hs
      _ = ∫ x, (s.indicator f) (M.T x) ∂M.μ := by
        rw [← integral_indicator hs0]
        apply integral_congr_ae
        filter_upwards [hsetinv] with x hx
        by_cases hTx : M.T x ∈ s
        · have hxS : x ∈ s := Eq.mp hx hTx
          simp [Set.indicator, hTx, hxS]
        · have hxS : x ∉ s := fun h ↦ hTx (Eq.mpr hx h)
          simp [Set.indicator, hTx, hxS]
      _ = ∫ x, s.indicator f x ∂M.μ := hmap.symm
      _ = ∫ x in s, f x ∂M.μ := integral_indicator hs0
  refine ae_eq_condExp_of_forall_setIntegral_eq
    (f := f) (g := condExp mCore M.μ (fun x ↦ f (M.T x)))
      hm hf ?_ ?_ ?_
  · intro s hs _
    exact integrable_condExp.integrableOn
  · intro s hs _
    exact hsetIntegral s hs
  · exact stronglyMeasurable_condExp.aestronglyMeasurable

/-- Any conditional expectation supplied for the countable invariant core is
the usual conditional expectation for its generated measurable space. -/
theorem coreConditionalExpectation_ae_eq_condExp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (f : M.X → ℂ) (hf : Integrable f M.μ) :
    E.op f =ᵐ[M.μ]
      condExp (invariantCoreMeasurableSpace M hM) M.μ f := by
  let mCore := invariantCoreMeasurableSpace M hM
  have hm : mCore ≤ M.measurableSpace :=
    invariantCoreMeasurableSpace_le M hM
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : SigmaFinite (M.μ.trim hm) := inferInstance
  obtain ⟨hfmeas, hfint, hfsets⟩ := hE f hf
  have hfmeas' : @Measurable M.X ℂ mCore (borel ℂ) (E.op f) := by
    apply measurable_of_isClosed
    intro C hC
    exact hfmeas C hC
  exact ae_eq_condExp_of_forall_setIntegral_eq hm hf
    (fun _ _ _ ↦ hfint.integrableOn)
    (fun B hB _ ↦ hfsets B hB)
    hfmeas'.aestronglyMeasurable

/-- The mass assigned by a conditional component to an ambient measurable
set, regarded as a complex-valued function of the component index. -/
def componentMassComplex
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (B : Set M.X) (x : M.X) : ℂ :=
  ((D.measureAt x B).toReal : ℂ)

/-- Component mass is measurable for the countable invariant core. -/
theorem componentMassComplex_measurable
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (B : Set M.X) (hB : MeasurableSet B) :
    @Measurable M.X ℂ (invariantCoreMeasurableSpace M hM) (borel ℂ)
      (componentMassComplex M hM D B) := by
  let mCore := invariantCoreMeasurableSpace M hM
  have hmass :
      @Measurable M.X ENNReal mCore (borel ENNReal)
        (fun x ↦ D.measureAt x B) := by
    refine @measurable_of_isClosed ENNReal M.X
      _ _ _ mCore (fun x ↦ D.measureAt x B) ?_
    intro C hC
    exact hD.2.2.2.1 B hB C hC
  exact Complex.continuous_ofReal.measurable.comp
    hmass.ennreal_toReal

/-- For an indicator, conditional expectation onto the invariant core is
the complex-valued mass of the corresponding conditional component. -/
theorem coreCondExp_indicator_ae_eq_componentMass
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (B : Set M.X) (hB : MeasurableSet B) :
    condExp (invariantCoreMeasurableSpace M hM) M.μ
      (CorrelationMean.indicatorComplex B) =ᵐ[M.μ]
      componentMassComplex M hM D B := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let f : M.X → ℂ := CorrelationMean.indicatorComplex B
  have hf : Integrable f M.μ :=
    (CorrelationMean.indicatorComplex_memLp M hM B hB 1)
      |>.integrable (by norm_num)
  have hCE :=
    coreConditionalExpectation_ae_eq_condExp M hM E hE f hf
  have hrep :
      E.op f =ᵐ[M.μ] fun x ↦ ∫ y, f y ∂(D.measureAt x) :=
    hD.2.2.2.2 f hf
  filter_upwards [hCE, hrep] with x hxCE hxrep
  have hint :
      (∫ y, f y ∂(D.measureAt x)) =
        componentMassComplex M hM D B x := by
    have hBInt :
        ∫ y : (invariantBaseProbabilitySpace M hM).X,
            B.indicator (fun _ ↦ (1 : ℂ)) y ∂(D.measureAt x) =
          (D.measureAt x).real B • (1 : ℂ) :=
      integral_indicator_const (μ := D.measureAt x) (1 : ℂ) hB
    rw [show f = B.indicator (fun _ ↦ (1 : ℂ)) by rfl, hBInt]
    simp [componentMassComplex, Measure.real_def]
  exact hxCE.symm.trans (hxrep.trans hint)

/-- Conditional expectation onto the countable invariant core agrees with
conditional expectation onto the full generated invariant sigma-algebra. -/
theorem coreCondExp_ae_eq_invariantCondExp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : Integrable f M.μ) :
    condExp (invariantCoreMeasurableSpace M hM) M.μ f =ᵐ[M.μ]
      condExp
        (MeasurableSpace.generateFrom (invariantSigmaAlgebra M))
        M.μ f := by
  let mCore := invariantCoreMeasurableSpace M hM
  let mInv :=
    MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  have hmCore : mCore ≤ M.measurableSpace :=
    invariantCoreMeasurableSpace_le M hM
  have hmInv : mInv ≤ M.measurableSpace := by
    apply MeasurableSpace.generateFrom_le
    intro B hB
    exact hB.1
  have hCoreInv : mCore ≤ mInv := by
    apply MeasurableSpace.generateFrom_le
    intro B hB
    apply MeasurableSpace.measurableSet_generateFrom
    exact ⟨invariantCountableCore_measurable M hM hB,
      invariantCountableCore_invariant M hM hB⟩
  letI : IsProbabilityMeasure M.μ := hM.1
  apply ae_eq_condExp_of_forall_setIntegral_eq hmInv hf
  · intro B hB _
    exact integrable_condExp.integrableOn
  · intro B hB _
    obtain ⟨C, hC, hBC⟩ :=
      invariantGeneratedSet_exists_core_ae M hM B hB
    calc
      (∫ x in B, condExp mCore M.μ f x ∂M.μ) =
          ∫ x in C, condExp mCore M.μ f x ∂M.μ := by
        rw [Measure.restrict_congr_set hBC]
      _ = ∫ x in C, f x ∂M.μ :=
        setIntegral_condExp hmCore hf hC
      _ = ∫ x in B, f x ∂M.μ := by
        rw [Measure.restrict_congr_set hBC]
  · exact
      (stronglyMeasurable_condExp.mono hCoreInv).aestronglyMeasurable

/-- Koopman Cesàro averages converge in ambient `L²` to conditional
expectation onto the countable invariant core. -/
theorem ergodicAverage_tendsto_coreCondExp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    Tendsto
      (fun n ↦ eLpNorm
        (fun x ↦ ergodicAverage M f n x -
          condExp (invariantCoreMeasurableSpace M hM) M.μ f x)
        2 M.μ)
      Filter.atTop (nhds 0) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  obtain ⟨fstar, _, _, hconv, hInv, _, _⟩ :=
    MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM f hf
  have hfint : Integrable f M.μ := hf.integrable (by norm_num)
  have hcore :
      condExp (invariantCoreMeasurableSpace M hM) M.μ f =ᵐ[M.μ]
        fstar :=
    (coreCondExp_ae_eq_invariantCondExp M hM f hfint).trans hInv
  apply hconv.congr'
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards [hcore] with x hx
  rw [hx]

/-- For every ambient measurable set, one subsequence of its Koopman
Cesàro averages converges almost everywhere to its conditional component
mass. -/
theorem ergodicAverage_subsequence_tendsto_componentMass
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (B : Set M.X) (hB : MeasurableSet B) :
    ∃ nseq : ℕ → ℕ, StrictMono nseq ∧
      ∀ᵐ x ∂M.μ,
        Tendsto
          (fun k ↦ ergodicAverage M
            (CorrelationMean.indicatorComplex B) (nseq k) x)
          Filter.atTop
          (nhds (componentMassComplex M hM D B x)) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let f : M.X → ℂ := CorrelationMean.indicatorComplex B
  have hf : M.lpMember 2 f :=
    CorrelationMean.indicatorComplex_memLp M hM B hB 2
  obtain ⟨fstar, hfstar, _, hconv, hInv, _, _⟩ :=
    MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM f hf
  obtain ⟨nseq, hnseq, hpoint⟩ :=
    Chapter00.Section01.lpNormConvergenceHasAeConvergentSubsequence
      (invariantBaseProbabilitySpace M hM)
      2 (by norm_num)
      (fun n ↦ ergodicAverage M f n) fstar
      (fun n ↦ ErgodicAverageLp.ergodicAverage_memLp M hM 2 f hf n)
      hfstar hconv
  have hfint : Integrable f M.μ := hf.integrable (by norm_num)
  have hcoreStar :
      condExp (invariantCoreMeasurableSpace M hM) M.μ f =ᵐ[M.μ]
        fstar :=
    (coreCondExp_ae_eq_invariantCondExp M hM f hfint).trans hInv
  have hcoreMass :
      condExp (invariantCoreMeasurableSpace M hM) M.μ f =ᵐ[M.μ]
        componentMassComplex M hM D B := by
    simpa [f] using
      coreCondExp_indicator_ae_eq_componentMass
        M hM E D hE hD B hB
  have hstarMass :
      fstar =ᵐ[M.μ] componentMassComplex M hM D B :=
    hcoreStar.symm.trans hcoreMass
  refine ⟨nseq, hnseq, ?_⟩
  filter_upwards [hpoint, hstarMass] with x hx hxeq
  change Tendsto
    (fun k ↦ ergodicAverage M
      (CorrelationMean.indicatorComplex B) (nseq k) x)
    Filter.atTop (nhds (fstar x)) at hx
  rw [hxeq] at hx
  exact hx

/-- The conditional measures over the invariant core assign the same mass to
a measurable set and to its one-step preimage, almost surely. -/
theorem coreConditionalMeasure_preimage_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (B : Set M.X) (hB : MeasurableSet B) :
    ∀ᵐ x ∂M.μ, D.measureAt x (M.T ⁻¹' B) = D.measureAt x B := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let f : M.X → ℂ := CorrelationMean.indicatorComplex B
  let g : M.X → ℂ := CorrelationMean.indicatorComplex (M.T ⁻¹' B)
  have hpre : MeasurableSet (M.T ⁻¹' B) := hM.2.measurable hB
  have hf : Integrable f M.μ :=
    (CorrelationMean.indicatorComplex_memLp M hM B hB 1).integrable (by norm_num)
  have hg : Integrable g M.μ :=
    (CorrelationMean.indicatorComplex_memLp M hM
      (M.T ⁻¹' B) hpre 1).integrable (by norm_num)
  have hgf : g = fun x ↦ f (M.T x) := by
    funext x
    simp only [f, g, CorrelationMean.indicatorComplex,
      Set.indicator, Set.mem_preimage]
  have hEf :=
    coreConditionalExpectation_ae_eq_condExp M hM E hE f hf
  have hEg :=
    coreConditionalExpectation_ae_eq_condExp M hM E hE g hg
  have hCore :
      condExp (invariantCoreMeasurableSpace M hM) M.μ g =ᵐ[M.μ]
        condExp (invariantCoreMeasurableSpace M hM) M.μ f := by
    rw [hgf]
    exact coreCondExp_comp M hM f hf
  have hCE : E.op g =ᵐ[M.μ] E.op f := by
    exact hEg.trans (hCore.trans hEf.symm)
  have hDrepF :
      E.op f =ᵐ[M.μ] fun x ↦ ∫ y, f y ∂(D.measureAt x) :=
    hD.2.2.2.2 f hf
  have hDrepG :
      E.op g =ᵐ[M.μ] fun x ↦ ∫ y, g y ∂(D.measureAt x) :=
    hD.2.2.2.2 g hg
  have hfull : ∀ᵐ x ∂M.μ, x ∈ D.fullSet := by
    rw [ae_iff]
    change M.μ D.fullSetᶜ = 0
    have hfullMeas : MeasurableSet D.fullSet :=
      invariantCoreSigmaAlgebra_le_ambient M hM hD.1
    have hfullOne : M.μ D.fullSet = 1 := hD.2.1
    calc
      M.μ D.fullSetᶜ = M.μ Set.univ - M.μ D.fullSet :=
        measure_compl hfullMeas (measure_ne_top M.μ D.fullSet)
      _ = 0 := by rw [hfullOne]; simp
  filter_upwards [hDrepG, hCE, hDrepF, hfull] with x hxG hxCE hxF hxfull
  letI : IsProbabilityMeasure (D.measureAt x) := hD.2.2.1 x hxfull
  have hint : ∫ y, g y ∂(D.measureAt x) =
      ∫ y, f y ∂(D.measureAt x) :=
    hxG.symm.trans (hxCE.trans hxF)
  have hreal :
      (D.measureAt x (M.T ⁻¹' B)).toReal =
        (D.measureAt x B).toReal := by
    have hint' :
        ∫ y, (M.T ⁻¹' B).indicator (fun _ ↦ (1 : ℂ)) y ∂(D.measureAt x) =
          ∫ y, B.indicator (fun _ ↦ (1 : ℂ)) y ∂(D.measureAt x) := by
      simpa [f, g, CorrelationMean.indicatorComplex] using hint
    have hpreInt :
        ∫ y : (invariantBaseProbabilitySpace M hM).X,
            (M.T ⁻¹' B).indicator (fun _ ↦ (1 : ℂ)) y ∂(D.measureAt x) =
          (D.measureAt x).real (M.T ⁻¹' B) • (1 : ℂ) :=
      integral_indicator_const (μ := D.measureAt x) (1 : ℂ) hpre
    have hBInt :
        ∫ y : (invariantBaseProbabilitySpace M hM).X,
            B.indicator (fun _ ↦ (1 : ℂ)) y ∂(D.measureAt x) =
          (D.measureAt x).real B • (1 : ℂ) :=
      integral_indicator_const (μ := D.measureAt x) (1 : ℂ) hB
    rw [hpreInt, hBInt] at hint'
    simpa [Measure.real_def] using hint'
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top (D.measureAt x) (M.T ⁻¹' B))
    (measure_ne_top (D.measureAt x) B)).mp hreal

/-- An ambient null measurable set is null in almost every conditional
component. -/
theorem coreConditionalMeasure_null_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (N : Set M.X) (hN : MeasurableSet N) (hNzero : M.μ N = 0) :
    ∀ᵐ x ∂M.μ, D.measureAt x N = 0 := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let f : M.X → ℂ := CorrelationMean.indicatorComplex N
  have hf : Integrable f M.μ :=
    (CorrelationMean.indicatorComplex_memLp M hM N hN 1)
      |>.integrable (by norm_num)
  have hfae : f =ᵐ[M.μ] 0 := by
    have haeN : ∀ᵐ x ∂M.μ, x ∉ N := by
      rw [ae_iff]
      have hset : {x : M.X | ¬ x ∉ N} = N := by
        ext x
        simp
      rw [hset]
      exact hNzero
    filter_upwards [haeN] with x hx
    simp [f, CorrelationMean.indicatorComplex, hx]
  have hEcore :=
    coreConditionalExpectation_ae_eq_condExp M hM E hE f hf
  have hcondZero :
      condExp (invariantCoreMeasurableSpace M hM) M.μ f =ᵐ[M.μ] 0 := by
    have hc := condExp_congr_ae
      (m := invariantCoreMeasurableSpace M hM) hfae
    simpa using hc
  have hEzero : E.op f =ᵐ[M.μ] 0 :=
    hEcore.trans hcondZero
  have hrep :
      E.op f =ᵐ[M.μ] fun x ↦ ∫ y, f y ∂(D.measureAt x) :=
    hD.2.2.2.2 f hf
  have hfull : ∀ᵐ x ∂M.μ, x ∈ D.fullSet := by
    rw [ae_iff]
    change M.μ D.fullSetᶜ = 0
    have hfullMeas : MeasurableSet D.fullSet :=
      invariantCoreSigmaAlgebra_le_ambient M hM hD.1
    have hfullOne : M.μ D.fullSet = 1 := hD.2.1
    calc
      M.μ D.fullSetᶜ = M.μ Set.univ - M.μ D.fullSet :=
        measure_compl hfullMeas (measure_ne_top M.μ D.fullSet)
      _ = 0 := by rw [hfullOne, measure_univ]; simp
  filter_upwards [hrep, hEzero, hfull] with x hxrep hxzero hxfull
  letI : IsProbabilityMeasure (D.measureAt x) := hD.2.2.1 x hxfull
  have hint : ∫ y, f y ∂(D.measureAt x) = 0 :=
    hxrep.symm.trans hxzero
  have hreal : (D.measureAt x N).toReal = 0 := by
    have hNInt :
        ∫ y, N.indicator (fun _ ↦ (1 : ℂ)) y ∂(D.measureAt x) =
          (D.measureAt x).real N • (1 : ℂ) :=
      integral_indicator_const (μ := D.measureAt x) (1 : ℂ) hN
    rw [show f = N.indicator (fun _ ↦ (1 : ℂ)) by
      rfl, hNInt] at hint
    simpa [Measure.real_def] using hint
  rcases (ENNReal.toReal_eq_zero_iff (D.measureAt x N)).mp hreal with
    hzero | htop
  · exact hzero
  · exact (measure_ne_top (D.measureAt x) N htop).elim

/-- Any ambient almost-everywhere statement holds almost everywhere inside
almost every conditional component. -/
theorem coreConditionalMeasure_ae_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (p : M.X → Prop) (hp : ∀ᵐ y ∂M.μ, p y) :
    ∀ᵐ x ∂M.μ, ∀ᵐ y ∂(D.measureAt x), p y := by
  let N : Set M.X := {y | ¬ p y}
  have hNzero : M.μ N = 0 := by
    rw [ae_iff] at hp
    exact hp
  let H : Set M.X := toMeasurable M.μ N
  have hNH : N ⊆ H := subset_toMeasurable M.μ N
  have hHmeas : MeasurableSet H := measurableSet_toMeasurable M.μ N
  have hHzero : M.μ H = 0 := by
    exact (measure_toMeasurable N).trans hNzero
  have hcomp :=
    coreConditionalMeasure_null_ae M hM E D hE hD H hHmeas hHzero
  filter_upwards [hcomp] with x hx
  rw [ae_iff]
  exact measure_mono_null hNH hx

/-- The same subsequence converges almost everywhere inside almost every
proper conditional component, now to the constant mass of that component. -/
theorem ergodicAverage_subsequence_tendsto_componentMass_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (hproper : ∀ x ∈ D.fullSet,
      D.measureAt x (invariantCoreAtom M hM x) = 1)
    (hsame : ∀ x ∈ D.fullSet, ∀ y ∈ D.fullSet,
      invariantCoreAtom M hM x = invariantCoreAtom M hM y →
        D.measureAt x = D.measureAt y)
    (B : Set M.X) (hB : MeasurableSet B) :
    ∃ nseq : ℕ → ℕ, StrictMono nseq ∧
      ∀ᵐ x ∂M.μ, ∀ᵐ y ∂(D.measureAt x),
        Tendsto
          (fun k ↦ ergodicAverage M
            (CorrelationMean.indicatorComplex B) (nseq k) y)
          Filter.atTop
          (nhds (componentMassComplex M hM D B x)) := by
  obtain ⟨nseq, hnseq, hpoint⟩ :=
    ergodicAverage_subsequence_tendsto_componentMass
      M hM E D hE hD B hB
  have htransfer :=
    coreConditionalMeasure_ae_ae M hM E D hE hD
      (fun y ↦ Tendsto
        (fun k ↦ ergodicAverage M
          (CorrelationMean.indicatorComplex B) (nseq k) y)
        Filter.atTop
        (nhds (componentMassComplex M hM D B y)))
      hpoint
  have hfull : ∀ᵐ x ∂M.μ, x ∈ D.fullSet := by
    rw [ae_iff]
    change M.μ D.fullSetᶜ = 0
    have hfullMeas : MeasurableSet D.fullSet :=
      invariantCoreSigmaAlgebra_le_ambient M hM hD.1
    have hfullOne : M.μ D.fullSet = 1 := hD.2.1
    letI : IsProbabilityMeasure M.μ := hM.1
    calc
      M.μ D.fullSetᶜ = M.μ Set.univ - M.μ D.fullSet :=
        measure_compl hfullMeas (measure_ne_top M.μ D.fullSet)
      _ = 0 := by rw [hfullOne, measure_univ]; simp
  refine ⟨nseq, hnseq, ?_⟩
  filter_upwards [htransfer, hfull] with x hxpoint hxfull
  have hkernel :=
    coreConditionalMeasure_ae_eq_on_atom
      M hM E D hD hproper hsame x hxfull
  filter_upwards [hxpoint, hkernel] with y hytend hymeasure
  change Tendsto
    (fun k ↦ ergodicAverage M
      (CorrelationMean.indicatorComplex B) (nseq k) y)
    Filter.atTop
    (nhds (componentMassComplex M hM D B y)) at hytend
  have heq :
      componentMassComplex M hM D B y =
        componentMassComplex M hM D B x := by
    change D.measureAt y = D.measureAt x at hymeasure
    rw [componentMassComplex, componentMassComplex, hymeasure]
  rw [heq] at hytend
  exact hytend

/-- If one strictly increasing subsequence of Koopman averages converges
almost everywhere to a constant, then the whole sequence converges to that
constant in `L²`. -/
theorem ergodicAverage_tendsto_const_of_subsequence_ae
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f)
    (c : ℂ) (nseq : ℕ → ℕ) (hnseq : StrictMono nseq)
    (hpoint : ∀ᵐ x ∂M.μ,
      Tendsto (fun k ↦ ergodicAverage M f (nseq k) x)
        Filter.atTop (nhds c)) :
    Tendsto
      (fun n ↦ eLpNorm
        (fun x ↦ ergodicAverage M f n x - c) 2 M.μ)
      Filter.atTop (nhds 0) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  obtain ⟨fstar, hfstar, _, hconv, _, _, _⟩ :=
    MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM f hf
  have hconvSub :
      Tendsto
        (fun k ↦ eLpNorm
          (fun x ↦ ergodicAverage M f (nseq k) x - fstar x)
          2 M.μ)
        Filter.atTop (nhds 0) :=
    hconv.comp hnseq.tendsto_atTop
  obtain ⟨kseq, hkseq, hstarPoint⟩ :=
    Chapter00.Section01.lpNormConvergenceHasAeConvergentSubsequence
      ({ X := M.X
         measurableSpace := M.measurableSpace
         μ := M.μ
         isProbability := hM.1 } :
        Chapter00.BasicProbabilitySpaceData)
      2 (by norm_num)
      (fun k ↦ ergodicAverage M f (nseq k)) fstar
      (fun k ↦ ErgodicAverageLp.ergodicAverage_memLp
        M hM 2 f hf (nseq k))
      hfstar hconvSub
  have hconstPoint :
      ∀ᵐ x ∂M.μ,
        Tendsto
          (fun j ↦ ergodicAverage M f (nseq (kseq j)) x)
          Filter.atTop (nhds c) := by
    filter_upwards [hpoint] with x hx
    exact hx.comp hkseq.tendsto_atTop
  have hstarConst : fstar =ᵐ[M.μ] fun _ ↦ c := by
    filter_upwards [hstarPoint, hconstPoint] with x hxstar hxc
    change Tendsto
      (fun j ↦ ergodicAverage M f (nseq (kseq j)) x)
      Filter.atTop (nhds (fstar x)) at hxstar
    exact tendsto_nhds_unique hxstar hxc
  apply hconv.congr'
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards [hstarConst] with x hx
  rw [hx]

/-- Almost every conditional component is preserved by the original
transformation. -/
theorem coreConditionalMeasure_measurePreserving_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D) :
    ∀ᵐ x ∂M.μ, MeasurePreserving M.T (D.measureAt x) (D.measureAt x) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let B : Set (Set M.X) := MeasurableSpace.countableGeneratingSet M.X
  let S : Set (Set M.X) := generatePiSystem B
  have hBcount : B.Countable :=
    MeasurableSpace.countable_countableGeneratingSet
  have hScount : S.Countable := by
    letI : Countable B := hBcount.to_subtype
    let interList : List B → Set M.X :=
      fun l ↦ l.foldr (fun s t ↦ s.1 ∩ t) Set.univ
    have interList_append (l r : List B) :
        interList (l ++ r) = interList l ∩ interList r := by
      induction l with
      | nil => simp [interList]
      | cons a l ih =>
          rw [List.cons_append]
          simp only [interList, List.foldr_cons]
          change a.1 ∩ interList (l ++ r) =
            (a.1 ∩ interList l) ∩ interList r
          rw [ih]
          exact (Set.inter_assoc _ _ _).symm
    have hrepr : ∀ {s : Set M.X}, s ∈ S →
        ∃ l : List B, interList l = s := by
      intro s hs
      induction hs with
      | base hmem =>
          exact ⟨[⟨_, hmem⟩], by simp [interList]⟩
      | inter hs ht _ ihs iht =>
          rcases ihs with ⟨l, rfl⟩
          rcases iht with ⟨r, rfl⟩
          exact ⟨l ++ r, interList_append l r⟩
    apply (Set.countable_range interList).mono
    intro s hs
    rcases hrepr hs with ⟨l, rfl⟩
    exact ⟨l, rfl⟩
  have hbasic : ∀ᵐ x ∂M.μ, ∀ s ∈ S,
      D.measureAt x (M.T ⁻¹' s) = D.measureAt x s := by
    letI : Countable S := hScount.to_subtype
    have hsubtype : ∀ t : S, ∀ᵐ x ∂M.μ,
        D.measureAt x (M.T ⁻¹' t.1) = D.measureAt x t.1 :=
      fun t ↦ coreConditionalMeasure_preimage_ae M hM E D hE hD t.1
        (generatePiSystem_measurableSet
          (fun u hu ↦ MeasurableSpace.measurableSet_countableGeneratingSet hu)
          t.1 t.2)
    have hall : ∀ᵐ x ∂M.μ, ∀ t : S,
        D.measureAt x (M.T ⁻¹' t.1) = D.measureAt x t.1 :=
      ae_all_iff.mpr hsubtype
    filter_upwards [hall] with x hx
    intro s hs
    exact hx ⟨s, hs⟩
  have hfull : ∀ᵐ x ∂M.μ, x ∈ D.fullSet := by
    rw [ae_iff]
    change M.μ D.fullSetᶜ = 0
    have hfullMeas : MeasurableSet D.fullSet :=
      invariantCoreSigmaAlgebra_le_ambient M hM hD.1
    have hfullOne : M.μ D.fullSet = 1 := hD.2.1
    calc
      M.μ D.fullSetᶜ = M.μ Set.univ - M.μ D.fullSet :=
        measure_compl hfullMeas (measure_ne_top M.μ D.fullSet)
      _ = 0 := by rw [hfullOne]; simp
  have hgen : M.measurableSpace = MeasurableSpace.generateFrom S := by
    simp [S, B, generateFrom_generatePiSystem_eq,
      MeasurableSpace.generateFrom_countableGeneratingSet]
  filter_upwards [hbasic, hfull] with x hx hxfull
  letI : IsProbabilityMeasure (D.measureAt x) := hD.2.2.1 x hxfull
  refine ⟨hM.2.measurable, ?_⟩
  apply Measure.ext_of_generateFrom_of_cover
      (μ := Measure.map M.T (D.measureAt x))
      (ν := D.measureAt x)
      (S := S) (T := {Set.univ}) hgen
      (Set.countable_singleton Set.univ)
      (isPiSystem_generatePiSystem B)
  · simp
  · intro t ht
    simp only [Set.mem_singleton_iff] at ht
    subst t
    rw [Measure.map_apply hM.2.measurable MeasurableSet.univ]
    exact measure_ne_top _ _
  · intro t ht s hs
    simp only [Set.mem_singleton_iff] at ht
    subst t
    rw [Set.inter_univ, Measure.map_apply hM.2.measurable
      (generatePiSystem_measurableSet
        (fun u hu ↦ MeasurableSpace.measurableSet_countableGeneratingSet hu)
        s hs)]
    exact hx s hs
  · intro t ht
    simp only [Set.mem_singleton_iff] at ht
    subst t
    rw [Measure.map_apply hM.2.measurable MeasurableSet.univ]
    congr 1

/-- On every proper conditional component, the countable invariant core is
measure-theoretically trivial. -/
theorem coreConditionalMeasure_core_zero_one
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (hproper : ∀ x ∈ D.fullSet,
      D.measureAt x
        (⋂₀ {B : Set M.X |
          B ∈ invariantCoreSigmaAlgebra M hM ∧ x ∈ B}) = 1)
    (x : M.X) (hx : x ∈ D.fullSet)
    (C : Set M.X) (hC : C ∈ invariantCoreSigmaAlgebra M hM) :
    D.measureAt x C = 0 ∨ D.measureAt x C = 1 := by
  letI : IsProbabilityMeasure (D.measureAt x) := hD.2.2.1 x hx
  let atom : Set M.X :=
    ⋂₀ {B : Set M.X |
      B ∈ invariantCoreSigmaAlgebra M hM ∧ x ∈ B}
  by_cases hxC : x ∈ C
  · right
    have hatom : atom ⊆ C := by
      intro y hy
      exact hy C ⟨hC, hxC⟩
    apply le_antisymm
    · calc
        D.measureAt x C ≤ D.measureAt x Set.univ :=
          measure_mono (Set.subset_univ C)
        _ = 1 := measure_univ
    · rw [← hproper x hx]
      exact measure_mono hatom
  · left
    have hCc : Cᶜ ∈ invariantCoreSigmaAlgebra M hM :=
      (invariantCoreSigmaAlgebra_isSigma M hM).2.1 C hC
    have hatom : atom ⊆ Cᶜ := by
      intro y hy
      exact hy Cᶜ ⟨hCc, hxC⟩
    have hcompOne : D.measureAt x Cᶜ = 1 := by
      apply le_antisymm
      · calc
          D.measureAt x Cᶜ ≤ D.measureAt x Set.univ :=
            measure_mono (Set.subset_univ Cᶜ)
          _ = 1 := measure_univ
      · rw [← hproper x hx]
        exact measure_mono hatom
    have hsub : (1 : ENNReal) - D.measureAt x C = 1 := by
      calc
        (1 : ENNReal) - D.measureAt x C =
            D.measureAt x Set.univ - D.measureAt x C := by rw [measure_univ]
        _ = D.measureAt x Cᶜ :=
          (measure_compl
            (invariantCoreSigmaAlgebra_le_ambient M hM hC)
            (measure_ne_top _ _)).symm
        _ = 1 := hcompOne
    by_contra hzero
    have hpos : 0 < D.measureAt x C := pos_iff_ne_zero.mpr hzero
    have hlt : (1 : ENNReal) - D.measureAt x C < 1 :=
      ENNReal.sub_lt_self (by simp) (by simp) (ne_of_gt hpos)
    rw [hsub] at hlt
    exact (lt_irrefl 1 hlt)

/-- The original transformation equipped with one conditional component
measure. -/
def conditionalComponentSystem
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (x : M.X) : System.{u} where
  X := M.X
  measurableSpace := M.measurableSpace
  μ := D.measureAt x
  T := M.T

/-- Almost every conditional component is itself a probability-preserving
system on the original measurable dynamics. -/
theorem conditionalComponentSystem_mps_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D) :
    ∀ᵐ x ∂M.μ, Chapter01.IsMeasurePreservingSystem
      (conditionalComponentSystem M hM D x) := by
  have hpres :=
    coreConditionalMeasure_measurePreserving_ae M hM E D hE hD
  have hfull : ∀ᵐ x ∂M.μ, x ∈ D.fullSet := by
    rw [ae_iff]
    change M.μ D.fullSetᶜ = 0
    have hfullMeas : MeasurableSet D.fullSet :=
      invariantCoreSigmaAlgebra_le_ambient M hM hD.1
    have hfullOne : M.μ D.fullSet = 1 := hD.2.1
    letI : IsProbabilityMeasure M.μ := hM.1
    calc
      M.μ D.fullSetᶜ = M.μ Set.univ - M.μ D.fullSet :=
        measure_compl hfullMeas (measure_ne_top M.μ D.fullSet)
      _ = 0 := by rw [hfullOne]; simp
  filter_upwards [hpres, hfull] with x hxpres hxfull
  exact ⟨hD.2.2.1 x hxfull, hxpres⟩

/-- `L²` convergence of indicator averages to the corresponding measure
constant implies the product limit for set correlations. -/
theorem cesaroCorrelations_of_ergodicAverage_tendsto_const
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hconv : Tendsto
      (fun n ↦ eLpNorm
        (fun x ↦ ergodicAverage M
          (CorrelationMean.indicatorComplex B) n x -
            (realMeasure M B : ℂ))
        2 M.μ)
      Filter.atTop (nhds 0)) :
    cesaroTendsTo (fun n ↦ correlation M A B n)
      (productMeasureValue M A B) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let a := CorrelationMean.indicatorComplex A
  let b := CorrelationMean.indicatorComplex B
  let bstar : M.X → ℂ := fun _ ↦ (realMeasure M B : ℂ)
  have ha2 := CorrelationMean.indicatorComplex_memLp M hM A hA 2
  have hb2 := CorrelationMean.indicatorComplex_memLp M hM B hB 2
  have hbstar2 : MemLp bstar 2 M.μ :=
    MeasureTheory.memLp_const (realMeasure M B : ℂ)
  have hconv' :
      Tendsto
        (fun n ↦ eLpNorm
          (fun x ↦ ergodicAverage M b n x - bstar x)
          2 M.μ)
        Filter.atTop (nhds 0) := by
    simpa [b, bstar] using hconv
  let havg (n : ℕ) :=
    ErgodicAverageLp.ergodicAverage_memLp M hM 2 b hb2 n
  let H (n : ℕ) : Lp ℂ 2 M.μ :=
    (havg n).toLp (ergodicAverage M b n)
  let G : Lp ℂ 2 M.μ := hbstar2.toLp bstar
  let A₂ : Lp ℂ 2 M.μ := ha2.toLp a
  have hHG : Tendsto H Filter.atTop (nhds G) := by
    exact CorrelationMean.tendsto_toLp_of_tendsto_eLpNorm_sub M.μ
      (fun n ↦ ergodicAverage M b n) bstar havg hbstar2 hconv'
  have hinner :
      Tendsto
        (fun n ↦ @inner ℂ (Lp ℂ 2 M.μ) _ A₂ (H n))
        Filter.atTop
        (nhds (@inner ℂ (Lp ℂ 2 M.μ) _ A₂ G)) :=
    tendsto_const_nhds.inner hHG
  have hre := Complex.continuous_re.continuousAt.tendsto.comp
    (hinner.comp (tendsto_add_atTop_nat 1))
  have hinner_avg (n : ℕ) :
      (@inner ℂ (Lp ℂ 2 M.μ) _ A₂ (H n)) =
        ∫ x, ergodicAverage M b n x * star (a x) ∂M.μ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha2.coeFn_toLp, (havg n).coeFn_toLp] with x hax hnx
    rw [RCLike.inner_apply, hax, hnx]
    simp [a]
  have hinner_lim :
      (@inner ℂ (Lp ℂ 2 M.μ) _ A₂ G).re =
        productMeasureValue M A B := by
    rw [MeasureTheory.L2.inner_def]
    have hGcoe := hbstar2.coeFn_toLp
    have heqint :
        (fun x ↦ @inner ℂ ℂ _ (⇑A₂ x) (⇑G x)) =ᵐ[M.μ]
          fun x ↦ (realMeasure M B : ℂ) * a x := by
      filter_upwards [ha2.coeFn_toLp, hGcoe] with x hax hgx
      rw [RCLike.inner_apply, hax, hgx]
      by_cases hxA : x ∈ A <;>
        simp [a, bstar, CorrelationMean.indicatorComplex,
          Set.indicator, hxA]
    rw [integral_congr_ae heqint, integral_const_mul,
      CorrelationMean.integral_indicatorComplex M A hA]
    simp [productMeasureValue, mul_comm]
  unfold cesaroTendsTo seqTendsTo
  convert hre using 1
  · funext N
    rw [CorrelationMean.cesaroCorrelation_eq_re_integral_ergodicAverage
      M hM A B hA hB]
    exact congrArg Complex.re (hinner_avg (N + 1)).symm
  · exact congrArg nhds hinner_lim.symm

/-- A countable set algebra generating the ambient standard Borel
measurable space. -/
def ambientCountableAlgebra
    (M : System.{u}) [StandardBorelSpace M.X] : Set (Set M.X) :=
  MeasureTheory.generateSetAlgebra
    (MeasurableSpace.countableGeneratingSet M.X)

theorem ambientCountableAlgebra_countable
    (M : System.{u}) [StandardBorelSpace M.X] :
    (ambientCountableAlgebra M).Countable := by
  exact MeasureTheory.countable_generateSetAlgebra
    MeasurableSpace.countable_countableGeneratingSet

theorem ambientCountableAlgebra_measurable
    (M : System.{u}) [StandardBorelSpace M.X]
    {A : Set M.X} (hA : A ∈ ambientCountableAlgebra M) :
    MeasurableSet A := by
  induction hA with
  | base A hA =>
      exact MeasurableSpace.measurableSet_countableGeneratingSet hA
  | empty => exact MeasurableSet.empty
  | compl A _ ih => exact ih.compl
  | union A B _ _ ihA ihB => exact ihA.union ihB

theorem ambientCountableAlgebra_isAlgebra
    (M : System.{u}) [StandardBorelSpace M.X] :
    Chapter00.IsAlgebra (ambientCountableAlgebra M) := by
  have hAlg : MeasureTheory.IsSetAlgebra (ambientCountableAlgebra M) := by
    exact MeasureTheory.isSetAlgebra_generateSetAlgebra
  refine ⟨hAlg.empty_mem, ?_, hAlg.compl_mem⟩
  intro E hE F hF
  simpa [Set.diff_eq] using hAlg.inter_mem hE (hAlg.compl_mem hF)

theorem ambientCountableAlgebra_isSemiAlgebra
    (M : System.{u}) [StandardBorelSpace M.X] :
    Chapter00.IsSemiAlgebra (ambientCountableAlgebra M) := by
  have hAlg := ambientCountableAlgebra_isAlgebra M
  constructor
  · refine MeasureTheory.IsSetSemiring.mk hAlg.1 ?_ ?_
    · intro s hs t ht
      have hdiff := hAlg.2.1 s hs tᶜ (hAlg.2.2 t ht)
      convert hdiff using 1
      ext x
      simp
    · intro s hs t ht
      let I : Finset (Set M.X) := {s \ t}
      refine ⟨I, ?_, ?_, ?_⟩
      · intro E hE
        have hEq : E = s \ t := by simpa [I] using hE
        subst E
        exact hAlg.2.1 s hs t ht
      · intro E hEI F hFI hEF
        simp [I] at hEI hFI
        exact (hEF (hEI.trans hFI.symm)).elim
      · simp [I]
  · let B : Fin 1 → Set M.X := fun _ ↦ Set.univ
    refine ⟨1, B, ?_, ?_, ?_⟩
    · intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
    · intro i
      convert hAlg.2.2 ∅ hAlg.1 using 1
      simp [B]
    · ext x
      simp [B]

theorem ambientCountableAlgebra_generates
    (M : System.{u}) [StandardBorelSpace M.X] :
    Chapter00.generatedSigmaAlgebra (ambientCountableAlgebra M) =
      {A : Set M.X | MeasurableSet A} := by
  have hspace :
      MeasurableSpace.generateFrom (ambientCountableAlgebra M) =
        M.measurableSpace := by
    apply le_antisymm
    · apply MeasurableSpace.generateFrom_le
      intro A hA
      exact ambientCountableAlgebra_measurable M hA
    · calc
        M.measurableSpace =
            MeasurableSpace.generateFrom
              (MeasurableSpace.countableGeneratingSet M.X) :=
          MeasurableSpace.generateFrom_countableGeneratingSet.symm
        _ ≤ MeasurableSpace.generateFrom (ambientCountableAlgebra M) :=
          MeasurableSpace.generateFrom_mono
            MeasureTheory.self_subset_generateSetAlgebra
  exact congrArg
    (fun m : MeasurableSpace M.X ↦
      {A : Set M.X | @MeasurableSet M.X m A})
    hspace

/-- For one ambient measurable set `B`, almost every conditional component
has the product correlation limit against every measurable test set `A`. -/
theorem conditionalComponent_cesaroCorrelations_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (hproper : ∀ x ∈ D.fullSet,
      D.measureAt x (invariantCoreAtom M hM x) = 1)
    (hsame : ∀ x ∈ D.fullSet, ∀ y ∈ D.fullSet,
      invariantCoreAtom M hM x = invariantCoreAtom M hM y →
        D.measureAt x = D.measureAt y)
    (B : Set M.X) (hB : MeasurableSet B) :
    ∀ᵐ x ∂M.μ, ∀ A : Set M.X, MeasurableSet A →
      cesaroTendsTo
        (fun n ↦ correlation
          (conditionalComponentSystem M hM D x) A B n)
        (productMeasureValue
          (conditionalComponentSystem M hM D x) A B) := by
  obtain ⟨nseq, hnseq, hpoint⟩ :=
    ergodicAverage_subsequence_tendsto_componentMass_ae
      M hM E D hE hD hproper hsame B hB
  have hmps :=
    conditionalComponentSystem_mps_ae M hM E D hE hD
  filter_upwards [hpoint, hmps] with x hxpoint hxMps
  intro A hA
  let C := conditionalComponentSystem M hM D x
  have hf : C.lpMember 2 (CorrelationMean.indicatorComplex B) :=
    CorrelationMean.indicatorComplex_memLp C hxMps B hB 2
  have hxpoint' :
      ∀ᵐ y ∂C.μ,
        Tendsto
          (fun k ↦ ergodicAverage C
            (CorrelationMean.indicatorComplex B) (nseq k) y)
          Filter.atTop
          (nhds (componentMassComplex M hM D B x)) := by
    simpa [C, conditionalComponentSystem] using hxpoint
  have hconv0 :=
    ergodicAverage_tendsto_const_of_subsequence_ae
      C hxMps (CorrelationMean.indicatorComplex B) hf
      (componentMassComplex M hM D B x) nseq hnseq hxpoint'
  have hconv :
      Tendsto
        (fun n ↦ eLpNorm
          (fun y ↦ ergodicAverage C
            (CorrelationMean.indicatorComplex B) n y -
              (realMeasure C B : ℂ))
          2 C.μ)
        Filter.atTop (nhds 0) := by
    simpa [componentMassComplex, realMeasure, C,
      conditionalComponentSystem] using hconv0
  exact cesaroCorrelations_of_ergodicAverage_tendsto_const
    C hxMps A B hA hB hconv

/-- The product limit for all measurable set correlations implies
ergodicity. -/
theorem isErgodic_of_cesaroCorrelations
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hlim : ∀ A B : Set M.X, MeasurableSet A → MeasurableSet B →
      cesaroTendsTo (fun n ↦ correlation M A B n)
        (productMeasureValue M A B)) :
    IsErgodic M := by
  letI : IsProbabilityMeasure M.μ := hM.1
  refine ⟨hM, ?_⟩
  intro A hA hInv
  have hself :=
    CorrelationMean.cesaroCorrelation_self_of_invariant M hM A hInv
  have hprod := hlim A A hA hA
  have heq : realMeasure M A = productMeasureValue M A A :=
    tendsto_nhds_unique hself hprod
  have hsq :
      (M.μ A).toReal = (M.μ A).toReal * (M.μ A).toReal := by
    simpa [realMeasure, productMeasureValue] using heq
  have hcases : (M.μ A).toReal = 0 ∨ (M.μ A).toReal = 1 := by
    have hnonneg : 0 ≤ (M.μ A).toReal := ENNReal.toReal_nonneg
    by_cases hzero : (M.μ A).toReal = 0
    · exact Or.inl hzero
    · right
      have hpos : 0 < (M.μ A).toReal :=
        lt_of_le_of_ne hnonneg (Ne.symm hzero)
      nlinarith
  rcases hcases with hzero | hone
  · left
    rcases (ENNReal.toReal_eq_zero_iff (M.μ A)).mp hzero with
      hzero | htop
    · exact hzero
    · exact (measure_ne_top M.μ A htop).elim
  · right
    exact (ENNReal.toReal_eq_one_iff (M.μ A)).mp hone

/-- Almost every proper conditional component over the countable invariant
core is ergodic. -/
theorem conditionalComponent_isErgodic_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (hproper : ∀ x ∈ D.fullSet,
      D.measureAt x (invariantCoreAtom M hM x) = 1)
    (hsame : ∀ x ∈ D.fullSet, ∀ y ∈ D.fullSet,
      invariantCoreAtom M hM x = invariantCoreAtom M hM y →
        D.measureAt x = D.measureAt y) :
    ∀ᵐ x ∂M.μ, IsErgodic (conditionalComponentSystem M hM D x) := by
  let S : Set (Set M.X) := ambientCountableAlgebra M
  have hScount : S.Countable := ambientCountableAlgebra_countable M
  letI : Countable S := hScount.to_subtype
  have hEach : ∀ B : S, ∀ᵐ x ∂M.μ,
      ∀ A : Set M.X, MeasurableSet A →
        cesaroTendsTo
          (fun n ↦ correlation
            (conditionalComponentSystem M hM D x) A B.1 n)
          (productMeasureValue
            (conditionalComponentSystem M hM D x) A B.1) := by
    intro B
    exact conditionalComponent_cesaroCorrelations_ae
      M hM E D hE hD hproper hsame B.1
        (ambientCountableAlgebra_measurable M B.2)
  have hAll : ∀ᵐ x ∂M.μ, ∀ B : S,
      ∀ A : Set M.X, MeasurableSet A →
        cesaroTendsTo
          (fun n ↦ correlation
            (conditionalComponentSystem M hM D x) A B.1 n)
          (productMeasureValue
            (conditionalComponentSystem M hM D x) A B.1) :=
    ae_all_iff.mpr hEach
  have hmps :=
    conditionalComponentSystem_mps_ae M hM E D hE hD
  filter_upwards [hAll, hmps] with x hxAll hxMps
  let C := conditionalComponentSystem M hM D x
  have hgen :
      Chapter00.generatedSigmaAlgebra S =
        {A : Set C.X | @MeasurableSet C.X C.measurableSpace A} := by
    simpa [S, C, conditionalComponentSystem] using
      ambientCountableAlgebra_generates M
  have hlimS :
      ∀ A B : Set C.X, A ∈ S → B ∈ S →
        cesaroTendsTo (fun n ↦ correlation C A B n)
          (productMeasureValue C A B) := by
    intro A B hA hB
    exact hxAll ⟨B, hB⟩ A
      (ambientCountableAlgebra_measurable M hA)
  have hlimAlg :=
    CorrelationSemiAlgebra.cesaro_on_generatedAlgebra
      C hxMps S
      (ambientCountableAlgebra_isSemiAlgebra M)
      hgen hlimS
  have hlimAll :=
    CorrelationSemiAlgebra.cesaro_on_all_measurable
      C hxMps S hgen hlimAlg
  exact isErgodic_of_cesaroCorrelations C hxMps hlimAll

/-- The standard conditional-expectation kernel over the full invariant
sigma-algebra agrees almost everywhere with any proper conditional family
over the countable invariant core.  This is the kernel-level bridge needed
to disintegrate the recursively defined relative joining into the ergodic
components constructed above. -/
theorem invariantCondExpKernel_ae_eq_coreConditionalMeasure
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D) :
    ∀ᵐ x ∂M.μ,
      HostKraStandardRelativeJoining.invariantCondExpKernel M hM x =
        D.measureAt x := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let κ :=
    HostKraStandardRelativeJoining.invariantCondExpKernel M hM
  let mInv :=
    MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  have hmInv : mInv ≤ M.measurableSpace := by
    apply MeasurableSpace.generateFrom_le
    intro B hB
    exact hB.1
  letI : IsMarkovKernel κ := by
    dsimp only [κ]
    unfold HostKraStandardRelativeJoining.invariantCondExpKernel
    infer_instance
  have hfull : ∀ᵐ x ∂M.μ, x ∈ D.fullSet := by
    rw [ae_iff]
    change M.μ D.fullSetᶜ = 0
    have hfullMeas : MeasurableSet D.fullSet :=
      invariantCoreSigmaAlgebra_le_ambient M hM hD.1
    have hfullOne : M.μ D.fullSet = 1 := hD.2.1
    letI : IsProbabilityMeasure M.μ := hM.1
    calc
      M.μ D.fullSetᶜ = M.μ Set.univ - M.μ D.fullSet :=
        measure_compl hfullMeas (measure_ne_top M.μ D.fullSet)
      _ = 0 := by rw [hfullOne, measure_univ]; simp
  have hseteq (B : Set M.X)
      (hB : @MeasurableSet M.X M.measurableSpace B) :
      ∀ᵐ x ∂M.μ, κ x B = D.measureAt x B := by
    letI : IsProbabilityMeasure M.μ := hM.1
    let r : M.X → ℝ := HostKraRelativeJoining.indicatorReal B
    let c : M.X → ℂ := CorrelationMean.indicatorComplex B
    have hrint : Integrable r M.μ :=
      (HostKraRelativeJoining.indicatorReal_memLp M hM B hB)
        |>.integrable (by norm_num)
    have hcint : Integrable c M.μ :=
      (CorrelationMean.indicatorComplex_memLp M hM B hB 1)
        |>.integrable (by norm_num)
    have hk :
        (fun x ↦ (κ x B).toReal) =ᵐ[M.μ]
          condExp mInv M.μ r := by
      simpa only [κ, mInv, r, Measure.real_def] using
        (@condExpKernel_ae_eq_condExp M.X mInv M.measurableSpace
          inferInstance M.μ inferInstance hmInv B hB)
    have hcomm :
        Complex.ofRealCLM ∘ condExp mInv M.μ r =ᵐ[M.μ]
          condExp mInv M.μ c := by
      have hraw : Complex.ofRealCLM ∘ r = c := by
        funext x
        by_cases hx : x ∈ B <;>
          simp [r, c, HostKraRelativeJoining.indicatorReal,
            CorrelationMean.indicatorComplex, Set.indicator, hx]
      simpa only [hraw] using
        Complex.ofRealCLM.comp_condExp_comm hrint
    have hcoreFull :
        condExp (invariantCoreMeasurableSpace M hM) M.μ c =ᵐ[M.μ]
          condExp mInv M.μ c := by
      simpa only [mInv] using
        coreCondExp_ae_eq_invariantCondExp M hM c hcint
    have hcoreMass :
        condExp (invariantCoreMeasurableSpace M hM) M.μ c =ᵐ[M.μ]
          componentMassComplex M hM D B :=
      coreCondExp_indicator_ae_eq_componentMass
        M hM E D hE hD B hB
    filter_upwards [hk, hcomm, hcoreFull, hcoreMass, hfull]
      with x hxκ hxcomm hxfullCE hxmass hxDfull
    letI : IsProbabilityMeasure (κ x) := by
      dsimp only [κ]
      infer_instance
    letI : IsProbabilityMeasure (D.measureAt x) :=
      hD.2.2.1 x hxDfull
    have hreal : (κ x B).toReal = (D.measureAt x B).toReal := by
      apply Complex.ofReal_injective
      calc
        ((κ x B).toReal : ℂ) =
            Complex.ofReal (condExp mInv M.μ r x) := by rw [hxκ]
        _ = condExp mInv M.μ c x := hxcomm
        _ = condExp (invariantCoreMeasurableSpace M hM) M.μ c x :=
          hxfullCE.symm
        _ = componentMassComplex M hM D B x := hxmass
        _ = ((D.measureAt x B).toReal : ℂ) := rfl
    exact (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top (κ x) B)
      (measure_ne_top (D.measureAt x) B)).mp hreal
  let S : Set (Set M.X) := ambientCountableAlgebra M
  have hScount : S.Countable :=
    ambientCountableAlgebra_countable M
  have hbasic : ∀ᵐ x ∂M.μ, ∀ s ∈ S,
      κ x s = D.measureAt x s := by
    letI : Countable S := hScount.to_subtype
    have hsubtype : ∀ t : S, ∀ᵐ x ∂M.μ,
        κ x t.1 = D.measureAt x t.1 :=
      fun t ↦ hseteq t.1
        (ambientCountableAlgebra_measurable M t.2)
    have hall : ∀ᵐ x ∂M.μ, ∀ t : S,
        κ x t.1 = D.measureAt x t.1 :=
      ae_all_iff.mpr hsubtype
    filter_upwards [hall] with x hx
    intro s hs
    exact hx ⟨s, hs⟩
  have hgen : M.measurableSpace = MeasurableSpace.generateFrom S := by
    apply MeasurableSpace.ext
    intro A
    have hmem := congrArg (fun F : Set (Set M.X) ↦ A ∈ F)
      (ambientCountableAlgebra_generates M)
    change
      @MeasurableSet M.X M.measurableSpace A ↔
        @MeasurableSet M.X (MeasurableSpace.generateFrom S) A
    exact (Iff.of_eq (by simpa [S, Chapter00.generatedSigmaAlgebra]
      using hmem)).symm
  have hpi : IsPiSystem S := by
    intro A hA B hB _
    have hAlg := ambientCountableAlgebra_isAlgebra M
    have hdiff := hAlg.2.1 A hA Bᶜ (hAlg.2.2 B hB)
    simpa [Set.diff_eq] using hdiff
  letI : MeasurableSpace M.X := M.measurableSpace
  have hallsets : ∀ᵐ x ∂M.μ, ∀ {s : Set M.X},
      @MeasurableSet M.X M.measurableSpace s →
      κ x s = D.measureAt x s := by
    apply MeasurableSpace.ae_induction_on_inter hgen hpi
    · simp
    · exact hbasic
    · filter_upwards [hfull] with x hxfull
      intro s hs heq
      letI : IsProbabilityMeasure (κ x) := by
        dsimp only [κ]
        infer_instance
      letI : IsProbabilityMeasure (D.measureAt x) :=
        hD.2.2.1 x hxfull
      rw [measure_compl (μ := κ x) hs (measure_ne_top _ _),
        measure_compl (μ := D.measureAt x) hs (measure_ne_top _ _), heq,
        measure_univ, measure_univ]
    · filter_upwards [hfull] with x hxfull
      intro f hdisj hfmeas heq
      letI : IsProbabilityMeasure (κ x) := by
        dsimp only [κ]
        infer_instance
      letI : IsProbabilityMeasure (D.measureAt x) :=
        hD.2.2.1 x hxfull
      rw [measure_iUnion (μ := κ x) hdisj hfmeas,
        measure_iUnion (μ := D.measureAt x) hdisj hfmeas]
      congr 1
      funext n
      exact heq n
  filter_upwards [hallsets] with x hx
  change κ x = D.measureAt x
  apply Measure.ext
  intro s hs
  exact hx hs

/-- On a measurable rectangle, the first relative Host--Kra joining is the
ambient mixture of the products of the conditional component measures. -/
theorem relativeJoiningMeasure_apply_prod_eq_lintegral_components
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    HostKraStandardRelativeJoining.relativeJoiningMeasure M hM (A ×ˢ B) =
      ∫⁻ x, D.measureAt x A * D.measureAt x B ∂M.μ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let κ :=
    HostKraStandardRelativeJoining.invariantCondExpKernel M hM
  let mInv :=
    MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  have hmInv : mInv ≤ M.measurableSpace :=
    HostKraRelativeJoining.invariantMeasurableSpace_le M
  have hκA : @Measurable M.X ENNReal mInv inferInstance
      (fun x ↦ κ x A) :=
    Kernel.measurable_coe κ hA
  have hκB : @Measurable M.X ENNReal mInv inferInstance
      (fun x ↦ κ x B) :=
    Kernel.measurable_coe κ hB
  have hκmul : @Measurable M.X ENNReal mInv inferInstance
      (fun x ↦ κ x A * κ x B) :=
    hκA.mul hκB
  rw [HostKraStandardRelativeJoining.relativeJoiningMeasure_apply_prod
    M hM A B hA hB]
  rw [lintegral_trim hmInv hκmul]
  apply lintegral_congr_ae
  filter_upwards [
    invariantCondExpKernel_ae_eq_coreConditionalMeasure
      M hM E D hE hD] with x hx
  rw [show κ x = D.measureAt x by
    simpa only [κ] using hx]
  rfl

/-- The first relative joining mass of a conditional component, with a
harmless zero value on the exceptional components that are not known to be
probability preserving.  Almost every component lies in the first branch. -/
def conditionalComponentRelativeJoiningMass
    (M : System.{u}) [instSB : StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (x : M.X) (s : Set (M.X × M.X)) : ENNReal := by
  let C := conditionalComponentSystem M hM D x
  letI : StandardBorelSpace C.X := by
    change @StandardBorelSpace M.X M.measurableSpace
    exact instSB
  exact if hx : Chapter01.IsMeasurePreservingSystem C then
    HostKraStandardRelativeJoining.relativeJoiningMeasure C hx s
  else 0

/-- The entire first relative Host--Kra joining disintegrates into the first
relative joinings of the almost-everywhere ergodic conditional components.
Unlike the preceding rectangle formula, this holds for every measurable
subset of the product space. -/
theorem relativeJoiningMeasure_apply_eq_lintegral_component_joinings
    (M : System.{u}) [instSB : StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (hproper : ∀ x ∈ D.fullSet,
      D.measureAt x (invariantCoreAtom M hM x) = 1)
    (hsame : ∀ x ∈ D.fullSet, ∀ y ∈ D.fullSet,
      invariantCoreAtom M hM x = invariantCoreAtom M hM y →
        D.measureAt x = D.measureAt y)
    (s : Set (M.X × M.X)) (hs : MeasurableSet s) :
    HostKraStandardRelativeJoining.relativeJoiningMeasure M hM s =
      ∫⁻ x, conditionalComponentRelativeJoiningMass M hM D x s ∂M.μ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : IsMarkovKernel
      (HostKraStandardRelativeJoining.invariantCondExpKernel M hM) := by
    unfold HostKraStandardRelativeJoining.invariantCondExpKernel
    infer_instance
  let κ :=
    HostKraStandardRelativeJoining.invariantCondExpKernel M hM
  let mInv :=
    MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  have hmInv : mInv ≤ M.measurableSpace :=
    HostKraRelativeJoining.invariantMeasurableSpace_le M
  have hκs : @Measurable M.X ENNReal mInv inferInstance
      (fun x ↦ ((Kernel.prod κ κ) x) s) :=
    Kernel.measurable_coe (Kernel.prod κ κ) hs
  rw [HostKraStandardRelativeJoining.relativeJoiningMeasure_apply
    M hM s hs]
  rw [lintegral_trim hmInv hκs]
  apply lintegral_congr_ae
  filter_upwards [
    invariantCondExpKernel_ae_eq_coreConditionalMeasure
      M hM E D hE hD,
    conditionalComponentSystem_mps_ae M hM E D hE hD,
    conditionalComponent_isErgodic_ae
      M hM E D hE hD hproper hsame] with x hxκ hxMps hxErg
  let C := conditionalComponentSystem M hM D x
  letI : StandardBorelSpace C.X := by
    change @StandardBorelSpace M.X M.measurableSpace
    exact instSB
  have hprod :
      (Kernel.prod κ κ) x =
        (D.measureAt x).prod (D.measureAt x) := by
    rw [Kernel.prod_apply, hxκ]
  rw [hprod]
  simp only [conditionalComponentRelativeJoiningMass, dif_pos hxMps]
  rw [HostKraErgodicRelativeJoining.relativeJoiningMeasure_eq_prod_of_ergodic
    (conditionalComponentSystem M hM D x) hxMps hxErg]
  rfl

end Chapter02.HostKraErgodicDecomposition
