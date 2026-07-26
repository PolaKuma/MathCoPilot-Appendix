import Chapter04.Descriptive.CountablyGeneratedModNull
import Chapter04.Descriptive.Invertibility

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter04.CountableCodeFactor

universe u v

/-- A measurable measure-preserving map which intertwines the dynamics almost
everywhere is a factor map in the chapter's invariant-conull-core sense. -/
theorem factorMap_of_ae_intertwining
    (M : System.{u}) (N : System.{v}) (π : M.X → N.X)
    [MeasurableEq N.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (hπ : MeasureTheory.MeasurePreserving π M.μ N.μ)
    (hinter : (fun x => π (M.T x)) =ᵐ[M.μ]
      (fun x => N.T (π x))) :
    Chapter01.IsFactorMap M N π := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  letI : MeasureTheory.IsProbabilityMeasure N.μ := hN.1
  let G : Set M.X := {x | π (M.T x) = N.T (π x)}
  have hGm : MeasurableSet G :=
    measurableSet_eq_fun (hπ.measurable.comp hM.2.measurable)
      (hN.2.measurable.comp hπ.measurable)
  have hGae : ∀ᵐ x ∂M.μ, x ∈ G := hinter
  have hGc0 : M.μ Gᶜ = 0 := MeasureTheory.mem_ae_iff.mp hGae
  let X₀ : Set M.X := {x | ∀ n : ℕ, (M.T^[n]) x ∈ G}
  have hX₀eq : X₀ = ⋂ n : ℕ, (M.T^[n]) ⁻¹' G := by
    ext x
    simp [X₀]
  have hX₀m : MeasurableSet X₀ := by
    rw [hX₀eq]
    exact MeasurableSet.iInter fun n =>
      hGm.preimage (hM.2.measurable.iterate n)
  have hX₀c : X₀ᶜ = ⋃ n : ℕ, (M.T^[n]) ⁻¹' Gᶜ := by
    rw [hX₀eq]
    ext x
    simp
  have hX₀c0 : M.μ X₀ᶜ = 0 := by
    rw [hX₀c]
    apply MeasureTheory.measure_iUnion_null
    intro n
    exact (hM.2.iterate n).measure_preimage hGm.compl.nullMeasurableSet |>.trans hGc0
  have hXfull : M.μ X₀ = 1 := by
    calc
      M.μ X₀ = M.μ Set.univ :=
        MeasureTheory.measure_congr (MeasureTheory.ae_eq_univ.mpr hX₀c0)
      _ = 1 := hM.1.measure_univ
  have hXT (x : M.X) (hx : x ∈ X₀) : M.T x ∈ X₀ := by
    intro n
    simpa [Function.iterate_succ_apply] using hx (n + 1)
  refine ⟨hM, hN, X₀, Set.univ, hXfull, hN.1.measure_univ,
    hXT, (fun y _ => Set.mem_univ (N.T y)), ?_, ?_⟩
  · refine ⟨hX₀m, MeasurableSet.univ, hXfull, hN.1.measure_univ,
      (fun x _ => Set.mem_univ (π x)), ?_⟩
    intro B hB
    constructor
    · simpa only [Set.inter_univ] using hX₀m.inter (hB.preimage hπ.measurable)
    · simp only [Set.inter_univ]
      calc
        M.μ (X₀ ∩ π ⁻¹' B) = M.μ (π ⁻¹' B) := by
          apply MeasureTheory.measure_congr
          filter_upwards [MeasureTheory.ae_eq_univ.mpr hX₀c0] with x hx
          have hx0 : x ∈ X₀ := (Iff.of_eq hx).mpr (Set.mem_univ x)
          apply propext
          constructor
          · exact fun h => h.2
          · exact fun h => ⟨hx0, h⟩
        _ = N.μ B := hπ.measure_preimage hB.nullMeasurableSet
  · intro x hx
    exact hx 0

/-- Membership in a countable family, encoded as a point of Cantor space. -/
def code {X : Type u} (D : ℕ → Set X) (x : X) (n : ℕ) : Bool :=
  decide (x ∈ D n)

/-- A universe-correct standard-Borel carrier for the Cantor code. -/
abbrev CantorTarget : Type u := (ℕ → Bool) × ULift.{u} Unit

def liftedCode {X : Type u} (D : ℕ → Set X) (x : X) : CantorTarget :=
  (code D x, ULift.up ())

def liftedTransform (S : (ℕ → Bool) → (ℕ → Bool)) :
    CantorTarget → CantorTarget :=
  fun y => (S y.1, y.2)

def cantorFactorSystem (M : System.{u}) (D : ℕ → Set M.X)
    (S : (ℕ → Bool) → (ℕ → Bool)) : System.{u} where
  X := CantorTarget
  measurableSpace := inferInstance
  μ := MeasureTheory.Measure.map (liftedCode D) M.μ
  T := liftedTransform S

theorem measurable_liftedCode {X : Type u} [MeasurableSpace X]
    (D : ℕ → Set X)
    (hcode : @Measurable X (ℕ → Bool) inferInstance
      MeasurableSpace.pi (code D)) :
    Measurable (liftedCode D : X → CantorTarget) := by
  exact hcode.prod measurable_const

theorem measurable_liftedTransform
    (S : (ℕ → Bool) → (ℕ → Bool))
    (hS : @Measurable (ℕ → Bool) (ℕ → Bool)
      MeasurableSpace.pi MeasurableSpace.pi S) :
    Measurable (liftedTransform S : CantorTarget → CantorTarget) := by
  exact (hS.comp measurable_fst).prod measurable_snd

theorem cantorFactorSystem_measurePreserving
    (M : System.{u}) (D : ℕ → Set M.X)
    (S : (ℕ → Bool) → (ℕ → Bool))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hcode : @Measurable M.X (ℕ → Bool) M.measurableSpace
      MeasurableSpace.pi (code D))
    (hS : @Measurable (ℕ → Bool) (ℕ → Bool)
      MeasurableSpace.pi MeasurableSpace.pi S)
    (hinter : (fun x => code D (M.T x)) =ᵐ[M.μ]
      (fun x => S (code D x))) :
    Chapter01.IsMeasurePreservingSystem (cantorFactorSystem M D S) := by
  let π : M.X → CantorTarget := liftedCode D
  let R : CantorTarget → CantorTarget := liftedTransform S
  have hπ : Measurable π := measurable_liftedCode D hcode
  have hR : Measurable R := measurable_liftedTransform S hS
  have hinter' : (fun x => π (M.T x)) =ᵐ[M.μ]
      (fun x => R (π x)) := by
    filter_upwards [hinter] with x hx
    exact Prod.ext hx rfl
  constructor
  · apply MeasureTheory.IsProbabilityMeasure.mk
    change (MeasureTheory.Measure.map π M.μ) Set.univ = 1
    rw [MeasureTheory.Measure.map_apply hπ MeasurableSet.univ]
    exact hM.1.measure_univ
  · refine ⟨hR, ?_⟩
    change MeasureTheory.Measure.map R
      (MeasureTheory.Measure.map π M.μ) = MeasureTheory.Measure.map π M.μ
    rw [MeasureTheory.Measure.map_map hR hπ]
    calc
      MeasureTheory.Measure.map (R ∘ π) M.μ =
          MeasureTheory.Measure.map (π ∘ M.T) M.μ :=
        MeasureTheory.Measure.map_congr hinter'.symm
      _ = MeasureTheory.Measure.map π
          (MeasureTheory.Measure.map M.T M.μ) := by
        rw [MeasureTheory.Measure.map_map hπ hM.2.measurable]
      _ = MeasureTheory.Measure.map π M.μ := by rw [hM.2.map_eq]

theorem measurable_code {X : Type u} [MeasurableSpace X]
    (D : ℕ → Set X) (hD : ∀ n, MeasurableSet (D n)) :
    @Measurable X (ℕ → Bool) inferInstance MeasurableSpace.pi (code D) := by
  rw [measurable_pi_iff]
  intro n
  apply measurable_to_bool
  have heq :
      (fun x => decide (x ∈ D n)) ⁻¹' ({true} : Set Bool) = D n := by
    ext x
    simp
  change MeasurableSet
    ((fun x => decide (x ∈ D n)) ⁻¹' ({true} : Set Bool))
  rw [heq]
  exact hD n

/-- Every set in the sigma algebra generated by the coding family is exactly
the pullback of a measurable Cantor-space set. -/
theorem exists_measurableSet_code_preimage {X : Type u}
    (D : ℕ → Set X) (B : Set X)
    (hB : B ∈ Chapter00.generatedSigmaAlgebra (Set.range D)) :
    ∃ C : Set (ℕ → Bool),
      @MeasurableSet (ℕ → Bool) MeasurableSpace.pi C ∧
      B = code D ⁻¹' C := by
  apply MeasurableSpace.generateFrom_induction (Set.range D)
    (fun B _ => ∃ C : Set (ℕ → Bool),
      @MeasurableSet (ℕ → Bool) MeasurableSpace.pi C ∧
      B = code D ⁻¹' C)
  · rintro B ⟨n, rfl⟩ -
    let C : Set (ℕ → Bool) := {y | y n = true}
    refine ⟨C, ?_, ?_⟩
    · dsimp [C]
      measurability
    · ext x
      simp [C, code]
  · exact ⟨∅, MeasurableSet.empty, by simp⟩
  · rintro B - ⟨C, hC, rfl⟩
    exact ⟨Cᶜ, hC.compl, by simp⟩
  · intro B hBgen hBrep
    choose C hC hpre using hBrep
    refine ⟨⋃ n, C n, MeasurableSet.iUnion hC, ?_⟩
    simp only [Set.preimage_iUnion]
    exact congrArg (fun E => ⋃ n, E n) (funext hpre)
  · exact hB

/-- A forward-invariant sub-sigma-algebra admits a Cantor code on which the
ambient dynamics descends almost everywhere.  The code represents every
sub-sigma measurable set modulo null sets, while every target measurable set
pulls back to the original sub-sigma-algebra exactly. -/
theorem exists_cantorCode_dynamics
    (M : System.{u}) (F : SetFamily M.X)
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hLeb : IsLebesgueProbabilitySpace M.toProbabilitySpace)
    (hF : Chapter00.IsSigmaAlgebraFamily F) (hsub : F ⊆ M.𝓧)
    (hInv : ∀ A : Set M.X, A ∈ F → M.T ⁻¹' A ∈ F) :
    ∃ D : ℕ → Set M.X, ∃ S : (ℕ → Bool) → (ℕ → Bool),
      (∀ n, D n ∈ F) ∧
      @Measurable M.X (ℕ → Bool) M.measurableSpace
        MeasurableSpace.pi (code D) ∧
      @Measurable (ℕ → Bool) (ℕ → Bool)
        MeasurableSpace.pi MeasurableSpace.pi S ∧
      (fun x => code D (M.T x)) =ᵐ[M.μ]
        (fun x => S (code D x)) ∧
      (∀ A : Set M.X, A ∈ F →
        ∃ C : Set (ℕ → Bool),
          @MeasurableSet (ℕ → Bool) MeasurableSpace.pi C ∧
          M.μ (Chapter00.symmDiff A (code D ⁻¹' C)) = 0) ∧
      ∀ C : Set (ℕ → Bool),
        @MeasurableSet (ℕ → Bool) MeasurableSpace.pi C →
        code D ⁻¹' C ∈ F := by
  obtain ⟨D, hDF, happrox⟩ :=
    Chapter04.CountablyGeneratedModNull.invariantSubSigma_exists_countable_generator_modNull
      M F hM hLeb hF hsub hInv
  have hDmeas (n : ℕ) : MeasurableSet (D n) := hsub (hDF n)
  choose B hBgen hBzero using fun n =>
    happrox (M.T ⁻¹' D n) (hInv (D n) (hDF n))
  choose C hCmeas hBpre using fun n =>
    exists_measurableSet_code_preimage D (B n) (hBgen n)
  let S : (ℕ → Bool) → (ℕ → Bool) :=
    fun y n => decide (y ∈ C n)
  have hcode :
      @Measurable M.X (ℕ → Bool) M.measurableSpace
        MeasurableSpace.pi (code D) :=
    measurable_code D hDmeas
  have hS :
      @Measurable (ℕ → Bool) (ℕ → Bool)
        MeasurableSpace.pi MeasurableSpace.pi S := by
    rw [measurable_pi_iff]
    intro n
    apply measurable_to_bool
    have heq :
        (fun y => decide (y ∈ C n)) ⁻¹' ({true} : Set Bool) = C n := by
      ext y
      simp
    change @MeasurableSet (ℕ → Bool) MeasurableSpace.pi
      ((fun y => decide (y ∈ C n)) ⁻¹' ({true} : Set Bool))
    rw [heq]
    exact hCmeas n
  have hinter :
      (fun x => code D (M.T x)) =ᵐ[M.μ]
        (fun x => S (code D x)) := by
    have hcoord (n : ℕ) :
        (fun x => code D (M.T x) n) =ᵐ[M.μ]
          (fun x => S (code D x) n) := by
      have hsets :
          M.T ⁻¹' D n =ᵐ[M.μ] B n := by
        apply MeasureTheory.measure_symmDiff_eq_zero_iff.mp
        simpa [Set.symmDiff_def, Chapter00.symmDiff, Set.union_comm] using
          hBzero n
      filter_upwards [hsets] with x hx
      change decide (M.T x ∈ D n) =
        decide (code D x ∈ C n)
      have hxT : M.T x ∈ D n ↔ x ∈ B n := Iff.of_eq hx
      have hxB : x ∈ B n ↔ code D x ∈ C n := by
        rw [hBpre n]
        rfl
      apply Bool.eq_iff_iff.mpr
      simpa using hxT.trans hxB
    filter_upwards [ae_all_iff.2 hcoord] with x hx
    funext n
    exact hx n
  refine ⟨D, S, hDF, hcode, hS, hinter, ?_, ?_⟩
  · intro A hA
    obtain ⟨B', hB'gen, hB'zero⟩ := happrox A hA
    obtain ⟨C', hC'meas, hB'pre⟩ :=
      exists_measurableSet_code_preimage D B' hB'gen
    exact ⟨C', hC'meas, by simpa [hB'pre] using hB'zero⟩
  · intro C' hC'
    have hpreGen :
        code D ⁻¹' C' ∈
          Chapter00.generatedSigmaAlgebra (Set.range D) := by
      change @MeasurableSet M.X
        (MeasurableSpace.generateFrom (Set.range D)) (code D ⁻¹' C')
      have hcodeGen :
          @Measurable M.X (ℕ → Bool)
            (MeasurableSpace.generateFrom (Set.range D))
            MeasurableSpace.pi (code D) := by
        letI : MeasurableSpace M.X :=
          MeasurableSpace.generateFrom (Set.range D)
        exact measurable_code D fun n =>
          MeasurableSpace.measurableSet_generateFrom
            (show D n ∈ Set.range D from ⟨n, rfl⟩)
      exact hcodeGen hC'
    have hle :
        MeasurableSpace.generateFrom (Set.range D) ≤
          InvariantSubSigmaFactor.familyMeasurableSpace F hF := by
      apply MeasurableSpace.generateFrom_le
      rintro A ⟨n, rfl⟩
      exact hDF n
    exact hle _ hpreGen

/-- The source-faithful mod-null form of the invariant-sub-sigma factor
construction.  The target is a Lebesgue (standard-Borel probability) system;
the prescribed family is represented modulo null sets, and all target sets
pull back to it exactly.  Exact strict invariance makes this factor invertible
modulo null sets. -/
theorem exists_lebesgueFactor_of_invariantSubSigma
    (M : System.{u}) (F : SetFamily M.X)
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hLeb : IsLebesgueProbabilitySpace M.toProbabilitySpace)
    (hF : Chapter00.IsSigmaAlgebraFamily F) (hsub : F ⊆ M.𝓧)
    (hInv : ∀ A : Set M.X, A ∈ F → M.T ⁻¹' A ∈ F) :
    ∃ N : System.{u}, ∃ π : M.X → N.X,
      Chapter01.IsFactorMap M N π ∧
      IsLebesgueProbabilitySpace N.toProbabilitySpace ∧
      (∀ A : Set M.X, A ∈ F →
        ∃ B : Set N.X, B ∈ N.𝓧 ∧
          M.μ (Chapter00.symmDiff A (π ⁻¹' B)) = 0) ∧
      (∀ B : Set N.X, B ∈ N.𝓧 → π ⁻¹' B ∈ F) ∧
      ({A : Set M.X | ∃ B ∈ F, A = M.T ⁻¹' B} = F →
        IsInvertibleModNull N) := by
  obtain ⟨D, S, hDF, hcode, hS, hinter, hrep, hpull⟩ :=
    exists_cantorCode_dynamics M F hM hLeb hF hsub hInv
  let π : M.X → CantorTarget := liftedCode D
  let N : System.{u} := cantorFactorSystem M D S
  have hπmeas : Measurable π := measurable_liftedCode D hcode
  have hN : Chapter01.IsMeasurePreservingSystem N :=
    cantorFactorSystem_measurePreserving M D S hM hcode hS hinter
  have hinterLift : (fun x => π (M.T x)) =ᵐ[M.μ]
      (fun x => N.T (π x)) := by
    filter_upwards [hinter] with x hx
    exact Prod.ext hx rfl
  have hπmp : MeasureTheory.MeasurePreserving π M.μ N.μ := by
    refine ⟨hπmeas, ?_⟩
    rfl
  letI : MeasurableEq N.X := by
    dsimp [N, cantorFactorSystem]
    infer_instance
  have hfactor : Chapter01.IsFactorMap M N π :=
    factorMap_of_ae_intertwining M N π hM hN hπmp hinterLift
  have hNstd : IsStandardBorelSpaceData
      { X := N.X, measurableSpace := N.measurableSpace } := by
    have hs : @StandardBorelSpace CantorTarget inferInstance := by
      infer_instance
    refine ⟨CantorTarget, inferInstance, hs, id, id,
      (fun _ => rfl), (fun _ => rfl), ?_, ?_⟩
    · exact measurable_id
    · exact measurable_id
  have hNLeb : IsLebesgueProbabilitySpace N.toProbabilitySpace :=
    ⟨hN.1, hNstd⟩
  have hrepLift : ∀ A : Set M.X, A ∈ F →
      ∃ B : Set N.X, B ∈ N.𝓧 ∧
        M.μ (Chapter00.symmDiff A (π ⁻¹' B)) = 0 := by
    intro A hA
    obtain ⟨C, hC, hzero⟩ := hrep A hA
    let B : Set N.X := C ×ˢ Set.univ
    refine ⟨B, ?_, ?_⟩
    · exact hC.prod MeasurableSet.univ
    · have hpre : π ⁻¹' B = code D ⁻¹' C := by
        ext x
        simp [B, π, liftedCode]
      rw [hpre]
      exact hzero
  have hpullLift : ∀ B : Set N.X, B ∈ N.𝓧 → π ⁻¹' B ∈ F := by
    intro B hB
    let i : (ℕ → Bool) → CantorTarget := fun y => (y, ULift.up ())
    let C : Set (ℕ → Bool) := i ⁻¹' B
    have hi : Measurable i := measurable_id.prod measurable_const
    change @MeasurableSet CantorTarget inferInstance B at hB
    have hC : @MeasurableSet (ℕ → Bool) MeasurableSpace.pi C :=
      hB.preimage hi
    have hpre : π ⁻¹' B = code D ⁻¹' C := by
      rfl
    rw [hpre]
    exact hpull C hC
  refine ⟨N, π, hfactor, hNLeb, hrepLift, hpullLift, ?_⟩
  intro hStrict
  apply Invertibility.invertibleModNull_of_inducedSigmaAlgebraSurjective
    N hN hNLeb
  constructor
  · exact hN.2.measurable
  · intro A hA
    have hpreA : π ⁻¹' A ∈ F := hpullLift A hA
    have hArange : π ⁻¹' A ∈
        {E : Set M.X | ∃ C ∈ F, E = M.T ⁻¹' C} := by
      rw [hStrict]
      exact hpreA
    rcases hArange with ⟨C, hCF, hstrictA⟩
    obtain ⟨B, hB, hCBzero⟩ := hrepLift C hCF
    refine ⟨B, hB, ?_⟩
    have hBmeas : @MeasurableSet CantorTarget inferInstance B := by
      change @MeasurableSet CantorTarget inferInstance B at hB
      exact hB
    have hCB : C =ᵐ[M.μ] π ⁻¹' B :=
      MeasureTheory.measure_symmDiff_eq_zero_iff.mp (by
        simpa [Set.symmDiff_def, Chapter00.symmDiff, Set.union_comm] using hCBzero)
    have hCBT : (fun x => C (M.T x)) =ᵐ[M.μ]
        (fun x => (π ⁻¹' B) (M.T x)) :=
      hM.2.quasiMeasurePreserving.ae hCB
    have hsource : π ⁻¹' (N.T ⁻¹' B) =ᵐ[M.μ] π ⁻¹' A := by
      filter_upwards [hinterLift, hCBT] with x hxinter hxCB
      apply propext
      have h₁ : N.T (π x) ∈ B ↔ π (M.T x) ∈ B := by rw [hxinter]
      have h₂ : π (M.T x) ∈ B ↔ M.T x ∈ C :=
        (Iff.of_eq hxCB).symm
      have h₃ : M.T x ∈ C ↔ π x ∈ A := by
        have hm := Set.ext_iff.mp hstrictA x
        exact hm.symm
      exact h₁.trans (h₂.trans h₃)
    have hsourceZero :
        M.μ (Chapter00.symmDiff (π ⁻¹' (N.T ⁻¹' B)) (π ⁻¹' A)) = 0 := by
      apply MeasureTheory.measure_symmDiff_eq_zero_iff.mpr
      exact hsource
    have hdiffMeas : MeasurableSet
        (Chapter00.symmDiff (N.T ⁻¹' B) A) := by
      exact (hBmeas.preimage hN.2.measurable).diff hA |>.union <|
        hA.diff (hBmeas.preimage hN.2.measurable)
    change N.μ (Chapter00.symmDiff (N.T ⁻¹' B) A) = 0
    change (MeasureTheory.Measure.map π M.μ)
      (Chapter00.symmDiff (N.T ⁻¹' B) A) = 0
    rw [MeasureTheory.Measure.map_apply hπmeas hdiffMeas]
    simpa [Chapter00.symmDiff] using hsourceZero

end Chapter04.CountableCodeFactor
