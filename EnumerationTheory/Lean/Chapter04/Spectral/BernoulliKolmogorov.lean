import Chapter04.Common
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.ZeroOne

noncomputable section

open Classical Filter MeasureTheory
open scoped BigOperators

namespace Chapter04.BernoulliKolmogorov

universe u

/-- Generation of sigma algebras respects generator-by-generator equality
modulo a measure. -/
theorem generatedSigmaAlgebra_subset_modulo
    {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (S T : Set (Set X))
    (hgen : ∀ A ∈ S, ∃ B ∈ Chapter00.generatedSigmaAlgebra T,
      μ (Chapter00.symmDiff A B) = 0) :
    ∀ A ∈ Chapter00.generatedSigmaAlgebra S,
      ∃ B ∈ Chapter00.generatedSigmaAlgebra T,
        μ (Chapter00.symmDiff A B) = 0 := by
  intro A hA
  change MeasurableSpace.GenerateMeasurable S A at hA
  induction hA with
  | basic A hAS => exact hgen A hAS
  | empty =>
      refine ⟨∅, ?_, by simp [Chapter00.symmDiff]⟩
      exact @MeasurableSet.empty X (MeasurableSpace.generateFrom T)
  | compl A _ ih =>
      rcases ih with ⟨B, hB, hzero⟩
      refine ⟨Bᶜ, ?_, ?_⟩
      · change @MeasurableSet X (MeasurableSpace.generateFrom T) Bᶜ
        have hB' : @MeasurableSet X (MeasurableSpace.generateFrom T) B := hB
        exact hB'.compl
      apply MeasureTheory.measure_symmDiff_eq_zero_iff.mpr
      have hae :=
        MeasureTheory.measure_symmDiff_eq_zero_iff.mp hzero
      filter_upwards [hae] with x hx
      exact congrArg Not hx
  | iUnion A _ ih =>
      choose B hB hzero using ih
      refine ⟨⋃ n, B n, ?_, ?_⟩
      · change @MeasurableSet X (MeasurableSpace.generateFrom T) (⋃ n, B n)
        exact MeasurableSet.iUnion hB
      apply MeasureTheory.measure_symmDiff_eq_zero_iff.mpr
      have hall : ∀ᵐ x ∂μ, ∀ n, x ∈ A n ↔ x ∈ B n :=
        MeasureTheory.ae_all_iff.mpr fun n => by
          have hn :=
            MeasureTheory.measure_symmDiff_eq_zero_iff.mp (hzero n)
          filter_upwards [hn] with x hx
          exact iff_of_eq hx
      filter_upwards [hall] with x hx
      apply propext
      change x ∈ (⋃ n, A n) ↔ x ∈ (⋃ n, B n)
      simpa only [Set.mem_iUnion] using exists_congr hx

def pullbackSetFamily {X Y : Type*} (e : X → Y)
    (F : Set (Set Y)) : Set (Set X) :=
  {A | ∃ B ∈ F, A = e ⁻¹' B}

theorem pullbackSetFamily_isSigmaAlgebra
    {X Y : Type*} (e : X → Y) (F : Set (Set Y))
    (hF : Chapter00.IsSigmaAlgebraFamily F) :
    Chapter00.IsSigmaAlgebraFamily (pullbackSetFamily e F) := by
  constructor
  · exact ⟨Set.univ, hF.1, by simp⟩
  constructor
  · rintro A ⟨B, hB, rfl⟩
    exact ⟨Bᶜ, hF.2.1 B hB, by simp⟩
  · rintro A hA
    choose B hB hAB using hA
    refine ⟨⋃ n, B n, hF.2.2 B hB, ?_⟩
    rw [show A = fun n => e ⁻¹' B n from funext hAB]
    exact Set.preimage_iUnion.symm

theorem preimage_mem_generatedSigmaAlgebra
    {X Y : Type*} (e : X → Y) (S : Set (Set Y))
    {A : Set Y} (hA : A ∈ Chapter00.generatedSigmaAlgebra S) :
    e ⁻¹' A ∈ Chapter00.generatedSigmaAlgebra
      (pullbackSetFamily e S) := by
  change MeasurableSpace.GenerateMeasurable S A at hA
  induction hA with
  | basic A hAS =>
      exact MeasurableSpace.measurableSet_generateFrom ⟨A, hAS, rfl⟩
  | empty =>
      exact @MeasurableSet.empty X
        (MeasurableSpace.generateFrom (pullbackSetFamily e S))
  | compl A _ ih =>
      have ih' : @MeasurableSet X
          (MeasurableSpace.generateFrom (pullbackSetFamily e S))
          (e ⁻¹' A) := ih
      simpa only [Set.preimage_compl] using ih'.compl
  | iUnion A _ ih =>
      have ih' : ∀ n, @MeasurableSet X
          (MeasurableSpace.generateFrom (pullbackSetFamily e S))
          (e ⁻¹' A n) := ih
      simpa only [Set.preimage_iUnion] using MeasurableSet.iUnion ih'

theorem ae_intertwining_iterate
    {X Y : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) (R : Y → Y) (e : X → Y)
    (hT : MeasurePreserving T μ μ)
    (hinter : (fun x => e (T x)) =ᵐ[μ] fun x => R (e x)) :
    ∀ n : ℕ,
      (fun x => e ((T^[n]) x)) =ᵐ[μ]
        fun x => (R^[n]) (e x) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have ihT := hT.quasiMeasurePreserving.ae_eq_comp ih
      filter_upwards [ihT, hinter] with x hx hi
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact hx.trans (congrArg (R^[n]) hi)

theorem coordinate_iIndepFun
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (ρ : @Measure Ω mΩ) (ν : @Measure (ℤ → Ω) MeasurableSpace.pi)
    (hcyl : ∀ I : Finset ℤ, ∀ C : ℤ → Set Ω,
      (∀ i ∈ I, @MeasurableSet Ω mΩ (C i)) →
      ν {x | ∀ i ∈ I, x i ∈ C i} = ∏ i ∈ I, ρ (C i)) :
    ProbabilityTheory.iIndepFun (fun i : ℤ => fun x : ℤ → Ω => x i) ν := by
  rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro I C hC
  have hleft :
      (⋂ i ∈ I, (fun x : ℤ → Ω => x i) ⁻¹' C i) =
        {x | ∀ i ∈ I, x i ∈ C i} := by
    ext x
    simp
  rw [hleft, hcyl I C hC]
  apply Finset.prod_congr rfl
  intro i hi
  have hsingle := hcyl {i} C (by
    intro j hj
    have hji : j = i := by simpa using hj
    subst j
    exact hC i hi)
  have hset :
      {x : ℤ → Ω | ∀ j ∈ ({i} : Finset ℤ), x j ∈ C j} =
        (fun x : ℤ → Ω => x i) ⁻¹' C i := by
    ext x
    simp
  simpa [hset] using hsingle.symm

def nonnegativeCoordinateSpace
    {Ω : Type u} [MeasurableSpace Ω] (n : ℕ) :
    MeasurableSpace (ℤ → Ω) :=
  MeasurableSpace.comap (fun x : ℤ → Ω => x (n : ℤ)) inferInstance

theorem nonnegativeCoordinateSpace_le
    {Ω : Type u} [MeasurableSpace Ω] (n : ℕ) :
    nonnegativeCoordinateSpace (Ω := Ω) n ≤ MeasurableSpace.pi :=
  (measurable_pi_apply (n : ℤ)).comap_le

def leftShift {Ω : Type u} (x : ℤ → Ω) (i : ℤ) : Ω :=
  x (i + 1)

def rightShift {Ω : Type u} (x : ℤ → Ω) (i : ℤ) : Ω :=
  x (i - 1)

@[simp] theorem leftShift_rightShift {Ω : Type u} (x : ℤ → Ω) :
    leftShift (rightShift x) = x := by
  funext i
  simp [leftShift, rightShift]

@[simp] theorem rightShift_leftShift {Ω : Type u} (x : ℤ → Ω) :
    rightShift (leftShift x) = x := by
  funext i
  simp [leftShift, rightShift]

theorem leftShift_iterate_apply {Ω : Type u}
    (n : ℕ) (x : ℤ → Ω) (i : ℤ) :
    (leftShift^[n]) x i = x (i + n) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      simp [leftShift, add_assoc]

theorem rightShift_iterate_apply {Ω : Type u}
    (n : ℕ) (x : ℤ → Ω) (i : ℤ) :
    (rightShift^[n]) x i = x (i - n) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      change x ((i - (n : ℤ)) - 1) = x (i - ((n + 1 : ℕ) : ℤ))
      push_cast
      congr 1
      omega

theorem leftShift_iterate_rightShift_iterate {Ω : Type u}
    (n : ℕ) (x : ℤ → Ω) :
    (leftShift^[n]) ((rightShift^[n]) x) = x := by
  funext i
  rw [leftShift_iterate_apply, rightShift_iterate_apply]
  simp

theorem rightShift_iterate_leftShift_iterate {Ω : Type u}
    (n : ℕ) (x : ℤ → Ω) :
    (rightShift^[n]) ((leftShift^[n]) x) = x := by
  funext i
  rw [rightShift_iterate_apply, leftShift_iterate_apply]
  simp

def futureSpace {Ω : Type u} [MeasurableSpace Ω] :
    MeasurableSpace (ℤ → Ω) :=
  ⨆ n : ℕ, nonnegativeCoordinateSpace (Ω := Ω) n

def futureSetFamily {Ω : Type u} [MeasurableSpace Ω] :
    Set (Set (ℤ → Ω)) :=
  {A | @MeasurableSet (ℤ → Ω) (futureSpace (Ω := Ω)) A}

def tailSpace {Ω : Type u} [MeasurableSpace Ω] (n : ℕ) :
    MeasurableSpace (ℤ → Ω) :=
  ⨆ k : ℕ, nonnegativeCoordinateSpace (Ω := Ω) (n + k)

theorem futureSpace_le_pi {Ω : Type u} [MeasurableSpace Ω] :
    futureSpace (Ω := Ω) ≤ MeasurableSpace.pi :=
  iSup_le nonnegativeCoordinateSpace_le

theorem futureSetFamily_isSigmaAlgebra
    {Ω : Type u} [MeasurableSpace Ω] :
    Chapter00.IsSigmaAlgebraFamily (futureSetFamily (Ω := Ω)) := by
  constructor
  · change @MeasurableSet (ℤ → Ω) (futureSpace (Ω := Ω)) Set.univ
    exact MeasurableSet.univ
  constructor
  · intro A hA
    change @MeasurableSet (ℤ → Ω) (futureSpace (Ω := Ω)) A at hA
    change @MeasurableSet (ℤ → Ω) (futureSpace (Ω := Ω)) Aᶜ
    exact hA.compl
  · intro A hA
    change ∀ n, @MeasurableSet (ℤ → Ω) (futureSpace (Ω := Ω)) (A n) at hA
    change @MeasurableSet (ℤ → Ω) (futureSpace (Ω := Ω)) (⋃ n, A n)
    exact MeasurableSet.iUnion hA

theorem leftShift_future_measurable
    {Ω : Type u} [MeasurableSpace Ω] :
    @Measurable (ℤ → Ω) (ℤ → Ω)
      (futureSpace (Ω := Ω)) (futureSpace (Ω := Ω))
      leftShift := by
  rw [measurable_iff_comap_le]
  rw [futureSpace, MeasurableSpace.comap_iSup]
  apply iSup_le
  intro n
  rw [nonnegativeCoordinateSpace, MeasurableSpace.comap_comp]
  have hfun :
      (fun x : ℤ → Ω => x (n : ℤ)) ∘ leftShift =
        fun x : ℤ → Ω => x ((n + 1 : ℕ) : ℤ) := by
    funext x
    simp [leftShift]
  rw [hfun]
  exact le_iSup (fun k : ℕ => nonnegativeCoordinateSpace (Ω := Ω) k) (n + 1)

theorem rightShift_measurable
    {Ω : Type u} [MeasurableSpace Ω] :
    @Measurable (ℤ → Ω) (ℤ → Ω) MeasurableSpace.pi MeasurableSpace.pi
      rightShift := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply (i - 1)

theorem leftShift_measurable
    {Ω : Type u} [MeasurableSpace Ω] :
    @Measurable (ℤ → Ω) (ℤ → Ω) MeasurableSpace.pi MeasurableSpace.pi
      leftShift := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply (i + 1)

theorem comap_leftShift_iterate_futureSpace
    {Ω : Type u} [MeasurableSpace Ω] (n : ℕ) :
    MeasurableSpace.comap (leftShift^[n]) (futureSpace (Ω := Ω)) =
      tailSpace (Ω := Ω) n := by
  rw [futureSpace, MeasurableSpace.comap_iSup]
  apply congrArg iSup
  funext k
  rw [nonnegativeCoordinateSpace, MeasurableSpace.comap_comp]
  have hfun :
      (fun x : ℤ → Ω => x (k : ℤ)) ∘ (leftShift^[n]) =
        fun x : ℤ → Ω => x ((n + k : ℕ) : ℤ) := by
    funext x
    rw [Function.comp_apply, leftShift_iterate_apply]
    congr 1
    push_cast
    omega
  rw [hfun]
  rfl

theorem limsup_nonnegativeCoordinateSpace_eq_iInf_tailSpace
    {Ω : Type u} [MeasurableSpace Ω] :
    Filter.limsup (nonnegativeCoordinateSpace (Ω := Ω)) atTop =
      ⨅ n : ℕ, tailSpace (Ω := Ω) n := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  apply congrArg iInf
  funext n
  apply le_antisymm
  · apply iSup_le
    intro i
    apply iSup_le
    intro hi
    rw [tailSpace]
    have hsum : n + (i - n) = i := Nat.add_sub_of_le hi
    rw [← hsum]
    exact le_iSup
      (fun k : ℕ => nonnegativeCoordinateSpace (Ω := Ω) (n + k)) (i - n)
  · rw [tailSpace]
    apply iSup_le
    intro k
    exact le_iSup_of_le (n + k)
      (le_iSup_of_le (Nat.le_add_right n k) le_rfl)

theorem tailSpace_antitone
    {Ω : Type u} [MeasurableSpace Ω] {m n : ℕ} (hmn : m ≤ n) :
    tailSpace (Ω := Ω) n ≤ tailSpace (Ω := Ω) m := by
  rw [tailSpace, tailSpace]
  apply iSup_le
  intro k
  let j := (n - m) + k
  have hindex : m + j = n + k := by
    dsimp [j]
    omega
  rw [← hindex]
  exact le_iSup
    (fun r : ℕ => nonnegativeCoordinateSpace (Ω := Ω) (m + r)) j

theorem futureSetFamily_subset_image_leftShift
    {Ω : Type u} [MeasurableSpace Ω] :
    futureSetFamily (Ω := Ω) ⊆
      imageSetFamily (leftShift (Ω := Ω)) (futureSetFamily (Ω := Ω)) := by
  intro A hA
  let D : Set (ℤ → Ω) := leftShift ⁻¹' A
  have hA' : @MeasurableSet (ℤ → Ω) (futureSpace (Ω := Ω)) A := hA
  have hD : D ∈ futureSetFamily (Ω := Ω) := by
    change @MeasurableSet (ℤ → Ω) (futureSpace (Ω := Ω)) D
    exact hA'.preimage leftShift_future_measurable
  refine ⟨D, hD, ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨rightShift x, ?_, leftShift_rightShift x⟩
    change leftShift (rightShift x) ∈ A
    simpa using hx
  · rintro x ⟨y, hy, rfl⟩
    exact hy

theorem image_leftShift_iterate_eq_preimage_rightShift_iterate
    {Ω : Type u} (n : ℕ) (A : Set (ℤ → Ω)) :
    (leftShift^[n]) '' A = (rightShift^[n]) ⁻¹' A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [rightShift_iterate_leftShift_iterate] using hy
  · intro hx
    refine ⟨(rightShift^[n]) x, hx, ?_⟩
    exact leftShift_iterate_rightShift_iterate n x

theorem backwardTail_member_measurable_limsup
    {Ω : Type u} [MeasurableSpace Ω] {U : Set (ℤ → Ω)}
    (hU : U ∈
      ⋂ n : ℕ,
        preimageSetFamily (leftShift^[n]) (futureSetFamily (Ω := Ω))) :
    @MeasurableSet (ℤ → Ω)
      (Filter.limsup (nonnegativeCoordinateSpace (Ω := Ω)) atTop) U := by
  rw [limsup_nonnegativeCoordinateSpace_eq_iInf_tailSpace,
    MeasurableSpace.measurableSet_iInf]
  intro n
  have hUn := Set.mem_iInter.mp hU n
  rcases hUn with ⟨C, hC, rfl⟩
  rw [← comap_leftShift_iterate_futureSpace]
  exact MeasurableSpace.measurableSet_comap.2 ⟨C, hC, rfl⟩

theorem generated_future_images
    {Ω : Type u} [MeasurableSpace Ω] :
    Chapter00.generatedSigmaAlgebra
        {B : Set (ℤ → Ω) |
          ∃ n : ℕ,
            B ∈ imageSetFamily (leftShift^[n])
              (futureSetFamily (Ω := Ω))} =
      {B : Set (ℤ → Ω) | MeasurableSet B} := by
  let G : Set (Set (ℤ → Ω)) :=
    {B | ∃ n : ℕ,
      B ∈ imageSetFamily (leftShift^[n]) (futureSetFamily (Ω := Ω))}
  have hGmeas : G ⊆ {B : Set (ℤ → Ω) | MeasurableSet B} := by
    intro B hB
    rcases hB with ⟨n, A, hA, rfl⟩
    rw [image_leftShift_iterate_eq_preimage_rightShift_iterate]
    have hApi : MeasurableSet A :=
      futureSpace_le_pi (Ω := Ω) A hA
    exact hApi.preimage (rightShift_measurable.iterate n)
  have hspace :
      MeasurableSpace.generateFrom G = MeasurableSpace.pi := by
    apply le_antisymm
    · exact MeasurableSpace.generateFrom_le hGmeas
    · rw [MeasurableSpace.pi_eq_generateFrom_projections]
      apply MeasurableSpace.generateFrom_le
      rintro B ⟨i, C, hC, rfl⟩
      apply MeasurableSpace.measurableSet_generateFrom
      cases i with
      | ofNat k =>
          refine ⟨0, {x : ℤ → Ω | x (k : ℤ) ∈ C}, ?_, ?_⟩
          · change @MeasurableSet (ℤ → Ω) (futureSpace (Ω := Ω))
              {x | x (k : ℤ) ∈ C}
            exact hC.preimage
              (show @Measurable (ℤ → Ω) Ω
                (futureSpace (Ω := Ω)) inferInstance
                (fun x => x (k : ℤ)) by
                rw [measurable_iff_comap_le]
                exact le_iSup
                  (fun n : ℕ => nonnegativeCoordinateSpace (Ω := Ω) n) k)
          · ext x
            simp
      | negSucc k =>
          let n := k + 1
          let A : Set (ℤ → Ω) := {x | x 0 ∈ C}
          refine ⟨n, A, ?_, ?_⟩
          · change @MeasurableSet (ℤ → Ω) (futureSpace (Ω := Ω)) A
            exact hC.preimage
              (show @Measurable (ℤ → Ω) Ω
                (futureSpace (Ω := Ω)) inferInstance
                (fun x => x 0) by
                rw [measurable_iff_comap_le]
                exact le_iSup
                  (fun m : ℕ => nonnegativeCoordinateSpace (Ω := Ω) m) 0)
          · rw [image_leftShift_iterate_eq_preimage_rightShift_iterate]
            ext x
            change (x (Int.negSucc k) ∈ C ↔
              (rightShift^[k + 1]) x 0 ∈ C)
            rw [rightShift_iterate_apply]
            simp [Int.negSucc_eq]
  ext B
  change @MeasurableSet (ℤ → Ω) (MeasurableSpace.generateFrom G) B ↔
    @MeasurableSet (ℤ → Ω) MeasurableSpace.pi B
  rw [hspace]

theorem nonnegativeCoordinate_iIndep
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (ρ : @Measure Ω mΩ) (ν : @Measure (ℤ → Ω) MeasurableSpace.pi)
    (hcyl : ∀ I : Finset ℤ, ∀ C : ℤ → Set Ω,
      (∀ i ∈ I, @MeasurableSet Ω mΩ (C i)) →
      ν {x | ∀ i ∈ I, x i ∈ C i} = ∏ i ∈ I, ρ (C i)) :
    ProbabilityTheory.iIndep
      (nonnegativeCoordinateSpace (Ω := Ω)) ν := by
  have h :=
    (coordinate_iIndepFun ρ ν hcyl).iIndep
  exact h.precomp Int.ofNat_injective

theorem nonnegativeCoordinate_tail_zero_one
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (ρ : @Measure Ω mΩ) (ν : @Measure (ℤ → Ω) MeasurableSpace.pi)
    (hcyl : ∀ I : Finset ℤ, ∀ C : ℤ → Set Ω,
      (∀ i ∈ I, @MeasurableSet Ω mΩ (C i)) →
      ν {x | ∀ i ∈ I, x i ∈ C i} = ∏ i ∈ I, ρ (C i))
    {A : Set (ℤ → Ω)}
    (hA : MeasurableSet[
      Filter.limsup (nonnegativeCoordinateSpace (Ω := Ω)) atTop] A) :
    ν A = 0 ∨ ν A = 1 := by
  exact ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop
    (fun n => nonnegativeCoordinateSpace_le (Ω := Ω) n)
    (nonnegativeCoordinate_iIndep ρ ν hcyl) hA

theorem tail_modulo_zero_one
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (ρ : @Measure Ω mΩ) (ν : @Measure (ℤ → Ω) MeasurableSpace.pi)
    (hcyl : ∀ I : Finset ℤ, ∀ E : ℤ → Set Ω,
      (∀ i ∈ I, @MeasurableSet Ω mΩ (E i)) →
      ν {x | ∀ i ∈ I, x i ∈ E i} = ∏ i ∈ I, ρ (E i))
    {D : Set (ℤ → Ω)} (C : ℕ → Set (ℤ → Ω))
    (hC : ∀ n, @MeasurableSet (ℤ → Ω) (tailSpace (Ω := Ω) n) (C n))
    (hDC : ∀ n, ν (Chapter00.symmDiff D (C n)) = 0) :
    ν D = 0 ∨ ν D = 1 := by
  let Ctail : Set (ℤ → Ω) := liminf C atTop
  have hcofinal (N : ℕ) :
      Ctail = ⋃ k : ℕ, ⋂ n : ℕ, ⋂ (_ : N + k ≤ n), C n := by
    dsimp [Ctail]
    rw [liminf_eq_iSup_iInf_of_nat]
    ext x
    simp only [Set.iSup_eq_iUnion, Set.iInf_eq_iInter,
      Set.mem_iUnion, Set.mem_iInter]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, fun n hn => hk n (le_trans (Nat.le_add_left k N) hn)⟩
    · rintro ⟨k, hk⟩
      exact ⟨N + k, hk⟩
  have hCtail :
      @MeasurableSet (ℤ → Ω)
        (Filter.limsup (nonnegativeCoordinateSpace (Ω := Ω)) atTop) Ctail := by
    rw [limsup_nonnegativeCoordinateSpace_eq_iInf_tailSpace,
      MeasurableSpace.measurableSet_iInf]
    intro N
    rw [hcofinal N]
    exact MeasurableSet.iUnion fun k =>
      MeasurableSet.iInter fun n =>
        MeasurableSet.iInter fun hn =>
          tailSpace_antitone (Ω := Ω)
            (le_trans (Nat.le_add_right N k) hn) (C n) (hC n)
  have hDCtail : ν (Chapter00.symmDiff D Ctail) = 0 := by
    apply MeasureTheory.measure_symmDiff_eq_zero_iff.mpr
    have hall : ∀ᵐ x ∂ν, ∀ n, D x = C n x :=
      MeasureTheory.ae_all_iff.mpr fun n =>
        MeasureTheory.measure_symmDiff_eq_zero_iff.mp (hDC n)
    filter_upwards [hall] with x hx
    apply propext
    change D x ↔ x ∈ Ctail
    rw [hcofinal 0]
    simp only [Set.iSup_eq_iUnion, Set.iInf_eq_iInter,
      Set.mem_iUnion, Set.mem_iInter]
    constructor
    · intro hxD
      exact ⟨0, fun n _ => (iff_of_eq (hx n).symm).mpr hxD⟩
    · rintro ⟨N, hN⟩
      exact (iff_of_eq (hx N)).mpr (hN N (by omega))
  have hzeroOne :=
    nonnegativeCoordinate_tail_zero_one ρ ν hcyl hCtail
  have hmeasure : ν D = ν Ctail :=
    MeasureTheory.measure_congr
      (MeasureTheory.measure_symmDiff_eq_zero_iff.mp hDCtail)
  rwa [hmeasure]

/-- The coordinate tail sigma algebra is trivial modulo the Bernoulli
measure.  This is the measure-algebra form needed by Definition 4.3.1. -/
theorem nonnegativeCoordinate_tail_equalModulo_trivial
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (ρ : @Measure Ω mΩ) (ν : @Measure (ℤ → Ω) MeasurableSpace.pi)
    [IsProbabilityMeasure ν]
    (hcyl : ∀ I : Finset ℤ, ∀ C : ℤ → Set Ω,
      (∀ i ∈ I, @MeasurableSet Ω mΩ (C i)) →
      ν {x | ∀ i ∈ I, x i ∈ C i} = ∏ i ∈ I, ρ (C i)) :
    (∀ U : Set (ℤ → Ω),
        MeasurableSet[
          Filter.limsup (nonnegativeCoordinateSpace (Ω := Ω)) atTop] U →
        ∃ V ∈ ({∅, Set.univ} : Set (Set (ℤ → Ω))),
          ν (Chapter00.symmDiff U V) = 0) ∧
      ∀ V ∈ ({∅, Set.univ} : Set (Set (ℤ → Ω))),
        ∃ U : Set (ℤ → Ω),
          MeasurableSet[
            Filter.limsup (nonnegativeCoordinateSpace (Ω := Ω)) atTop] U ∧
          ν (Chapter00.symmDiff U V) = 0 := by
  constructor
  · intro U hU
    rcases nonnegativeCoordinate_tail_zero_one ρ ν hcyl hU with h0 | h1
    · refine ⟨∅, by simp, ?_⟩
      simpa [Chapter00.symmDiff] using h0
    · refine ⟨Set.univ, by simp, ?_⟩
      have hUmeas : MeasurableSet U :=
        (Filter.limsup_le_iSup.trans
          (iSup_le (nonnegativeCoordinateSpace_le (Ω := Ω)))) U hU
      have hcompl : ν Uᶜ = 0 := by
        rw [measure_compl hUmeas (measure_ne_top ν U), h1]
        simp
      have hdiff : Chapter00.symmDiff U Set.univ = Uᶜ := by
        ext x
        simp [Chapter00.symmDiff]
      rw [hdiff]
      exact hcompl
  · intro V hV
    rcases hV with (rfl | hV)
    · refine ⟨∅, ?_, by simp [Chapter00.symmDiff]⟩
      exact @MeasurableSet.empty _ 
        (Filter.limsup (nonnegativeCoordinateSpace (Ω := Ω)) atTop)
    · have hVuniv : V = Set.univ := by simpa using hV
      subst V
      refine ⟨Set.univ, ?_, by simp [Chapter00.symmDiff]⟩
      exact @MeasurableSet.univ _
        (Filter.limsup (nonnegativeCoordinateSpace (Ω := Ω)) atTop)

theorem bernoulliData_isKolmogorov
    (M : System.{u})
    (hLeb : IsLebesgueProbabilitySpace M.toProbabilitySpace)
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hinv : IsInvertibleModNull M)
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (ρ : @Measure Ω mΩ) [IsProbabilityMeasure ρ]
    (C₀ : Set Ω) (hC₀ : @MeasurableSet Ω mΩ C₀)
    (hC₀pos : 0 < ρ C₀) (hC₀lt : ρ C₀ < 1)
    (ν : @Measure (ℤ → Ω) MeasurableSpace.pi)
    [IsProbabilityMeasure ν]
    (e : M.X → (ℤ → Ω)) (inv : (ℤ → Ω) → M.X)
    (he : Measurable e) (hinvmeas : Measurable inv)
    (hinv_e : (fun x => inv (e x)) =ᵐ[M.μ] id)
    (_he_inv : (fun x => e (inv x)) =ᵐ[ν] id)
    (hmap : Measure.map e M.μ = ν)
    (hinter :
      (fun x => e (M.T x)) =ᵐ[M.μ] fun x => leftShift (e x))
    (hcyl : ∀ I : Finset ℤ, ∀ E : ℤ → Set Ω,
      (∀ i ∈ I, @MeasurableSet Ω mΩ (E i)) →
      ν {x | ∀ i ∈ I, x i ∈ E i} = ∏ i ∈ I, ρ (E i)) :
    IsKolmogorovSystem M := by
  letI : IsProbabilityMeasure M.μ := hM.1
  rcases hinv with ⟨S, hSmeas, hSmp, hST, hTS⟩
  let A : SetFamily M.X :=
    pullbackSetFamily e (futureSetFamily (Ω := Ω))
  have he_mp : MeasurePreserving e M.μ ν := ⟨he, hmap⟩
  have hmeasure_preimage
      (D : Set (ℤ → Ω)) (hD : MeasurableSet D) :
      M.μ (e ⁻¹' D) = ν D := by
    rw [← Measure.map_apply he hD, hmap]
  have hSinv :
      (fun x => e (S x)) =ᵐ[M.μ] fun x => rightShift (e x) := by
    have hinterS := hSmp.quasiMeasurePreserving.ae_eq_comp hinter
    filter_upwards [hinterS, hTS] with x hx hTx
    have hleft : leftShift (e (S x)) = e x := by
      simp only [Function.comp_apply] at hx
      calc
        leftShift (e (S x)) = e (M.T (S x)) := hx.symm
        _ = e x := congrArg e hTx
    calc
      e (S x) = rightShift (leftShift (e (S x))) :=
        (rightShift_leftShift _).symm
      _ = rightShift (e x) := congrArg rightShift hleft
  have hSiter (n : ℕ) :
      (fun x => e ((S^[n]) x)) =ᵐ[M.μ]
        fun x => (rightShift^[n]) (e x) :=
    ae_intertwining_iterate M.μ S rightShift e hSmp hSinv n
  have hTiter (n : ℕ) :
      (fun x => e ((M.T^[n]) x)) =ᵐ[M.μ]
        fun x => (leftShift^[n]) (e x) :=
    ae_intertwining_iterate M.μ M.T leftShift e hM.2 hinter n
  have hnontrivial :
      ∃ B : Set M.X, MeasurableSet B ∧
        0 < M.μ B ∧ M.μ B < 1 := by
    let D₀ : Set (ℤ → Ω) := {x | x 0 ∈ C₀}
    have hD₀ : MeasurableSet D₀ :=
      hC₀.preimage (measurable_pi_apply 0)
    have hνD₀ : ν D₀ = ρ C₀ := by
      have h := hcyl {0} (fun _ => C₀) (by
        intro i hi
        exact hC₀)
      simpa [D₀] using h
    refine ⟨e ⁻¹' D₀, hD₀.preimage he, ?_, ?_⟩
    · rw [hmeasure_preimage D₀ hD₀, hνD₀]
      exact hC₀pos
    · rw [hmeasure_preimage D₀ hD₀, hνD₀]
      exact hC₀lt
  have hsub : IsSubSigmaAlgebra M A := by
    refine ⟨pullbackSetFamily_isSigmaAlgebra e
      (futureSetFamily (Ω := Ω)) futureSetFamily_isSigmaAlgebra, ?_⟩
    rintro B ⟨D, hD, rfl⟩
    exact (futureSpace_le_pi (Ω := Ω) D hD).preimage he
  have hmono :
      FamilySubsetModuloMeasure M A (preimageSetFamily S A) := by
    rintro B ⟨D, hD, rfl⟩
    rcases futureSetFamily_subset_image_leftShift (Ω := Ω) hD with
      ⟨E, hE, hDE⟩
    have hcanon : D = rightShift ⁻¹' E := by
      calc
        D = leftShift '' E := hDE
        _ = rightShift ⁻¹' E := by
          simpa using
            image_leftShift_iterate_eq_preimage_rightShift_iterate 1 E
    refine ⟨S ⁻¹' (e ⁻¹' E), ⟨e ⁻¹' E, ⟨E, hE, rfl⟩, rfl⟩, ?_⟩
    apply MeasureTheory.measure_symmDiff_eq_zero_iff.mpr
    filter_upwards [hSinv] with x hxi
    change (e x ∈ D) = (e (S x) ∈ E)
    have hmem :
        (e x ∈ D) = (rightShift (e x) ∈ E) := by
      rw [hcanon]
      change (rightShift (e x) ∈ E) = (rightShift (e x) ∈ E)
      rfl
    calc
      (e x ∈ D) = (rightShift (e x) ∈ E) := hmem
      _ = (e (S x) ∈ E) := congrArg (fun y => y ∈ E) hxi.symm
  let Gcanon : Set (Set (ℤ → Ω)) :=
    {B | ∃ n : ℕ,
      B ∈ preimageSetFamily (rightShift^[n])
        (futureSetFamily (Ω := Ω))}
  let GM : Set (Set M.X) :=
    {B | ∃ n : ℕ, B ∈ preimageSetFamily (S^[n]) A}
  have hgenerator :
      ∀ B ∈ pullbackSetFamily e Gcanon,
        ∃ V ∈ Chapter00.generatedSigmaAlgebra GM,
          M.μ (Chapter00.symmDiff B V) = 0 := by
    rintro B ⟨D, ⟨n, E, hE, rfl⟩, rfl⟩
    let V : Set M.X := (S^[n]) ⁻¹' (e ⁻¹' E)
    refine ⟨V, MeasurableSpace.measurableSet_generateFrom
      ⟨n, e ⁻¹' E, ⟨E, hE, rfl⟩, rfl⟩, ?_⟩
    apply MeasureTheory.measure_symmDiff_eq_zero_iff.mpr
    filter_upwards [hSiter n] with x hx
    change ((rightShift^[n]) (e x) ∈ E) =
      (e ((S^[n]) x) ∈ E)
    exact congrArg (fun y => y ∈ E) hx.symm
  have hforward :
      EqualModuloMeasure M (kolmogorovForwardJoin M S A) M.𝓧 := by
    change EqualModuloMeasure M
      (Chapter00.generatedSigmaAlgebra GM) M.𝓧
    constructor
    · intro B hB
      have hGMmeas : GM ⊆ M.𝓧 := by
        rintro V ⟨n, E, ⟨D, hD, rfl⟩, rfl⟩
        exact ((futureSpace_le_pi (Ω := Ω) D hD).preimage he).preimage
          (hSmeas.iterate n)
      exact ⟨B, MeasurableSpace.generateFrom_le hGMmeas B hB,
        by simp [Chapter00.symmDiff]⟩
    · intro B hB
      let D : Set (ℤ → Ω) := inv ⁻¹' B
      have hD : MeasurableSet D := hB.preimage hinvmeas
      have hDgen : D ∈ Chapter00.generatedSigmaAlgebra Gcanon := by
        have hfull := generated_future_images (Ω := Ω)
        have hcanonFamilies :
            Gcanon =
              {Q : Set (ℤ → Ω) |
                ∃ n : ℕ,
                  Q ∈ imageSetFamily (leftShift^[n])
                    (futureSetFamily (Ω := Ω))} := by
          ext Q
          constructor
          · rintro ⟨n, E, hE, rfl⟩
            exact ⟨n, E, hE,
              (image_leftShift_iterate_eq_preimage_rightShift_iterate n E).symm⟩
          · rintro ⟨n, E, hE, rfl⟩
            exact ⟨n, E, hE,
              image_leftShift_iterate_eq_preimage_rightShift_iterate n E⟩
        rw [hcanonFamilies, hfull]
        exact hD
      have heDgen :
          e ⁻¹' D ∈ Chapter00.generatedSigmaAlgebra
            (pullbackSetFamily e Gcanon) :=
        preimage_mem_generatedSigmaAlgebra e Gcanon hDgen
      obtain ⟨V, hV, heDV⟩ :=
        generatedSigmaAlgebra_subset_modulo M.μ
          (pullbackSetFamily e Gcanon) GM hgenerator
          (e ⁻¹' D) heDgen
      refine ⟨V, hV, ?_⟩
      apply MeasureTheory.measure_symmDiff_eq_zero_iff.mpr
      have hBeD : B =ᵐ[M.μ] e ⁻¹' D := by
        filter_upwards [hinv_e] with x hx
        change (x ∈ B) = (inv (e x) ∈ B)
        exact congrArg (fun y => y ∈ B) hx.symm
      exact (hBeD.trans
        (MeasureTheory.measure_symmDiff_eq_zero_iff.mp heDV)).symm
  have htail :
      EqualModuloMeasure M (kolmogorovBackwardTail M A) {∅, Set.univ} := by
    constructor
    · intro B hB
      have hBmeas : MeasurableSet B := by
        have hB0 := Set.mem_iInter.mp hB 0
        rcases hB0 with ⟨E, ⟨D, hD, rfl⟩, rfl⟩
        simpa using (futureSpace_le_pi (Ω := Ω) D hD).preimage he
      let D : Set (ℤ → Ω) := inv ⁻¹' B
      have hD : MeasurableSet D := hBmeas.preimage hinvmeas
      choose E hE hBE using fun n => Set.mem_iInter.mp hB n
      choose C hC hEC using hE
      have hCtail (n : ℕ) :
          @MeasurableSet (ℤ → Ω) (tailSpace (Ω := Ω) n)
            ((leftShift^[n]) ⁻¹' C n) := by
        rw [← comap_leftShift_iterate_futureSpace]
        exact MeasurableSpace.measurableSet_comap.2 ⟨C n, hC n, rfl⟩
      have hDtail (n : ℕ) :
          ν (Chapter00.symmDiff D ((leftShift^[n]) ⁻¹' C n)) = 0 := by
        have hBeD : B =ᵐ[M.μ] e ⁻¹' D := by
          filter_upwards [hinv_e] with x hx
          change (x ∈ B) = (inv (e x) ∈ B)
          exact congrArg (fun y => y ∈ B) hx.symm
        have hBtail :
            B =ᵐ[M.μ] e ⁻¹' ((leftShift^[n]) ⁻¹' C n) := by
          filter_upwards [hTiter n] with x hx
          rw [hBE n, hEC n]
          change (e ((M.T^[n]) x) ∈ C n) =
            ((leftShift^[n]) (e x) ∈ C n)
          exact congrArg (fun y => y ∈ C n) hx
        have hpull :
            M.μ (Chapter00.symmDiff (e ⁻¹' D)
              (e ⁻¹' ((leftShift^[n]) ⁻¹' C n))) = 0 :=
          MeasureTheory.measure_symmDiff_eq_zero_iff.mpr
            (hBeD.symm.trans hBtail)
        have hsymmMeas :
            MeasurableSet
              (Chapter00.symmDiff D ((leftShift^[n]) ⁻¹' C n)) := by
          rw [Chapter00.symmDiff]
          exact (hD.diff
            ((futureSpace_le_pi (Ω := Ω) (C n) (hC n)).preimage
              (leftShift_measurable.iterate n))).union
            (((futureSpace_le_pi (Ω := Ω) (C n) (hC n)).preimage
              (leftShift_measurable.iterate n)).diff hD)
        calc
          ν (Chapter00.symmDiff D ((leftShift^[n]) ⁻¹' C n)) =
              (Measure.map e M.μ)
                (Chapter00.symmDiff D ((leftShift^[n]) ⁻¹' C n)) := by
                rw [hmap]
          _ = M.μ (e ⁻¹'
                (Chapter00.symmDiff D ((leftShift^[n]) ⁻¹' C n))) :=
            Measure.map_apply he hsymmMeas
          _ = 0 := by
            simpa [Chapter00.symmDiff, Set.preimage_diff,
              Set.preimage_union] using hpull
      have hzeroOne := tail_modulo_zero_one ρ ν hcyl
        (fun n => (leftShift^[n]) ⁻¹' C n) hCtail hDtail
      have hBDmeasure : M.μ B = ν D := by
        calc
          M.μ B = M.μ (e ⁻¹' D) := MeasureTheory.measure_congr (by
            filter_upwards [hinv_e] with x hx
            change (x ∈ B) = (inv (e x) ∈ B)
            exact congrArg (fun y => y ∈ B) hx.symm)
          _ = ν D := hmeasure_preimage D hD
      rcases hzeroOne with hzero | hone
      · refine ⟨∅, by simp, ?_⟩
        simpa [Chapter00.symmDiff, hBDmeasure] using hzero
      · refine ⟨Set.univ, by simp, ?_⟩
        have hBcompl : M.μ Bᶜ = 0 := by
          rw [measure_compl hBmeas (measure_ne_top M.μ B), hBDmeasure, hone]
          simp
        have hdiff : Chapter00.symmDiff B Set.univ = Bᶜ := by
          ext x
          simp [Chapter00.symmDiff]
        rwa [hdiff]
    · intro V hV
      have hVcases : V = ∅ ∨ V = Set.univ := by simpa using hV
      refine ⟨V, ?_, by simp [Chapter00.symmDiff]⟩
      rcases hVcases with rfl | rfl
      · apply Set.mem_iInter.2
        intro n
        refine ⟨∅, ⟨∅, ?_, rfl⟩, by simp⟩
        exact @MeasurableSet.empty _ (futureSpace (Ω := Ω))
      · apply Set.mem_iInter.2
        intro n
        refine ⟨Set.univ, ⟨Set.univ, ?_, rfl⟩, by simp⟩
        exact @MeasurableSet.univ _ (futureSpace (Ω := Ω))
  exact ⟨hLeb, hM, ⟨S, hSmeas, hSmp, hST, hTS⟩, hnontrivial,
    S, ⟨hSmeas, hSmp, hST, hTS⟩, A, hsub, hmono, hforward, htail⟩

def shiftSystem {Ω : Type u} [MeasurableSpace Ω]
    (ν : Measure (ℤ → Ω)) : System.{u} where
  X := ℤ → Ω
  measurableSpace := MeasurableSpace.pi
  μ := ν
  T := leftShift

/-- The future-coordinate sigma algebra supplies all four filtration
obligations in the canonical two-sided Bernoulli model. -/
theorem canonical_future_filtration
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (ρ : @Measure Ω mΩ) (ν : @Measure (ℤ → Ω) MeasurableSpace.pi)
    [IsProbabilityMeasure ν]
    (hcyl : ∀ I : Finset ℤ, ∀ C : ℤ → Set Ω,
      (∀ i ∈ I, @MeasurableSet Ω mΩ (C i)) →
      ν {x | ∀ i ∈ I, x i ∈ C i} = ∏ i ∈ I, ρ (C i)) :
    let N := shiftSystem ν
    IsSubSigmaAlgebra N (futureSetFamily (Ω := Ω)) ∧
      FamilySubsetModuloMeasure N (futureSetFamily (Ω := Ω))
        (preimageSetFamily rightShift (futureSetFamily (Ω := Ω))) ∧
      EqualModuloMeasure N
        (kolmogorovForwardJoin N rightShift
          (futureSetFamily (Ω := Ω))) N.𝓧 ∧
      EqualModuloMeasure N
        (kolmogorovBackwardTail N (futureSetFamily (Ω := Ω)))
        {∅, Set.univ} := by
  let N := shiftSystem ν
  have hsub :
      IsSubSigmaAlgebra N (futureSetFamily (Ω := Ω)) := by
    refine ⟨futureSetFamily_isSigmaAlgebra, ?_⟩
    intro A hA
    exact futureSpace_le_pi (Ω := Ω) A hA
  have hmono :
      FamilySubsetModuloMeasure N (futureSetFamily (Ω := Ω))
        (preimageSetFamily rightShift (futureSetFamily (Ω := Ω))) := by
    intro A hA
    have himage :=
      futureSetFamily_subset_image_leftShift (Ω := Ω) hA
    rcases himage with ⟨D, hD, hAD⟩
    refine ⟨A, ⟨D, hD, ?_⟩, ?_⟩
    · calc
        A = leftShift '' D := hAD
        _ = rightShift ⁻¹' D := by
          simpa using
            image_leftShift_iterate_eq_preimage_rightShift_iterate 1 D
    simp [Chapter00.symmDiff]
  have hforward :
      EqualModuloMeasure N
        (kolmogorovForwardJoin N rightShift
          (futureSetFamily (Ω := Ω))) N.𝓧 := by
    have heq :
        kolmogorovForwardJoin N rightShift
          (futureSetFamily (Ω := Ω)) = N.𝓧 := by
      rw [kolmogorovForwardJoin]
      have hfamilies :
          {B : Set (ℤ → Ω) |
            ∃ n : ℕ,
              B ∈ preimageSetFamily (rightShift^[n])
                (futureSetFamily (Ω := Ω))} =
            {B : Set (ℤ → Ω) |
              ∃ n : ℕ,
                B ∈ imageSetFamily (leftShift^[n])
                  (futureSetFamily (Ω := Ω))} := by
        ext B
        constructor
        · rintro ⟨n, D, hD, rfl⟩
          refine ⟨n, D, hD, ?_⟩
          exact (image_leftShift_iterate_eq_preimage_rightShift_iterate n D).symm
        · rintro ⟨n, D, hD, rfl⟩
          refine ⟨n, D, hD, ?_⟩
          exact image_leftShift_iterate_eq_preimage_rightShift_iterate n D
      calc
        Chapter00.generatedSigmaAlgebra
            {B : Set (ℤ → Ω) |
              ∃ n : ℕ,
                B ∈ preimageSetFamily (rightShift^[n])
                  (futureSetFamily (Ω := Ω))} =
            Chapter00.generatedSigmaAlgebra
              {B : Set (ℤ → Ω) |
                ∃ n : ℕ,
                  B ∈ imageSetFamily (leftShift^[n])
                    (futureSetFamily (Ω := Ω))} :=
          congrArg Chapter00.generatedSigmaAlgebra hfamilies
        _ = N.𝓧 := generated_future_images (Ω := Ω)
    rw [heq]
    constructor <;> intro A hA <;>
      exact ⟨A, hA, by simp [Chapter00.symmDiff]⟩
  have htail :
      EqualModuloMeasure N
        (kolmogorovBackwardTail N (futureSetFamily (Ω := Ω)))
        {∅, Set.univ} := by
    constructor
    · intro U hU
      have hUtail :=
        backwardTail_member_measurable_limsup (Ω := Ω) hU
      exact
        (nonnegativeCoordinate_tail_equalModulo_trivial ρ ν hcyl).1 U hUtail
    · intro V hV
      have hVcases : V = ∅ ∨ V = Set.univ := by simpa using hV
      refine ⟨V, ?_, by simp [Chapter00.symmDiff]⟩
      apply Set.mem_iInter.2
      intro n
      refine ⟨V, ?_, ?_⟩
      · rcases hVcases with rfl | rfl
        · exact @MeasurableSet.empty _ (futureSpace (Ω := Ω))
        · exact @MeasurableSet.univ _ (futureSpace (Ω := Ω))
      · rcases hVcases with rfl | rfl <;> simp
  exact ⟨hsub, hmono, hforward, htail⟩

end Chapter04.BernoulliKolmogorov
