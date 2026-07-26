import Mathlib

noncomputable section

open Classical Filter

universe u

structure ProbeSystem where
  X : Type u
  measurableSpace : MeasurableSpace X
  μ : MeasureTheory.Measure X
  T : X → X

attribute [instance] ProbeSystem.measurableSpace

def ProbeMPS (M : ProbeSystem.{u}) : Prop :=
  MeasureTheory.IsProbabilityMeasure M.μ ∧
    MeasureTheory.MeasurePreserving M.T M.μ M.μ

def ProbeInvertible (M : ProbeSystem.{u}) : Prop :=
  ∃ S : M.X → M.X, Measurable S ∧
    MeasureTheory.MeasurePreserving S M.μ M.μ ∧
    (fun x => S (M.T x)) =ᵐ[M.μ] id ∧
    (fun x => M.T (S x)) =ᵐ[M.μ] id

def ProbeSurjective (M : ProbeSystem.{u}) : Prop :=
  Measurable M.T ∧ ∀ A : Set M.X, MeasurableSet A →
    ∃ B : Set M.X, MeasurableSet B ∧
      M.μ ((M.T ⁻¹' B \ A) ∪ (A \ M.T ⁻¹' B)) = 0

theorem inducedSigmaAlgebraSurjective_of_invertibleModNull
    (M : ProbeSystem.{u}) (hM : ProbeMPS M)
    (hinv : ProbeInvertible M) : ProbeSurjective M := by
  rcases hinv with ⟨S, hS, hSmp, hST, hTS⟩
  refine ⟨hM.2.measurable, ?_⟩
  intro A hA
  refine ⟨S ⁻¹' A, hA.preimage hS, ?_⟩
  have heq : M.T ⁻¹' (S ⁻¹' A) =ᵐ[M.μ] A := by
    filter_upwards [hST] with x hx
    simpa using congrArg (fun y => y ∈ A) hx
  have hparts := MeasureTheory.ae_eq_set.mp heq
  simp [hparts.1, hparts.2]

theorem invertibleModNull_of_inducedSigmaAlgebraSurjective
    (M : ProbeSystem.{u}) [StandardBorelSpace M.X]
    (hM : ProbeMPS M) (hsurj : ProbeSurjective M) : ProbeInvertible M := by
  rcases hsurj with ⟨hT, hsurj⟩
  obtain ⟨c, hc, hcinj⟩ :=
    MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated M.X
  let A : ℕ → Set M.X := fun n => {x | c x n = true}
  have hA (n : ℕ) : MeasurableSet (A n) := by
    exact ((measurable_pi_apply n).comp hc) (MeasurableSet.singleton true)
  choose B hB hdiff using fun n => hsurj (A n) (hA n)
  let D : ℕ → Set M.X := fun n => (M.T ⁻¹' B n \ A n) ∪ (A n \ M.T ⁻¹' B n)
  have hD (n : ℕ) : MeasurableSet (D n) :=
    ((hB n).preimage hT).diff (hA n) |>.union <| (hA n).diff ((hB n).preimage hT)
  have hD0 (n : ℕ) : M.μ (D n) = 0 := hdiff n
  let X₀ : Set M.X := (⋃ n, D n)ᶜ
  have hX₀ : MeasurableSet X₀ := (MeasurableSet.iUnion hD).compl
  have hX₀c0 : M.μ X₀ᶜ = 0 := by
    simp only [X₀, compl_compl]
    exact MeasureTheory.measure_iUnion_null hD0
  have hX₀ne : X₀.Nonempty := by
    by_contra hne
    have hzero : M.μ Set.univ = 0 := by
      simpa [Set.not_nonempty_iff_eq_empty.mp hne] using hX₀c0
    simpa [hM.1.measure_univ] using hzero
  letI : StandardBorelSpace X₀ := hX₀.standardBorel
  letI : Nonempty X₀ := hX₀ne.to_subtype
  have hTin : Set.InjOn M.T X₀ := by
    intro x hx y hy hxy
    apply hcinj
    funext n
    have hxnot : x ∉ D n := by
      intro hxn
      exact hx (Set.mem_iUnion.2 ⟨n, hxn⟩)
    have hynot : y ∉ D n := by
      intro hyn
      exact hy (Set.mem_iUnion.2 ⟨n, hyn⟩)
    have hxiff : M.T x ∈ B n ↔ x ∈ A n := by
      constructor
      · intro htx
        by_contra hxa
        exact hxnot (Or.inl ⟨htx, hxa⟩)
      · intro hxa
        by_contra htx
        exact hxnot (Or.inr ⟨hxa, htx⟩)
    have hyiff : M.T y ∈ B n ↔ y ∈ A n := by
      constructor
      · intro hty
        by_contra hya
        exact hynot (Or.inl ⟨hty, hya⟩)
      · intro hya
        by_contra hty
        exact hynot (Or.inr ⟨hya, hty⟩)
    have hmem : x ∈ A n ↔ y ∈ A n := by
      rw [← hxiff, ← hyiff, hxy]
    change (c x n = true ↔ c y n = true) at hmem
    change c x n = c y n
    cases hxv : c x n <;> cases hyv : c y n <;> simp_all
  let f : X₀ → M.X := fun x => M.T x
  have hf : Measurable f := hT.comp measurable_subtype_coe
  have hfinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (hTin x.2 y.2 hxy)
  let emb : MeasurableEmbedding f := hf.measurableEmbedding hfinj
  let S : M.X → M.X := fun y => (emb.invFun y).1
  have hS : Measurable S := measurable_subtype_coe.comp emb.measurable_invFun
  have hST : (fun x => S (M.T x)) =ᵐ[M.μ] id := by
    filter_upwards [show ∀ᵐ x ∂M.μ, x ∈ X₀ from MeasureTheory.mem_ae_iff.mpr hX₀c0]
      with x hx
    have hleft := emb.leftInverse_invFun ⟨x, hx⟩
    exact congrArg Subtype.val hleft
  have hrange0 : M.μ (Set.range f)ᶜ = 0 := by
    rw [← hM.2.measure_preimage emb.measurableSet_range.compl.nullMeasurableSet]
    apply MeasureTheory.measure_mono_null (t := X₀ᶜ) ?_ hX₀c0
    intro x hx hx₀
    exact hx ⟨⟨x, hx₀⟩, rfl⟩
  have hTS : (fun x => M.T (S x)) =ᵐ[M.μ] id := by
    filter_upwards [show ∀ᵐ x ∂M.μ, x ∈ Set.range f from
      MeasureTheory.mem_ae_iff.mpr hrange0] with x hx
    change f (emb.invFun x) = x
    rw [MeasurableEmbedding.invFun, dif_pos hx]
    have heq := emb.equivRange.apply_symm_apply ⟨x, hx⟩
    rw [emb.equivRange_apply] at heq
    exact congrArg Subtype.val heq
  have hSmp : MeasureTheory.MeasurePreserving S M.μ M.μ := by
    refine ⟨hS, ?_⟩
    apply MeasureTheory.Measure.ext
    intro E hE
    rw [MeasureTheory.Measure.map_apply hS hE]
    calc
      M.μ (S ⁻¹' E) = M.μ (M.T ⁻¹' (S ⁻¹' E)) :=
        (hM.2.measure_preimage (hE.preimage hS).nullMeasurableSet).symm
      _ = M.μ E := by
        apply MeasureTheory.measure_congr
        filter_upwards [hST] with x hx
        simpa using congrArg (fun y => y ∈ E) hx
  exact ⟨S, hS, hSmp, hST, hTS⟩
