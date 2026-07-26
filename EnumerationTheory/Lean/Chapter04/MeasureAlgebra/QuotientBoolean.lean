import Chapter04.Descriptive.StandardBorel
import Mathlib.MeasureTheory.MeasurableSpace.Pi

noncomputable section

open Classical

namespace Chapter04.QuotientBoolean

universe u v

theorem ideal_mono {X : Type u} {I : Set (Set X)} (hI : IsSigmaIdeal I)
    {A B : Set X} (hAB : A ⊆ B) (hB : B ∈ I) : A ∈ I :=
  hI.1.2.1 A B hAB hB

theorem equiv_refl {X : Type u} {I : Set (Set X)} (hI : IsSigmaIdeal I)
    (A : Set X) : quotientEquivalentByIdeal I A A := by
  simpa [quotientEquivalentByIdeal, Chapter00.symmDiff] using hI.1.1

theorem equiv_symm {X : Type u} {I : Set (Set X)} {A B : Set X}
    (h : quotientEquivalentByIdeal I A B) : quotientEquivalentByIdeal I B A := by
  rw [quotientEquivalentByIdeal, show Chapter00.symmDiff B A =
    Chapter00.symmDiff A B by
      ext x
      simp [Chapter00.symmDiff, or_comm]]
  exact h

theorem equiv_trans {X : Type u} {I : Set (Set X)} (hI : IsSigmaIdeal I)
    {A B C : Set X} (hAB : quotientEquivalentByIdeal I A B)
    (hBC : quotientEquivalentByIdeal I B C) : quotientEquivalentByIdeal I A C := by
  apply ideal_mono hI (B := Chapter00.symmDiff A B ∪ Chapter00.symmDiff B C)
  · intro x hx
    simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff] at hx ⊢
    rcases hx with ⟨hxA, hxC⟩ | ⟨hxC, hxA⟩
    · by_cases hxB : x ∈ B
      · exact Or.inr (Or.inl ⟨hxB, hxC⟩)
      · exact Or.inl (Or.inl ⟨hxA, hxB⟩)
    · by_cases hxB : x ∈ B
      · exact Or.inl (Or.inr ⟨hxB, hxA⟩)
      · exact Or.inr (Or.inr ⟨hxC, hxB⟩)
  · exact hI.1.2.2 _ _ hAB hBC

theorem equiv_compl {X : Type u} {I : Set (Set X)} {A B : Set X}
    (h : quotientEquivalentByIdeal I A B) :
    quotientEquivalentByIdeal I Aᶜ Bᶜ := by
  rw [quotientEquivalentByIdeal, show Chapter00.symmDiff Aᶜ Bᶜ =
    Chapter00.symmDiff A B by
      ext x
      simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff,
        Set.mem_compl_iff, not_not]
      constructor
      · rintro (⟨hxA, hxB⟩ | ⟨hxB, hxA⟩)
        · exact Or.inr ⟨hxB, hxA⟩
        · exact Or.inl ⟨hxA, hxB⟩
      · rintro (⟨hxA, hxB⟩ | ⟨hxB, hxA⟩)
        · exact Or.inr ⟨hxB, hxA⟩
        · exact Or.inl ⟨hxA, hxB⟩]
  exact h

theorem equiv_union {X : Type u} {I : Set (Set X)} (hI : IsSigmaIdeal I)
    {A B C D : Set X} (hAC : quotientEquivalentByIdeal I A C)
    (hBD : quotientEquivalentByIdeal I B D) :
    quotientEquivalentByIdeal I (A ∪ B) (C ∪ D) := by
  apply ideal_mono hI
    (B := Chapter00.symmDiff A C ∪ Chapter00.symmDiff B D)
  · intro x hx
    simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff] at hx ⊢
    aesop
  · exact hI.1.2.2 _ _ hAC hBD

theorem equiv_iUnion {X : Type u} {I : Set (Set X)} (hI : IsSigmaIdeal I)
    {A B : ℕ → Set X} (h : ∀ n, quotientEquivalentByIdeal I (A n) (B n)) :
    quotientEquivalentByIdeal I (⋃ n, A n) (⋃ n, B n) := by
  apply ideal_mono hI (B := ⋃ n, Chapter00.symmDiff (A n) (B n))
  · intro x hx
    simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff, Set.mem_iUnion] at hx ⊢
    rcases hx with ⟨⟨n, hAn⟩, hB⟩ | ⟨⟨n, hBn⟩, hA⟩
    · exact ⟨n, Or.inl ⟨hAn, fun hBn => hB ⟨n, hBn⟩⟩⟩
    · exact ⟨n, Or.inr ⟨hBn, fun hAn => hA ⟨n, hAn⟩⟩⟩
  · exact hI.2 _ h

theorem map_empty {M : MeasurableSpaceData.{u}} {N : MeasurableSpaceData.{v}}
    {I : Set (Set M.X)} {J : Set (Set N.X)}
    (hI : IsSigmaIdeal I) {Φ : QuotientBooleanHomData M N I J}
    (hΦ : IsQuotientBooleanHom Φ) :
    quotientEquivalentByIdeal I (Φ.map ∅) ∅ := by
  have hc := hΦ.2.2.2.1 ∅ MeasurableSet.empty
  have hu := hΦ.2.2.1 ∅ Set.univ MeasurableSet.empty MeasurableSet.univ
  have hc' : quotientEquivalentByIdeal I (Φ.map Set.univ) (Φ.map ∅)ᶜ := by
    simpa using hc
  have hu' : quotientEquivalentByIdeal I (Φ.map Set.univ)
      (Φ.map ∅ ∪ Φ.map Set.univ) := by
    simpa using hu
  change Chapter00.symmDiff (Φ.map ∅) ∅ ∈ I
  have hsub : Φ.map ∅ ⊆
      Chapter00.symmDiff (Φ.map Set.univ) (Φ.map ∅)ᶜ ∪
        Chapter00.symmDiff (Φ.map Set.univ) (Φ.map ∅ ∪ Φ.map Set.univ) := by
    intro x hx
    by_cases hu' : x ∈ Φ.map Set.univ
    · left
      exact Or.inl ⟨hu', by simpa using hx⟩
    · right
      exact Or.inr ⟨Or.inl hx, hu'⟩
  have hsmall := hI.1.2.2 _ _ hc' hu'
  simpa [Chapter00.symmDiff] using ideal_mono hI hsub hsmall

theorem map_univ {M : MeasurableSpaceData.{u}} {N : MeasurableSpaceData.{v}}
    {I : Set (Set M.X)} {J : Set (Set N.X)}
    (hI : IsSigmaIdeal I) {Φ : QuotientBooleanHomData M N I J}
    (hΦ : IsQuotientBooleanHom Φ) :
    quotientEquivalentByIdeal I (Φ.map Set.univ) Set.univ := by
  have hc := hΦ.2.2.2.1 ∅ MeasurableSet.empty
  have hc' : quotientEquivalentByIdeal I (Φ.map Set.univ) (Φ.map ∅)ᶜ := by
    simpa using hc
  have h0c := equiv_compl (map_empty hI hΦ)
  exact equiv_trans hI hc' (by simpa using h0c)

/-- A quotient Boolean homomorphism evaluated on the countable Borel code of
the target is represented by a measurable Cantor-valued map. -/
theorem cantor_code_representation
    (M : MeasurableSpaceData.{u}) (N : MeasurableSpaceData.{v})
    (I : Set (Set M.X)) (J : Set (Set N.X))
    (Φ : QuotientBooleanHomData M N I J)
    (hN : IsStandardBorelSpaceData N) (hI : IsSigmaIdeal I)
    (hΦ : IsQuotientBooleanHom Φ) :
    ∃ c : N.X → ℕ → Bool, Measurable c ∧ Function.Injective c ∧
    ∃ d : M.X → ℕ → Bool, Measurable d ∧
      ∀ B : Set (ℕ → Bool), MeasurableSet B →
        quotientEquivalentByIdeal I (d ⁻¹' B)
          (Φ.map (c ⁻¹' B)) := by
  letI : StandardBorelSpace N.X := StandardBorel.instanceOfData N hN
  obtain ⟨c, hc, hcinj⟩ :=
    MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated N.X
  let E : ℕ → Set N.X := fun n => c ⁻¹' {z | z n = true}
  let d : M.X → ℕ → Bool := fun x n => decide (x ∈ Φ.map (E n))
  have hE (n : ℕ) : E n ∈ N.sets := by
    exact ((measurable_pi_apply n).comp hc) (MeasurableSet.singleton true)
  have hd : Measurable d := by
    apply measurable_pi_lambda
    intro n
    apply measurable_to_bool
    have heq : d ⁻¹' {z | z n = true} = Φ.map (E n) := by
      ext x
      simp [d]
    rw [show (fun x => d x n) ⁻¹' {true} = d ⁻¹' {z | z n = true} by rfl, heq]
    exact hΦ.1 (E n) (hE n)
  refine ⟨c, hc, hcinj, d, hd, ?_⟩
  intro B hB
  have hB' : @MeasurableSet (ℕ → Bool) MeasurableSpace.pi B := hB
  rw [MeasurableSpace.pi_eq_generateFrom_projections] at hB'
  refine MeasurableSpace.generateFrom_induction
    {B : Set (ℕ → Bool) |
      ∃ (n : ℕ) (A : Set Bool), MeasurableSet A ∧ (fun z => z n) ⁻¹' A = B}
    (fun C _ => quotientEquivalentByIdeal I (d ⁻¹' C) (Φ.map (c ⁻¹' C)))
    ?_ ?_ ?_ ?_ B hB'
  · rintro C ⟨n, A, hA, rfl⟩ _
    by_cases ht : true ∈ A <;> by_cases hf : false ∈ A
    · have hAu : A = Set.univ := by
        ext b
        cases b <;> simp_all
      subst A
      simpa only [Set.preimage_univ] using equiv_symm (map_univ hI hΦ)
    · have hAt : A = {true} := by
        ext b
        cases b <;> simp_all
      subst A
      have hdEq : d ⁻¹' ((fun z => z n) ⁻¹' ({true} : Set Bool)) = Φ.map (E n) := by
        ext x
        simp [d]
      have hcEq : c ⁻¹' ((fun z => z n) ⁻¹' ({true} : Set Bool)) = E n := by
        rfl
      rw [hdEq, hcEq]
      exact equiv_refl hI (Φ.map (E n))
    · have hAf : A = {false} := by
        ext b
        cases b <;> simp_all
      subst A
      have hcomp := hΦ.2.2.2.1 (E n) (hE n)
      have hdEq : d ⁻¹' ((fun z => z n) ⁻¹' ({false} : Set Bool)) =
          (Φ.map (E n))ᶜ := by
        ext x
        simp [d]
      have hcEq : c ⁻¹' ((fun z => z n) ⁻¹' ({false} : Set Bool)) = (E n)ᶜ := by
        ext x
        simp [E]
      rw [hdEq, hcEq]
      exact equiv_symm hcomp
    · have hAe : A = ∅ := by
        ext b
        cases b <;> simp_all
      subst A
      simpa only [Set.preimage_empty] using equiv_symm (map_empty hI hΦ)
  · simpa only [Set.preimage_empty] using equiv_symm (map_empty hI hΦ)
  · intro C hC hrep
    have hCpi : @MeasurableSet (ℕ → Bool) MeasurableSpace.pi C := by
      rw [MeasurableSpace.pi_eq_generateFrom_projections]
      exact hC
    have hcC : c ⁻¹' C ∈ N.sets := hCpi.preimage hc
    have hcomp := hΦ.2.2.2.1 (c ⁻¹' C) hcC
    have hrep' := equiv_compl hrep
    exact equiv_trans hI (by simpa using hrep') (equiv_symm (by simpa using hcomp))
  · intro C hC hrep
    have hCpi (n : ℕ) : @MeasurableSet (ℕ → Bool) MeasurableSpace.pi (C n) := by
      rw [MeasurableSpace.pi_eq_generateFrom_projections]
      exact hC n
    have hcC (n : ℕ) : c ⁻¹' C n ∈ N.sets := (hCpi n).preimage hc
    have hi := hΦ.2.2.2.2 (fun n => c ⁻¹' C n) hcC
    have hrep' := equiv_iUnion hI hrep
    exact equiv_trans hI (by simpa only [Set.preimage_iUnion] using hrep')
      (equiv_symm (by simpa only [Set.preimage_iUnion] using hi))

/-- Spatial realization of a quotient Boolean sigma-homomorphism.  This is the
Cantor-code proof of Proposition 4.1.14. -/
theorem realized_by_measurable_map
    (M : MeasurableSpaceData.{u}) (N : MeasurableSpaceData.{v})
    (I : Set (Set M.X)) (J : Set (Set N.X))
    (Φ : QuotientBooleanHomData M N I J)
    (hN0 : Nonempty N.X) (hN : IsStandardBorelSpaceData N)
    (hI : IsSigmaIdeal I) (hΦ : IsQuotientBooleanHom Φ) :
    ∃ φ : M.X → N.X, IsMeasurableMap M N φ ∧
      (∀ A ∈ N.sets, quotientEquivalentByIdeal I (φ ⁻¹' A) (Φ.map A)) ∧
      ∀ ψ : M.X → N.X, IsMeasurableMap M N ψ →
        (∀ A ∈ N.sets, quotientEquivalentByIdeal I (ψ ⁻¹' A) (Φ.map A)) →
        {x : M.X | φ x ≠ ψ x} ∈ I := by
  letI : StandardBorelSpace N.X := StandardBorel.instanceOfData N hN
  letI : Nonempty N.X := hN0
  obtain ⟨c, hc, hcinj, d, hd, hrep⟩ :=
    cantor_code_representation M N I J Φ hN hI hΦ
  let emb : MeasurableEmbedding c := hc.measurableEmbedding hcinj
  have hR : MeasurableSet (Set.range c) := emb.measurableSet_range
  let bad : Set M.X := d ⁻¹' (Set.range c)ᶜ
  have hbad : bad ∈ I := by
    have hr := hrep (Set.range c)ᶜ hR.compl
    have hcempty : c ⁻¹' (Set.range c)ᶜ = ∅ := by
      ext y
      simp
    rw [hcempty] at hr
    have hz := equiv_trans hI hr (map_empty hI hΦ)
    simpa [bad, quotientEquivalentByIdeal, Chapter00.symmDiff] using hz
  let φ : M.X → N.X := fun x => emb.invFun (d x)
  have hφmeas : Measurable φ := emb.measurable_invFun.comp hd
  have hφrep : ∀ A ∈ N.sets,
      quotientEquivalentByIdeal I (φ ⁻¹' A) (Φ.map A) := by
    intro A hA
    have hcA : MeasurableSet (c '' A) := emb.measurableSet_image.2 hA
    have hclose : quotientEquivalentByIdeal I (φ ⁻¹' A) (d ⁻¹' (c '' A)) := by
      apply ideal_mono hI (B := bad)
      · intro x hx
        by_contra hxgood
        have hdx : d x ∈ Set.range c := by
          simpa [bad] using hxgood
        have heq : c (φ x) = d x := by
          change c (emb.invFun (d x)) = d x
          rw [MeasurableEmbedding.invFun, dif_pos hdx]
          have hinv := emb.equivRange.apply_symm_apply ⟨d x, hdx⟩
          rw [emb.equivRange_apply] at hinv
          exact congrArg Subtype.val hinv
        simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff,
          Set.mem_preimage, Set.mem_image] at hx
        rcases hx with ⟨hxA, hnot⟩ | ⟨⟨y, hyA, hy⟩, hxA⟩
        · exact hnot ⟨φ x, hxA, heq⟩
        · have : y = φ x := hcinj (hy.trans heq.symm)
          exact hxA (this ▸ hyA)
      · exact hbad
    have hr := hrep (c '' A) hcA
    have hcpre : c ⁻¹' (c '' A) = A := hcinj.preimage_image A
    rw [hcpre] at hr
    exact equiv_trans hI hclose hr
  refine ⟨φ, hφmeas, hφrep, ?_⟩
  intro ψ hψmeas hψrep
  let E : ℕ → Set N.X := fun n => c ⁻¹' {z | z n = true}
  have hE (n : ℕ) : E n ∈ N.sets := by
    exact ((measurable_pi_apply n).comp hc) (MeasurableSet.singleton true)
  have hcoord (n : ℕ) :
      quotientEquivalentByIdeal I (φ ⁻¹' E n) (ψ ⁻¹' E n) :=
    equiv_trans hI (hφrep (E n) (hE n)) (equiv_symm (hψrep (E n) (hE n)))
  apply ideal_mono hI
    (B := ⋃ n, Chapter00.symmDiff (φ ⁻¹' E n) (ψ ⁻¹' E n))
  · intro x hx
    have hcne : c (φ x) ≠ c (ψ x) := fun heq => hx (hcinj heq)
    have hex : ∃ n, c (φ x) n ≠ c (ψ x) n := by
      by_contra hn
      apply hcne
      funext n
      by_contra hne
      exact hn ⟨n, hne⟩
    obtain ⟨n, hn⟩ := hex
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff,
      Set.mem_preimage, E]
    cases hcx : c (φ x) n <;> cases hcy : c (ψ x) n <;> simp_all
  · exact hI.2 _ hcoord

private noncomputable def inverseMap
    {M : MeasurableSpaceData.{u}} {N : MeasurableSpaceData.{v}}
    {I : Set (Set M.X)} {J : Set (Set N.X)}
    (Φ : QuotientBooleanHomData M N I J) (hiso : IsQuotientBooleanIso Φ)
    (C : Set M.X) : Set N.X :=
  if hC : C ∈ M.sets then Classical.choose (hiso.2.2 C hC) else ∅

theorem inverse_hom_of_iso
    (M : MeasurableSpaceData.{u}) (N : MeasurableSpaceData.{v})
    (I : Set (Set M.X)) (J : Set (Set N.X))
    (Φ : QuotientBooleanHomData M N I J)
    (hI : IsSigmaIdeal I) (_hJ : IsSigmaIdeal J)
    (hiso : IsQuotientBooleanIso Φ) :
    ∃ Ψ : QuotientBooleanHomData N M J I,
      IsQuotientBooleanHom Ψ ∧
      (∀ C ∈ M.sets, quotientEquivalentByIdeal I (Φ.map (Ψ.map C)) C) ∧
      ∀ A ∈ N.sets, quotientEquivalentByIdeal J (Ψ.map (Φ.map A)) A := by
  let Ψ : QuotientBooleanHomData N M J I :=
    { map := inverseMap Φ hiso }
  have hspec (C : Set M.X) (hC : C ∈ M.sets) :
      Ψ.map C ∈ N.sets ∧ quotientEquivalentByIdeal I (Φ.map (Ψ.map C)) C := by
    simpa [Ψ, inverseMap, hC] using (Classical.choose_spec (hiso.2.2 C hC))
  have hΨmeas : ∀ C, C ∈ M.sets → Ψ.map C ∈ N.sets := fun C hC => (hspec C hC).1
  have hleft (C : Set M.X) (hC : C ∈ M.sets) := (hspec C hC).2
  have hright (A : Set N.X) (hA : A ∈ N.sets) :
      quotientEquivalentByIdeal J (Ψ.map (Φ.map A)) A := by
    apply hiso.2.1 (Ψ.map (Φ.map A)) A
      (hΨmeas _ (hiso.1.1 A hA)) hA
    exact equiv_trans hI (hleft (Φ.map A) (hiso.1.1 A hA)) (equiv_refl hI (Φ.map A))
  refine ⟨Ψ, ?_, hleft, hright⟩
  refine ⟨hΨmeas, ?_, ?_, ?_, ?_⟩
  · intro C D hC hD hCD
    apply hiso.2.1 (Ψ.map C) (Ψ.map D) (hΨmeas C hC) (hΨmeas D hD)
    exact equiv_trans hI (hleft C hC)
      (equiv_trans hI hCD (equiv_symm (hleft D hD)))
  · intro C D hC hD
    have hCD : C ∪ D ∈ M.sets := hC.union hD
    apply hiso.2.1 (Ψ.map (C ∪ D)) (Ψ.map C ∪ Ψ.map D)
      (hΨmeas _ hCD) ((hΨmeas C hC).union (hΨmeas D hD))
    have hu := hiso.1.2.2.1 (Ψ.map C) (Ψ.map D) (hΨmeas C hC) (hΨmeas D hD)
    have hsides := equiv_union hI (hleft C hC) (hleft D hD)
    exact equiv_trans hI (hleft (C ∪ D) hCD)
      (equiv_trans hI (equiv_symm hsides) (equiv_symm hu))
  · intro C hC
    have hCc : Cᶜ ∈ M.sets := hC.compl
    apply hiso.2.1 (Ψ.map Cᶜ) (Ψ.map C)ᶜ
      (hΨmeas _ hCc) (hΨmeas C hC).compl
    have hc := hiso.1.2.2.2.1 (Ψ.map C) (hΨmeas C hC)
    have hside := equiv_compl (hleft C hC)
    exact equiv_trans hI (hleft Cᶜ hCc)
      (equiv_trans hI (equiv_symm hside) (equiv_symm hc))
  · intro C hC
    have hCu : (⋃ n, C n) ∈ M.sets := MeasurableSet.iUnion hC
    apply hiso.2.1 (Ψ.map (⋃ n, C n)) (⋃ n, Ψ.map (C n))
      (hΨmeas _ hCu) (MeasurableSet.iUnion fun n => hΨmeas (C n) (hC n))
    have hi := hiso.1.2.2.2.2 (fun n => Ψ.map (C n))
      (fun n => hΨmeas (C n) (hC n))
    have hsides := equiv_iUnion hI (fun n => hleft (C n) (hC n))
    exact equiv_trans hI (hleft (⋃ n, C n) hCu)
      (equiv_trans hI (equiv_symm hsides) (equiv_symm hi))

theorem maps_equal_mod_ideal
    (M : MeasurableSpaceData.{u}) (N : MeasurableSpaceData.{v})
    (I : Set (Set M.X)) (hN : IsStandardBorelSpaceData N)
    (hI : IsSigmaIdeal I) (f g : M.X → N.X)
    (_hf : IsMeasurableMap M N f) (_hg : IsMeasurableMap M N g)
    (hpre : ∀ A ∈ N.sets,
      quotientEquivalentByIdeal I (f ⁻¹' A) (g ⁻¹' A)) :
    {x : M.X | f x ≠ g x} ∈ I := by
  letI : StandardBorelSpace N.X := StandardBorel.instanceOfData N hN
  obtain ⟨c, hc, hcinj⟩ :=
    MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated N.X
  let E : ℕ → Set N.X := fun n => c ⁻¹' {z | z n = true}
  have hE (n : ℕ) : E n ∈ N.sets :=
    ((measurable_pi_apply n).comp hc) (MeasurableSet.singleton true)
  apply ideal_mono hI
    (B := ⋃ n, Chapter00.symmDiff (f ⁻¹' E n) (g ⁻¹' E n))
  · intro x hx
    have hcne : c (f x) ≠ c (g x) := fun heq => hx (hcinj heq)
    have hex : ∃ n, c (f x) n ≠ c (g x) n := by
      by_contra hn
      apply hcne
      funext n
      by_contra hne
      exact hn ⟨n, hne⟩
    obtain ⟨n, hn⟩ := hex
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff,
      Set.mem_preimage, E]
    cases hcx : c (f x) n <;> cases hcy : c (g x) n <;> simp_all
  · exact hI.2 _ (fun n => hpre (E n) (hE n))

theorem iso_has_borel_core
    (M : MeasurableSpaceData.{u}) (N : MeasurableSpaceData.{v})
    (I : Set (Set M.X)) (J : Set (Set N.X))
    (Φ : QuotientBooleanHomData M N I J)
    (hM0 : Nonempty M.X) (hN0 : Nonempty N.X)
    (hM : IsStandardBorelSpaceData M) (hN : IsStandardBorelSpaceData N)
    (hI : IsSigmaIdeal I) (hJ : IsSigmaIdeal J)
    (hiso : IsQuotientBooleanIso Φ) :
    ∃ X₀ : Set M.X, ∃ Y₀ : Set N.X,
      MeasurableSet X₀ ∧ MeasurableSet Y₀ ∧ X₀ᶜ ∈ I ∧ Y₀ᶜ ∈ J ∧
      ∃ φ : X₀ → Y₀, ∃ ψ : Y₀ → X₀,
        Function.LeftInverse ψ φ ∧ Function.RightInverse ψ φ ∧
        @Measurable X₀ Y₀
          (MeasurableSpace.comap Subtype.val M.measurableSpace)
          (MeasurableSpace.comap Subtype.val N.measurableSpace) φ ∧
        @Measurable Y₀ X₀
          (MeasurableSpace.comap Subtype.val N.measurableSpace)
          (MeasurableSpace.comap Subtype.val M.measurableSpace) ψ ∧
        (∀ A : Set N.X, A ∈ N.sets →
          (A ∈ J ↔
            Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' (A ∩ Y₀))) ∈ I)) ∧
        ∀ A : Set N.X, A ∈ N.sets →
          quotientEquivalentByIdeal I (Φ.map A)
            (Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' (A ∩ Y₀)))) := by
  letI : StandardBorelSpace M.X := StandardBorel.instanceOfData M hM
  letI : StandardBorelSpace N.X := StandardBorel.instanceOfData N hN
  letI : UpgradedStandardBorel M.X := upgradeStandardBorel M.X
  letI : UpgradedStandardBorel N.X := upgradeStandardBorel N.X
  obtain ⟨Ψ, hΨ, hΦΨ, hΨΦ⟩ := inverse_hom_of_iso M N I J Φ hI hJ hiso
  obtain ⟨φg, hφmeas, hφrep, _hφuniq⟩ :=
    realized_by_measurable_map M N I J Φ hN0 hN hI hiso.1
  obtain ⟨ψg, hψmeas, hψrep, _hψuniq⟩ :=
    realized_by_measurable_map N M J I Ψ hM0 hM hJ hΨ
  have hφmeas' : Measurable φg := hφmeas
  have hψmeas' : Measurable ψg := hψmeas
  have hψφmeas : Measurable (fun x => ψg (φg x)) := hψmeas'.comp hφmeas'
  have hφψmeas : Measurable (fun y => φg (ψg y)) := hφmeas'.comp hψmeas'
  have hψφpre (A : Set M.X) (hA : A ∈ M.sets) :
      quotientEquivalentByIdeal I ((fun x => ψg (φg x)) ⁻¹' A) A := by
    have hψA : ψg ⁻¹' A ∈ N.sets := hA.preimage hψmeas
    have h1 := hφrep (ψg ⁻¹' A) hψA
    have h2 := hiso.1.2.1 (ψg ⁻¹' A) (Ψ.map A) hψA (hΨ.1 A hA) (hψrep A hA)
    exact equiv_trans hI (by simpa [Function.comp_def] using h1)
      (equiv_trans hI h2 (hΦΨ A hA))
  have hφψpre (A : Set N.X) (hA : A ∈ N.sets) :
      quotientEquivalentByIdeal J ((fun y => φg (ψg y)) ⁻¹' A) A := by
    have hφA : φg ⁻¹' A ∈ M.sets := hA.preimage hφmeas
    have h1 := hψrep (φg ⁻¹' A) hφA
    have h2 := hΨ.2.1 (φg ⁻¹' A) (Φ.map A) hφA (hiso.1.1 A hA) (hφrep A hA)
    exact equiv_trans hJ (by simpa [Function.comp_def] using h1)
      (equiv_trans hJ h2 (hΨΦ A hA))
  have hXbad : {x : M.X | ψg (φg x) ≠ x} ∈ I :=
    maps_equal_mod_ideal M M I hM hI _ _ hψφmeas measurable_id
      (fun A hA => by simpa using hψφpre A hA)
  have hYbad : {y : N.X | φg (ψg y) ≠ y} ∈ J :=
    maps_equal_mod_ideal N N J hN hJ _ _ hφψmeas measurable_id
      (fun A hA => by simpa using hφψpre A hA)
  let X₀ : Set M.X := {x | ψg (φg x) = x}
  let Y₀ : Set N.X := {y | φg (ψg y) = y}
  have hX₀ : MeasurableSet X₀ := measurableSet_eq_fun hψφmeas measurable_id
  have hY₀ : MeasurableSet Y₀ := measurableSet_eq_fun hφψmeas measurable_id
  have hXc : X₀ᶜ ∈ I := by simpa [X₀] using hXbad
  have hYc : Y₀ᶜ ∈ J := by simpa [Y₀] using hYbad
  have hφin (x : X₀) : φg x.1 ∈ Y₀ := by
    change φg (ψg (φg x.1)) = φg x.1
    rw [x.2]
  have hψin (y : Y₀) : ψg y.1 ∈ X₀ := by
    change ψg (φg (ψg y.1)) = ψg y.1
    rw [y.2]
  let φ : X₀ → Y₀ := fun x => ⟨φg x.1, hφin x⟩
  let ψ : Y₀ → X₀ := fun y => ⟨ψg y.1, hψin y⟩
  have hleft : Function.LeftInverse ψ φ := by
    intro x
    apply Subtype.ext
    exact x.2
  have hright : Function.RightInverse ψ φ := by
    intro y
    apply Subtype.ext
    exact y.2
  have hφm : Measurable φ := by
    change Measurable (fun x : X₀ => (⟨φg x.1, hφin x⟩ : Y₀))
    exact (hφmeas'.comp measurable_subtype_coe).subtype_mk
  have hψm : Measurable ψ := by
    change Measurable (fun y : Y₀ => (⟨ψg y.1, hψin y⟩ : X₀))
    exact (hψmeas'.comp measurable_subtype_coe).subtype_mk
  have hfinal (A : Set N.X) (hA : A ∈ N.sets) :
      quotientEquivalentByIdeal I (Φ.map A)
        (Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' (A ∩ Y₀)))) := by
    have hrestrict :
      Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' (A ∩ Y₀))) = X₀ ∩ φg ⁻¹' A := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.2, hz.1⟩
      · rintro ⟨hx0, hxA⟩
        exact ⟨⟨x, hx0⟩, ⟨hxA, hφin ⟨x, hx0⟩⟩, rfl⟩
    rw [hrestrict]
    apply equiv_trans hI (equiv_symm (hφrep A hA))
    apply ideal_mono hI (B := X₀ᶜ)
    · intro x hx
      simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff,
        Set.mem_inter_iff, Set.mem_preimage] at hx
      rcases hx with ⟨hxA, hxnot⟩ | ⟨⟨hx0, hxA⟩, hnot⟩
      · exact fun hx0 => hxnot ⟨hx0, hxA⟩
      · exact (hnot hxA).elim
    · exact hXc
  have hideal (A : Set N.X) (hA : A ∈ N.sets) :
      A ∈ J ↔ Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' (A ∩ Y₀))) ∈ I := by
    let R := Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' (A ∩ Y₀)))
    have hFA0 : quotientEquivalentByIdeal I (Φ.map A) ∅ ↔ R ∈ I := by
      constructor
      · intro hzero
        have := equiv_trans hI (equiv_symm (hfinal A hA)) hzero
        simpa [R, quotientEquivalentByIdeal, Chapter00.symmDiff] using this
      · intro hR
        have hR0 : quotientEquivalentByIdeal I R ∅ := by
          simpa [R, quotientEquivalentByIdeal, Chapter00.symmDiff] using hR
        exact equiv_trans hI (hfinal A hA) hR0
    constructor
    · intro hAJ
      have hA0 : quotientEquivalentByIdeal J A ∅ := by
        simpa [quotientEquivalentByIdeal, Chapter00.symmDiff] using hAJ
      have hΦAΦ0 := hiso.1.2.1 A ∅ hA MeasurableSet.empty hA0
      have hΦA0 := equiv_trans hI hΦAΦ0 (map_empty hI hiso.1)
      exact hFA0.mp hΦA0
    · intro hR
      have hΦA0 := hFA0.mpr hR
      have hΦAΦ0 := equiv_trans hI hΦA0 (equiv_symm (map_empty hI hiso.1))
      have hA0 := hiso.2.1 A ∅ hA MeasurableSet.empty hΦAΦ0
      simpa [quotientEquivalentByIdeal, Chapter00.symmDiff] using hA0
  exact ⟨X₀, Y₀, hX₀, hY₀, hXc, hYc, φ, ψ, hleft, hright, hφm, hψm,
    hideal, hfinal⟩

/-- The global measurable realizers used before restricting a quotient Boolean
isomorphism to its Borel bijection core.  Keeping these maps available is useful
when an additional endomorphism has to be intertwined almost everywhere. -/
theorem iso_has_global_realizers
    (M : MeasurableSpaceData.{u}) (N : MeasurableSpaceData.{v})
    (I : Set (Set M.X)) (J : Set (Set N.X))
    (Φ : QuotientBooleanHomData M N I J)
    (hM0 : Nonempty M.X) (hN0 : Nonempty N.X)
    (hM : IsStandardBorelSpaceData M) (hN : IsStandardBorelSpaceData N)
    (hI : IsSigmaIdeal I) (hJ : IsSigmaIdeal J)
    (hiso : IsQuotientBooleanIso Φ) :
    ∃ φ : M.X → N.X, ∃ ψ : N.X → M.X,
      IsMeasurableMap M N φ ∧ IsMeasurableMap N M ψ ∧
      {x : M.X | ψ (φ x) ≠ x} ∈ I ∧
      {y : N.X | φ (ψ y) ≠ y} ∈ J ∧
      ∀ A : Set N.X, A ∈ N.sets →
        quotientEquivalentByIdeal I (φ ⁻¹' A) (Φ.map A) := by
  letI : StandardBorelSpace M.X := StandardBorel.instanceOfData M hM
  letI : StandardBorelSpace N.X := StandardBorel.instanceOfData N hN
  letI : UpgradedStandardBorel M.X := upgradeStandardBorel M.X
  letI : UpgradedStandardBorel N.X := upgradeStandardBorel N.X
  obtain ⟨Ψ, hΨ, hΦΨ, hΨΦ⟩ := inverse_hom_of_iso M N I J Φ hI hJ hiso
  obtain ⟨φ, hφmeas, hφrep, _hφuniq⟩ :=
    realized_by_measurable_map M N I J Φ hN0 hN hI hiso.1
  obtain ⟨ψ, hψmeas, hψrep, _hψuniq⟩ :=
    realized_by_measurable_map N M J I Ψ hM0 hM hJ hΨ
  have hφmeas' : Measurable φ := hφmeas
  have hψmeas' : Measurable ψ := hψmeas
  have hψφmeas : Measurable (fun x => ψ (φ x)) := hψmeas'.comp hφmeas'
  have hφψmeas : Measurable (fun y => φ (ψ y)) := hφmeas'.comp hψmeas'
  have hψφpre (A : Set M.X) (hA : A ∈ M.sets) :
      quotientEquivalentByIdeal I ((fun x => ψ (φ x)) ⁻¹' A) A := by
    have hψA : ψ ⁻¹' A ∈ N.sets := hA.preimage hψmeas
    have h1 := hφrep (ψ ⁻¹' A) hψA
    have h2 := hiso.1.2.1 (ψ ⁻¹' A) (Ψ.map A) hψA (hΨ.1 A hA) (hψrep A hA)
    exact equiv_trans hI (by simpa [Function.comp_def] using h1)
      (equiv_trans hI h2 (hΦΨ A hA))
  have hφψpre (A : Set N.X) (hA : A ∈ N.sets) :
      quotientEquivalentByIdeal J ((fun y => φ (ψ y)) ⁻¹' A) A := by
    have hφA : φ ⁻¹' A ∈ M.sets := hA.preimage hφmeas
    have h1 := hψrep (φ ⁻¹' A) hφA
    have h2 := hΨ.2.1 (φ ⁻¹' A) (Φ.map A) hφA (hiso.1.1 A hA) (hφrep A hA)
    exact equiv_trans hJ (by simpa [Function.comp_def] using h1)
      (equiv_trans hJ h2 (hΨΦ A hA))
  have hXbad : {x : M.X | ψ (φ x) ≠ x} ∈ I :=
    maps_equal_mod_ideal M M I hM hI _ _ hψφmeas measurable_id
      (fun A hA => by simpa using hψφpre A hA)
  have hYbad : {y : N.X | φ (ψ y) ≠ y} ∈ J :=
    maps_equal_mod_ideal N N J hN hJ _ _ hφψmeas measurable_id
      (fun A hA => by simpa using hφψpre A hA)
  exact ⟨φ, ψ, hφmeas, hψmeas, hXbad, hYbad, hφrep⟩

theorem borel_core_gives_iso
    (M : MeasurableSpaceData.{u}) (N : MeasurableSpaceData.{v})
    (I : Set (Set M.X)) (J : Set (Set N.X))
    (Φ : QuotientBooleanHomData M N I J)
    (hI : IsSigmaIdeal I) (hJ : IsSigmaIdeal J)
    (hΦ : IsQuotientBooleanHom Φ)
    {X₀ : Set M.X} {Y₀ : Set N.X}
    (hX₀ : MeasurableSet X₀) (hY₀ : MeasurableSet Y₀)
    (hXc : X₀ᶜ ∈ I) (hYc : Y₀ᶜ ∈ J)
    (φ : X₀ → Y₀) (ψ : Y₀ → X₀)
    (hleft : Function.LeftInverse ψ φ) (hright : Function.RightInverse ψ φ)
    (hφm : @Measurable X₀ Y₀
      (MeasurableSpace.comap Subtype.val M.measurableSpace)
      (MeasurableSpace.comap Subtype.val N.measurableSpace) φ)
    (hψm : @Measurable Y₀ X₀
      (MeasurableSpace.comap Subtype.val N.measurableSpace)
      (MeasurableSpace.comap Subtype.val M.measurableSpace) ψ)
    (hideal : ∀ A : Set N.X, A ∈ N.sets →
      (A ∈ J ↔ Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' (A ∩ Y₀))) ∈ I))
    (hrep : ∀ A : Set N.X, A ∈ N.sets →
      quotientEquivalentByIdeal I (Φ.map A)
        (Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' (A ∩ Y₀))))) :
    IsQuotientBooleanIso Φ := by
  let R : Set N.X → Set M.X := fun A =>
    Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' (A ∩ Y₀)))
  refine ⟨hΦ, ?_, ?_⟩
  · intro A B hA hB hΦAB
    have hRAB : quotientEquivalentByIdeal I (R A) (R B) :=
      equiv_trans hI (equiv_symm (hrep A hA))
        (equiv_trans hI hΦAB (hrep B hB))
    have hsd : Chapter00.symmDiff A B ∈ N.sets :=
      (hA.diff hB).union (hB.diff hA)
    have hReq : R (Chapter00.symmDiff A B) = Chapter00.symmDiff (R A) (R B) := by
      ext x
      simp only [R, Chapter00.symmDiff, Set.mem_image, Set.mem_preimage,
        Set.mem_inter_iff, Set.mem_union, Set.mem_diff]
      constructor
      · rintro ⟨z, ⟨(⟨hzA, hzB⟩ | ⟨hzB, hzA⟩), hzY⟩, rfl⟩
        · left
          refine ⟨⟨z, ⟨hzA, hzY⟩, rfl⟩, ?_⟩
          rintro ⟨w, ⟨hwB, _⟩, hw⟩
          have : w = z := Subtype.ext hw
          exact hzB (this ▸ hwB)
        · right
          refine ⟨⟨z, ⟨hzB, hzY⟩, rfl⟩, ?_⟩
          rintro ⟨w, ⟨hwA, _⟩, hw⟩
          have : w = z := Subtype.ext hw
          exact hzA (this ▸ hwA)
      · rintro (⟨⟨z, ⟨hzA, hzY⟩, rfl⟩, hnot⟩ |
          ⟨⟨z, ⟨hzB, hzY⟩, rfl⟩, hnot⟩)
        · refine ⟨z, ⟨Or.inl ⟨hzA, ?_⟩, hzY⟩, rfl⟩
          intro hzB
          exact hnot ⟨z, ⟨hzB, hzY⟩, rfl⟩
        · refine ⟨z, ⟨Or.inr ⟨hzB, ?_⟩, hzY⟩, rfl⟩
          intro hzA
          exact hnot ⟨z, ⟨hzA, hzY⟩, rfl⟩
    have hRsmall : R (Chapter00.symmDiff A B) ∈ I := by
      rw [hReq]
      exact hRAB
    exact (hideal (Chapter00.symmDiff A B) hsd).2 hRsmall
  · intro C hC
    let S : Set Y₀ := ψ ⁻¹' (Subtype.val ⁻¹' (C ∩ X₀))
    let A : Set N.X := Subtype.val '' S
    have hCX : MeasurableSet (C ∩ X₀) := hC.inter hX₀
    have hS : MeasurableSet S := by
      exact (hCX.preimage measurable_subtype_coe).preimage hψm
    have hA : A ∈ N.sets := hY₀.subtype_image hS
    refine ⟨A, hA, ?_⟩
    have hRA : R A = X₀ ∩ C := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        change (φ z).1 ∈ (Subtype.val '' S) ∩ Y₀ at hz
        rcases hz.1 with ⟨y, hyS, hy⟩
        have hyφ : y = φ z := Subtype.ext hy
        subst y
        change (ψ (φ z)).1 ∈ C ∩ X₀ at hyS
        exact ⟨z.2, by simpa [hleft z] using hyS.1⟩
      · rintro ⟨hx0, hxC⟩
        let z : X₀ := ⟨x, hx0⟩
        refine ⟨z, ?_, rfl⟩
        refine ⟨?_, (φ z).2⟩
        exact ⟨φ z, by
          change (ψ (φ z)).1 ∈ C ∩ X₀
          simpa [hleft z] using hxC, rfl⟩
    have hcore : quotientEquivalentByIdeal I (X₀ ∩ C) C := by
      apply ideal_mono hI (B := X₀ᶜ)
      · intro x hx
        simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff,
          Set.mem_inter_iff] at hx
        rcases hx with ⟨⟨hx0, hxC⟩, hnot⟩ | ⟨hxC, hnot⟩
        · exact (hnot hxC).elim
        · exact fun hx0 => hnot ⟨hx0, hxC⟩
      · exact hXc
    rw [← hRA] at hcore
    exact equiv_trans hI (hrep A hA) hcore

end Chapter04.QuotientBoolean
