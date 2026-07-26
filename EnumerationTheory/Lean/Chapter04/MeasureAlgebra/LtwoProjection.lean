import Chapter04.MeasureAlgebra.InducedMeasureAlgebra

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter04.LtwoProjection

universe u v

def indicatorOne {X : Type u} (A : Set X) : X → ℂ :=
  A.indicator fun _ => 1

def partialUnion {X : Type u} (f : ℕ → Set X) : ℕ → Set X
  | 0 => f 0
  | n + 1 => partialUnion f n ∪ f (n + 1)

theorem partialUnion_measurable {X : Type u} [MeasurableSpace X]
    (f : ℕ → Set X) (hf : ∀ n, MeasurableSet (f n)) :
    ∀ n, MeasurableSet (partialUnion f n)
  | 0 => hf 0
  | n + 1 => (partialUnion_measurable f hf n).union (hf (n + 1))

theorem partialUnion_mono {X : Type u} (f : ℕ → Set X) :
    Monotone (partialUnion f) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Set.subset_union_left

theorem subset_partialUnion {X : Type u} (f : ℕ → Set X) (n : ℕ) :
    f n ⊆ partialUnion f n := by
  cases n with
  | zero => exact Set.Subset.rfl
  | succ n => exact Set.subset_union_right

theorem iUnion_partialUnion {X : Type u} (f : ℕ → Set X) :
    (⋃ n, partialUnion f n) = ⋃ n, f n := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
    induction n with
    | zero =>
        exact Set.mem_iUnion_of_mem 0 hxn
    | succ n ih =>
        rcases hxn with hxn | hxn
        · exact ih hxn
        · exact Set.mem_iUnion_of_mem (n + 1) hxn
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
    exact Set.mem_iUnion_of_mem n (subset_partialUnion f n hxn)

noncomputable def partialCarrier
    (P : ProbabilitySpace.{u})
    (f : ℕ → (inducedMeasureAlgebra P).carrier) (n : ℕ) :
    (inducedMeasureAlgebra P).carrier :=
  ⟨partialUnion (fun k => (f k).1) n,
    partialUnion_measurable (fun k => (f k).1) (fun k => (f k).2) n⟩

theorem indicatorOne_memLp
    (P : ProbabilitySpace.{u}) (hP : Chapter01.IsProbabilitySpace P)
    {A : Set P.X} (hA : MeasurableSet A) (p : ENNReal) :
    MemLp (indicatorOne A) p P.μ := by
  letI : IsProbabilityMeasure P.μ := hP
  apply memLp_indicator_const p hA 1
  right
  exact (measure_ne_top P.μ A)

/-- A unital multiplicative L² algebra unitary sends every measurable
indicator to a measurable indicator, modulo null sets. -/
theorem image_indicator
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hQ : Chapter01.IsProbabilitySpace Q)
    (W : (Q.X → ℂ) → (P.X → ℂ))
    (hW : IsLtwoAlgebraUnitaryFor P Q W)
    {B : Set Q.X} (hB : MeasurableSet B) :
    ∃ C : Set P.X, MeasurableSet C ∧
      W (indicatorOne B) =ᵐ[P.μ] indicatorOne C := by
  rcases hW with
    ⟨hae, _hadd, _hsmul, hL2, _hdense, _hLinf, _hLinfSurj, _hone, hmul⟩
  let e : Q.X → ℂ := indicatorOne B
  have he2 : (fun y => e y * e y) = e := by
    funext y
    by_cases hy : y ∈ B <;> simp [e, indicatorOne, hy]
  have heTop : MemLp e ⊤ Q.μ := indicatorOne_memLp Q hQ hB ⊤
  have heTwo : MemLp e 2 Q.μ := indicatorOne_memLp Q hQ hB 2
  have hWe : MemLp (W e) 2 P.μ := (hL2 e heTwo).1
  let r : P.X → ℂ := hWe.aestronglyMeasurable.mk (W e)
  have hrm : Measurable r := hWe.aestronglyMeasurable.measurable_mk
  have hWer : W e =ᵐ[P.μ] r := hWe.aestronglyMeasurable.ae_eq_mk
  have hmul' : W (fun y => e y * e y) =ᵐ[P.μ]
      fun x => W e x * W e x := hmul e e heTop heTop
  have hsame : W (fun y => e y * e y) =ᵐ[P.μ] W e := by
    exact Filter.Eventually.of_forall fun x => by rw [he2]
  have hidemW : (fun x => W e x * W e x) =ᵐ[P.μ] W e :=
    hmul'.symm.trans hsame
  have hidemR : (fun x => r x * r x) =ᵐ[P.μ] r := by
    filter_upwards [hWer, hidemW] with x hxr hxidem
    rw [← hxr]
    exact hxidem
  let C : Set P.X := {x | r x = 1}
  have hC : MeasurableSet C :=
    measurableSet_eq_fun hrm measurable_const
  refine ⟨C, hC, ?_⟩
  filter_upwards [hWer, hidemR] with x hxr hxidem
  rw [hxr]
  change r x = C.indicator (fun _ => (1 : ℂ)) x
  have hzero_or_one : r x = 0 ∨ r x = 1 := by
    have hfactor : r x * (r x - 1) = 0 := by
      calc
        r x * (r x - 1) = r x * r x - r x := by ring
        _ = 0 := sub_eq_zero.mpr hxidem
    rcases mul_eq_zero.mp hfactor with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr (sub_eq_zero.mp hone)
  rcases hzero_or_one with hzero | hone
  · have hxnot : x ∉ C := by
      intro hx
      exact zero_ne_one (hzero.symm.trans hx)
    simp [Set.indicator_of_notMem hxnot, hzero]
  · have hxmem : x ∈ C := hone
    simp [Set.indicator_of_mem hxmem, hone]

noncomputable def indicatorImage
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hQ : Chapter01.IsProbabilitySpace Q)
    (W : (Q.X → ℂ) → (P.X → ℂ))
    (hW : IsLtwoAlgebraUnitaryFor P Q W)
    (B : (inducedMeasureAlgebra Q).carrier) :
    (inducedMeasureAlgebra P).carrier :=
  ⟨Classical.choose (image_indicator P Q hQ W hW B.2),
    (Classical.choose_spec (image_indicator P Q hQ W hW B.2)).1⟩

theorem indicatorImage_spec
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hQ : Chapter01.IsProbabilitySpace Q)
    (W : (Q.X → ℂ) → (P.X → ℂ))
    (hW : IsLtwoAlgebraUnitaryFor P Q W)
    (B : (inducedMeasureAlgebra Q).carrier) :
    W (indicatorOne B.1) =ᵐ[P.μ]
      indicatorOne (indicatorImage P Q hQ W hW B).1 :=
  (Classical.choose_spec (image_indicator P Q hQ W hW B.2)).2

theorem indicatorImage_measure
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hQ : Chapter01.IsProbabilitySpace Q)
    (W : (Q.X → ℂ) → (P.X → ℂ))
    (hW : IsLtwoAlgebraUnitaryFor P Q W)
    (B : (inducedMeasureAlgebra Q).carrier) :
    P.μ (indicatorImage P Q hQ W hW B).1 = Q.μ B.1 := by
  have hW' := hW
  rcases hW with
    ⟨_hae, _hadd, _hsmul, hL2, _hdense, _hLinf, _hLinfSurj, _hone, _hmul⟩
  have hBmem : MemLp (indicatorOne B.1) 2 Q.μ :=
    indicatorOne_memLp Q hQ B.2 2
  have hnorm := (hL2 (indicatorOne B.1) hBmem).2
  have hspec := indicatorImage_spec P Q hQ W hW' B
  rw [eLpNorm_congr_ae hspec] at hnorm
  change eLpNorm
      ((indicatorImage P Q hQ W hW' B).1.indicator fun _ => (1 : ℂ))
        2 P.μ =
    eLpNorm (B.1.indicator fun _ => (1 : ℂ)) 2 Q.μ at hnorm
  rw [eLpNorm_indicator_const
      (indicatorImage P Q hQ W hW' B).2
      (by norm_num) (by norm_num),
    eLpNorm_indicator_const B.2 (by norm_num) (by norm_num)] at hnorm
  simp only [enorm_one, one_mul, ENNReal.toReal_ofNat] at hnorm
  exact ENNReal.rpow_left_injective (by norm_num : (1 / (2 : ℝ)) ≠ 0) hnorm

theorem indicatorOne_ae_iff
    (P : ProbabilitySpace.{u}) {A B : Set P.X}
    (_hA : MeasurableSet A) (_hB : MeasurableSet B) :
    indicatorOne A =ᵐ[P.μ] indicatorOne B ↔
      P.μ (Chapter00.symmDiff A B) = 0 := by
  constructor
  · intro h
    have hsets : A =ᵐ[P.μ] B := by
      filter_upwards [h] with x hx
      change (x ∈ A) = (x ∈ B)
      apply propext
      by_cases hAx : x ∈ A <;> by_cases hBx : x ∈ B <;>
        simp_all [indicatorOne]
    simpa [Set.symmDiff_def, Chapter00.symmDiff] using
      (MeasureTheory.measure_symmDiff_eq_zero_iff.mpr hsets)
  · intro hμ
    have hsets : A =ᵐ[P.μ] B := by
      apply MeasureTheory.measure_symmDiff_eq_zero_iff.mp
      simpa [Set.symmDiff_def, Chapter00.symmDiff] using hμ
    filter_upwards [hsets] with x hx
    by_cases hAx : x ∈ A
    · have hBx : x ∈ B := hx.mp hAx
      simp [indicatorOne, hAx, hBx]
    · have hBx : x ∉ B := fun hxB => hAx (hx.mpr hxB)
      simp [indicatorOne, hAx, hBx]

theorem inducedEquiv_iff_ae
    (P : ProbabilitySpace.{u})
    (A B : (inducedMeasureAlgebra P).carrier) :
    (inducedMeasureAlgebra P).equiv A B ↔ A.1 =ᵐ[P.μ] B.1 := by
  exact MeasureTheory.measure_symmDiff_eq_zero_iff

noncomputable def indicatorHom
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hQ : Chapter01.IsProbabilitySpace Q)
    (W : (Q.X → ℂ) → (P.X → ℂ))
    (hW : IsLtwoAlgebraUnitaryFor P Q W) :
    MeasureAlgebraHomData (inducedMeasureAlgebra Q) (inducedMeasureAlgebra P) where
  map := indicatorImage P Q hQ W hW

theorem indicatorHom_equiv
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hQ : Chapter01.IsProbabilitySpace Q)
    (W : (Q.X → ℂ) → (P.X → ℂ))
    (hW : IsLtwoAlgebraUnitaryFor P Q W)
    (B C : (inducedMeasureAlgebra Q).carrier)
    (hBC : (inducedMeasureAlgebra Q).equiv B C) :
    (inducedMeasureAlgebra P).equiv
      ((indicatorHom P Q hQ W hW).map B)
      ((indicatorHom P Q hQ W hW).map C) := by
  have hBCae : indicatorOne B.1 =ᵐ[Q.μ] indicatorOne C.1 :=
    (indicatorOne_ae_iff Q B.2 C.2).2 hBC
  have hBtwo : MemLp (indicatorOne B.1) 2 Q.μ :=
    indicatorOne_memLp Q hQ B.2 2
  have hCtwo : MemLp (indicatorOne C.1) 2 Q.μ :=
    indicatorOne_memLp Q hQ C.2 2
  have hWae := hW.1 (indicatorOne B.1) (indicatorOne C.1)
    hBtwo hCtwo hBCae
  have hBspec := indicatorImage_spec P Q hQ W hW B
  have hCspec := indicatorImage_spec P Q hQ W hW C
  apply (indicatorOne_ae_iff P
    ((indicatorHom P Q hQ W hW).map B).2
    ((indicatorHom P Q hQ W hW).map C).2).1
  exact hBspec.symm.trans (hWae.trans hCspec)

theorem indicatorHom_inter
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hQ : Chapter01.IsProbabilitySpace Q)
    (W : (Q.X → ℂ) → (P.X → ℂ))
    (hW : IsLtwoAlgebraUnitaryFor P Q W)
    (B C : (inducedMeasureAlgebra Q).carrier) :
    (inducedMeasureAlgebra P).equiv
      ((indicatorHom P Q hQ W hW).map
        ((inducedMeasureAlgebra Q).inter B C))
      ((inducedMeasureAlgebra P).inter
        ((indicatorHom P Q hQ W hW).map B)
      ((indicatorHom P Q hQ W hW).map C)) := by
  have hW' := hW
  obtain ⟨hae, _hadd, _hsmul, _hL2, _hdense, _hLinf,
    _hLinfSurj, _hone, hmul⟩ := hW'
  let eB : Q.X → ℂ := indicatorOne B.1
  let eC : Q.X → ℂ := indicatorOne C.1
  have hBtop : MemLp eB ⊤ Q.μ := indicatorOne_memLp Q hQ B.2 ⊤
  have hCtop : MemLp eC ⊤ Q.μ := indicatorOne_memLp Q hQ C.2 ⊤
  have hBtwo : MemLp eB 2 Q.μ := indicatorOne_memLp Q hQ B.2 2
  have hCtwo : MemLp eC 2 Q.μ := indicatorOne_memLp Q hQ C.2 2
  have hInterTwo : MemLp (indicatorOne (B.1 ∩ C.1)) 2 Q.μ :=
    indicatorOne_memLp Q hQ (B.2.inter C.2) 2
  have hin : (fun y => eB y * eC y) =
      indicatorOne (B.1 ∩ C.1) := by
    funext y
    by_cases hyB : y ∈ B.1 <;> by_cases hyC : y ∈ C.1 <;>
      simp [eB, eC, indicatorOne, hyB, hyC]
  have hProdTwo : MemLp (fun y => eB y * eC y) 2 Q.μ :=
    (memLp_congr_ae
      (Filter.Eventually.of_forall fun y => congrFun hin y)).2 hInterTwo
  have hWin : W (fun y => eB y * eC y) =ᵐ[ P.μ]
      W (indicatorOne (B.1 ∩ C.1)) :=
    hae _ _ hProdTwo hInterTwo
      (Filter.Eventually.of_forall fun y => congrFun hin y)
  have hmul' := hmul eB eC hBtop hCtop
  have hBspec := indicatorImage_spec P Q hQ W hW B
  have hCspec := indicatorImage_spec P Q hQ W hW C
  have hIspec := indicatorImage_spec P Q hQ W hW
    ((inducedMeasureAlgebra Q).inter B C)
  apply (indicatorOne_ae_iff P
    ((indicatorHom P Q hQ W hW).map
      ((inducedMeasureAlgebra Q).inter B C)).2
    ((inducedMeasureAlgebra P).inter
      ((indicatorHom P Q hQ W hW).map B)
      ((indicatorHom P Q hQ W hW).map C)).2).1
  filter_upwards [hWin, hmul', hBspec, hCspec, hIspec]
    with x hxWin hxmul hxB hxC hxI
  change indicatorOne
      (indicatorImage P Q hQ W hW
        ((inducedMeasureAlgebra Q).inter B C)).1 x =
    indicatorOne
      ((indicatorImage P Q hQ W hW B).1 ∩
        (indicatorImage P Q hQ W hW C).1) x
  change W (indicatorOne (B.1 ∩ C.1)) x =
    indicatorOne
      (indicatorImage P Q hQ W hW
        ((inducedMeasureAlgebra Q).inter B C)).1 x at hxI
  rw [← hxI, ← hxWin, hxmul, hxB, hxC]
  by_cases hxMB : x ∈ (indicatorImage P Q hQ W hW B).1 <;>
    by_cases hxMC : x ∈ (indicatorImage P Q hQ W hW C).1 <;>
    simp [indicatorOne, hxMB, hxMC]

theorem indicatorHom_compl
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hQ : Chapter01.IsProbabilitySpace Q)
    (W : (Q.X → ℂ) → (P.X → ℂ))
    (hW : IsLtwoAlgebraUnitaryFor P Q W)
    (B : (inducedMeasureAlgebra Q).carrier) :
    (inducedMeasureAlgebra P).equiv
      ((indicatorHom P Q hQ W hW).map
        ((inducedMeasureAlgebra Q).compl B))
      ((inducedMeasureAlgebra P).compl
      ((indicatorHom P Q hQ W hW).map B)) := by
  have hW' := hW
  obtain ⟨hae, hadd, hsmul, _hL2, _hdense, _hLinf,
    _hLinfSurj, hone, _hmul⟩ := hW'
  let eB : Q.X → ℂ := indicatorOne B.1
  let oneQ : Q.X → ℂ := fun _ => 1
  have hOneTwo : MemLp oneQ 2 Q.μ :=
    by
      simpa [oneQ, indicatorOne] using
        (indicatorOne_memLp Q hQ MeasurableSet.univ 2)
  have hBtwo : MemLp eB 2 Q.μ := indicatorOne_memLp Q hQ B.2 2
  have hNegBtwo : MemLp (fun y => (-1 : ℂ) * eB y) 2 Q.μ :=
    hBtwo.const_mul (-1)
  have hSumTwo : MemLp (fun y => oneQ y + (-1 : ℂ) * eB y) 2 Q.μ :=
    hOneTwo.add hNegBtwo
  have hComplTwo : MemLp (indicatorOne B.1ᶜ) 2 Q.μ :=
    indicatorOne_memLp Q hQ B.2.compl 2
  have hin : (fun y => oneQ y + (-1 : ℂ) * eB y) =
      indicatorOne B.1ᶜ := by
    funext y
    by_cases hyB : y ∈ B.1 <;> simp [oneQ, eB, indicatorOne, hyB]
  have hWin : W (fun y => oneQ y + (-1 : ℂ) * eB y) =ᵐ[P.μ]
      W (indicatorOne B.1ᶜ) :=
    hae _ _ hSumTwo hComplTwo
      (Filter.Eventually.of_forall fun y => congrFun hin y)
  have hadd' := hadd oneQ (fun y => (-1 : ℂ) * eB y) hOneTwo hNegBtwo
  have hsmul' := hsmul (-1 : ℂ) eB hBtwo
  have hBspec := indicatorImage_spec P Q hQ W hW B
  have hCspec := indicatorImage_spec P Q hQ W hW
    ((inducedMeasureAlgebra Q).compl B)
  apply (indicatorOne_ae_iff P
    ((indicatorHom P Q hQ W hW).map
      ((inducedMeasureAlgebra Q).compl B)).2
    ((inducedMeasureAlgebra P).compl
      ((indicatorHom P Q hQ W hW).map B)).2).1
  filter_upwards [hWin, hadd', hsmul', hone, hBspec, hCspec]
    with x hxWin hxadd hxsmul hxone hxB hxC
  change indicatorOne
      (indicatorImage P Q hQ W hW
        ((inducedMeasureAlgebra Q).compl B)).1 x =
    indicatorOne (indicatorImage P Q hQ W hW B).1ᶜ x
  change W (indicatorOne B.1ᶜ) x =
    indicatorOne
      (indicatorImage P Q hQ W hW
        ((inducedMeasureAlgebra Q).compl B)).1 x at hxC
  rw [← hxC, ← hxWin, hxadd, hxsmul, hxone, hxB]
  by_cases hxMB : x ∈ (indicatorImage P Q hQ W hW B).1 <;>
    simp [indicatorOne, hxMB]

theorem indicatorHom_union
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hQ : Chapter01.IsProbabilitySpace Q)
    (W : (Q.X → ℂ) → (P.X → ℂ))
    (hW : IsLtwoAlgebraUnitaryFor P Q W)
    (B C : (inducedMeasureAlgebra Q).carrier) :
    (inducedMeasureAlgebra P).equiv
      ((indicatorHom P Q hQ W hW).map
        ((inducedMeasureAlgebra Q).union B C))
      ((inducedMeasureAlgebra P).union
        ((indicatorHom P Q hQ W hW).map B)
        ((indicatorHom P Q hQ W hW).map C)) := by
  have hW' := hW
  obtain ⟨hae, hadd, hsmul, _hL2, _hdense, _hLinf,
    _hLinfSurj, _hone, hmul⟩ := hW'
  let eB : Q.X → ℂ := indicatorOne B.1
  let eC : Q.X → ℂ := indicatorOne C.1
  let prod : Q.X → ℂ := fun y => eB y * eC y
  let sum : Q.X → ℂ := fun y => eB y + eC y
  let expr : Q.X → ℂ := fun y => sum y + (-1 : ℂ) * prod y
  have hBtop : MemLp eB ⊤ Q.μ := indicatorOne_memLp Q hQ B.2 ⊤
  have hCtop : MemLp eC ⊤ Q.μ := indicatorOne_memLp Q hQ C.2 ⊤
  have hBtwo : MemLp eB 2 Q.μ := indicatorOne_memLp Q hQ B.2 2
  have hCtwo : MemLp eC 2 Q.μ := indicatorOne_memLp Q hQ C.2 2
  have hProdTwo : MemLp prod 2 Q.μ :=
    (memLp_congr_ae
      (Filter.Eventually.of_forall fun y => by
        change prod y = indicatorOne (B.1 ∩ C.1) y
        by_cases hyB : y ∈ B.1 <;> by_cases hyC : y ∈ C.1 <;>
          simp [prod, eB, eC, indicatorOne, hyB, hyC])).2
      (indicatorOne_memLp Q hQ (B.2.inter C.2) 2)
  have hSumTwo : MemLp sum 2 Q.μ := hBtwo.add hCtwo
  have hNegProdTwo : MemLp (fun y => (-1 : ℂ) * prod y) 2 Q.μ :=
    hProdTwo.const_mul (-1)
  have hExprTwo : MemLp expr 2 Q.μ := hSumTwo.add hNegProdTwo
  have hUnionTwo : MemLp (indicatorOne (B.1 ∪ C.1)) 2 Q.μ :=
    indicatorOne_memLp Q hQ (B.2.union C.2) 2
  have hin : expr = indicatorOne (B.1 ∪ C.1) := by
    funext y
    by_cases hyB : y ∈ B.1 <;> by_cases hyC : y ∈ C.1 <;>
      simp [expr, sum, prod, eB, eC, indicatorOne, hyB, hyC]
  have hWin : W expr =ᵐ[P.μ] W (indicatorOne (B.1 ∪ C.1)) :=
    hae _ _ hExprTwo hUnionTwo
      (Filter.Eventually.of_forall fun y => congrFun hin y)
  have hadd1 := hadd eB eC hBtwo hCtwo
  have hmul' := hmul eB eC hBtop hCtop
  have hsmul' := hsmul (-1 : ℂ) prod hProdTwo
  have hadd2 := hadd sum (fun y => (-1 : ℂ) * prod y)
    hSumTwo hNegProdTwo
  have hBspec := indicatorImage_spec P Q hQ W hW B
  have hCspec := indicatorImage_spec P Q hQ W hW C
  have hUspec := indicatorImage_spec P Q hQ W hW
    ((inducedMeasureAlgebra Q).union B C)
  apply (indicatorOne_ae_iff P
    ((indicatorHom P Q hQ W hW).map
      ((inducedMeasureAlgebra Q).union B C)).2
    ((inducedMeasureAlgebra P).union
      ((indicatorHom P Q hQ W hW).map B)
      ((indicatorHom P Q hQ W hW).map C)).2).1
  filter_upwards [hWin, hadd1, hmul', hsmul', hadd2,
    hBspec, hCspec, hUspec]
    with x hxWin hxadd1 hxmul hxsmul hxadd2 hxB hxC hxU
  change indicatorOne
      (indicatorImage P Q hQ W hW
        ((inducedMeasureAlgebra Q).union B C)).1 x =
    indicatorOne
      ((indicatorImage P Q hQ W hW B).1 ∪
        (indicatorImage P Q hQ W hW C).1) x
  change W (indicatorOne (B.1 ∪ C.1)) x =
    indicatorOne
      (indicatorImage P Q hQ W hW
        ((inducedMeasureAlgebra Q).union B C)).1 x at hxU
  change W expr x = W (indicatorOne (B.1 ∪ C.1)) x at hxWin
  change W sum x = W eB x + W eC x at hxadd1
  change W prod x = W eB x * W eC x at hxmul
  change W (fun y => (-1 : ℂ) * prod y) x = (-1 : ℂ) * W prod x at hxsmul
  change W expr x =
    W sum x + W (fun y => (-1 : ℂ) * prod y) x at hxadd2
  rw [← hxU, ← hxWin, hxadd2, hxadd1, hxsmul, hxmul, hxB, hxC]
  by_cases hxMB : x ∈ (indicatorImage P Q hQ W hW B).1 <;>
    by_cases hxMC : x ∈ (indicatorImage P Q hQ W hW C).1 <;>
    simp [indicatorOne, hxMB, hxMC]

theorem indicatorHom_partialUnion
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (W : (Q.X → ℂ) → (P.X → ℂ))
    (hW : IsLtwoAlgebraUnitaryFor P Q W)
    (f : ℕ → (inducedMeasureAlgebra Q).carrier) (n : ℕ) :
    (inducedMeasureAlgebra P).equiv
      ((indicatorHom P Q hQ W hW).map (partialCarrier Q f n))
      (partialCarrier P (fun k => (indicatorHom P Q hQ W hW).map (f k)) n) := by
  let hPA := isMeasureAlgebra_inducedMeasureAlgebra P hP
  induction n with
  | zero =>
      apply hPA.1.1
  | succ n ih =>
      have hSource :
          partialCarrier Q f (n + 1) =
            (inducedMeasureAlgebra Q).union (partialCarrier Q f n) (f (n + 1)) :=
        Subtype.ext (by rfl)
      have hTarget :
          partialCarrier P
              (fun k => (indicatorHom P Q hQ W hW).map (f k)) (n + 1) =
            (inducedMeasureAlgebra P).union
              (partialCarrier P
                (fun k => (indicatorHom P Q hQ W hW).map (f k)) n)
              ((indicatorHom P Q hQ W hW).map (f (n + 1))) :=
        Subtype.ext (by rfl)
      rw [hSource, hTarget]
      exact hPA.1.3
        (indicatorHom_union P Q hQ W hW (partialCarrier Q f n) (f (n + 1)))
        ((hPA.2.1 _ _ _ _ ih
          (hPA.1.1 ((indicatorHom P Q hQ W hW).map (f (n + 1))))).1)

theorem indicatorHom_iUnion_measure
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (W : (Q.X → ℂ) → (P.X → ℂ))
    (hW : IsLtwoAlgebraUnitaryFor P Q W)
    (f : ℕ → (inducedMeasureAlgebra Q).carrier) :
    P.μ (⋃ n, ((indicatorHom P Q hQ W hW).map (f n)).1) =
      Q.μ (⋃ n, (f n).1) := by
  let g : ℕ → (inducedMeasureAlgebra P).carrier :=
    fun n => (indicatorHom P Q hQ W hW).map (f n)
  have hpartial : ∀ n, P.μ (partialCarrier P g n).1 =
      Q.μ (partialCarrier Q f n).1 := by
    intro n
    calc
      P.μ (partialCarrier P g n).1 =
          P.μ ((indicatorHom P Q hQ W hW).map
            (partialCarrier Q f n)).1 := by
        apply MeasureTheory.measure_congr
        exact (inducedEquiv_iff_ae P _ _).mp
          (indicatorHom_partialUnion P Q hP hQ W hW f n) |>.symm
      _ = Q.μ (partialCarrier Q f n).1 :=
        indicatorImage_measure P Q hQ W hW (partialCarrier Q f n)
  calc
    P.μ (⋃ n, ((indicatorHom P Q hQ W hW).map (f n)).1) =
        P.μ (⋃ n, (partialCarrier P g n).1) := by
      apply congrArg P.μ
      change (⋃ n, (g n).1) =
        ⋃ n, partialUnion (fun k => (g k).1) n
      exact (iUnion_partialUnion (fun k => (g k).1)).symm
    _ = ⨆ n, P.μ (partialCarrier P g n).1 :=
      (partialUnion_mono (fun n => (g n).1)).measure_iUnion
    _ = ⨆ n, Q.μ (partialCarrier Q f n).1 := by
      congr 1
      funext n
      exact hpartial n
    _ = Q.μ (⋃ n, (partialCarrier Q f n).1) :=
      (partialUnion_mono (fun n => (f n).1)).measure_iUnion.symm
    _ = Q.μ (⋃ n, (f n).1) := by
      apply congrArg Q.μ
      change (⋃ n, partialUnion (fun k => (f k).1) n) =
        ⋃ n, (f n).1
      exact iUnion_partialUnion (fun k => (f k).1)

theorem indicatorHom_iUnion
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (W : (Q.X → ℂ) → (P.X → ℂ))
    (hW : IsLtwoAlgebraUnitaryFor P Q W)
    (f : ℕ → (inducedMeasureAlgebra Q).carrier) :
    (inducedMeasureAlgebra P).equiv
      ((indicatorHom P Q hQ W hW).map
        ((inducedMeasureAlgebra Q).iUnion f))
      ((inducedMeasureAlgebra P).iUnion
        (fun n => (indicatorHom P Q hQ W hW).map (f n))) := by
  letI : IsProbabilityMeasure P.μ := hP
  let U := (inducedMeasureAlgebra Q).iUnion f
  let A := (indicatorHom P Q hQ W hW).map U
  let g : ℕ → (inducedMeasureAlgebra P).carrier :=
    fun n => (indicatorHom P Q hQ W hW).map (f n)
  let V := (inducedMeasureAlgebra P).iUnion g
  have hfnU : ∀ n, (inducedMeasureAlgebra Q).equiv
      ((inducedMeasureAlgebra Q).inter (f n) U) (f n) := by
    intro n
    apply (inducedEquiv_iff_ae Q _ _).2
    filter_upwards with x
    change (x ∈ (f n).1 ∩ ⋃ k, (f k).1) = (x ∈ (f n).1)
    apply propext
    simp only [Set.mem_inter_iff, Set.mem_iUnion]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, ⟨n, hx⟩⟩⟩
  have hgnA : ∀ n, (inducedMeasureAlgebra P).equiv
      ((inducedMeasureAlgebra P).inter (g n) A) (g n) := by
    intro n
    have hInter := indicatorHom_inter P Q hQ W hW (f n) U
    have hMap := indicatorHom_equiv P Q hQ W hW
      ((inducedMeasureAlgebra Q).inter (f n) U) (f n) (hfnU n)
    exact (isMeasureAlgebra_inducedMeasureAlgebra P hP).1.3
      ((isMeasureAlgebra_inducedMeasureAlgebra P hP).1.2 hInter) hMap
  have hdiffZero : ∀ n, P.μ ((g n).1 \ A.1) = 0 := by
    intro n
    have hae := (inducedEquiv_iff_ae P _ _).1 (hgnA n)
    apply MeasureTheory.measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hae] with x hx
    intro hxDiff
    have hxInter : x ∈ (g n).1 ∩ A.1 := hx.mpr hxDiff.1
    exact hxDiff.2 hxInter.2
  have hVAzero : P.μ (V.1 \ A.1) = 0 := by
    have hset : V.1 \ A.1 = ⋃ n, ((g n).1 \ A.1) := by
      ext x
      simp [V, inducedMeasureAlgebra]
    rw [hset]
    exact MeasureTheory.measure_iUnion_null hdiffZero
  have hInterMeasure : P.μ (A.1 ∩ V.1) = P.μ V.1 := by
    apply MeasureTheory.measure_congr
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hVAzero]
      with x hx
    change (x ∈ A.1 ∩ V.1) = (x ∈ V.1)
    apply propext
    constructor
    · exact fun h => h.2
    · intro hxV
      exact ⟨by
        by_contra hxA
        exact hx ⟨hxV, hxA⟩, hxV⟩
  have hMeasureVA : P.μ V.1 = P.μ A.1 := by
    calc
      P.μ V.1 = Q.μ U.1 := by
        exact indicatorHom_iUnion_measure P Q hP hQ W hW f
      _ = P.μ A.1 := (indicatorImage_measure P Q hQ W hW U).symm
  have hAVzero : P.μ (A.1 \ V.1) = 0 := by
    have hfinite : P.μ (A.1 ∩ V.1) ≠ ⊤ :=
      MeasureTheory.measure_ne_top P.μ _
    calc
      P.μ (A.1 \ V.1) = P.μ (A.1 \ (A.1 ∩ V.1)) := by
        apply congrArg P.μ
        ext x
        simp only [Set.mem_diff, Set.mem_inter_iff]
        tauto
      _ = P.μ A.1 - P.μ (A.1 ∩ V.1) :=
        MeasureTheory.measure_diff Set.inter_subset_left
          (A.2.inter V.2).nullMeasurableSet hfinite
      _ = 0 := by rw [hInterMeasure, hMeasureVA.symm, tsub_self]
  have hFinal : (inducedMeasureAlgebra P).equiv A V := by
    change P.μ (Chapter00.symmDiff A.1 V.1) = 0
    simp only [Chapter00.symmDiff]
    exact MeasureTheory.measure_union_null hAVzero hVAzero
  simpa [A, V, U, g] using hFinal

theorem ae_injective_on_ltwo
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (W : (Q.X → ℂ) → (P.X → ℂ))
    (hW : IsLtwoAlgebraUnitaryFor P Q W)
    (f g : Q.X → ℂ) (hf : MemLp f 2 Q.μ) (hg : MemLp g 2 Q.μ)
    (hfg : W f =ᵐ[P.μ] W g) :
    f =ᵐ[Q.μ] g := by
  have hW' := hW
  obtain ⟨_hae, hadd, hsmul, hL2, _hdense, _hLinf,
    _hLinfSurj, _hone, _hmul⟩ := hW'
  let d : Q.X → ℂ := fun y => f y - g y
  have hd : MemLp d 2 Q.μ := hf.sub hg
  have hdform : d = fun y => f y + (-1 : ℂ) * g y := by
    funext y
    rw [show d y = f y - g y by rfl, sub_eq_add_neg, neg_one_mul]
  have hNegG : MemLp (fun y => (-1 : ℂ) * g y) 2 Q.μ :=
    hg.const_mul (-1)
  have hadd' := hadd f (fun y => (-1 : ℂ) * g y) hf hNegG
  have hsmul' := hsmul (-1 : ℂ) g hg
  have hWd0 : W d =ᵐ[P.μ] fun _ => (0 : ℂ) := by
    filter_upwards [hadd', hsmul', hfg] with x hxadd hxsmul hxfg
    rw [hdform]
    rw [hxadd, hxsmul, hxfg]
    ring
  have hnormOut : eLpNorm (W d) 2 P.μ = 0 := by
    rw [eLpNorm_congr_ae hWd0]
    simp
  have hnormIn : eLpNorm d 2 Q.μ = 0 := by
    rw [← (hL2 d hd).2]
    exact hnormOut
  have hd0 : d =ᵐ[Q.μ] fun _ => (0 : ℂ) :=
    (eLpNorm_eq_zero_iff hd.aestronglyMeasurable (by norm_num)).1 hnormIn
  filter_upwards [hd0] with y hy
  change f y - g y = 0 at hy
  exact sub_eq_zero.mp hy

theorem indicatorHom_injective
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hQ : Chapter01.IsProbabilitySpace Q)
    (W : (Q.X → ℂ) → (P.X → ℂ))
    (hW : IsLtwoAlgebraUnitaryFor P Q W)
    (B C : (inducedMeasureAlgebra Q).carrier)
    (hBC : (inducedMeasureAlgebra P).equiv
      ((indicatorHom P Q hQ W hW).map B)
      ((indicatorHom P Q hQ W hW).map C)) :
    (inducedMeasureAlgebra Q).equiv B C := by
  have hImageAe : indicatorOne
      ((indicatorHom P Q hQ W hW).map B).1 =ᵐ[P.μ]
      indicatorOne ((indicatorHom P Q hQ W hW).map C).1 :=
    (indicatorOne_ae_iff P
      ((indicatorHom P Q hQ W hW).map B).2
      ((indicatorHom P Q hQ W hW).map C).2).2 hBC
  have hWAe : W (indicatorOne B.1) =ᵐ[P.μ] W (indicatorOne C.1) :=
    (indicatorImage_spec P Q hQ W hW B).trans
      (hImageAe.trans (indicatorImage_spec P Q hQ W hW C).symm)
  apply (indicatorOne_ae_iff Q B.2 C.2).1
  exact ae_injective_on_ltwo P Q W hW _ _
    (indicatorOne_memLp Q hQ B.2 2)
    (indicatorOne_memLp Q hQ C.2 2) hWAe

theorem idempotent_is_indicator
    (P : ProbabilitySpace.{u}) (f : P.X → ℂ)
    (hf : AEStronglyMeasurable f P.μ)
    (hidem : (fun x => f x * f x) =ᵐ[P.μ] f) :
    ∃ A : Set P.X, MeasurableSet A ∧ f =ᵐ[P.μ] indicatorOne A := by
  let r : P.X → ℂ := hf.mk f
  have hrm : Measurable r := hf.measurable_mk
  have hfr : f =ᵐ[P.μ] r := hf.ae_eq_mk
  have hidemR : (fun x => r x * r x) =ᵐ[P.μ] r := by
    filter_upwards [hfr, hidem] with x hxr hxidem
    rw [← hxr]
    exact hxidem
  let A : Set P.X := {x | r x = 1}
  have hA : MeasurableSet A := measurableSet_eq_fun hrm measurable_const
  refine ⟨A, hA, ?_⟩
  filter_upwards [hfr, hidemR] with x hxr hxidem
  rw [hxr]
  have hzero_or_one : r x = 0 ∨ r x = 1 := by
    have hfactor : r x * (r x - 1) = 0 := by
      calc
        r x * (r x - 1) = r x * r x - r x := by ring
        _ = 0 := sub_eq_zero.mpr hxidem
    rcases mul_eq_zero.mp hfactor with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr (sub_eq_zero.mp hone)
  rcases hzero_or_one with hzero | hone
  · have hxnot : x ∉ A := by
      intro hx
      exact zero_ne_one (hzero.symm.trans hx)
    simp [indicatorOne, Set.indicator_of_notMem hxnot, hzero]
  · have hxmem : x ∈ A := hone
    simp [indicatorOne, Set.indicator_of_mem hxmem, hone]

theorem indicatorHom_surjective
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (W : (Q.X → ℂ) → (P.X → ℂ))
    (hW : IsLtwoAlgebraUnitaryFor P Q W)
    (A : (inducedMeasureAlgebra P).carrier) :
    ∃ B : (inducedMeasureAlgebra Q).carrier,
      (inducedMeasureAlgebra P).equiv
        ((indicatorHom P Q hQ W hW).map B) A := by
  letI : IsProbabilityMeasure Q.μ := hQ
  have hW' := hW
  obtain ⟨_hae, _hadd, _hsmul, _hL2, _hdense, _hLinf,
    hLinfSurj, _hone, hmul⟩ := hW'
  have hAtop : MemLp (indicatorOne A.1) ⊤ P.μ :=
    indicatorOne_memLp P hP A.2 ⊤
  obtain ⟨f, hfTop, hWf⟩ := hLinfSurj (indicatorOne A.1) hAtop
  have hfTwo : MemLp f 2 Q.μ := hfTop.mono_exponent (by norm_num)
  have hffTop : MemLp (fun y => f y * f y) ⊤ Q.μ := hfTop.mul hfTop
  have hffTwo : MemLp (fun y => f y * f y) 2 Q.μ :=
    hffTop.mono_exponent (by norm_num)
  have hmul' := hmul f f hfTop hfTop
  have hWidem : W (fun y => f y * f y) =ᵐ[P.μ] W f := by
    filter_upwards [hmul', hWf] with x hxmul hxWf
    rw [hxmul, hxWf]
    by_cases hxA : x ∈ A.1 <;> simp [indicatorOne, hxA]
  have hidem : (fun y => f y * f y) =ᵐ[Q.μ] f :=
    ae_injective_on_ltwo P Q W hW _ _ hffTwo hfTwo hWidem
  obtain ⟨B, hB, hfB⟩ :=
    idempotent_is_indicator Q f hfTop.aestronglyMeasurable hidem
  let B' : (inducedMeasureAlgebra Q).carrier := ⟨B, hB⟩
  refine ⟨B', ?_⟩
  apply (indicatorOne_ae_iff P
    ((indicatorHom P Q hQ W hW).map B').2 A.2).1
  exact (indicatorImage_spec P Q hQ W hW B').symm.trans
    ((hW.1 _ _ hfTwo
      (indicatorOne_memLp Q hQ hB 2) hfB).symm.trans hWf)

theorem indicatorHom_isMeasureAlgebraIsomorphism
    (P : ProbabilitySpace.{u}) (Q : ProbabilitySpace.{v})
    (hP : Chapter01.IsProbabilitySpace P)
    (hQ : Chapter01.IsProbabilitySpace Q)
    (W : (Q.X → ℂ) → (P.X → ℂ))
    (hW : IsLtwoAlgebraUnitaryFor P Q W) :
    IsMeasureAlgebraIsomorphism (indicatorHom P Q hQ W hW) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact indicatorHom_equiv P Q hQ W hW
  · exact indicatorHom_union P Q hQ W hW
  · exact indicatorHom_compl P Q hQ W hW
  · exact indicatorHom_iUnion P Q hP hQ W hW
  · intro B
    exact congrArg ENNReal.toReal
      (indicatorImage_measure P Q hQ W hW B)
  · exact indicatorHom_injective P Q hQ W hW
  · exact indicatorHom_surjective P Q hP hQ W hW

theorem systemConjugate_of_algebraicSpectralIsomorphism
    (M : System.{u}) (N : System.{v})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (hIso : IsAlgebraicSpectralIsomorphism M N) :
    IsSystemConjugate M N := by
  obtain ⟨W, hSpec, hAlg⟩ := hIso
  obtain ⟨_hae, _hadd, _hsmul, _hL2, _hdense, hintertwine⟩ := hSpec
  let Φ := indicatorHom M.toProbabilitySpace N.toProbabilitySpace hN.1 W hAlg
  refine ⟨Φ, indicatorHom_isMeasureAlgebraIsomorphism
    M.toProbabilitySpace N.toProbabilitySpace hM.1 hN.1 W hAlg, ?_⟩
  intro B
  have hBtwo : MemLp (indicatorOne B.1) 2 N.μ :=
    indicatorOne_memLp N.toProbabilitySpace hN.1 B.2 2
  have hInt := hintertwine (indicatorOne B.1) hBtwo
  have hBspec := indicatorImage_spec
    M.toProbabilitySpace N.toProbabilitySpace hN.1 W hAlg B
  have hBspecComp :
      (fun x => W (indicatorOne B.1) (M.T x)) =ᵐ[M.μ]
        fun x => indicatorOne (Φ.map B).1 (M.T x) :=
    hM.2.quasiMeasurePreserving.ae_eq_comp hBspec
  have hTspec := indicatorImage_spec
    M.toProbabilitySpace N.toProbabilitySpace hN.1 W hAlg
      ((inducedMeasureAlgebraSystem N).transform B)
  have hTN :
      (inducedMeasureAlgebraSystem N).transform B =
        ⟨N.T ⁻¹' B.1, B.2.preimage hN.2.measurable⟩ := by
    simp [inducedMeasureAlgebraSystem, hN.2.measurable]
  have hTM :
      (inducedMeasureAlgebraSystem M).transform (Φ.map B) =
        ⟨M.T ⁻¹' (Φ.map B).1,
          (Φ.map B).2.preimage hM.2.measurable⟩ := by
    simp [inducedMeasureAlgebraSystem, hM.2.measurable]
  rw [hTN] at hTspec
  rw [hTN, hTM]
  apply (indicatorOne_ae_iff M.toProbabilitySpace
    (Φ.map ⟨N.T ⁻¹' B.1, B.2.preimage hN.2.measurable⟩).2
    ((Φ.map B).2.preimage hM.2.measurable)).1
  filter_upwards [hTspec, hInt, hBspecComp]
    with x hxT hxInt hxComp
  change indicatorOne
      (Φ.map ⟨N.T ⁻¹' B.1, B.2.preimage hN.2.measurable⟩).1 x =
    indicatorOne (M.T ⁻¹' (Φ.map B).1) x
  change W (indicatorOne (N.T ⁻¹' B.1)) x =
    indicatorOne (Φ.map
      ⟨N.T ⁻¹' B.1, B.2.preimage hN.2.measurable⟩).1 x at hxT
  change W (fun y => indicatorOne B.1 (N.T y)) x =
    W (indicatorOne B.1) (M.T x) at hxInt
  change W (indicatorOne B.1) (M.T x) =
    indicatorOne (Φ.map B).1 (M.T x) at hxComp
  have hpreN :
      indicatorOne (N.T ⁻¹' B.1) =
        fun y => indicatorOne B.1 (N.T y) := by
    funext y
    rfl
  have hpreM :
      indicatorOne (M.T ⁻¹' (Φ.map B).1) x =
        indicatorOne (Φ.map B).1 (M.T x) := rfl
  rw [← hxT, hpreN, hxInt, hpreM, hxComp]

end Chapter04.LtwoProjection
