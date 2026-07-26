import Chapter04.Spectral.LebesgueSpectrumStrongMixing
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section

open Classical

namespace Chapter04.LebesgueSpectrum

universe u

abbrev SpectrumIndex := Option (ℕ × ℤ)

def orbitFunction (M : System.{u}) (U : MeasureIntegerActionData M)
    (fbase : ℕ → M.X → ℂ) (q : ℕ × ℤ) : M.X → ℂ :=
  Chapter01.koopman (U.act q.2) (fbase q.1)

theorem orbitFunction_memLp
    (M : System.{u}) (U : MeasureIntegerActionData M)
    (fbase : ℕ → M.X → ℂ) (hf : ∀ i, M.lpMember 2 (fbase i))
    (q : ℕ × ℤ) : M.lpMember 2 (orbitFunction M U fbase q) := by
  exact (hf q.1).comp_measurePreserving (U.measure_preserving q.2)

def orbitLp
    (M : System.{u}) (U : MeasureIntegerActionData M)
    (fbase : ℕ → M.X → ℂ) (hf : ∀ i, M.lpMember 2 (fbase i))
    (q : ℕ × ℤ) : MeasureTheory.Lp ℂ 2 M.μ :=
  (orbitFunction_memLp M U fbase hf q).toLp (orbitFunction M U fbase q)

def spectrumVector
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (U : MeasureIntegerActionData M) (fbase : ℕ → M.X → ℂ)
    (hf : ∀ i, M.lpMember 2 (fbase i)) :
    SpectrumIndex → MeasureTheory.Lp ℂ 2 M.μ
  | none => Chapter02.CorrelationMean.oneLp M hM
  | some q => orbitLp M U fbase hf q

theorem integral_comp_measurePreserving
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : MeasureTheory.Measure X} {ν : MeasureTheory.Measure Y}
    (T : X → Y) (hT : MeasureTheory.MeasurePreserving T μ ν)
    (f : Y → ℂ) (hf : MeasureTheory.AEStronglyMeasurable f ν) :
    ∫ x, f (T x) ∂μ = ∫ y, f y ∂ν := by
  have hmap := MeasureTheory.integral_map hT.measurable.aemeasurable (by
    rw [hT.map_eq]
    exact hf)
  calc
    ∫ x, f (T x) ∂μ = ∫ y, f y ∂MeasureTheory.Measure.map T μ := hmap.symm
    _ = ∫ y, f y ∂ν := by rw [hT.map_eq]

theorem integral_orbitFunction
    (M : System.{u}) (U : MeasureIntegerActionData M)
    (fbase : ℕ → M.X → ℂ) (hf : ∀ i, M.lpMember 2 (fbase i))
    (hzero : ∀ i, ∫ x, fbase i x ∂M.μ = 0) (q : ℕ × ℤ) :
    ∫ x, orbitFunction M U fbase q x ∂M.μ = 0 := by
  rw [show (∫ x, orbitFunction M U fbase q x ∂M.μ) =
      ∫ x, fbase q.1 x ∂M.μ by
    exact integral_comp_measurePreserving (U.act q.2) (U.measure_preserving q.2)
      (fbase q.1) (hf q.1).1]
  exact hzero q.1

theorem inner_toLp_eq_l2Inner
    (M : System.{u}) (f g : M.X → ℂ)
    (hf : M.lpMember 2 f) (hg : M.lpMember 2 g) :
    @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (hf.toLp f) (hg.toLp g) =
      l2Inner M g f := by
  rw [MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [RCLike.inner_apply, hfx, hgx]
  simp only [starRingEnd_apply]

theorem spectrumVector_orthonormal
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (U : MeasureIntegerActionData M) (fbase : ℕ → M.X → ℂ)
    (hf : ∀ i, M.lpMember 2 (fbase i))
    (hzero : ∀ i, ∫ x, fbase i x ∂M.μ = 0)
    (horth : ∀ i j m n, l2Inner M
      (Chapter01.koopman (U.act m) (fbase i))
      (Chapter01.koopman (U.act n) (fbase j)) =
        if i = j ∧ m = n then 1 else 0) :
    Orthonormal ℂ (spectrumVector M hM U fbase hf) := by
  classical
  rw [orthonormal_iff_ite]
  intro p q
  cases p with
  | none =>
      cases q with
      | none =>
          letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
          change @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
              (Chapter02.CorrelationMean.oneLp M hM)
              (Chapter02.CorrelationMean.oneLp M hM) = 1
          rw [← Chapter02.CorrelationMean.integral_eq_inner_oneLp]
          unfold Chapter02.CorrelationMean.oneLp
          have hcoe := (MeasureTheory.memLp_const
            (μ := M.μ) (p := (2 : ENNReal)) (1 : ℂ)).coeFn_toLp
          rw [MeasureTheory.integral_congr_ae hcoe]
          simp
      | some q =>
          change @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
              (Chapter02.CorrelationMean.oneLp M hM)
              (orbitLp M U fbase hf q) = 0
          rw [← Chapter02.CorrelationMean.integral_eq_inner_oneLp]
          unfold orbitLp
          have hcoe := (orbitFunction_memLp M U fbase hf q).coeFn_toLp
          rw [MeasureTheory.integral_congr_ae hcoe]
          rw [integral_orbitFunction M U fbase hf hzero q]
  | some p =>
      cases q with
      | none =>
          change @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
              (orbitLp M U fbase hf p)
              (Chapter02.CorrelationMean.oneLp M hM) = 0
          calc
            @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
                (orbitLp M U fbase hf p)
                (Chapter02.CorrelationMean.oneLp M hM) =
              star (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
                (Chapter02.CorrelationMean.oneLp M hM)
                (orbitLp M U fbase hf p)) :=
                (inner_conj_symm (orbitLp M U fbase hf p)
                  (Chapter02.CorrelationMean.oneLp M hM)).symm
            _ = 0 := by
              rw [← Chapter02.CorrelationMean.integral_eq_inner_oneLp]
              unfold orbitLp
              have hcoe := (orbitFunction_memLp M U fbase hf p).coeFn_toLp
              rw [MeasureTheory.integral_congr_ae hcoe]
              rw [integral_orbitFunction M U fbase hf hzero p]
              simp
      | some q =>
          rw [show spectrumVector M hM U fbase hf (some p) =
              orbitLp M U fbase hf p by rfl,
            show spectrumVector M hM U fbase hf (some q) =
              orbitLp M U fbase hf q by rfl]
          unfold orbitLp
          rw [inner_toLp_eq_l2Inner M
            (orbitFunction M U fbase p) (orbitFunction M U fbase q)]
          unfold orbitFunction
          rw [horth q.1 p.1 q.2 p.2]
          simp [Prod.ext_iff, and_comm, eq_comm]

theorem spectrumVector_orthogonal_eq_bot
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (U : MeasureIntegerActionData M) (fbase : ℕ → M.X → ℂ)
    (hbasis : (∀ i, M.lpMember 2 (fbase i) ∧ ∫ x, fbase i x ∂M.μ = 0) ∧
      (∀ i j m n, l2Inner M
        (Chapter01.koopman (U.act m) (fbase i))
        (Chapter01.koopman (U.act n) (fbase j)) =
          if i = j ∧ m = n then 1 else 0) ∧
      IsTotalInZeroMeanL2 M
        {g | ∃ i n, g = Chapter01.koopman (U.act n) (fbase i)}) :
    (Submodule.span ℂ (Set.range
      (spectrumVector M hM U fbase (fun i => (hbasis.1 i).1))))ᗮ = ⊥ := by
  let v := spectrumVector M hM U fbase (fun i => (hbasis.1 i).1)
  let K := Submodule.span ℂ (Set.range v)
  apply le_antisymm
  · intro X hX
    rw [Submodule.mem_bot]
    have horthX (q : SpectrumIndex) :
        @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ X (v q) = 0 := by
      exact (K.mem_orthogonal' X).1 hX (v q)
        (Submodule.subset_span (Set.mem_range_self q))
    have hmean : ∫ x, X x ∂M.μ = 0 := by
      have hz := horthX none
      change @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ X
          (Chapter02.CorrelationMean.oneLp M hM) = 0 at hz
      calc
        ∫ x, X x ∂M.μ = @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
            (Chapter02.CorrelationMean.oneLp M hM) X :=
          Chapter02.CorrelationMean.integral_eq_inner_oneLp M hM X
        _ = 0 := inner_eq_zero_symm.mp hz
    by_contra hX0
    have hnorm : 0 < ‖X‖ := norm_pos_iff.mpr hX0
    let δ : ℝ := ‖X‖ / 2
    have hδ : 0 < δ := half_pos hnorm
    obtain ⟨s, hsV, c, hs⟩ := hbasis.2.2 (fun x => X x)
      (MeasureTheory.Lp.memLp X) hmean δ hδ
    choose is zs hreps using fun q : {q // q ∈ s} => hsV q.2
    let Yfun : M.X → ℂ := combination s c
    have hYLp : M.lpMember 2 Yfun := combination_memLp M s c (fun q hq => by
      obtain ⟨i, z, hqrep⟩ := hsV hq
      rw [hqrep]
      exact (hbasis.1 i).1.comp_measurePreserving (U.measure_preserving z))
    let Y : MeasureTheory.Lp ℂ 2 M.μ := hYLp.toLp Yfun
    let Z : MeasureTheory.Lp ℂ 2 M.μ :=
      ∑ q ∈ s.attach, c q.1 •
        orbitLp M U fbase (fun i => (hbasis.1 i).1) (is q, zs q)
    have hZmem : Z ∈ K := by
      apply Submodule.sum_mem
      intro q hq
      apply Submodule.smul_mem
      exact Submodule.subset_span
        (show orbitLp M U fbase (fun i => (hbasis.1 i).1) (is q, zs q) ∈
            Set.range v from ⟨some (is q, zs q), rfl⟩)
    have hZY : Z = Y := by
      apply MeasureTheory.Lp.ext
      have hsum :
          (((∑ q ∈ s.attach, c q.1 •
              orbitLp M U fbase (fun i => (hbasis.1 i).1) (is q, zs q)) :
              MeasureTheory.Lp ℂ 2 M.μ) : M.X → ℂ) =ᵐ[M.μ]
            fun x => ∑ q ∈ s.attach,
              ((c q.1 • orbitLp M U fbase (fun i => (hbasis.1 i).1)
                (is q, zs q) : MeasureTheory.Lp ℂ 2 M.μ) : M.X → ℂ) x := by
        let F : {q // q ∈ s} → MeasureTheory.Lp ℂ 2 M.μ := fun q =>
          c q.1 • orbitLp M U fbase (fun i => (hbasis.1 i).1) (is q, zs q)
        have haux (t : Finset {q // q ∈ s}) :
            (((∑ q ∈ t, F q) : MeasureTheory.Lp ℂ 2 M.μ) : M.X → ℂ) =ᵐ[M.μ]
              fun x => ∑ q ∈ t, (F q : M.X → ℂ) x := by
          induction t using Finset.induction_on with
          | empty =>
              simpa using (MeasureTheory.Lp.coeFn_zero ℂ (2 : ENNReal) M.μ)
          | @insert q t hqt ih =>
              filter_upwards [MeasureTheory.Lp.coeFn_add (F q) (∑ r ∈ t, F r), ih]
                with x hadd htail
              rw [Finset.sum_insert hqt, Finset.sum_insert hqt, hadd,
                Pi.add_apply, htail]
        simpa [F] using haux s.attach
      have hterms : ∀ q ∈ s.attach,
          ((c q.1 • orbitLp M U fbase (fun i => (hbasis.1 i).1)
              (is q, zs q) : MeasureTheory.Lp ℂ 2 M.μ) : M.X → ℂ) =ᵐ[M.μ]
            fun x => c q.1 * q.1 x := by
        intro q hq
        filter_upwards [MeasureTheory.Lp.coeFn_smul (c q.1)
            (orbitLp M U fbase (fun i => (hbasis.1 i).1) (is q, zs q)),
          (orbitFunction_memLp M U fbase (fun i => (hbasis.1 i).1)
            (is q, zs q)).coeFn_toLp] with x hsmul horbit
        rw [hsmul, Pi.smul_apply, smul_eq_mul]
        change c q.1 *
            ((orbitFunction_memLp M U fbase (fun i => (hbasis.1 i).1)
              (is q, zs q)).toLp (orbitFunction M U fbase (is q, zs q))) x = _
        rw [horbit]
        unfold orbitFunction
        rw [← hreps q]
      have hallAux (t : Finset {q // q ∈ s})
          (ht : ∀ q ∈ t,
            ((c q.1 • orbitLp M U fbase (fun i => (hbasis.1 i).1)
                (is q, zs q) : MeasureTheory.Lp ℂ 2 M.μ) : M.X → ℂ) =ᵐ[M.μ]
              fun x => c q.1 * q.1 x) :
          ∀ᶠ x in MeasureTheory.ae M.μ, ∀ q ∈ t,
            ((c q.1 • orbitLp M U fbase (fun i => (hbasis.1 i).1)
                (is q, zs q) : MeasureTheory.Lp ℂ 2 M.μ) : M.X → ℂ) x =
              c q.1 * q.1 x := by
        induction t using Finset.induction_on with
        | empty => simp
        | @insert q t hqt ih =>
            have hq := ht q (Finset.mem_insert_self q t)
            have ht' : ∀ r ∈ t,
                ((c r.1 • orbitLp M U fbase (fun i => (hbasis.1 i).1)
                    (is r, zs r) : MeasureTheory.Lp ℂ 2 M.μ) : M.X → ℂ) =ᵐ[M.μ]
                  fun x => c r.1 * r.1 x := fun r hr =>
              ht r (Finset.mem_insert_of_mem hr)
            filter_upwards [hq, ih ht'] with x hqx htx
            intro r hr
            rcases Finset.mem_insert.mp hr with rfl | hr
            · exact hqx
            · exact htx r hr
      have hall := hallAux s.attach hterms
      have hYcoe := hYLp.coeFn_toLp
      filter_upwards [hsum, hall, hYcoe] with x hsumx htermsx hYx
      change (Z : M.X → ℂ) x = (Y : M.X → ℂ) x
      rw [hsumx, hYx]
      calc
        ∑ q ∈ s.attach,
            ((c q.1 • orbitLp M U fbase (fun i => (hbasis.1 i).1)
              (is q, zs q) : MeasureTheory.Lp ℂ 2 M.μ) : M.X → ℂ) x =
          ∑ q ∈ s.attach, c q.1 * q.1 x := by
            apply Finset.sum_congr rfl
            intro q hq
            exact htermsx q hq
        _ = Yfun x := by
          change (∑ q ∈ s.attach, (fun g => c g * g x) q.1) =
            ∑ g ∈ s, c g * g x
          simpa only using (Finset.sum_attach s (fun g => c g * g x))
    have hYmem : Y ∈ K := by rw [← hZY]; exact hZmem
    have hXY : @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ X Y = 0 :=
      (K.mem_orthogonal' X).1 hX Y hYmem
    have hErrLp : M.lpMember 2 (fun x => X x - Yfun x) :=
      (MeasureTheory.Lp.memLp X).sub hYLp
    have hnormErr : ‖X - Y‖ < δ := by
      have hsub := (MeasureTheory.Lp.memLp X).toLp_sub hYLp
      rw [MeasureTheory.Lp.toLp_coeFn] at hsub
      have hsub' : hErrLp.toLp (fun x => X x - Yfun x) = X - Y := by
        simpa only [Pi.sub_apply] using hsub
      have hsR : (MeasureTheory.eLpNorm (fun x => X x - Yfun x) 2 M.μ).toReal < δ := by
        have ht := (ENNReal.toReal_lt_toReal hErrLp.2.ne (by simp)).mpr hs
        simpa [ENNReal.toReal_ofReal hδ.le] using ht
      calc
        ‖X - Y‖ = ‖hErrLp.toLp (fun x => X x - Yfun x)‖ :=
          congrArg norm hsub'.symm
        _ = (MeasureTheory.eLpNorm (fun x => X x - Yfun x) 2 M.μ).toReal :=
          MeasureTheory.Lp.norm_toLp _ hErrLp
        _ < δ := hsR
    have hinner : @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ X (X - Y) =
        @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ X X := by
      rw [inner_sub_right, hXY, sub_zero]
    have hbound :
        ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ X (X - Y)‖ ≤
          ‖X‖ * ‖X - Y‖ := norm_inner_le_norm X (X - Y)
    rw [hinner, inner_self_eq_norm_sq_to_K] at hbound
    rw [norm_pow, RCLike.norm_ofReal, abs_norm] at hbound
    have hnonneg : 0 ≤ ‖X - Y‖ := norm_nonneg _
    have hnormnonneg : 0 ≤ ‖X‖ := norm_nonneg _
    dsimp [δ] at hnormErr
    nlinarith
  · exact bot_le

def spectrumHilbertBasis
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (U : MeasureIntegerActionData M) (fbase : ℕ → M.X → ℂ)
    (hbasis : (∀ i, M.lpMember 2 (fbase i) ∧ ∫ x, fbase i x ∂M.μ = 0) ∧
      (∀ i j m n, l2Inner M
        (Chapter01.koopman (U.act m) (fbase i))
        (Chapter01.koopman (U.act n) (fbase j)) =
          if i = j ∧ m = n then 1 else 0) ∧
      IsTotalInZeroMeanL2 M
        {g | ∃ i n, g = Chapter01.koopman (U.act n) (fbase i)}) :
    HilbertBasis SpectrumIndex ℂ (MeasureTheory.Lp ℂ 2 M.μ) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (spectrumVector_orthonormal M hM U fbase
      (fun i => (hbasis.1 i).1) (fun i => (hbasis.1 i).2) hbasis.2.1)
    (spectrumVector_orthogonal_eq_bot M hM U fbase hbasis)

theorem spectrumHilbertBasis_apply
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (U : MeasureIntegerActionData M) (fbase : ℕ → M.X → ℂ)
    (hbasis : (∀ i, M.lpMember 2 (fbase i) ∧ ∫ x, fbase i x ∂M.μ = 0) ∧
      (∀ i j m n, l2Inner M
        (Chapter01.koopman (U.act m) (fbase i))
        (Chapter01.koopman (U.act n) (fbase j)) =
          if i = j ∧ m = n then 1 else 0) ∧
      IsTotalInZeroMeanL2 M
        {g | ∃ i n, g = Chapter01.koopman (U.act n) (fbase i)})
    (q : SpectrumIndex) :
    spectrumHilbertBasis M hM U fbase hbasis q =
      spectrumVector M hM U fbase (fun i => (hbasis.1 i).1) q := by
  unfold spectrumHilbertBasis
  rw [show (HilbertBasis.mkOfOrthogonalEqBot
      (spectrumVector_orthonormal M hM U fbase
        (fun i => (hbasis.1 i).1) (fun i => (hbasis.1 i).2) hbasis.2.1)
      (spectrumVector_orthogonal_eq_bot M hM U fbase hbasis) :
        SpectrumIndex → MeasureTheory.Lp ℂ 2 M.μ) =
      spectrumVector M hM U fbase (fun i => (hbasis.1 i).1) by
    exact HilbertBasis.coe_mkOfOrthogonalEqBot _ _]

end Chapter04.LebesgueSpectrum
