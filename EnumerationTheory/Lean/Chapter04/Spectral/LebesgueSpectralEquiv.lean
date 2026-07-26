import Chapter04.Spectral.LebesgueSpectralBasis

noncomputable section

open Classical

namespace Chapter04.LebesgueSpectrum

universe u

def spectralL2Equiv
    (M N : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (UM : MeasureIntegerActionData M) (UN : MeasureIntegerActionData N)
    (fM : ℕ → M.X → ℂ) (fN : ℕ → N.X → ℂ)
    (hBM : (∀ i, M.lpMember 2 (fM i) ∧ ∫ x, fM i x ∂M.μ = 0) ∧
      (∀ i j m n, l2Inner M
        (Chapter01.koopman (UM.act m) (fM i))
        (Chapter01.koopman (UM.act n) (fM j)) =
          if i = j ∧ m = n then 1 else 0) ∧
      IsTotalInZeroMeanL2 M
        {g | ∃ i n, g = Chapter01.koopman (UM.act n) (fM i)})
    (hBN : (∀ i, N.lpMember 2 (fN i) ∧ ∫ x, fN i x ∂N.μ = 0) ∧
      (∀ i j m n, l2Inner N
        (Chapter01.koopman (UN.act m) (fN i))
        (Chapter01.koopman (UN.act n) (fN j)) =
          if i = j ∧ m = n then 1 else 0) ∧
      IsTotalInZeroMeanL2 N
        {g | ∃ i n, g = Chapter01.koopman (UN.act n) (fN i)}) :
    MeasureTheory.Lp ℂ 2 N.μ ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
  (spectrumHilbertBasis N hN UN fN hBN).repr.trans
    (spectrumHilbertBasis M hM UM fM hBM).repr.symm

theorem spectralL2Equiv_basis
    (M N : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (UM : MeasureIntegerActionData M) (UN : MeasureIntegerActionData N)
    (fM : ℕ → M.X → ℂ) (fN : ℕ → N.X → ℂ)
    (hBM : (∀ i, M.lpMember 2 (fM i) ∧ ∫ x, fM i x ∂M.μ = 0) ∧
      (∀ i j m n, l2Inner M
        (Chapter01.koopman (UM.act m) (fM i))
        (Chapter01.koopman (UM.act n) (fM j)) =
          if i = j ∧ m = n then 1 else 0) ∧
      IsTotalInZeroMeanL2 M
        {g | ∃ i n, g = Chapter01.koopman (UM.act n) (fM i)})
    (hBN : (∀ i, N.lpMember 2 (fN i) ∧ ∫ x, fN i x ∂N.μ = 0) ∧
      (∀ i j m n, l2Inner N
        (Chapter01.koopman (UN.act m) (fN i))
        (Chapter01.koopman (UN.act n) (fN j)) =
          if i = j ∧ m = n then 1 else 0) ∧
      IsTotalInZeroMeanL2 N
        {g | ∃ i n, g = Chapter01.koopman (UN.act n) (fN i)})
    (q : SpectrumIndex) :
    spectralL2Equiv M N hM hN UM UN fM fN hBM hBN
        (spectrumVector N hN UN fN (fun i => (hBN.1 i).1) q) =
      spectrumVector M hM UM fM (fun i => (hBM.1 i).1) q := by
  rw [← spectrumHilbertBasis_apply N hN UN fN hBN q,
    ← spectrumHilbertBasis_apply M hM UM fM hBM q]
  unfold spectralL2Equiv
  change (spectrumHilbertBasis M hM UM fM hBM).repr.symm
      ((spectrumHilbertBasis N hN UN fN hBN).repr
        ((spectrumHilbertBasis N hN UN fN hBN) q)) =
    (spectrumHilbertBasis M hM UM fM hBM) q
  rw [HilbertBasis.repr_self, HilbertBasis.repr_symm_single]

def shiftSpectrumIndex : SpectrumIndex → SpectrumIndex
  | none => none
  | some q => some (q.1, q.2 + 1)

theorem koopmanOne_spectrumVector
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (U : MeasureIntegerActionData M) (fbase : ℕ → M.X → ℂ)
    (hf : ∀ i, M.lpMember 2 (fbase i)) (q : SpectrumIndex) :
    Chapter02.CorrelationMean.koopmanIterLp M hM 1
        (spectrumVector M hM U fbase hf q) =
      spectrumVector M hM U fbase hf (shiftSpectrumIndex q) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  cases q with
  | none =>
      apply MeasureTheory.Lp.ext
      have hcomp := MeasureTheory.Lp.coeFn_compMeasurePreserving
        (Chapter02.CorrelationMean.oneLp M hM) (hM.2.iterate 1)
      have hone := (MeasureTheory.memLp_const
        (μ := M.μ) (p := (2 : ENNReal)) (1 : ℂ)).coeFn_toLp
      filter_upwards [hcomp, hone,
        (hM.2.iterate 1).quasiMeasurePreserving.ae_eq_comp hone] with x hx honeX honeT
      change ((Chapter02.CorrelationMean.koopmanIterLp M hM 1
        (Chapter02.CorrelationMean.oneLp M hM) :
          MeasureTheory.Lp ℂ 2 M.μ) : M.X → ℂ) x =
        (Chapter02.CorrelationMean.oneLp M hM : M.X → ℂ) x
      have honeT' :
          (Chapter02.CorrelationMean.oneLp M hM : M.X → ℂ) ((M.T^[1]) x) = 1 := by
        change (Chapter02.CorrelationMean.oneLp M hM : M.X → ℂ) ((M.T^[1]) x) =
          (fun _ : M.X => (1 : ℂ)) ((M.T^[1]) x) at honeT
        exact honeT
      calc
        ((Chapter02.CorrelationMean.koopmanIterLp M hM 1
          (Chapter02.CorrelationMean.oneLp M hM) :
            MeasureTheory.Lp ℂ 2 M.μ) : M.X → ℂ) x =
            (Chapter02.CorrelationMean.oneLp M hM : M.X → ℂ) ((M.T^[1]) x) := by
              simpa [Chapter02.CorrelationMean.koopmanIterLp, Function.comp_apply] using hx
        _ = 1 := honeT'
        _ = (Chapter02.CorrelationMean.oneLp M hM : M.X → ℂ) x := honeX.symm
  | some q =>
      simp only [shiftSpectrumIndex]
      unfold spectrumVector orbitLp
      rw [Chapter02.CorrelationMean.koopmanIterLp_apply_toLp]
      apply MeasureTheory.Lp.ext
      have hleft :
          (((orbitFunction_memLp M U fbase hf q).comp_measurePreserving
            (hM.2.iterate 1)).toLp
              (fun x => orbitFunction M U fbase q ((M.T^[1]) x) ) :
                MeasureTheory.Lp ℂ 2 M.μ) =ᵐ[M.μ]
            fun x => orbitFunction M U fbase q ((M.T^[1]) x) := by
        simpa [Function.comp_def] using
          ((orbitFunction_memLp M U fbase hf q).comp_measurePreserving
            (hM.2.iterate 1)).coeFn_toLp
      have hright := (orbitFunction_memLp M U fbase hf (q.1, q.2 + 1)).coeFn_toLp
      filter_upwards [hleft, hright] with x hleftx hrightx
      rw [hleftx, hrightx]
      unfold orbitFunction Chapter01.koopman
      rw [show (M.T^[1]) x = M.T x by simp, ← U.one_act]
      have hadd := congrFun (U.add_act q.2 1) x
      exact congrArg (fbase q.1) hadd.symm

theorem spectralL2Equiv_intertwines
    (M N : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (UM : MeasureIntegerActionData M) (UN : MeasureIntegerActionData N)
    (fM : ℕ → M.X → ℂ) (fN : ℕ → N.X → ℂ)
    (hBM : (∀ i, M.lpMember 2 (fM i) ∧ ∫ x, fM i x ∂M.μ = 0) ∧
      (∀ i j m n, l2Inner M
        (Chapter01.koopman (UM.act m) (fM i))
        (Chapter01.koopman (UM.act n) (fM j)) =
          if i = j ∧ m = n then 1 else 0) ∧
      IsTotalInZeroMeanL2 M
        {g | ∃ i n, g = Chapter01.koopman (UM.act n) (fM i)})
    (hBN : (∀ i, N.lpMember 2 (fN i) ∧ ∫ x, fN i x ∂N.μ = 0) ∧
      (∀ i j m n, l2Inner N
        (Chapter01.koopman (UN.act m) (fN i))
        (Chapter01.koopman (UN.act n) (fN j)) =
          if i = j ∧ m = n then 1 else 0) ∧
      IsTotalInZeroMeanL2 N
        {g | ∃ i n, g = Chapter01.koopman (UN.act n) (fN i)})
    (F : MeasureTheory.Lp ℂ 2 N.μ) :
    spectralL2Equiv M N hM hN UM UN fM fN hBM hBN
        (Chapter02.CorrelationMean.koopmanIterLp N hN 1 F) =
      Chapter02.CorrelationMean.koopmanIterLp M hM 1
        (spectralL2Equiv M N hM hN UM UN fM fN hBM hBN F) := by
  let E := spectralL2Equiv M N hM hN UM UN fM fN hBM hBN
  let KN := Chapter02.CorrelationMean.koopmanIterLp N hN 1
  let KM := Chapter02.CorrelationMean.koopmanIterLp M hM 1
  let L : MeasureTheory.Lp ℂ 2 N.μ →L[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
    E.toContinuousLinearEquiv.toContinuousLinearMap.comp KN.toContinuousLinearMap
  let R : MeasureTheory.Lp ℂ 2 N.μ →L[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
    KM.toContinuousLinearMap.comp E.toContinuousLinearEquiv.toContinuousLinearMap
  have hdense : Dense (Submodule.span ℂ
      (Set.range (spectrumVector N hN UN fN (fun i => (hBN.1 i).1))) :
        Set (MeasureTheory.Lp ℂ 2 N.μ)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    have hrange : Set.range (spectrumVector N hN UN fN (fun i => (hBN.1 i).1)) =
        Set.range (spectrumHilbertBasis N hN UN fN hBN) := by
      congr 1
      funext q
      exact (spectrumHilbertBasis_apply N hN UN fN hBN q).symm
    rw [hrange]
    exact (spectrumHilbertBasis N hN UN fN hBN).dense_span
  have hLR : L = R := by
    apply ContinuousLinearMap.ext_on hdense
    rintro X ⟨q, rfl⟩
    change E (KN (spectrumVector N hN UN fN (fun i => (hBN.1 i).1) q)) =
      KM (E (spectrumVector N hN UN fN (fun i => (hBN.1 i).1) q))
    rw [koopmanOne_spectrumVector N hN UN fN (fun i => (hBN.1 i).1),
      spectralL2Equiv_basis M N hM hN UM UN fM fN hBM hBN,
      spectralL2Equiv_basis M N hM hN UM UN fM fN hBM hBN,
      koopmanOne_spectrumVector M hM UM fM (fun i => (hBM.1 i).1)]
  have happ := congrArg (fun T : MeasureTheory.Lp ℂ 2 N.μ →L[ℂ]
      MeasureTheory.Lp ℂ 2 M.μ => T F) hLR
  simpa [L, R, E, KN, KM] using happ

end Chapter04.LebesgueSpectrum
