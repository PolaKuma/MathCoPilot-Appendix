import Chapter04.Spectral.LebesgueSpectralEquiv

noncomputable section

open Classical

namespace Chapter04.LebesgueSpectrum

universe u

def rawSpectralMap
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
    (f : N.X → ℂ) : M.X → ℂ :=
  if hf : N.lpMember 2 f then
    fun x => spectralL2Equiv M N hM hN UM UN fM fN hBM hBN (hf.toLp f) x
  else 0

theorem rawSpectralMap_isIntertwiner
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
    IsSpectralIntertwinerFor M N
      (rawSpectralMap M N hM hN UM UN fM fN hBM hBN) := by
  let E := spectralL2Equiv M N hM hN UM UN fM fN hBM hBN
  let W := rawSpectralMap M N hM hN UM UN fM fN hBM hBN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g hf hg hfg
    have hLp : hf.toLp f = hg.toLp g := (hf.toLp_eq_toLp_iff hg).2 hfg
    simp only [rawSpectralMap, dif_pos hf, dif_pos hg]
    rw [hLp]
  · intro f g hf hg
    have hfg : N.lpMember 2 (fun y => f y + g y) := by
      simpa only [Pi.add_apply] using hf.add hg
    simp only [rawSpectralMap, dif_pos hf, dif_pos hg, dif_pos hfg]
    have hto : hfg.toLp (fun y => f y + g y) = hf.toLp f + hg.toLp g := by
      simpa only [Pi.add_apply] using hf.toLp_add hg
    rw [hto, map_add]
    exact MeasureTheory.Lp.coeFn_add (E (hf.toLp f)) (E (hg.toLp g))
  · intro c f hf
    have hcf : N.lpMember 2 (fun y => c * f y) := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hf.const_smul c
    simp only [rawSpectralMap, dif_pos hf, dif_pos hcf]
    have hto : hcf.toLp (fun y => c * f y) = c • hf.toLp f := by
      simpa only [Pi.smul_apply, smul_eq_mul] using
        MeasureTheory.MemLp.toLp_const_smul c hf
    rw [hto, map_smul]
    exact MeasureTheory.Lp.coeFn_smul c (E (hf.toLp f))
  · intro f hf
    simp only [rawSpectralMap, dif_pos hf]
    let F := E (hf.toLp f)
    refine ⟨MeasureTheory.Lp.memLp F, ?_⟩
    calc
      MeasureTheory.eLpNorm (fun x => F x) 2 M.μ = ‖F‖ₑ :=
        (MeasureTheory.Lp.enorm_def F).symm
      _ = ‖hf.toLp f‖ₑ := by
        rw [enorm_eq_nnnorm, E.nnnorm_map, ← enorm_eq_nnnorm]
      _ = MeasureTheory.eLpNorm f 2 N.μ := MeasureTheory.Lp.enorm_toLp hf
  · intro h hh ε hε
    let H : MeasureTheory.Lp ℂ 2 M.μ := hh.toLp h
    let F : MeasureTheory.Lp ℂ 2 N.μ := E.symm H
    let f : N.X → ℂ := fun x => F x
    have hf : N.lpMember 2 f := MeasureTheory.Lp.memLp F
    refine ⟨f, hf, ?_⟩
    have hW : W f =ᵐ[M.μ] h := by
      simp only [W, rawSpectralMap, dif_pos hf]
      have hto : hf.toLp f = F := MeasureTheory.Lp.toLp_coeFn F hf
      rw [hto]
      change (fun x => E F x) =ᵐ[M.μ] h
      rw [show E F = H by simp [F]]
      exact hh.coeFn_toLp
    have hz : MeasureTheory.eLpNorm (fun x => h x - W f x) 2 M.μ = 0 := by
      calc
        MeasureTheory.eLpNorm (fun x => h x - W f x) 2 M.μ =
            MeasureTheory.eLpNorm (0 : M.X → ℂ) 2 M.μ :=
          MeasureTheory.eLpNorm_congr_ae (by
            filter_upwards [hW] with x hx
            rw [hx, sub_self]
            rfl)
        _ = 0 := MeasureTheory.eLpNorm_zero
    rw [hz]
    exact ENNReal.ofReal_pos.mpr hε
  · intro f hf
    have hk : N.lpMember 2 (Chapter01.koopman N.T f) :=
      hf.comp_measurePreserving hN.2
    simp only [rawSpectralMap, dif_pos hf, dif_pos hk]
    have hE := spectralL2Equiv_intertwines M N hM hN UM UN fM fN hBM hBN
      (hf.toLp f)
    have hNto := Chapter02.CorrelationMean.koopmanIterLp_apply_toLp N hN 1 f hf
    have hMcoe := MeasureTheory.Lp.coeFn_compMeasurePreserving
      (E (hf.toLp f)) (hM.2.iterate 1)
    filter_upwards [hMcoe] with x hMx
    change E (hk.toLp (Chapter01.koopman N.T f)) x =
      E (hf.toLp f) (M.T x)
    have hkEq : hk.toLp (Chapter01.koopman N.T f) =
        Chapter02.CorrelationMean.koopmanIterLp N hN 1 (hf.toLp f) := by
      rw [hNto]
      apply MeasureTheory.Lp.ext
      filter_upwards [hk.coeFn_toLp,
        ((hf.comp_measurePreserving (hN.2.iterate 1)).coeFn_toLp)] with y hy hk1y
      rw [hy]
      simpa [Chapter01.koopman, Function.comp_def] using hk1y.symm
    rw [hkEq, hE]
    simpa [Chapter02.CorrelationMean.koopmanIterLp, Function.comp_apply] using hMx

theorem countableLebesgueSpectrum_spectrallyIsomorphic
    (M N : System.{u})
    (hSM : HasCountableLebesgueSpectrum M)
    (hSN : HasCountableLebesgueSpectrum N) :
    IsSpectrallyIsomorphic M N := by
  rcases hSM with ⟨hLebM, _hInvM, UM, fM, hBM⟩
  rcases hSN with ⟨hLebN, _hInvN, UN, fN, hBN⟩
  have hM : Chapter01.IsMeasurePreservingSystem M := by
    refine ⟨hLebM.1, ?_⟩
    simpa [UM.one_act] using UM.measure_preserving 1
  have hN : Chapter01.IsMeasurePreservingSystem N := by
    refine ⟨hLebN.1, ?_⟩
    simpa [UN.one_act] using UN.measure_preserving 1
  exact ⟨rawSpectralMap M N hM hN UM UN fM fN hBM hBN,
    rawSpectralMap_isIntertwiner M N hM hN UM UN fM fN hBM hBN⟩

end Chapter04.LebesgueSpectrum
