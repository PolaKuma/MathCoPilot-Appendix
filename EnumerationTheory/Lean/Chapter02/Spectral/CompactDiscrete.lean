import Chapter02.Spectral.AlmostPeriodic
import Chapter02.Spectral.WeakSpectrum

noncomputable section

open Classical Filter MeasureTheory
open scoped BigOperators ENNReal

namespace Chapter02.CompactDiscrete

universe u

lemma almostPeriodicFunction_to_vector (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : IsAlmostPeriodicFunction M f) :
    IsAlmostPeriodicVector (WeakSpectrum.koopmanData M hM) (hf.1.toLp f) := by
  intro ε hε
  obtain ⟨inv, hleft, hright, horbit⟩ := hf.2
  obtain ⟨F, hFLp, hF⟩ := horbit ε hε
  let toV : (M.X → ℂ) → MeasureTheory.Lp ℂ 2 M.μ :=
    fun g => if hg : M.lpMember 2 g then hg.toLp g else 0
  refine ⟨F.image toV, ?_⟩
  intro n
  obtain ⟨g, hgF, hdist⟩ := hF (n : ℤ)
  have hg : M.lpMember 2 g := hFLp g hgF
  refine ⟨hg.toLp g, Finset.mem_image.mpr ⟨g, hgF, by simp [toV, hg]⟩, ?_⟩
  have hcomp : ((WeakSpectrum.koopmanData M hM).U^[n]) (hf.1.toLp f) =
      (hf.1.comp_measurePreserving (hM.2.iterate n)).toLp
        (fun x => f ((M.T^[n]) x)) := by
    rw [WeakSpectrum.koopmanData_iter_eq_koopmanIterLp]
    exact CorrelationMean.koopmanIterLp_apply_toLp M hM n f hf.1
  rw [hcomp]
  have hsub := (hf.1.comp_measurePreserving (hM.2.iterate n)).sub hg
  have hnorm :
      ‖(hf.1.comp_measurePreserving (hM.2.iterate n)).toLp
          (fun x => f ((M.T^[n]) x)) - hg.toLp g‖ =
        (eLpNorm (fun x => f ((M.T^[n]) x) - g x) 2 M.μ).toReal := by
    have hto : hsub.toLp (fun x => f ((M.T^[n]) x) - g x) =
        (hf.1.comp_measurePreserving (hM.2.iterate n)).toLp
          (fun x => f ((M.T^[n]) x)) - hg.toLp g := by
      simpa only [Function.comp_apply] using
        MemLp.toLp_sub (hf.1.comp_measurePreserving (hM.2.iterate n)) hg
    rw [← hto, MeasureTheory.Lp.norm_toLp]
  rw [hnorm]
  have hdist' : eLpNorm (fun x => f ((M.T^[n]) x) - g x) 2 M.μ <
      ENNReal.ofReal ε := by
    simpa using hdist
  have htop : eLpNorm (fun x => f ((M.T^[n]) x) - g x) 2 M.μ ≠ ⊤ :=
    ne_top_of_lt hdist'
  have hof : ENNReal.ofReal ε ≠ ⊤ := by simp
  have := ENNReal.toReal_lt_toReal htop hof |>.mpr hdist'
  simpa [ENNReal.toReal_ofReal hε.le] using this

lemma discreteVector_to_rawEigenApprox (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (X : MeasureTheory.Lp ℂ 2 M.μ)
    (hX : InDiscreteSpectralSubspace (WeakSpectrum.koopmanData M hM) X)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : Finset (M.X → ℂ),
      (∀ g ∈ t, ∃ lam : ℂ, Eigenfunction M lam g) ∧
      ∃ d : (M.X → ℂ) → ℂ,
        eLpNorm (fun x => X x - ∑ g ∈ t, d g * g x) 2 M.μ < ENNReal.ofReal ε := by
  obtain ⟨(s : Finset (MeasureTheory.Lp ℂ 2 M.μ)), hs, c, happrox⟩ := hX ε hε
  let q : (MeasureTheory.Lp ℂ 2 M.μ) → (M.X → ℂ) := fun Y x => Y x
  have hqinj : Function.Injective q := by
    intro Y Z hYZ
    apply MeasureTheory.Lp.ext
    exact Filter.Eventually.of_forall (congrFun hYZ)
  let t : Finset (M.X → ℂ) := s.image q
  let d : (M.X → ℂ) → ℂ := fun g => c (Function.invFun q g)
  have hsum (x : M.X) :
      ∑ g ∈ t, d g * g x = ∑ Y ∈ s, c Y * Y x := by
    dsimp only [t, d]
    rw [Finset.sum_image hqinj.injOn]
    apply Finset.sum_congr rfl
    intro Y hYs
    rw [Function.leftInverse_invFun hqinj]
  refine ⟨t, ?_, d, ?_⟩
  · intro g hg
    obtain ⟨Y, hYs, rfl⟩ := Finset.mem_image.mp hg
    exact WeakSpectrum.eigenvector_to_eigenfunction M hM Y (hs Y hYs)
  · have hterm (g : M.X → ℂ) (hg : g ∈ t) :
        M.lpMember 2 (fun x => d g * g x) := by
      obtain ⟨Y, hYs, rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨lam, heig⟩ :=
        WeakSpectrum.eigenvector_to_eigenfunction M hM Y (hs Y hYs)
      exact heig.1.const_mul (d (q Y))
    have hall (u : Finset (M.X → ℂ))
        (hu : ∀ g ∈ u, M.lpMember 2 (fun x => d g * g x)) :
        M.lpMember 2 (fun x => ∑ g ∈ u, d g * g x) := by
      induction u using Finset.induction_on with
      | empty =>
          convert (MemLp.zero' : MemLp (fun _ : M.X => (0 : ℂ)) 2 M.μ) using 1
      | @insert g u hgu ih =>
          have hgm := hu g (Finset.mem_insert_self _ _)
          have hut : ∀ z ∈ u, M.lpMember 2 (fun x => d z * z x) := by
            intro z hz
            exact hu z (Finset.mem_insert_of_mem hz)
          simpa [Finset.sum_insert hgu] using hgm.add (ih hut)
    have hraw : M.lpMember 2 (fun x => ∑ g ∈ t, d g * g x) := hall t hterm
    have hsub : M.lpMember 2
        (fun x => X x - ∑ g ∈ t, d g * g x) := (MeasureTheory.Lp.memLp X).sub hraw
    have hnorm :
        (eLpNorm (fun x => X x - ∑ g ∈ t, d g * g x) 2 M.μ).toReal =
          ‖X - ∑ Y ∈ s, c Y • Y‖ := by
      rw [← MeasureTheory.Lp.norm_toLp _ hsub]
      congr 1
      apply MeasureTheory.Lp.ext
      have hsumcoe (u : Finset (MeasureTheory.Lp ℂ 2 M.μ)) :
          ∀ᵐ x ∂M.μ,
            (((∑ Y ∈ u, c Y • Y : MeasureTheory.Lp ℂ 2 M.μ) :
              M.X → ℂ) x) = ∑ Y ∈ u, c Y * Y x := by
        induction u using Finset.induction_on with
        | empty => exact MeasureTheory.Lp.coeFn_zero ℂ 2 M.μ
        | @insert Y u hYu ih =>
            filter_upwards [MeasureTheory.Lp.coeFn_add (c Y • Y)
              (∑ Z ∈ u, c Z • Z), MeasureTheory.Lp.coeFn_smul (c Y) Y,
              ih] with x hadd hsmul htail
            rw [Finset.sum_insert hYu, Finset.sum_insert hYu, hadd]
            change ((c Y • Y : MeasureTheory.Lp ℂ 2 M.μ) : M.X → ℂ) x +
              (((∑ Z ∈ u, c Z • Z : MeasureTheory.Lp ℂ 2 M.μ) : M.X → ℂ) x) = _
            rw [hsmul, htail]
            simp
      filter_upwards [hsub.coeFn_toLp, MeasureTheory.Lp.coeFn_sub X
        (∑ Y ∈ s, c Y • Y), hsumcoe s] with x hx hxy hsumx
      rw [hx, hxy]
      simp only [Pi.sub_apply]
      congr 1
      rw [hsum]
      exact hsumx.symm
    have hreal :
        (eLpNorm (fun x => X x - ∑ g ∈ t, d g * g x) 2 M.μ).toReal < ε := by
      rw [hnorm]
      exact happrox
    apply (ENNReal.toReal_lt_toReal (by exact hsub.eLpNorm_ne_top)
      (by simp)).mp
    simpa [ENNReal.toReal_ofReal hε.le] using hreal

lemma compactFunctions_imply_discreteSpectrum (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hInv : Chapter01.IsInvertibleMeasurePreservingMap M.𝓧 M.μ M.𝓧 M.μ M.T)
    (hcompact : IsCompactSystem M) : HasDiscreteSpectrum M := by
  intro f hf ε hε
  obtain ⟨g, hgAP, hfg⟩ := hcompact f hf (ε / 3) (by positivity)
  have hD := WeakSpectrum.koopmanData_unitary M hM hInv
  have hgvec : IsAlmostPeriodicVector (WeakSpectrum.koopmanData M hM)
      (hgAP.1.toLp g) := almostPeriodicFunction_to_vector M hM g hgAP
  have hgdisc : InDiscreteSpectralSubspace (WeakSpectrum.koopmanData M hM)
      (hgAP.1.toLp g) :=
    (AlmostPeriodic.almostPeriodicVector (WeakSpectrum.koopmanData M hM) hD
      (hgAP.1.toLp g)).mp hgvec
  obtain ⟨t, ht, d, hgt⟩ := discreteVector_to_rawEigenApprox M hM
    (hgAP.1.toLp g) hgdisc (ε / 3) (by positivity)
  refine ⟨t, ht, d, ?_⟩
  have htLp : M.lpMember 2 (fun x => ∑ h ∈ t, d h * h x) := by
    have hterm (h : M.X → ℂ) (hh : h ∈ t) :
        M.lpMember 2 (fun x => d h * h x) := by
      obtain ⟨lam, heig⟩ := ht h hh
      exact heig.1.const_mul (d h)
    have hall (u : Finset (M.X → ℂ))
        (hu : ∀ h ∈ u, M.lpMember 2 (fun x => d h * h x)) :
        M.lpMember 2 (fun x => ∑ h ∈ u, d h * h x) := by
      induction u using Finset.induction_on with
      | empty =>
          convert (MemLp.zero' : MemLp (fun _ : M.X => (0 : ℂ)) 2 M.μ) using 1
      | @insert h u hhu ih =>
          simpa [Finset.sum_insert hhu] using
            (hu h (Finset.mem_insert_self _ _)).add
              (ih (fun z hz => hu z (Finset.mem_insert_of_mem hz)))
    exact hall t hterm
  have htri :
      eLpNorm (fun x => f x - ∑ h ∈ t, d h * h x) 2 M.μ ≤
        eLpNorm (fun x => f x - g x) 2 M.μ +
        eLpNorm (fun x => g x - ∑ h ∈ t, d h * h x) 2 M.μ := by
    rw [show (fun x => f x - ∑ h ∈ t, d h * h x) =
        fun x => (f x - g x) + (g x - ∑ h ∈ t, d h * h x) by
      funext x
      ring]
    exact eLpNorm_add_le (hf.sub hgAP.1).1 (hgAP.1.sub htLp).1 (by norm_num)
  have hgt' :
      eLpNorm (fun x => g x - ∑ h ∈ t, d h * h x) 2 M.μ <
        ENNReal.ofReal (ε / 3) := by
    apply lt_of_eq_of_lt (eLpNorm_congr_ae ?_) hgt
    filter_upwards [hgAP.1.coeFn_toLp] with x hx
    rw [hx]
  calc
    eLpNorm (fun x => f x - ∑ h ∈ t, d h * h x) 2 M.μ
        ≤ eLpNorm (fun x => f x - g x) 2 M.μ +
          eLpNorm (fun x => g x - ∑ h ∈ t, d h * h x) 2 M.μ := htri
    _ < ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) :=
      ENNReal.add_lt_add hfg hgt'
    _ < ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)

lemma eigenfunction_forward_iter_ae (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (lam : ℂ) (hf : Eigenfunction M lam f) (n : ℕ) :
    (fun x => f ((M.T^[n]) x)) =ᵐ[M.μ] fun x => lam ^ n * f x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have heigN := (hM.2.iterate n).quasiMeasurePreserving.ae_eq_comp hf.2.2
      filter_upwards [heigN, ih] with x hx hix
      rw [Function.iterate_succ_apply']
      change f (M.T ((M.T^[n]) x)) = lam * f ((M.T^[n]) x) at hx
      rw [hx, hix, pow_succ]
      ring

lemma eigenfunction_inverse_ae (M : System.{u})
    (_hM : Chapter01.IsMeasurePreservingSystem M)
    (S : M.X → M.X) (hS : MeasurePreserving S M.μ M.μ)
    (hright : Function.RightInverse S M.T)
    (f : M.X → ℂ) (lam : ℂ) (hf : Eigenfunction M lam f)
    (hlam : lam ≠ 0) :
    (fun x => f (S x)) =ᵐ[M.μ] fun x => lam⁻¹ * f x := by
  have heigS := hS.quasiMeasurePreserving.ae_eq_comp hf.2.2
  filter_upwards [heigS] with x hx
  change f (M.T (S x)) = lam * f (S x) at hx
  rw [hright x] at hx
  calc
    f (S x) = lam⁻¹ * (lam * f (S x)) := by field_simp
    _ = lam⁻¹ * f x := by rw [← hx]

lemma eigenfunction_inverse_iter_ae (M : System.{u})
    (S : M.X → M.X) (hS : MeasurePreserving S M.μ M.μ)
    (f : M.X → ℂ) (lam : ℂ)
    (hone : (fun x => f (S x)) =ᵐ[M.μ] fun x => lam⁻¹ * f x)
    (n : ℕ) :
    (fun x => f ((S^[n]) x)) =ᵐ[M.μ] fun x => lam⁻¹ ^ n * f x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have honeN := (hS.iterate n).quasiMeasurePreserving.ae_eq_comp hone
      filter_upwards [honeN, ih] with x hx hix
      rw [Function.iterate_succ_apply']
      change f (S ((S^[n]) x)) = lam⁻¹ * f ((S^[n]) x) at hx
      rw [hx, hix, pow_succ]
      ring

lemma eigenfunction_to_eigenvector_eq (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (lam : ℂ) (hf : Eigenfunction M lam f) :
    (WeakSpectrum.koopmanData M hM).U (hf.1.toLp f) = lam • hf.1.toLp f := by
  rw [WeakSpectrum.koopmanData_apply_toLp]
  apply MeasureTheory.Lp.ext
  filter_upwards [(hf.1.comp_measurePreserving hM.2).coeFn_toLp,
    MeasureTheory.Lp.coeFn_smul lam (hf.1.toLp f), hf.1.coeFn_toLp,
    hf.2.2] with x hcomp hsmul hcoe heig
  change ((hf.1.comp_measurePreserving hM.2).toLp (f ∘ M.T) : M.X → ℂ) x = _
  rw [hcomp, hsmul]
  change f (M.T x) = lam * ((hf.1.toLp f : M.X → ℂ) x)
  rw [hcoe]
  exact heig

lemma finiteEigenfunctionCombination_almostPeriodic (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hInv : Chapter01.IsInvertibleMeasurePreservingMap M.𝓧 M.μ M.𝓧 M.μ M.T)
    (s : Finset (M.X → ℂ))
    (hs : ∀ g ∈ s, ∃ lam : ℂ, Eigenfunction M lam g)
    (c : (M.X → ℂ) → ℂ) :
    IsAlmostPeriodicFunction M (fun x => ∑ g ∈ s, c g * g x) := by
  obtain ⟨S, _hTmap, hSmap, hleft, hright⟩ := hInv
  let hS : MeasurePreserving S M.μ M.μ :=
    WeakSpectrum.measurePreserving_of_project_map M S hSmap
  let lam : (g : s) → ℂ := fun g => Classical.choose (hs g.1 g.2)
  have hlam (g : s) : Eigenfunction M (lam g) g.1 :=
    Classical.choose_spec (hs g.1 g.2)
  have hlam0 (g : s) : lam g ≠ 0 := by
    have hv := WeakSpectrum.eigenfunction_to_eigenvector M hM (lam g) g.1 (hlam g)
    have hn := SpectralWiener.eigenvalue_norm_one (WeakSpectrum.koopmanData M hM)
      (WeakSpectrum.koopmanData_unitary M hM ⟨S, _hTmap, hSmap, hleft, hright⟩)
      ((hlam g).1.toLp g.1) hv.1 (lam g)
      (eigenfunction_to_eigenvector_eq M hM g.1 (lam g) (hlam g))
    intro hz
    simp [hz] at hn
  have hlamNorm (g : s) : ‖lam g‖ = 1 :=
    SpectralWiener.eigenvalue_norm_one (WeakSpectrum.koopmanData M hM)
      (WeakSpectrum.koopmanData_unitary M hM ⟨S, _hTmap, hSmap, hleft, hright⟩)
      ((hlam g).1.toLp g.1)
      (WeakSpectrum.eigenfunction_to_eigenvector M hM (lam g) g.1 (hlam g)).1
      (lam g) (eigenfunction_to_eigenvector_eq M hM g.1 (lam g) (hlam g))
  let e : (g : s) → Circle := fun g =>
    ⟨lam g, mem_sphere_zero_iff_norm.mpr (hlamNorm g)⟩
  let Φ : (s → Circle) → MeasureTheory.Lp ℂ 2 M.μ := fun q =>
    ∑ g : s, ((((q g : Circle) : ℂ) * c g.1) • (hlam g).1.toLp g.1)
  have hΦ : Continuous Φ := by
    dsimp [Φ]
    fun_prop
  have hcompact : IsCompact (Set.range Φ) := isCompact_range hΦ
  have hzLp : M.lpMember 2 (fun x => ∑ g ∈ s, c g * g x) := by
    have hterm (g : M.X → ℂ) (hg : g ∈ s) :
        M.lpMember 2 (fun x => c g * g x) := by
      obtain ⟨a, ha⟩ := hs g hg
      exact ha.1.const_mul (c g)
    have hall (u : Finset (M.X → ℂ))
        (hu : ∀ g ∈ u, M.lpMember 2 (fun x => c g * g x)) :
        M.lpMember 2 (fun x => ∑ g ∈ u, c g * g x) := by
      induction u using Finset.induction_on with
      | empty =>
          convert (MemLp.zero' : MemLp (fun _ : M.X => (0 : ℂ)) 2 M.μ) using 1
      | @insert g t hgt ih =>
          simpa [Finset.sum_insert hgt] using
            (hu g (Finset.mem_insert_self _ _)).add
              (ih (fun z hz => hu z (Finset.mem_insert_of_mem hz)))
    exact hall s hterm
  refine ⟨hzLp, S, hleft, hright, ?_⟩
  intro ε hε
  obtain ⟨t, htfin, htcover⟩ :=
    Metric.totallyBounded_iff.mp hcompact.totallyBounded ε hε
  let raw : MeasureTheory.Lp ℂ 2 M.μ → (M.X → ℂ) := fun Y x => Y x
  refine ⟨htfin.toFinset.image raw, ?_, ?_⟩
  · intro y hy
    obtain ⟨Y, _hY, rfl⟩ := Finset.mem_image.mp hy
    exact MeasureTheory.Lp.memLp Y
  · intro n
    let q : s → Circle := fun g =>
      if 0 ≤ n then e g ^ n.toNat else (e g)⁻¹ ^ n.natAbs
    have hmem : Φ q ∈ Set.range Φ := ⟨q, rfl⟩
    have hcover := htcover hmem
    simp only [Set.mem_iUnion, Metric.mem_ball] at hcover
    obtain ⟨Y, hYt, hdist⟩ := hcover
    refine ⟨raw Y, Finset.mem_image.mpr
      ⟨Y, (Set.Finite.mem_toFinset htfin).2 hYt, rfl⟩, ?_⟩
    have horbit :
        (fun x => (∑ g ∈ s, c g * g
          ((if 0 ≤ n then M.T^[n.toNat] else S^[n.natAbs]) x))) =ᵐ[M.μ]
          fun x => (Φ q : M.X → ℂ) x := by
      have hterm (g : s) :
          (fun x => c g.1 * g.1
            ((if 0 ≤ n then M.T^[n.toNat] else S^[n.natAbs]) x)) =ᵐ[M.μ]
          fun x => ((((q g : Circle) : ℂ) * c g.1) * g.1 x) := by
        by_cases hn : 0 ≤ n
        · have hi := eigenfunction_forward_iter_ae M hM g.1 (lam g) (hlam g) n.toNat
          filter_upwards [hi] with x hx
          simp only [hn, if_pos, q, e]
          rw [hx]
          change c g.1 * (lam g ^ n.toNat * g.1 x) =
            (lam g ^ n.toNat * c g.1) * g.1 x
          ring
        · have hi := eigenfunction_inverse_iter_ae M S hS g.1 (lam g)
            (eigenfunction_inverse_ae M hM S hS hright g.1 (lam g) (hlam g)
              (hlam0 g)) n.natAbs
          filter_upwards [hi] with x hx
          simp only [q, e]
          rw [if_neg hn, if_neg hn, hx]
          change c g.1 * ((lam g)⁻¹ ^ n.natAbs * g.1 x) =
            ((lam g)⁻¹ ^ n.natAbs * c g.1) * g.1 x
          ring
      have hsum (u : Finset s) :
          (fun x => ∑ g ∈ u, c g.1 * g.1
            ((if 0 ≤ n then M.T^[n.toNat] else S^[n.natAbs]) x)) =ᵐ[M.μ]
          fun x => ∑ g ∈ u, ((((q g : Circle) : ℂ) * c g.1) * g.1 x) := by
        induction u using Finset.induction_on with
        | empty => simp
        | @insert g u hgu ih =>
            filter_upwards [hterm g, ih] with x hgx hux
            simp only [Finset.sum_insert hgu]
            rw [hgx, hux]
      have hΦcoe :
          (fun x => (Φ q : M.X → ℂ) x) =ᵐ[M.μ]
          fun x => ∑ g : s, ((((q g : Circle) : ℂ) * c g.1) * g.1 x) := by
        dsimp only [Φ]
        have hcoe (u : Finset s) :
            ∀ᵐ x ∂M.μ,
              (((∑ g ∈ u, ((((q g : Circle) : ℂ) * c g.1) •
                (hlam g).1.toLp g.1) : MeasureTheory.Lp ℂ 2 M.μ) : M.X → ℂ) x) =
                ∑ g ∈ u, ((((q g : Circle) : ℂ) * c g.1) * g.1 x) := by
          induction u using Finset.induction_on with
          | empty => exact MeasureTheory.Lp.coeFn_zero ℂ 2 M.μ
          | @insert g u hgu ih =>
              let a : ℂ := (((q g : Circle) : ℂ) * c g.1)
              filter_upwards [MeasureTheory.Lp.coeFn_add
                (a • (hlam g).1.toLp g.1)
                (∑ z ∈ u, ((((q z : Circle) : ℂ) * c z.1) •
                  (hlam z).1.toLp z.1)),
                MeasureTheory.Lp.coeFn_smul a ((hlam g).1.toLp g.1),
                (hlam g).1.coeFn_toLp, ih] with
                  x hadd hsmul hgcoe hucoe
              rw [Finset.sum_insert hgu, Finset.sum_insert hgu, hadd]
              simp only [Pi.add_apply]
              rw [hsmul]
              simp only [Pi.smul_apply, smul_eq_mul]
              rw [hgcoe, hucoe]
        filter_upwards [hcoe Finset.univ] with x hx
        simpa using hx
      have hsall := hsum Finset.univ
      filter_upwards [hsall, hΦcoe] with x hx hpx
      calc
        ∑ g ∈ s, c g * g
              ((if 0 ≤ n then M.T^[n.toNat] else S^[n.natAbs]) x) =
            ∑ g : s, c g.1 * g.1
              ((if 0 ≤ n then M.T^[n.toNat] else S^[n.natAbs]) x) := by
                rw [← Finset.sum_attach]
                rw [show s.attach = Finset.univ by ext g; simp]
        _ = (Φ q : M.X → ℂ) x := hx.trans hpx.symm
    have hsub : M.lpMember 2 (fun x => ∑ g ∈ s, c g * g
        ((if 0 ≤ n then M.T^[n.toNat] else S^[n.natAbs]) x)) := by
      by_cases hn : 0 ≤ n
      · simpa [hn, Function.comp_def] using
          hzLp.comp_measurePreserving (hM.2.iterate n.toNat)
      · simpa [hn, Function.comp_def] using
          hzLp.comp_measurePreserving (hS.iterate n.natAbs)
    have hrawY : M.lpMember 2 (raw Y) := MeasureTheory.Lp.memLp Y
    have hnorm :
        (eLpNorm ((fun x => (∑ g ∈ s, c g * g
          ((if 0 ≤ n then M.T^[n.toNat] else S^[n.natAbs]) x))) - raw Y)
          2 M.μ).toReal = ‖Φ q - Y‖ := by
      rw [← MeasureTheory.Lp.norm_toLp _ (hsub.sub hrawY)]
      congr 1
      apply MeasureTheory.Lp.ext
      filter_upwards [(hsub.sub hrawY).coeFn_toLp,
        MeasureTheory.Lp.coeFn_sub (Φ q) Y, horbit] with x hx hxy horbx
      rw [hx, hxy]
      simp only [Pi.sub_apply]
      rw [horbx]
    have hfinal : eLpNorm ((fun x => (∑ g ∈ s, c g * g
          ((if 0 ≤ n then M.T^[n.toNat] else S^[n.natAbs]) x))) - raw Y)
          2 M.μ < ENNReal.ofReal ε := by
      apply (ENNReal.toReal_lt_toReal
      ((hsub.sub hrawY).eLpNorm_ne_top) (by simp)).mp
      rw [hnorm, ENNReal.toReal_ofReal hε.le]
      simpa [dist_eq_norm] using hdist
    simpa only [Pi.sub_apply] using hfinal

lemma discreteSpectrum_implies_compactFunctions (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hInv : Chapter01.IsInvertibleMeasurePreservingMap M.𝓧 M.μ M.𝓧 M.μ M.T)
    (hdisc : HasDiscreteSpectrum M) : IsCompactSystem M := by
  intro f hf ε hε
  obtain ⟨s, hs, c, happrox⟩ := hdisc f hf ε hε
  refine ⟨(fun x => ∑ g ∈ s, c g * g x),
    finiteEigenfunctionCombination_almostPeriodic M hM hInv s hs c, happrox⟩

theorem compactIffDiscreteSpectrumWeakMixingIffContinuousSpectrum
    (M : System.{u}) : CompactIffDiscreteSpectrumStatement M := by
  intro hErg hInv
  refine ⟨⟨compactFunctions_imply_discreteSpectrum M hErg.1 hInv,
    discreteSpectrum_implies_compactFunctions M hErg.1 hInv⟩, ?_⟩
  exact WeakSpectrum.weakMixing_iff_continuousSpectrum M hErg.1 hInv

end Chapter02.CompactDiscrete
