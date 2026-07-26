import Chapter02.Ergodic.ErgodicCorrelations
import Chapter02.Ergodic.CorrelationSemiAlgebra
import Chapter02.Ergodic.ZeroDensity

noncomputable section

open Classical MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Chapter02.ProductWeakMixing

universe u v

def productSystem (M : System.{u}) (N : System.{v}) : System where
  X := M.X × N.X
  measurableSpace := inferInstance
  μ := M.μ.prod N.μ
  T := fun p => (M.T p.1, N.T p.2)

def rectangles (M : System.{u}) (N : System.{v}) : SetFamily (M.X × N.X) :=
  {E | ∃ A : Set M.X, MeasurableSet A ∧
    ∃ B : Set N.X, MeasurableSet B ∧ E = A ×ˢ B}

lemma product_measurableSpace_generated (M : System.{u}) (N : System.{v}) :
    Chapter00.generatedSigmaAlgebra (rectangles M N) =
      (productSystem M N).𝓧 := by
  have hspace : MeasurableSpace.generateFrom (rectangles M N) =
      (inferInstance : MeasurableSpace (M.X × N.X)) := by
    change MeasurableSpace.generateFrom (rectangles M N) =
      (MeasurableSpace.comap Prod.fst M.measurableSpace ⊔
        MeasurableSpace.comap Prod.snd N.measurableSpace)
    apply le_antisymm
    · rw [MeasurableSpace.generateFrom_le_iff]
      rintro E ⟨A, hA, B, hB, rfl⟩
      exact hA.prod hB
    · apply sup_le
      · apply Measurable.comap_le
        intro A hA
        apply MeasurableSpace.measurableSet_generateFrom
        refine ⟨A, hA, Set.univ, MeasurableSet.univ, ?_⟩
        ext p
        simp
      · apply Measurable.comap_le
        intro B hB
        apply MeasurableSpace.measurableSet_generateFrom
        refine ⟨Set.univ, MeasurableSet.univ, B, hB, ?_⟩
        ext p
        simp
  ext E
  change @MeasurableSet (M.X × N.X)
    (MeasurableSpace.generateFrom (rectangles M N)) E ↔ MeasurableSet E
  rw [hspace]

lemma rectangles_semiAlgebra (M : System.{u}) (N : System.{v}) :
    Chapter00.IsSemiAlgebra (rectangles M N) := by
  constructor
  · constructor
    · refine ⟨∅, MeasurableSet.empty, Set.univ, MeasurableSet.univ, ?_⟩
      simp
    · rintro E ⟨A, hA, B, hB, rfl⟩ F ⟨C, hC, D, hD, rfl⟩
      refine ⟨A ∩ C, hA.inter hC, B ∩ D, hB.inter hD, ?_⟩
      ext p
      simp [and_assoc, and_left_comm]
    · rintro E ⟨A, hA, B, hB, rfl⟩ F ⟨C, hC, D, hD, rfl⟩
      let R₁ : Set (M.X × N.X) := (A \ C) ×ˢ B
      let R₂ : Set (M.X × N.X) := (A ∩ C) ×ˢ (B \ D)
      refine ⟨{R₁, R₂}, ?_, ?_, ?_⟩
      · intro R hR
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hR
        rcases hR with rfl | rfl
        · exact ⟨A \ C, hA.diff hC, B, hB, rfl⟩
        · exact ⟨A ∩ C, hA.inter hC, B \ D, hB.diff hD, rfl⟩
      · intro X hX Y hY hXY
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hX hY
        rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
        · exact (hXY rfl).elim
        · exact Set.disjoint_left.2 (by
            intro p hp hq
            exact hp.1.2 hq.1.2)
        · exact Set.disjoint_left.2 (by
            intro p hp hq
            exact hq.1.2 hp.1.2)
        · exact (hXY rfl).elim
      · ext p
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.sUnion_insert,
          Set.sUnion_singleton, Set.mem_diff, Set.mem_prod, Set.mem_union,
          Set.mem_inter_iff, R₁, R₂]
        tauto
  · refine ⟨1, fun _ => Set.univ, ?_, ?_, ?_⟩
    · intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
    · intro i
      exact ⟨Set.univ, MeasurableSet.univ, Set.univ, MeasurableSet.univ, by ext; simp⟩
    · ext p
      simp

lemma productSystem_mps (M : System.{u}) (N : System.{v})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N) :
    Chapter01.IsMeasurePreservingSystem (productSystem M N) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : IsProbabilityMeasure N.μ := hN.1
  constructor
  · change IsProbabilityMeasure (M.μ.prod N.μ)
    infer_instance
  simpa [productSystem, Prod.map] using hM.2.prod hN.2

lemma product_iter (M : System.{u}) (N : System.{v}) (n : ℕ) (p : M.X × N.X) :
    (((productSystem M N).T^[n]) p) = ((M.T^[n]) p.1, (N.T^[n]) p.2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih]
      rfl

lemma correlation_rectangle (M : System.{u}) (N : System.{v})
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (A B : Set M.X) (C D : Set N.X) (n : ℕ) :
    correlation (productSystem M N) (A ×ˢ C) (B ×ˢ D) n =
      correlation M A B n * correlation N C D n := by
  letI : IsProbabilityMeasure N.μ := hN.1
  simp only [correlation, realMeasure, preimageIter, Chapter01.iterateMap,
    productSystem]
  rw [show ((fun p : M.X × N.X => (M.T p.1, N.T p.2))^[n]) ⁻¹' (B ×ˢ D) =
      ((M.T^[n]) ⁻¹' B) ×ˢ ((N.T^[n]) ⁻¹' D) by
    ext p
    simp only [Set.mem_preimage, Set.mem_prod]
    have hi := product_iter M N n p
    change ((fun p : M.X × N.X => (M.T p.1, N.T p.2))^[n]) p = _ at hi
    rw [hi]]
  rw [show (A ×ˢ C) ∩ (((M.T^[n]) ⁻¹' B) ×ˢ ((N.T^[n]) ⁻¹' D)) =
      (A ∩ (M.T^[n]) ⁻¹' B) ×ˢ (C ∩ (N.T^[n]) ⁻¹' D) by
    ext p
    simp [and_assoc, and_left_comm]]
  rw [Measure.prod_prod, ENNReal.toReal_mul]

lemma productMeasureValue_rectangle (M : System.{u}) (N : System.{v})
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (A B : Set M.X) (C D : Set N.X) :
    productMeasureValue (productSystem M N) (A ×ˢ C) (B ×ˢ D) =
      productMeasureValue M A B * productMeasureValue N C D := by
  letI : IsProbabilityMeasure N.μ := hN.1
  simp only [productMeasureValue, realMeasure, productSystem, Measure.prod_prod,
    ENNReal.toReal_mul]
  ring

lemma cesaroTendsTo_of_abs {a : ℕ → ℝ}
    (h : cesaroTendsTo (fun n => |a n|) 0) : cesaroTendsTo a 0 := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at h ⊢
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (g := fun N =>
    (((N + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1), |a n|))
  · intro N
    exact norm_nonneg _
  · intro N
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    gcongr
    exact Finset.abs_sum_le_sum_abs _ _
  · exact h

lemma cesaroTendsTo_sub_const {a : ℕ → ℝ} {c : ℝ}
    (h : cesaroTendsTo a c) :
    cesaroTendsTo (fun n => a n - c) 0 := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at h ⊢
  have ht := h.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (nhds c))
  convert ht using 1
  · funext N
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have hpos : (0 : ℝ) < N + 1 := by positivity
    field_simp
  · simp

lemma cesaroTendsTo_add_const {a : ℕ → ℝ} {x c : ℝ}
    (h : cesaroTendsTo a x) :
    cesaroTendsTo (fun n => a n + c) (x + c) := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at h ⊢
  have ht := h.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (nhds c))
  convert ht using 1
  funext N
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  have hpos : (0 : ℝ) < N + 1 := by positivity
  field_simp

lemma correlation_le_one (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (n : ℕ) : correlation M A B n ≤ 1 := by
  letI : IsProbabilityMeasure M.μ := hM.1
  change M.μ.real (A ∩ preimageIter M n B) ≤ 1
  calc
    M.μ.real (A ∩ preimageIter M n B) ≤ M.μ.real Set.univ :=
      MeasureTheory.measureReal_mono (Set.subset_univ _) (by simp)
    _ = 1 := by simp [Measure.real]

lemma correlation_univ (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (n : ℕ) :
    correlation M Set.univ Set.univ n = 1 := by
  letI : IsProbabilityMeasure M.μ := hM.1
  simp [correlation, preimageIter, realMeasure]

lemma productMeasureValue_univ (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    productMeasureValue M Set.univ Set.univ = 1 := by
  letI : IsProbabilityMeasure M.μ := hM.1
  simp [productMeasureValue, realMeasure]

lemma cesaroTendsTo_add {a b : ℕ → ℝ} {x y : ℝ}
    (ha : cesaroTendsTo a x) (hb : cesaroTendsTo b y) :
    cesaroTendsTo (fun n => a n + b n) (x + y) := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at ha hb ⊢
  have ht := ha.add hb
  convert ht using 1
  funext N
  rw [Finset.sum_add_distrib, mul_add]

lemma cesaroTendsTo_sub {a b : ℕ → ℝ} {x y : ℝ}
    (ha : cesaroTendsTo a x) (hb : cesaroTendsTo b y) :
    cesaroTendsTo (fun n => a n - b n) (x - y) := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at ha hb ⊢
  have ht := ha.sub hb
  convert ht using 1
  funext N
  rw [Finset.sum_sub_distrib, mul_sub]

lemma weaklyDisjoint_iff_product_ergodic (M : System.{u}) (N : System.{v})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N) :
    AreWeaklyDisjoint M N ↔ IsErgodic (productSystem M N) := by
  constructor
  · intro h
    exact ⟨productSystem_mps M N hM hN, h.2.2⟩
  · intro h
    exact ⟨hM, hN, h.2⟩

lemma weak_product_ergodic (M : System.{u}) (N : System.{v})
    (hweak : IsWeakMixing M) (hNerg : IsErgodic N) :
    IsErgodic (productSystem M N) := by
  have hM := hweak.1
  have hN := hNerg.1
  have hP := productSystem_mps M N hM hN
  rw [ErgodicCorrelations.ergodicIffCesaroCorrelations
    (productSystem M N) hP]
  have hrect : ∀ E F : Set (M.X × N.X), E ∈ rectangles M N →
      F ∈ rectangles M N →
      cesaroTendsTo (fun n => correlation (productSystem M N) E F n)
        (productMeasureValue (productSystem M N) E F) := by
    rintro E F ⟨A, hA, C, hC, rfl⟩ ⟨B, hB, D, hD, rfl⟩
    let a : ℕ → ℝ := fun n => correlation M A B n - productMeasureValue M A B
    let b : ℕ → ℝ := fun n => correlation N C D n - productMeasureValue N C D
    have ha : cesaroTendsTo (fun n => |a n|) 0 := by
      simpa [a] using hweak.2 A B hA hB
    have habsMul : cesaroTendsTo
        (fun n => |a n * correlation N C D n|) 0 := by
      refine CorrelationMean.cesaroTendsTo_zero_of_le
        (a := fun n => |a n * correlation N C D n|)
        (b := fun n => |a n|) ?_ ?_ ha
      · intro n
        exact abs_nonneg _
      · intro n
        change |a n * correlation N C D n| ≤ |a n|
        rw [abs_mul]
        have hc0 : 0 ≤ correlation N C D n := MeasureTheory.measureReal_nonneg
        have hc1 := correlation_le_one N hN C D n
        simpa [abs_of_nonneg hc0] using
          (mul_le_mul_of_nonneg_left hc1 (abs_nonneg (a n)))
    have hamul : cesaroTendsTo (fun n => a n * correlation N C D n) 0 :=
      cesaroTendsTo_of_abs habsMul
    have hbCorr :=
      (ErgodicCorrelations.ergodicIffCesaroCorrelations N hN).mp
        hNerg C D hC hD
    have hb : cesaroTendsTo b 0 := cesaroTendsTo_sub_const hbCorr
    have hbm := CorrelationMean.cesaroTendsTo_const_mul
      (productMeasureValue M A B) hb
    have hadd : cesaroTendsTo
        (fun n => a n * correlation N C D n + productMeasureValue M A B * b n) 0 := by
      unfold cesaroTendsTo seqTendsTo cesaroAverage at hamul hbm ⊢
      have ht := hamul.add hbm
      convert ht using 1
      · funext K
        rw [Finset.sum_add_distrib, mul_add]
      · simp
    have hfull := cesaroTendsTo_add_const
      (c := productMeasureValue M A B * productMeasureValue N C D) hadd
    convert hfull using 1
    · funext n
      rw [correlation_rectangle M N hN]
      dsimp [a, b]
      ring
    · rw [productMeasureValue_rectangle M N hN]
      simp
  have hAlg := CorrelationSemiAlgebra.cesaro_on_generatedAlgebra
    (productSystem M N) hP (rectangles M N) (rectangles_semiAlgebra M N)
    (product_measurableSpace_generated M N) hrect
  exact CorrelationSemiAlgebra.cesaro_on_all_measurable
    (productSystem M N) hP (rectangles M N)
    (product_measurableSpace_generated M N) hAlg

set_option maxHeartbeats 800000 in
lemma self_product_ergodic_implies_weak (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hprod : IsErgodic (productSystem M M)) : IsWeakMixing M := by
  have hP := productSystem_mps M M hM hM
  have hPcorr := (ErgodicCorrelations.ergodicIffCesaroCorrelations
    (productSystem M M) hP).mp hprod
  have hMerg : IsErgodic M := by
    rw [ErgodicCorrelations.ergodicIffCesaroCorrelations M hM]
    intro A B hA hB
    have hp := hPcorr (A ×ˢ Set.univ) (B ×ˢ Set.univ)
      (hA.prod MeasurableSet.univ) (hB.prod MeasurableSet.univ)
    convert hp using 1
    · funext n
      rw [correlation_rectangle M M hM, correlation_univ M hM n, mul_one]
    · rw [productMeasureValue_rectangle M M hM,
        productMeasureValue_univ M hM, mul_one]
  refine ⟨hM, ?_⟩
  intro A B hA hB
  let d : ℕ → ℝ := fun n => correlation M A B n - productMeasureValue M A B
  have hc : cesaroTendsTo (fun n => correlation M A B n)
      (productMeasureValue M A B) :=
    (ErgodicCorrelations.ergodicIffCesaroCorrelations M hM).mp
      hMerg A B hA hB
  have hsquareCorr : cesaroTendsTo (fun n => (correlation M A B n) ^ 2)
      ((productMeasureValue M A B) ^ 2) := by
    have hp := hPcorr (A ×ˢ A) (B ×ˢ B)
      (hA.prod hA) (hB.prod hB)
    convert hp using 1
    · funext n
      rw [correlation_rectangle M M hM]
      ring
    · rw [productMeasureValue_rectangle M M hM]
      ring
  have hlinear := CorrelationMean.cesaroTendsTo_const_mul
    (-2 * productMeasureValue M A B) hc
  have hsum := cesaroTendsTo_add hsquareCorr hlinear
  have hsq : cesaroTendsTo (fun n => d n ^ 2) 0 := by
    have ht := cesaroTendsTo_add_const
      (c := (productMeasureValue M A B) ^ 2) hsum
    convert ht using 1
    · funext n
      dsimp [d]
      ring
    · ring
  let z : ℕ → ℂ := fun n => (d n : ℂ)
  have hzsq : cesaroTendsTo (fun n => ‖z n‖ ^ 2) 0 := by
    simpa only [z, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hsq
  have hznorm := ZeroDensity.cesaro_norm_of_cesaro_norm_sq z hzsq
  simpa only [z, d, Complex.norm_real, Real.norm_eq_abs] using hznorm

lemma weakMixing_iff_selfProduct_ergodic (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    IsWeakMixing M ↔ IsErgodic (productSystem M M) := by
  constructor
  · intro hw
    have hMerg : IsErgodic M :=
      (ErgodicCorrelations.ergodicIffCesaroCorrelations M hM).mpr (by
      intro A B hA hB
      have hd := cesaroTendsTo_of_abs (hw.2 A B hA hB)
      have ht := cesaroTendsTo_add_const
        (c := productMeasureValue M A B) hd
      convert ht using 1
      · funext n
        ring
      · simp)
    exact weak_product_ergodic M M hw hMerg
  · exact self_product_ergodic_implies_weak M hM

lemma product_ergodic_implies_left_ergodic (M : System.{u}) (N : System.{v})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (hprod : IsErgodic (productSystem M N)) : IsErgodic M := by
  have hP := productSystem_mps M N hM hN
  rw [ErgodicCorrelations.ergodicIffCesaroCorrelations M hM]
  intro A B hA hB
  have hp := (ErgodicCorrelations.ergodicIffCesaroCorrelations
    (productSystem M N) hP).mp hprod
    (A ×ˢ Set.univ) (B ×ˢ Set.univ)
    (hA.prod MeasurableSet.univ) (hB.prod MeasurableSet.univ)
  convert hp using 1
  · funext n
    rw [correlation_rectangle M N hN, correlation_univ N hN n, mul_one]
  · rw [productMeasureValue_rectangle M N hN,
      productMeasureValue_univ N hN, mul_one]

noncomputable def trivialSystem : System.{u} where
  X := PUnit.{u + 1}
  measurableSpace := ⊤
  μ := Measure.dirac PUnit.unit
  T := id

lemma trivialSystem_mps :
    Chapter01.IsMeasurePreservingSystem (trivialSystem.{u}) := by
  constructor
  · change IsProbabilityMeasure (Measure.dirac (PUnit.unit : PUnit.{u + 1}))
    infer_instance
  · change MeasurePreserving (id : PUnit.{u + 1} → PUnit.{u + 1})
      (Measure.dirac PUnit.unit) (Measure.dirac PUnit.unit)
    exact ⟨measurable_id, Measure.map_id⟩

lemma trivialSystem_ergodic : IsErgodic (trivialSystem.{u}) := by
  refine ⟨trivialSystem_mps, ?_⟩
  intro A _hA _hinv
  by_cases h : (PUnit.unit : PUnit.{u + 1}) ∈ A
  · right
    have hAU : A = Set.univ := by
      ext x
      cases x
      simp [h]
    rw [hAU]
    simp [trivialSystem]
  · left
    have hAE : A = ∅ := by
      ext x
      cases x
      simp [h]
    rw [hAE]
    simp

theorem productWeakMixingCharacterization (M : System.{u}) :
    ProductWeakMixingCharacterization M := by
  intro hM
  constructor
  · rw [weaklyDisjoint_iff_product_ergodic M M hM hM]
    exact weakMixing_iff_selfProduct_ergodic M hM
  · constructor
    · intro hw N hNerg
      exact (weaklyDisjoint_iff_product_ergodic M N hM hNerg.1).mpr
        (weak_product_ergodic M N hw hNerg)
    · intro hall
      have htriv := hall (trivialSystem.{u}) trivialSystem_ergodic
      have hM' : Chapter01.IsMeasurePreservingSystem M := htriv.1
      have hprodTriv : IsErgodic (productSystem M (trivialSystem.{u})) :=
        (weaklyDisjoint_iff_product_ergodic M (trivialSystem.{u}) hM'
          trivialSystem_mps).mp htriv
      have hMerg : IsErgodic M := product_ergodic_implies_left_ergodic
        M (trivialSystem.{u}) hM' trivialSystem_mps hprodTriv
      have hself := hall M hMerg
      have hselfErg := (weaklyDisjoint_iff_product_ergodic M M hM' hM').mp hself
      exact (weakMixing_iff_selfProduct_ergodic M hM').mpr hselfErg

end Chapter02.ProductWeakMixing
