import Chapter00.Probability.Section03Examples

noncomputable section

open Classical Filter MeasureTheory ProbabilityTheory

namespace Chapter00.Section03

universe u v

theorem equivarianceOfDisintegrationAux
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (T : X → X) (S : Y → Y) (φ : X → Y)
    (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Measurable T → Measurable S → Measurable φ →
    Function.Bijective T → Function.Bijective S →
    Measure.map T μ = μ → Measure.map S ν = ν →
    Measure.map φ μ = ν → φ ∘ T = S ∘ φ →
    HasMeasureDisintegration φ μ ν →
      ∃ μy : Y → Measure X,
        (∀ᵐ y ∂ν, IsProbabilityMeasure (μy y) ∧
          μy y (φ ⁻¹' {y}) = 1) ∧
        (∀ B : Set X, MeasurableSet B → Measurable fun y => μy y B) ∧
        (∀ B : Set X, MeasurableSet B → μ B = ∫⁻ y, μy y B ∂ν) ∧
        ∀ᵐ y ∂ν, Measure.map T (μy y) = μy (S y) := by
  intro hT hS hφ _hTbij hSbij hTinv hSinv hpush hcomm hdis
  rcases hdis with ⟨_hφ', _hpush', μy, hprob, hmeas, hdecomp, huniq⟩
  letI : Nonempty Y := nonempty_of_isProbabilityMeasure ν
  have hSemb : MeasurableEmbedding S := hS.measurableEmbedding hSbij.1
  let R : Y → Y := hSemb.invFun
  have hRmeas : Measurable R := hSemb.measurable_invFun
  have hRS : Function.LeftInverse R S := hSemb.leftInverse_invFun
  have hSR : Function.RightInverse R S := by
    intro y
    obtain ⟨z, rfl⟩ := hSbij.2 y
    rw [hRS z]
  have hRinv : Measure.map R ν = ν := by
    calc
      Measure.map R ν = Measure.map R (Measure.map S ν) := by rw [hSinv]
      _ = Measure.map (R ∘ S) ν := Measure.map_map hRmeas hS
      _ = Measure.map id ν := by rw [show R ∘ S = id from funext hRS]
      _ = ν := Measure.map_id
  have hSmp : MeasurePreserving S ν ν := ⟨hS, hSinv⟩
  have hRmp : MeasurePreserving R ν ν := ⟨hRmeas, hRinv⟩
  let μy' : Y → Measure X := fun y => Measure.map T (μy (R y))
  have hprob' : ∀ᵐ y ∂ν, IsProbabilityMeasure (μy' y) ∧
      μy' y (φ ⁻¹' {y}) = 1 := by
    have hpull := hRmp.quasiMeasurePreserving.ae hprob
    filter_upwards [hpull] with y hy
    letI : IsProbabilityMeasure (μy (R y)) := hy.1
    have htarget : MeasurableSet (φ ⁻¹' {y}) :=
      (measurableSet_singleton y).preimage hφ
    have hsub : φ ⁻¹' {R y} ⊆ T ⁻¹' (φ ⁻¹' {y}) := by
      intro x hx
      change φ x = R y at hx
      change φ (T x) = y
      have hc := congrFun hcomm x
      change φ (T x) = S (φ x) at hc
      rw [hc, hx, hSR y]
    have hprobmap : IsProbabilityMeasure (Measure.map T (μy (R y))) :=
      Measure.isProbabilityMeasure_map hT.aemeasurable
    refine ⟨by simpa [μy'] using hprobmap, ?_⟩
    rw [show μy' y = Measure.map T (μy (R y)) from rfl,
      Measure.map_apply hT htarget]
    apply le_antisymm
    · calc
        μy (R y) (T ⁻¹' (φ ⁻¹' {y})) ≤ μy (R y) Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    rw [← hy.2]
    exact measure_mono hsub
  have hmeas' : ∀ B : Set X, MeasurableSet B →
      Measurable fun y => μy' y B := by
    intro B hB
    have hpre : MeasurableSet (T ⁻¹' B) := hB.preimage hT
    have hc : (fun y => μy' y B) = (fun z => μy z (T ⁻¹' B)) ∘ R := by
      funext y
      simp [μy', Measure.map_apply hT hB]
    rw [hc]
    exact (hmeas (T ⁻¹' B) hpre).comp hRmeas
  have hdecomp' : ∀ B : Set X, MeasurableSet B →
      μ B = ∫⁻ y, μy' y B ∂ν := by
    intro B hB
    have hpre : MeasurableSet (T ⁻¹' B) := hB.preimage hT
    have hcoord : Measurable fun z => μy z (T ⁻¹' B) := hmeas _ hpre
    calc
      μ B = (Measure.map T μ) B := by rw [hTinv]
      _ = μ (T ⁻¹' B) := Measure.map_apply hT hB
      _ = ∫⁻ z, μy z (T ⁻¹' B) ∂ν := hdecomp _ hpre
      _ = ∫⁻ y, μy (R y) (T ⁻¹' B) ∂ν :=
        (hRmp.lintegral_comp hcoord).symm
      _ = ∫⁻ y, μy' y B ∂ν := by
        apply lintegral_congr
        intro y
        simp [μy', Measure.map_apply hT hB]
  have heq : ∀ᵐ y ∂ν, μy y = μy' y := huniq μy' hprob' hmeas' hdecomp'
  have heqS : ∀ᵐ y ∂ν, μy (S y) = μy' (S y) :=
    hSmp.quasiMeasurePreserving.ae heq
  refine ⟨μy, hprob, hmeas, hdecomp, ?_⟩
  filter_upwards [heqS] with y hy
  rw [hy]
  simp [μy', hRS y]

end Chapter00.Section03
