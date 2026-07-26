import Chapter02.HostKra.HostKraFourfoldStructuredReduction

open Classical Set

noncomputable section

namespace Chapter02.HostKraStructuredRecurrence

universe u

/-- The finite-open-cover form of minimality needed for forward orbit
recurrence.  It is deliberately stated independently of Chapter 05, whose
book-level characterization theorem is not available without proof risks. -/
def HasFiniteOrbitCover {X : Type u} [TopologicalSpace X]
    (T : X → X) : Prop :=
  ∀ U : Set X, IsOpen U → U.Nonempty →
    ∃ K : Finset ℕ, Set.univ ⊆ ⋃ k ∈ (K : Set ℕ), (T^[k]) ⁻¹' U

/-- Pointwise orbit-density in the only form needed below: every forward
orbit meets every nonempty open set. -/
def EveryOrbitHitsOpen {X : Type u} [TopologicalSpace X]
    (T : X → X) : Prop :=
  ∀ x : X, ∀ U : Set X, IsOpen U → U.Nonempty →
    ∃ n : ℕ, (T^[n]) x ∈ U

/-- On a compact space, continuity and pointwise orbit-density give the
finite-open-cover form of minimality. -/
theorem hasFiniteOrbitCover_of_compact
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (T : X → X) (hT : Continuous T)
    (hdense : EveryOrbitHitsOpen T) :
    HasFiniteOrbitCover T := by
  intro U hUopen hUne
  let V : ℕ → Set X := fun n ↦ (T^[n]) ⁻¹' U
  have hVopen : ∀ n : ℕ, IsOpen (V n) := by
    intro n
    exact hUopen.preimage (hT.iterate n)
  have hcover : (Set.univ : Set X) ⊆ ⋃ n, V n := by
    intro x hx
    obtain ⟨n, hn⟩ := hdense x U hUopen hUne
    simp only [Set.mem_iUnion]
    exact ⟨n, hn⟩
  obtain ⟨K, hK⟩ :=
    isCompact_univ.elim_finite_subcover V hVopen hcover
  exact ⟨K, by simpa only [V] using hK⟩

/-- A continuous scalar observation of a forward orbit in a system with the
finite-cover form of minimality returns syndetically to its initial value. -/
theorem isSyndetic_observation_returns
    {X : Type u} [TopologicalSpace X]
    (T : X → X) (hcover : HasFiniteOrbitCover T)
    (x : X) (f : X → ℝ) (hf : Continuous f)
    (δ : ℝ) (hδ : 0 < δ) :
    IsSyndetic {n : ℕ | |f ((T^[n]) x) - f x| < δ} := by
  let U : Set X := f ⁻¹' Metric.ball (f x) δ
  have hUopen : IsOpen U := (Metric.isOpen_ball.preimage hf)
  have hxU : x ∈ U := by
    change dist (f x) (f x) < δ
    simpa using hδ
  obtain ⟨K, hK⟩ := hcover U hUopen ⟨x, hxU⟩
  let B : ℕ := K.sup id + 1
  refine ⟨B, by exact Nat.succ_pos _, ?_⟩
  intro i
  have hi : (T^[i]) x ∈ Set.univ := Set.mem_univ _
  have hmem := hK hi
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨k, hkK, hkU⟩ := hmem
  refine ⟨i + k, ?_, Nat.le_add_right i k, ?_⟩
  · change |f ((T^[i + k]) x) - f x| < δ
    have hiter : (T^[i + k]) x = (T^[k]) ((T^[i]) x) := by
      rw [Nat.add_comm, Function.iterate_add_apply]
    rw [hiter]
    change dist (f ((T^[k]) ((T^[i]) x))) (f x) < δ
    simpa [U, Metric.mem_ball, dist_comm] using hkU
  · have hk : k ≤ K.sup id :=
      Finset.le_sup (f := fun n : ℕ ↦ n) hkK
    dsimp only [B]
    omega

/-- Syndetic recurrence at the initial value for a real sequence. -/
def SyndeticallyRecurrentAtZero (a : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    IsSyndetic {n : ℕ | |a n - a 0| < δ}

/-- Orbit observations satisfying the preceding finite-cover hypothesis are
syndetically recurrent at time zero. -/
theorem observation_syndeticallyRecurrentAtZero
    {X : Type u} [TopologicalSpace X]
    (T : X → X) (hcover : HasFiniteOrbitCover T)
    (x : X) (f : X → ℝ) (hf : Continuous f) :
    SyndeticallyRecurrentAtZero (fun n ↦ f ((T^[n]) x)) := by
  intro δ hδ
  simpa using isSyndetic_observation_returns T hcover x f hf δ hδ

/-- A real sequence represented by a continuous observation along an orbit
of a compact minimal forward system.  This is the exact recurrence content
needed from a basic nilsequence; no nilpotent structure is baked into the
definition. -/
def IsMinimalOrbitSequence (a : ℕ → ℝ) : Prop :=
  ∃ X : Type u, ∃ _top : TopologicalSpace X, ∃ _compact : CompactSpace X,
    ∃ T : X → X, ∃ x : X, ∃ f : X → ℝ,
      Continuous T ∧ EveryOrbitHitsOpen T ∧ Continuous f ∧
        ∀ n : ℕ, a n = f ((T^[n]) x)

/-- Every compact-minimal orbit sequence returns syndetically to its initial
value. -/
theorem IsMinimalOrbitSequence.syndeticallyRecurrentAtZero
    {a : ℕ → ℝ} (ha : IsMinimalOrbitSequence a) :
    SyndeticallyRecurrentAtZero a := by
  obtain ⟨X, top, compact, T, x, f, hT, hdense, hf, haeq⟩ := ha
  letI : TopologicalSpace X := top
  letI : CompactSpace X := compact
  have hcover := hasFiniteOrbitCover_of_compact T hT hdense
  intro δ hδ
  simpa only [haeq] using
    isSyndetic_observation_returns T hcover x f hf δ hδ

/-- A continuous observation along a compact-minimal orbit visits every
nonempty open superlevel set syndetically. -/
theorem IsMinimalOrbitSequence.isSyndetic_superlevel_of_exists
    {a : ℕ → ℝ} (ha : IsMinimalOrbitSequence a)
    (c : ℝ) (hne : ∃ n : ℕ, c < a n) :
    IsSyndetic {n : ℕ | c < a n} := by
  obtain ⟨X, top, compact, T, x, f, hT, hdense, hf, haeq⟩ := ha
  letI : TopologicalSpace X := top
  letI : CompactSpace X := compact
  let U : Set X := f ⁻¹' Set.Ioi c
  have hUopen : IsOpen U := isOpen_Ioi.preimage hf
  obtain ⟨n₀, hn₀⟩ := hne
  have hUne : U.Nonempty := by
    refine ⟨(T^[n₀]) x, ?_⟩
    change c < f ((T^[n₀]) x)
    simpa only [haeq] using hn₀
  have hcover := hasFiniteOrbitCover_of_compact T hT hdense
  obtain ⟨K, hK⟩ := hcover U hUopen hUne
  let B : ℕ := K.sup id + 1
  refine ⟨B, by exact Nat.succ_pos _, ?_⟩
  intro i
  have hi : (T^[i]) x ∈ Set.univ := Set.mem_univ _
  have hmem := hK hi
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨k, hkK, hkU⟩ := hmem
  refine ⟨i + k, ?_, Nat.le_add_right i k, ?_⟩
  · change c < a (i + k)
    rw [haeq]
    have hiter : (T^[i + k]) x = (T^[k]) ((T^[i]) x) := by
      rw [Nat.add_comm, Function.iterate_add_apply]
    rw [hiter]
    exact hkU
  · have hk : k ≤ K.sup id :=
      Finset.le_sup (f := fun n : ℕ ↦ n) hkK
    dsimp only [B]
    omega

/-- Uniform-limit (pro-minimal, in the intended nilsequence application)
closure of compact-minimal orbit sequences. -/
def IsUniformLimitOfMinimalOrbitSequences (a : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ b : ℕ → ℝ, IsMinimalOrbitSequence.{0} b ∧
      ∀ n : ℕ, |a n - b n| < η

/-- Uniform approximation by one recurrent sequence transfers recurrence at
the initial value.  The approximant may depend on the requested tolerance. -/
theorem syndeticallyRecurrentAtZero_of_uniform_approximation
    (a : ℕ → ℝ)
    (happrox :
      ∀ η : ℝ, 0 < η →
        ∃ b : ℕ → ℝ, SyndeticallyRecurrentAtZero b ∧
          ∀ n : ℕ, |a n - b n| < η) :
    SyndeticallyRecurrentAtZero a := by
  intro δ hδ
  obtain ⟨b, hbrec, hab⟩ := happrox (δ / 3) (by positivity)
  have hb := hbrec (δ / 3) (by positivity)
  obtain ⟨B, hB, hreturns⟩ := hb
  refine ⟨B, hB, ?_⟩
  intro i
  obtain ⟨n, hn, hin, hnB⟩ := hreturns i
  refine ⟨n, ?_, hin, hnB⟩
  change |a n - a 0| < δ
  change |b n - b 0| < δ / 3 at hn
  have hn' : |a n - b n| < δ / 3 := hab n
  have h0' : |a 0 - b 0| < δ / 3 := hab 0
  have htri :
      |a n - a 0| ≤ |a n - b n| + |b n - b 0| + |b 0 - a 0| := by
    calc
      |a n - a 0| =
          |(a n - b n) + ((b n - b 0) + (b 0 - a 0))| := by ring_nf
      _ ≤ |a n - b n| + |(b n - b 0) + (b 0 - a 0)| :=
        abs_add_le _ _
      _ ≤ |a n - b n| + (|b n - b 0| + |b 0 - a 0|) :=
        add_le_add_right (abs_add_le _ _) _
      _ = |a n - b n| + |b n - b 0| + |b 0 - a 0| := by ring
  have hlast : |b 0 - a 0| < δ / 3 := by
    simpa [abs_sub_comm] using h0'
  linarith

/-- Uniform limits of compact-minimal orbit sequences retain syndetic
recurrence at the initial value. -/
theorem IsUniformLimitOfMinimalOrbitSequences.syndeticallyRecurrentAtZero
    {a : ℕ → ℝ} (ha : IsUniformLimitOfMinimalOrbitSequences a) :
    SyndeticallyRecurrentAtZero a := by
  apply syndeticallyRecurrentAtZero_of_uniform_approximation a
  intro η hη
  obtain ⟨b, hb, hab⟩ := ha η hη
  exact ⟨b, hb.syndeticallyRecurrentAtZero, hab⟩

/-- A pro-minimal sequence has syndetic strict superlevel sets below any one
of its values.  The positive margin absorbs the chosen uniform
approximation. -/
theorem IsUniformLimitOfMinimalOrbitSequences.isSyndetic_superlevel_of_exists
    {a : ℕ → ℝ} (ha : IsUniformLimitOfMinimalOrbitSequences a)
    (c η : ℝ) (hη : 0 < η) (hne : ∃ n : ℕ, c + η < a n) :
    IsSyndetic {n : ℕ | c < a n} := by
  obtain ⟨b, hbminimal, hab⟩ := ha (η / 3) (by positivity)
  obtain ⟨n₀, hn₀⟩ := hne
  have hbn₀ : c + 2 * (η / 3) < b n₀ := by
    have hnclose := hab n₀
    rw [abs_lt] at hnclose
    linarith
  have hbsynd :
      IsSyndetic {n : ℕ | c + 2 * (η / 3) < b n} :=
    hbminimal.isSyndetic_superlevel_of_exists
      (c + 2 * (η / 3)) ⟨n₀, hbn₀⟩
  obtain ⟨B, hB, hhit⟩ := hbsynd
  refine ⟨B, hB, ?_⟩
  intro i
  obtain ⟨n, hn, hin, hnB⟩ := hhit i
  refine ⟨n, ?_, hin, hnB⟩
  change c < a n
  change c + 2 * (η / 3) < b n at hn
  have hnclose := hab n
  rw [abs_lt] at hnclose
  linarith

/-- The exact remaining fourfold structured-return obligation follows from
the pro-minimal (in the intended application, pro-nilsequence) representation
of the constructed fifteen-dual correlation sequence. -/
theorem fifteenDualStructuredCorrelation_returns_of_uniformLimit
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hseq :
      IsUniformLimitOfMinimalOrbitSequences
        (HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation
          M hM A hA)) :
    ∀ δ : ℝ, 0 < δ →
      IsSyndetic {n : ℕ |
        |HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation
              M hM A hA n -
            HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation
              M hM A hA 0| < δ} :=
  hseq.syndeticallyRecurrentAtZero

/-- With the pro-minimal sequence representation supplied, the checked
time-zero lower bound and uniform-density characteristic error give the exact
fourfold BHK syndetic conclusion. -/
theorem quadruple_syndetic_of_structured_uniformLimit
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hseq :
      IsUniformLimitOfMinimalOrbitSequences
        (HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation
          M hM A hA))
    (ε : ℝ) (hε : 0 < ε) :
    IsSyndetic {n : ℕ |
      MultipleKhintchineSyndetic.quadrupleCorrelation M A n >
        (realMeasure M A) ^ 4 - ε} := by
  apply
    HostKraFourfoldStructuredReduction.quadruple_syndetic_of_fifteenDualStructured_recurrence
      M hM hErg A hA
  · apply
      HostKraFourfoldStructuredReduction.fifteenDualStructured_recurrence_of_zero_and_returns
        M hM A hA
    · exact
        HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation_zero_lower_bound
          M hM A hA
    · exact
        fifteenDualStructuredCorrelation_returns_of_uniformLimit
          M hM A hA hseq
  · exact hε

/-- Semantically exact BHK decomposition route.  It is enough that, at every
positive scale, the structured correlation differ in uniform density from a
pro-minimal sequence which has one value within that scale of the sharp
`μ(A)^4` lower bound.  Minimality makes that high value recur syndetically,
and the two uniform-density errors are then absorbed at once. -/
theorem quadruple_syndetic_of_structured_nilDecomposition
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hdecomp :
      ∀ δ : ℝ, 0 < δ →
        ∃ c : ℕ → ℝ,
          IsUniformLimitOfMinimalOrbitSequences c ∧
          MultipleKhintchineSyndetic.TendsToZeroInUniformDensity
            (fun n ↦
              HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation
                  M hM A hA n - c n) ∧
          ∃ n : ℕ, (realMeasure M A) ^ 4 - δ < c n)
    (ε : ℝ) (hε : 0 < ε) :
    IsSyndetic {n : ℕ |
      MultipleKhintchineSyndetic.quadrupleCorrelation M A n >
        (realMeasure M A) ^ 4 - ε} := by
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨c, hcminimal, hstructured_c, n₀, hn₀⟩ :=
    hdecomp (ε / 4) hε4
  have hcsynd :
      IsSyndetic {n : ℕ |
        (realMeasure M A) ^ 4 - ε / 2 < c n} := by
    apply hcminimal.isSyndetic_superlevel_of_exists
      ((realMeasure M A) ^ 4 - ε / 2) (ε / 4) hε4
    refine ⟨n₀, ?_⟩
    have hthreshold :
        (realMeasure M A) ^ 4 - ε / 2 + ε / 4 =
          (realMeasure M A) ^ 4 - ε / 4 := by
      ring
    rwa [hthreshold]
  apply
    MultipleKhintchineSyndetic.isSyndetic_superlevel_of_uniformDensity_close
      (MultipleKhintchineSyndetic.quadrupleCorrelation M A)
      c ((realMeasure M A) ^ 4 - ε) (ε / 2) (by positivity)
  · convert hcsynd using 1
    ext n
    simp only [Set.mem_setOf_eq]
    ring_nf
  · have horiginal :=
      HostKraFourfoldStructuredReduction.quadrupleCorrelation_sub_fifteenDualStructured_uniformDensity
        M hM hErg A hA
    have hadd := horiginal.add hstructured_c
    simpa only [sub_add_sub_cancel] using hadd

end Chapter02.HostKraStructuredRecurrence
