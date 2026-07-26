import Chapter02.Dynamics.ProMinimalInverseLimit
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UrysohnsLemma

open Classical Set

noncomputable section

namespace Chapter02.DirectedMinimalInverseLimit

open Chapter02.HostKraStructuredRecurrence

universe u v

variable {X : Type u} [TopologicalSpace X] [CompactSpace X]
variable {I : Type v} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]
variable {Y : I → Type}
  [∀ i, TopologicalSpace (Y i)]
  [∀ i, CompactSpace (Y i)]
  [∀ i, T2Space (Y i)]

/-- The real continuous functions which factor through one stage of a
directed inverse system. -/
def finiteStageSubalgebra
    (π : ∀ i, C(X, Y i))
    (bond : ∀ {i j : I}, i ≤ j → C(Y j, Y i))
    (compat : ∀ {i j : I} (hij : i ≤ j),
      π i = (bond hij).comp (π j)) :
    Subalgebra ℝ C(X, ℝ) where
  carrier := {f | ∃ i : I, ∃ g : C(Y i, ℝ), f = g.comp (π i)}
  zero_mem' := by
    let i : I := Classical.choice inferInstance
    refine ⟨i, 0, ?_⟩
    ext x
    rfl
  one_mem' := by
    let i : I := Classical.choice inferInstance
    refine ⟨i, 1, ?_⟩
    ext x
    rfl
  add_mem' := by
    rintro f g ⟨i, fi, rfl⟩ ⟨j, gj, rfl⟩
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, fi.comp (bond hik) + gj.comp (bond hjk), ?_⟩
    ext x
    have hi := congrArg (fun p : C(X, Y i) ↦ p x) (compat hik)
    have hj := congrArg (fun p : C(X, Y j) ↦ p x) (compat hjk)
    change π i x = bond hik (π k x) at hi
    change π j x = bond hjk (π k x) at hj
    simp only [ContinuousMap.comp_apply, ContinuousMap.add_apply]
    rw [hi, hj]
  mul_mem' := by
    rintro f g ⟨i, fi, rfl⟩ ⟨j, gj, rfl⟩
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, fi.comp (bond hik) * gj.comp (bond hjk), ?_⟩
    ext x
    have hi := congrArg (fun p : C(X, Y i) ↦ p x) (compat hik)
    have hj := congrArg (fun p : C(X, Y j) ↦ p x) (compat hjk)
    change π i x = bond hik (π k x) at hi
    change π j x = bond hjk (π k x) at hj
    simp only [ContinuousMap.comp_apply, ContinuousMap.mul_apply]
    rw [hi, hj]
  algebraMap_mem' := by
    intro r
    let i : I := Classical.choice inferInstance
    refine ⟨i, ContinuousMap.const (Y i) r, ?_⟩
    ext x
    simp

omit [CompactSpace X] in
/-- If the stage projections jointly distinguish points, finite-stage
continuous functions separate points of the inverse limit. -/
theorem finiteStageSubalgebra_separatesPoints
    (π : ∀ i, C(X, Y i))
    (bond : ∀ {i j : I}, i ≤ j → C(Y j, Y i))
    (compat : ∀ {i j : I} (hij : i ≤ j),
      π i = (bond hij).comp (π j))
    (hjoint : ∀ x y : X, (∀ i, π i x = π i y) → x = y) :
    (finiteStageSubalgebra π bond compat).SeparatesPoints := by
  intro x y hxy
  have hstage : ∃ i : I, π i x ≠ π i y := by
    by_contra h
    push_neg at h
    exact hxy (hjoint x y h)
  obtain ⟨i, hi⟩ := hstage
  have hdisjoint : Disjoint ({π i x} : Set (Y i)) {π i y} := by
    simpa [Set.disjoint_singleton_right] using hi
  obtain ⟨g, hgx, hgy, -⟩ :=
    exists_continuous_zero_one_of_isClosed
      (isClosed_singleton : IsClosed ({π i x} : Set (Y i)))
      (isClosed_singleton : IsClosed ({π i y} : Set (Y i)))
      hdisjoint
  let f : C(X, ℝ) := g.comp (π i)
  refine ⟨f, ?_, ?_⟩
  · exact ⟨f, ⟨i, g, rfl⟩, rfl⟩
  · have hx : g (π i x) = 0 := hgx (Set.mem_singleton _)
    have hy : g (π i y) = 1 := hgy (Set.mem_singleton _)
    change g (π i x) ≠ g (π i y)
    rw [hx, hy]
    norm_num

/-- Stone--Weierstrass in inverse-limit form: every continuous real
observable is uniformly approximated by a continuous observable from one
finite stage. -/
theorem exists_finiteStage_uniform_approximation
    (π : ∀ i, C(X, Y i))
    (bond : ∀ {i j : I}, i ≤ j → C(Y j, Y i))
    (compat : ∀ {i j : I} (hij : i ≤ j),
      π i = (bond hij).comp (π j))
    (hjoint : ∀ x y : X, (∀ i, π i x = π i y) → x = y)
    (f : C(X, ℝ)) {η : ℝ} (hη : 0 < η) :
    ∃ i : I, ∃ g : C(Y i, ℝ),
      ∀ x : X, |f x - g (π i x)| < η := by
  obtain ⟨a, ha⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      (finiteStageSubalgebra π bond compat)
      (finiteStageSubalgebra_separatesPoints π bond compat hjoint)
      f η hη
  obtain ⟨i, g, hag⟩ := a.property
  refine ⟨i, g, fun x ↦ ?_⟩
  have hpoint : ‖(a : C(X, ℝ)) x - f x‖ < η :=
    (ContinuousMap.norm_lt_iff _ hη).mp ha x
  rw [hag] at hpoint
  simpa [abs_sub_comm] using hpoint

/-- If every stage dynamics is compact minimal and the inverse-limit
projections are equivariant and jointly injective, every continuous orbit
observation is pro-minimal. -/
theorem orbit_isUniformLimitOfMinimalOrbitSequences
    (T : X → X)
    (π : ∀ i, C(X, Y i))
    (bond : ∀ {i j : I}, i ≤ j → C(Y j, Y i))
    (compat : ∀ {i j : I} (hij : i ≤ j),
      π i = (bond hij).comp (π j))
    (hjoint : ∀ x y : X, (∀ i, π i x = π i y) → x = y)
    (S : ∀ i, Y i → Y i)
    (hScontinuous : ∀ i, Continuous (S i))
    (hSminimal : ∀ i, EveryOrbitHitsOpen (S i))
    (hequiv : ∀ i x, π i (T x) = S i (π i x))
    (f : C(X, ℝ)) (x : X) :
    IsUniformLimitOfMinimalOrbitSequences
      (fun n ↦ f ((T^[n]) x)) := by
  apply
    Chapter02.ProMinimalInverseLimit.isUniformLimitOfMinimalOrbitSequences_orbit
      T f
  intro η hη
  obtain ⟨i, g, hfg⟩ :=
    exists_finiteStage_uniform_approximation
      π bond compat hjoint f hη
  exact ⟨Y i, inferInstance, inferInstance, S i, π i, g,
    hScontinuous i, hSminimal i, (π i).continuous,
    hequiv i, g.continuous, hfg⟩

/-- A fully explicit directed compact-minimal inverse-limit presentation of
a real sequence.  All topology and order instances are stored as data, so
the proposition can be used as a theorem interface without ambient instance
assumptions. -/
structure Presentation (a : ℕ → ℝ) where
  X : Type
  topX : TopologicalSpace X
  compactX : @CompactSpace X topX
  I : Type
  preorderI : Preorder I
  nonemptyI : Nonempty I
  directedI : @IsDirected I
    (fun i j => @LE.le I preorderI.toLE i j)
  Y : I → Type
  topY : ∀ i, TopologicalSpace (Y i)
  compactY : ∀ i, @CompactSpace (Y i) (topY i)
  t2Y : ∀ i, @T2Space (Y i) (topY i)
  T : X → X
  π : ∀ i, @ContinuousMap X (Y i) topX (topY i)
  bond : ∀ {i j : I}, @LE.le I preorderI.toLE i j →
    @ContinuousMap (Y j) (Y i) (topY j) (topY i)
  compat : ∀ {i j : I} (hij : @LE.le I preorderI.toLE i j),
    π i = (bond hij).comp (π j)
  jointly_injective : ∀ x y : X, (∀ i, π i x = π i y) → x = y
  S : ∀ i, Y i → Y i
  continuous_S : ∀ i, @Continuous (Y i) (Y i) (topY i) (topY i) (S i)
  minimal_S : ∀ i, @EveryOrbitHitsOpen (Y i) (topY i) (S i)
  equivariant : ∀ i x, π i (T x) = S i (π i x)
  f : @ContinuousMap X ℝ topX inferInstance
  x : X
  sequence_eq : ∀ n, a n = f ((T^[n]) x)

/-- Every sequence presented by a directed inverse limit of compact minimal
systems is a uniform limit of compact-minimal orbit sequences. -/
theorem Presentation.isUniformLimitOfMinimalOrbitSequences
    {a : ℕ → ℝ} (P : Presentation a) :
    IsUniformLimitOfMinimalOrbitSequences a := by
  letI : TopologicalSpace P.X := P.topX
  letI : CompactSpace P.X := P.compactX
  letI : Preorder P.I := P.preorderI
  letI : Nonempty P.I := P.nonemptyI
  letI : IsDirected P.I (· ≤ ·) := P.directedI
  letI (i : P.I) : TopologicalSpace (P.Y i) := P.topY i
  letI (i : P.I) : CompactSpace (P.Y i) := P.compactY i
  letI (i : P.I) : T2Space (P.Y i) := P.t2Y i
  have horbit :
      IsUniformLimitOfMinimalOrbitSequences
        (fun n ↦ P.f ((P.T^[n]) P.x)) :=
    orbit_isUniformLimitOfMinimalOrbitSequences
      P.T P.π P.bond P.compat P.jointly_injective P.S
      P.continuous_S P.minimal_S P.equivariant P.f P.x
  have heq :
      a = fun n ↦ P.f ((P.T^[n]) P.x) :=
    funext P.sequence_eq
  rw [heq]
  exact horbit

end Chapter02.DirectedMinimalInverseLimit
