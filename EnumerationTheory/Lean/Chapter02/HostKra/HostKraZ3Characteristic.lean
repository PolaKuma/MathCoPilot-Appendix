import Chapter02.HostKra.HostKraU4Nullspace
import Chapter02.HostKra.HostKraZ2Characteristic

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraZ3Characteristic

universe u

open HostKraCubeSeminorm
open Chapter02.HostKraZ2Characteristic

/-- The `L²` vectors represented by bounded `U⁴`-null functions. -/
def u4NullGenerators
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Set (Lp ℂ 2 M.μ) :=
  {G | ∃ f : M.X → ℂ, ∃ hf : MemLp f ⊤ M.μ,
    HasZeroHostKraU4 M hM f hf ∧
      G = boundedToLp M hM f hf}

/-- The algebraic span of bounded `U⁴`-null vectors. -/
def u4NullSpan
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Submodule ℂ (Lp ℂ 2 M.μ) :=
  Submodule.span ℂ (u4NullGenerators M hM)

/-- The closed analytic unstructured space `N₃`. -/
def u4NullClosedSpan
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Submodule ℂ (Lp ℂ 2 M.μ) :=
  (u4NullSpan M hM).topologicalClosure

/-- The analytic `Z₃` candidate is the orthogonal complement of `N₃`. -/
def hostKraZ3Subspace
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Submodule ℂ (Lp ℂ 2 M.μ) :=
  (u4NullClosedSpan M hM)ᗮ

/-- Every bounded `U⁴`-null generator is already a bounded `U³`-null
generator. -/
theorem u4NullGenerators_subset_u3NullGenerators
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    u4NullGenerators M hM ⊆
      Chapter02.HostKraZ2Characteristic.u3NullGenerators M hM := by
  intro G hG
  rcases hG with ⟨f, hf, hzero, rfl⟩
  refine ⟨f, hf, ?_, rfl⟩
  exact
    Chapter02.HostKraRelativeJoiningComplex.hostKraU3Power_eq_zero_of_hasZeroHostKraU4
      M hM f hf hzero

/-- The order-four algebraic null span is contained in the order-three
algebraic null span. -/
theorem u4NullSpan_le_u3NullSpan
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    u4NullSpan M hM ≤
      Chapter02.HostKraZ2Characteristic.u3NullSpan M hM := by
  apply Submodule.span_le.mpr
  intro G hG
  exact Submodule.subset_span
    (u4NullGenerators_subset_u3NullGenerators M hM hG)

/-- The closed order-four nullspace is contained in the closed order-three
nullspace. -/
theorem u4NullClosedSpan_le_u3NullClosedSpan
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    u4NullClosedSpan M hM ≤
      Chapter02.HostKraZ2Characteristic.u3NullClosedSpan M hM := by
  unfold u4NullClosedSpan
    Chapter02.HostKraZ2Characteristic.u3NullClosedSpan
  exact Submodule.topologicalClosure_minimal
    (u4NullSpan M hM)
    ((u4NullSpan_le_u3NullSpan M hM).trans
      (Chapter02.HostKraZ2Characteristic.u3NullSpan M hM).le_topologicalClosure)
    (Chapter02.HostKraZ2Characteristic.u3NullSpan M hM).isClosed_topologicalClosure

/-- The analytic Host--Kra candidates form the expected hierarchy
`Z₂ ≤ Z₃`. -/
theorem hostKraZ2Subspace_le_hostKraZ3Subspace
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter02.HostKraZ2Characteristic.hostKraZ2Subspace M hM ≤
      hostKraZ3Subspace M hM := by
  intro F hF
  rw [hostKraZ3Subspace, Submodule.mem_orthogonal]
  intro G hG
  rw [Chapter02.HostKraZ2Characteristic.hostKraZ2Subspace,
    Submodule.mem_orthogonal] at hF
  exact hF G (u4NullClosedSpan_le_u3NullClosedSpan M hM hG)

lemma isClosed_u4NullClosedSpan
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    IsClosed (u4NullClosedSpan M hM : Set (Lp ℂ 2 M.μ)) :=
  (u4NullSpan M hM).isClosed_topologicalClosure

lemma u4NullGenerator_mem_closedSpan
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {G : Lp ℂ 2 M.μ} (hG : G ∈ u4NullGenerators M hM) :
    G ∈ u4NullClosedSpan M hM :=
  (u4NullSpan M hM).le_topologicalClosure
    (Submodule.subset_span hG)

/-- The bounded `U⁴`-null generators are forward-invariant. -/
lemma u4NullGenerators_koopman
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {G : Lp ℂ 2 M.μ} (hG : G ∈ u4NullGenerators M hM) :
    (MultipleKhintchineCharacteristic.KData M hM).U G ∈
      u4NullGenerators M hM := by
  rcases hG with ⟨f, hf, hzero, rfl⟩
  let hfT : MemLp (f ∘ M.T) ⊤ M.μ :=
    hf.comp_measurePreserving hM.2
  refine ⟨f ∘ M.T, hfT, ?_, ?_⟩
  · exact
      (HostKraCubeSeminormDynamics.hasZeroHostKraU4_comp_iff
        M hM f hf).2 hzero
  · exact (boundedToLp_comp M hM f hf).symm

/-- The algebraic `U⁴`-null span is forward-invariant. -/
lemma u4NullSpan_koopman
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {G : Lp ℂ 2 M.μ} (hG : G ∈ u4NullSpan M hM) :
    (MultipleKhintchineCharacteristic.KData M hM).U G ∈
      u4NullSpan M hM := by
  let D := MultipleKhintchineCharacteristic.KData M hM
  let K : Submodule ℂ (Lp ℂ 2 M.μ) :=
    (u4NullSpan M hM).comap D.U.toLinearMap
  have hgen : u4NullGenerators M hM ⊆ K := by
    intro F hF
    change D.U F ∈ u4NullSpan M hM
    apply Submodule.subset_span
    simpa only [D] using u4NullGenerators_koopman M hM hF
  exact (Submodule.span_le.mpr hgen) hG

/-- The closed analytic nullspace `N₃` is forward-invariant. -/
lemma u4NullClosedSpan_koopman
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {G : Lp ℂ 2 M.μ} (hG : G ∈ u4NullClosedSpan M hM) :
    (MultipleKhintchineCharacteristic.KData M hM).U G ∈
      u4NullClosedSpan M hM := by
  let D := MultipleKhintchineCharacteristic.KData M hM
  let K : Submodule ℂ (Lp ℂ 2 M.μ) :=
    (u4NullClosedSpan M hM).comap D.U.toLinearMap
  have hspan : u4NullSpan M hM ≤ K := by
    intro F hF
    exact (u4NullSpan M hM).le_topologicalClosure
      (u4NullSpan_koopman M hM hF)
  have hKclosed : IsClosed (K : Set (Lp ℂ 2 M.μ)) := by
    change IsClosed
      (D.U ⁻¹' (u4NullClosedSpan M hM :
        Set (Lp ℂ 2 M.μ)))
    exact isClosed_u4NullClosedSpan M hM |>.preimage D.U.continuous
  exact
    (Submodule.topologicalClosure_minimal
      (u4NullSpan M hM) hspan hKclosed) hG

/-- The algebraic `U⁴`-null span is stable under conjugation. -/
theorem lpStar_mem_u4NullSpan
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {F : Lp ℂ 2 M.μ} (hF : F ∈ u4NullSpan M hM) :
    ForwardKroneckerFactor.lpStar M F ∈ u4NullSpan M hM := by
  refine Submodule.span_induction
    (p := fun F _ ↦ ForwardKroneckerFactor.lpStar M F ∈
      u4NullSpan M hM) ?_ ?_ ?_ ?_ hF
  · intro F hF
    rcases hF with ⟨f, hf, hzero, rfl⟩
    rw [lpStar_boundedToLp]
    exact Submodule.subset_span
      ⟨fun x ↦ star (f x), hf.star,
        HostKraU4Nullspace.hasZeroHostKraU4_star M hM f hf hzero, rfl⟩
  · change ForwardKroneckerFactor.lpStar M 0 ∈ u4NullSpan M hM
    rw [lpStar_zero]
    exact (u4NullSpan M hM).zero_mem
  · intro F G _ _ hF hG
    rw [lpStar_add]
    exact (u4NullSpan M hM).add_mem hF hG
  · intro c F _ hF
    rw [lpStar_smul]
    exact (u4NullSpan M hM).smul_mem (star c) hF

/-- The closed `U⁴`-null span is stable under conjugation. -/
theorem lpStar_mem_u4NullClosedSpan
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {F : Lp ℂ 2 M.μ} (hF : F ∈ u4NullClosedSpan M hM) :
    ForwardKroneckerFactor.lpStar M F ∈ u4NullClosedSpan M hM := by
  change F ∈ closure (u4NullSpan M hM : Set (Lp ℂ 2 M.μ)) at hF
  change ForwardKroneckerFactor.lpStar M F ∈
    closure (u4NullSpan M hM : Set (Lp ℂ 2 M.μ))
  rw [Metric.mem_closure_iff] at hF ⊢
  intro ε hε
  obtain ⟨G, hGspan, hGF⟩ := hF ε hε
  refine ⟨ForwardKroneckerFactor.lpStar M G,
    lpStar_mem_u4NullSpan M hM hGspan, ?_⟩
  rw [dist_eq_norm, ← ForwardKroneckerFactor.lpStar_sub,
    ForwardKroneckerFactor.norm_lpStar, ← dist_eq_norm]
  exact hGF

/-- The analytic `Z₃` subspace is stable under conjugation. -/
theorem lpStar_mem_hostKraZ3Subspace
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {F : Lp ℂ 2 M.μ} (hF : F ∈ hostKraZ3Subspace M hM) :
    ForwardKroneckerFactor.lpStar M F ∈ hostKraZ3Subspace M hM := by
  rw [hostKraZ3Subspace, Submodule.mem_orthogonal] at hF ⊢
  intro G hG
  rw [HostKraU3Nullspace.inner_lpStar_right M G F,
    hF (ForwardKroneckerFactor.lpStar M G)
      (lpStar_mem_u4NullClosedSpan M hM hG),
    star_zero]

end Chapter02.HostKraZ3Characteristic
