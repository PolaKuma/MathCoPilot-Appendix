import Chapter02.Spectral.SpectralDecomposition

open Classical Filter Set

noncomputable section

namespace Chapter02.OrthogonalCyclicDecomposition

universe u

/-- The smallest closed reducing subspace containing the first `n` members of
a sequence. -/
def initialSubmodule (D : HilbertOperatorData.{u}) (d : ℕ → D.H) (n : ℕ) :
    Submodule ℂ D.H where
  carrier := {y | ∀ K : Set D.H, IsClosedReducingSubspace D K →
    (∀ i < n, d i ∈ K) → y ∈ K}
  zero_mem' := by
    intro K hK hd
    exact hK.1
  add_mem' := by
    intro x y hx hy K hK hd
    simpa using hK.2.1 x (hx K hK hd) y (hy K hK hd) 1 1
  smul_mem' := by
    intro c x hx K hK hd
    simpa using hK.2.1 x (hx K hK hd) 0 hK.1 c 0

theorem initialSubmodule_reducing (D : HilbertOperatorData.{u})
    (d : ℕ → D.H) (n : ℕ) :
    IsClosedReducingSubspace D (initialSubmodule D d n : Set D.H) := by
  refine ⟨(initialSubmodule D d n).zero_mem, ?_, ?_, ?_⟩
  · intro x hx y hy a b
    exact (initialSubmodule D d n).add_mem
      ((initialSubmodule D d n).smul_mem a hx)
      ((initialSubmodule D d n).smul_mem b hy)
  · intro s hs x hlim K hK hd
    exact hK.2.2.1 s (fun i ↦ hs i K hK hd) x hlim
  · intro x
    constructor
    · intro hx K hK hd
      exact (hK.2.2.2 x).mp (hx K hK hd)
    · intro hUx K hK hd
      exact (hK.2.2.2 x).mpr (hUx K hK hd)

theorem initialSubmodule_isClosed (D : HilbertOperatorData.{u})
    (d : ℕ → D.H) (n : ℕ) :
    IsClosed (initialSubmodule D d n : Set D.H) := by
  rw [← isSeqClosed_iff_isClosed]
  intro s x hs hlim
  exact (initialSubmodule_reducing D d n).2.2.1 s hs x hlim

noncomputable instance initialSubmodule_hasOrthogonalProjection
    (D : HilbertOperatorData.{u}) (d : ℕ → D.H) (n : ℕ) :
    (initialSubmodule D d n).HasOrthogonalProjection := by
  letI : CompleteSpace (initialSubmodule D d n) :=
    (initialSubmodule_isClosed D d n).completeSpace_coe
  infer_instance

theorem initialSubmodule_mono (D : HilbertOperatorData.{u})
    (d : ℕ → D.H) {n m : ℕ} (hnm : n ≤ m) :
    initialSubmodule D d n ≤ initialSubmodule D d m := by
  intro x hx K hK hd
  exact hx K hK (fun i hi ↦ hd i (lt_of_lt_of_le hi hnm))

def residualSequence (D : HilbertOperatorData.{u})
    (d : ℕ → D.H) (n : ℕ) : D.H :=
  d n - (initialSubmodule D d n).starProjection (d n)

theorem residualSequence_mem_orthogonal (D : HilbertOperatorData.{u})
    (d : ℕ → D.H) (n : ℕ) :
    residualSequence D d n ∈ (initialSubmodule D d n)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal (d n)

theorem residualSequence_mem_initial_succ (D : HilbertOperatorData.{u})
    (d : ℕ → D.H) (n : ℕ) :
    residualSequence D d n ∈ initialSubmodule D d (n + 1) := by
  have hd : d n ∈ initialSubmodule D d (n + 1) := by
    intro K hK hgen
    exact hgen n (by omega)
  have hp : (initialSubmodule D d n).starProjection (d n) ∈
      initialSubmodule D d (n + 1) :=
    initialSubmodule_mono D d (Nat.le_succ n)
      ((initialSubmodule D d n).starProjection_apply_mem (d n))
  exact (initialSubmodule D d (n + 1)).sub_mem hd hp

theorem orthogonalCyclicSubspaces_symm (D : HilbertOperatorData.{u})
    {x y : D.H} (hxy : OrthogonalCyclicSubspaces D x y) :
    OrthogonalCyclicSubspaces D y x := by
  intro a b ha hb
  rw [← inner_conj_symm]
  rw [hxy b a hb ha, map_zero]

theorem residualSequence_pairwise_orthogonal (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (d : ℕ → D.H) :
    ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D
      (residualSequence D d i) (residualSequence D d j) := by
  intro i j hij
  wlog hijlt : i < j generalizing i j
  · apply orthogonalCyclicSubspaces_symm D
    exact this j i hij.symm (lt_of_le_of_ne (Nat.le_of_not_gt hijlt) hij.symm)
  have hxi : residualSequence D d i ∈ initialSubmodule D d j :=
    initialSubmodule_mono D d (by omega)
      (residualSequence_mem_initial_succ D d i)
  exact SpectralRelations.cyclic_subspaces_orthogonal_of_mem D
    (initialSubmodule D d j) (residualSequence D d i)
    (residualSequence D d j)
    (initialSubmodule_reducing D d j)
    (SpectralRelations.orthogonal_reducing D hD (initialSubmodule D d j)
      (initialSubmodule_reducing D d j))
    hxi (residualSequence_mem_orthogonal D d j)

/-- The smallest closed reducing subspace containing every member of a vector
sequence. -/
def generatedSubmodule (D : HilbertOperatorData.{u}) (x : ℕ → D.H) :
    Submodule ℂ D.H where
  carrier := {y | ∀ K : Set D.H, IsClosedReducingSubspace D K →
    (∀ n, x n ∈ K) → y ∈ K}
  zero_mem' := by
    intro K hK hx
    exact hK.1
  add_mem' := by
    intro y z hy hz K hK hx
    simpa using hK.2.1 y (hy K hK hx) z (hz K hK hx) 1 1
  smul_mem' := by
    intro c y hy K hK hx
    simpa using hK.2.1 y (hy K hK hx) 0 hK.1 c 0

theorem generatedSubmodule_reducing (D : HilbertOperatorData.{u})
    (x : ℕ → D.H) :
    IsClosedReducingSubspace D (generatedSubmodule D x : Set D.H) := by
  refine ⟨(generatedSubmodule D x).zero_mem, ?_, ?_, ?_⟩
  · intro y hy z hz a b
    exact (generatedSubmodule D x).add_mem
      ((generatedSubmodule D x).smul_mem a hy)
      ((generatedSubmodule D x).smul_mem b hz)
  · intro s hs y hlim K hK hx
    exact hK.2.2.1 s (fun n ↦ hs n K hK hx) y hlim
  · intro y
    constructor
    · intro hy K hK hx
      exact (hK.2.2.2 y).mp (hy K hK hx)
    · intro hUy K hK hx
      exact (hK.2.2.2 y).mpr (hUy K hK hx)

theorem generator_mem_generatedSubmodule (D : HilbertOperatorData.{u})
    (x : ℕ → D.H) (n : ℕ) : x n ∈ generatedSubmodule D x := by
  intro K hK hx
  exact hx n

theorem generatedSubmodule_isClosed (D : HilbertOperatorData.{u})
    (x : ℕ → D.H) : IsClosed (generatedSubmodule D x : Set D.H) := by
  rw [← isSeqClosed_iff_isClosed]
  intro s y hs hlim
  exact (generatedSubmodule_reducing D x).2.2.1 s hs y hlim

theorem initialSubmodule_le_generated_of_generators
    (D : HilbertOperatorData.{u}) (d x : ℕ → D.H) (n : ℕ)
    (hd : ∀ i < n, d i ∈ generatedSubmodule D x) :
    initialSubmodule D d n ≤ generatedSubmodule D x := by
  intro y hy
  exact hy _ (generatedSubmodule_reducing D x) hd

theorem dense_generators_mem_residual_generated (D : HilbertOperatorData.{u})
    (d : ℕ → D.H) :
    ∀ n, d n ∈ generatedSubmodule D (residualSequence D d) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hproj : (initialSubmodule D d n).starProjection (d n) ∈
          generatedSubmodule D (residualSequence D d) :=
        initialSubmodule_le_generated_of_generators D d
          (residualSequence D d) n ih
          ((initialSubmodule D d n).starProjection_apply_mem (d n))
      have hres : residualSequence D d n ∈
          generatedSubmodule D (residualSequence D d) :=
        generator_mem_generatedSubmodule D (residualSequence D d) n
      have hadd := (generatedSubmodule D (residualSequence D d)).add_mem
        hproj hres
      simpa [residualSequence] using hadd

theorem generatedSubmodule_eq_top_of_denseRange (D : HilbertOperatorData.{u})
    (d : ℕ → D.H) (hdense : DenseRange d) :
    generatedSubmodule D (residualSequence D d) = ⊤ := by
  apply top_unique
  intro y hy
  apply closure_minimal (s := Set.range d) (t :=
    (generatedSubmodule D (residualSequence D d) : Set D.H))
      (by
        rintro _ ⟨n, rfl⟩
        exact dense_generators_mem_residual_generated D d n)
      (generatedSubmodule_isClosed D (residualSequence D d))
  rw [hdense.closure_range]
  exact Set.mem_univ y

/-- The vectors orthogonal to every cyclic component. -/
def commonOrthogonal (D : HilbertOperatorData.{u}) (x : ℕ → D.H) :
    Submodule ℂ D.H :=
  ⨅ n, (SpectralDecomposition.cyclicSubmodule D (x n))ᗮ

theorem mem_commonOrthogonal_iff (D : HilbertOperatorData.{u})
    (x : ℕ → D.H) (y : D.H) :
    y ∈ commonOrthogonal D x ↔
      ∀ n, y ∈ (SpectralDecomposition.cyclicSubmodule D (x n))ᗮ := by
  exact Submodule.mem_iInf _

theorem commonOrthogonal_reducing (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H) :
    IsClosedReducingSubspace D (commonOrthogonal D x : Set D.H) := by
  have hred (n : ℕ) : IsClosedReducingSubspace D
      ((SpectralDecomposition.cyclicSubmodule D (x n))ᗮ : Set D.H) :=
    SpectralRelations.orthogonal_reducing D hD
      (SpectralDecomposition.cyclicSubmodule D (x n))
      (SpectralDecomposition.cyclicSubmodule_reducing D (x n))
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (0 : D.H) ∈ commonOrthogonal D x
    rw [mem_commonOrthogonal_iff]
    intro n
    exact (hred n).1
  · intro y hy z hz a b
    change y ∈ commonOrthogonal D x at hy
    change z ∈ commonOrthogonal D x at hz
    change a • y + b • z ∈ commonOrthogonal D x
    rw [mem_commonOrthogonal_iff] at hy hz ⊢
    intro n
    exact (hred n).2.1 y (hy n) z (hz n) a b
  · intro s hs y hlim
    change (∀ n, s n ∈ commonOrthogonal D x) at hs
    change y ∈ commonOrthogonal D x
    rw [mem_commonOrthogonal_iff]
    intro n
    exact (hred n).2.2.1 s
      (fun i ↦ (mem_commonOrthogonal_iff D x (s i)).1 (hs i) n) y hlim
  · intro y
    change (y ∈ commonOrthogonal D x ↔ D.U y ∈ commonOrthogonal D x)
    rw [mem_commonOrthogonal_iff, mem_commonOrthogonal_iff]
    constructor
    · intro hy n
      exact ((hred n).2.2.2 y).mp (hy n)
    · intro hUy n
      exact ((hred n).2.2.2 y).mpr (hUy n)

theorem generatedSubmodule_le_commonOrthogonal_orthogonal
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D) (x : ℕ → D.H) :
    generatedSubmodule D x ≤ (commonOrthogonal D x)ᗮ := by
  intro y hy
  apply hy _
    (SpectralRelations.orthogonal_reducing D hD (commonOrthogonal D x)
      (commonOrthogonal_reducing D hD x))
  intro n
  change x n ∈ (commonOrthogonal D x)ᗮ
  rw [Submodule.mem_orthogonal]
  intro z hz
  rw [mem_commonOrthogonal_iff] at hz
  have hzn := hz n
  rw [Submodule.mem_orthogonal] at hzn
  rw [← inner_conj_symm, hzn (x n)
    (SpectralDecomposition.generator_mem_cyclicSubmodule D (x n)), map_zero]

theorem commonOrthogonal_eq_bot_of_generated_eq_top
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D) (x : ℕ → D.H)
    (hgen : generatedSubmodule D x = ⊤) : commonOrthogonal D x = ⊥ := by
  have horthTop : (commonOrthogonal D x)ᗮ = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact generatedSubmodule_le_commonOrthogonal_orthogonal D hD x
  exact (Submodule.orthogonal_eq_top_iff (commonOrthogonal D x)).mp horthTop

theorem residualSequence_complete_of_denseRange (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (d : ℕ → D.H) (hdense : DenseRange d) :
    ∀ r : D.H,
      (∀ n, r ∈ (SpectralDecomposition.cyclicSubmodule D
        (residualSequence D d n))ᗮ) → r = 0 := by
  intro r hr
  have hbot : commonOrthogonal D (residualSequence D d) = ⊥ :=
    commonOrthogonal_eq_bot_of_generated_eq_top D hD _
      (generatedSubmodule_eq_top_of_denseRange D d hdense)
  have hrC : r ∈ commonOrthogonal D (residualSequence D d) :=
    (mem_commonOrthogonal_iff D _ r).2 hr
  rw [hbot] at hrC
  exact hrC

theorem residualSequence_isOrthogonalCyclicDecomposition
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (d : ℕ → D.H) (hdense : DenseRange d) :
    IsOrthogonalCyclicDecomposition D (residualSequence D d) := by
  exact SpectralDecomposition.orthogonalCyclicDecomposition_of_complete D _
    (residualSequence_pairwise_orthogonal D hD d)
    (residualSequence_complete_of_denseRange D hD d hdense)

theorem exists_orthogonalCyclicDecomposition
    (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D) :
    ∃ x : ℕ → D.H, IsOrthogonalCyclicDecomposition D x := by
  letI : TopologicalSpace.SeparableSpace D.H := hsep
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq D.H
  exact ⟨residualSequence D d,
    residualSequence_isOrthogonalCyclicDecomposition D hD d hd⟩

theorem residualSequence_mem_submodule
    (D : HilbertOperatorData.{u}) (d : ℕ → D.H)
    (S : Submodule ℂ D.H) (hS : IsClosedReducingSubspace D (S : Set D.H))
    (hd : ∀ n, d n ∈ S) (n : ℕ) : residualSequence D d n ∈ S := by
  have hinit : initialSubmodule D d n ≤ S := by
    intro y hy
    exact hy S hS (fun i hi ↦ hd i)
  have hp : (initialSubmodule D d n).starProjection (d n) ∈ S :=
    hinit ((initialSubmodule D d n).starProjection_apply_mem (d n))
  exact S.sub_mem (hd n) hp

theorem generatedResidual_le_submodule
    (D : HilbertOperatorData.{u}) (d : ℕ → D.H)
    (S : Submodule ℂ D.H) (hS : IsClosedReducingSubspace D (S : Set D.H))
    (hd : ∀ n, d n ∈ S) :
    generatedSubmodule D (residualSequence D d) ≤ S := by
  intro y hy
  exact hy S hS (residualSequence_mem_submodule D d S hS hd)

theorem denseSubtype_mem_generatedResidual
    (D : HilbertOperatorData.{u}) (S : Submodule ℂ D.H)
    (d : ℕ → S) (hdense : DenseRange d) :
    ∀ y : S, (y : D.H) ∈ generatedSubmodule D
      (residualSequence D (fun n ↦ (d n : D.H))) := by
  intro y
  let K : Set D.H := generatedSubmodule D
    (residualSequence D (fun n ↦ (d n : D.H)))
  apply closure_minimal (s := Set.range (fun n ↦ (d n : D.H))) (t := K)
      (by
        rintro _ ⟨n, rfl⟩
        exact dense_generators_mem_residual_generated D (fun n ↦ (d n : D.H)) n)
      (generatedSubmodule_isClosed D _)
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := hdense.exists_dist_lt y hε
  refine ⟨(d n : D.H), ⟨n, rfl⟩, ?_⟩
  exact hn

theorem residualSequence_complete_on_submodule
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (S : Submodule ℂ D.H) (hS : IsClosedReducingSubspace D (S : Set D.H))
    (d : ℕ → S) (hdense : DenseRange d) (r : D.H) (hrS : r ∈ S)
    (hr : ∀ n, r ∈ (SpectralDecomposition.cyclicSubmodule D
      (residualSequence D (fun i ↦ (d i : D.H)) n))ᗮ) : r = 0 := by
  let x : ℕ → D.H := residualSequence D (fun i ↦ (d i : D.H))
  have hrC : r ∈ commonOrthogonal D x :=
    (mem_commonOrthogonal_iff D x r).2 hr
  have hrOrth : r ∈ (commonOrthogonal D x)ᗮ := by
    apply generatedSubmodule_le_commonOrthogonal_orthogonal D hD x
    exact denseSubtype_mem_generatedResidual D S d hdense ⟨r, hrS⟩
  rw [Submodule.mem_orthogonal] at hrOrth
  exact inner_self_eq_zero.mp (hrOrth r hrC)

theorem tsum_projection_eq_on_submodule
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (S : Submodule ℂ D.H) (hS : IsClosedReducingSubspace D (S : Set D.H))
    (d : ℕ → S) (hdense : DenseRange d) (y : D.H) (hyS : y ∈ S) :
    ∑' n, SpectralDecomposition.cyclicProjectionFamily D
      (residualSequence D (fun i ↦ (d i : D.H))) y n = y := by
  let x : ℕ → D.H := residualSequence D (fun i ↦ (d i : D.H))
  have hxorth := residualSequence_pairwise_orthogonal D hD
    (fun i ↦ (d i : D.H))
  let p : D.H := ∑' n, SpectralDecomposition.cyclicProjectionFamily D x y n
  have hpS : p ∈ S := by
    have hsum := SpectralDecomposition.cyclicProjectionFamily_summable D x hxorth y
    apply hS.2.2.1
      (fun N ↦ ∑ n ∈ Finset.range N,
        SpectralDecomposition.cyclicProjectionFamily D x y n)
      (fun N ↦ ?_) p hsum.hasSum.tendsto_sum_nat
    apply Submodule.sum_mem
    intro n hn
    have hproj := SpectralDecomposition.cyclicProjectionFamily_mem D x y n
    exact hproj S hS
      (residualSequence_mem_submodule D _ S hS (fun i ↦ (d i).property) n)
  have hres : y - p = 0 := residualSequence_complete_on_submodule
    D hD S hS d hdense (y - p) (S.sub_mem hyS hpS)
    (fun n ↦ SpectralDecomposition.tsum_projection_residual_mem_orthogonal
      D x hxorth y n)
  exact (sub_eq_zero.mp hres).symm

theorem exists_orthogonalFamily_complete_on_submodule
    (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (S : Submodule ℂ D.H) (hS : IsClosedReducingSubspace D (S : Set D.H)) :
    ∃ x : ℕ → D.H,
      (∀ n, x n ∈ S) ∧
      (∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j)) ∧
      ∀ y : D.H, y ∈ S →
        ∑' n, SpectralDecomposition.cyclicProjectionFamily D x y n = y := by
  letI : TopologicalSpace.SeparableSpace D.H := hsep
  letI : TopologicalSpace.SeparableSpace S := inferInstance
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq S
  let x : ℕ → D.H := residualSequence D (fun n ↦ (d n : D.H))
  refine ⟨x, ?_, residualSequence_pairwise_orthogonal D hD _, ?_⟩
  · intro n
    exact residualSequence_mem_submodule D _ S hS (fun i ↦ (d i).property) n
  · intro y hy
    exact tsum_projection_eq_on_submodule D hD S hS d hd y hy

end Chapter02.OrthogonalCyclicDecomposition
