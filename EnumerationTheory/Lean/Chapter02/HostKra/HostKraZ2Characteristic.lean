import Chapter02.HostKra.HostKraU3Nullspace
import Chapter02.HostKra.HostKraU3ProgressionDecay

open Classical Filter MeasureTheory
open scoped BigOperators

noncomputable section

namespace Chapter02.HostKraZ2Characteristic

universe u

open HostKraCubeSeminorm

/-- Regard an essentially bounded function as an `L²` vector on a probability
system. -/
noncomputable def boundedToLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    Lp ℂ 2 M.μ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  exact (hf.mono_exponent (by simp)).toLp f

/-- The `L²` vectors represented by bounded `U³`-null functions. -/
def u3NullGenerators
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Set (Lp ℂ 2 M.μ) :=
  {G | ∃ f : M.X → ℂ, ∃ hf : MemLp f ⊤ M.μ,
    HasZeroHostKraU3 M hM f hf ∧ G = boundedToLp M hM f hf}

/-- The algebraic complex span of bounded `U³`-null vectors. -/
def u3NullSpan
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Submodule ℂ (Lp ℂ 2 M.μ) :=
  Submodule.span ℂ (u3NullGenerators M hM)

/-- The analytic unstructured subspace `N₂`: the closed complex span of
bounded `U³`-null vectors. -/
def u3NullClosedSpan
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Submodule ℂ (Lp ℂ 2 M.μ) :=
  (u3NullSpan M hM).topologicalClosure

/-- The analytic `Z₂` candidate is the orthogonal complement of `N₂`. -/
def hostKraZ2Subspace
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Submodule ℂ (Lp ℂ 2 M.μ) :=
  (u3NullClosedSpan M hM)ᗮ

/-- Passing a bounded representative through the transformation agrees
with applying the forward Koopman isometry to its `L²` class. -/
lemma boundedToLp_comp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    boundedToLp M hM (f ∘ M.T)
        (hf.comp_measurePreserving hM.2) =
      (MultipleKhintchineCharacteristic.KData M hM).U
        (boundedToLp M hM f hf) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  unfold boundedToLp
  rw [MultipleKhintchineKronecker.koopmanData_apply_toLp]
  apply Lp.ext
  filter_upwards [
    ((hf.comp_measurePreserving hM.2).mono_exponent
      (by simp)).coeFn_toLp,
    (((hf.mono_exponent (by simp)).comp_measurePreserving
      hM.2)).coeFn_toLp] with x hx hy
  rw [hx]
  simpa [Chapter01.koopman, Function.comp_def] using hy.symm

/-- The bounded `U³`-null generators are forward-invariant. -/
lemma u3NullGenerators_koopman
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {G : Lp ℂ 2 M.μ} (hG : G ∈ u3NullGenerators M hM) :
    (MultipleKhintchineCharacteristic.KData M hM).U G ∈
      u3NullGenerators M hM := by
  rcases hG with ⟨f, hf, hzero, rfl⟩
  let hfT : MemLp (f ∘ M.T) ⊤ M.μ :=
    hf.comp_measurePreserving hM.2
  refine ⟨f ∘ M.T, hfT, ?_, ?_⟩
  · exact
      (HostKraCubeSeminormDynamics.hasZeroHostKraU3_comp_iff
        M hM f hf).2 hzero
  · exact (boundedToLp_comp M hM f hf).symm

/-- The algebraic span of bounded `U³`-null vectors is forward-invariant. -/
lemma u3NullSpan_koopman
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {G : Lp ℂ 2 M.μ} (hG : G ∈ u3NullSpan M hM) :
    (MultipleKhintchineCharacteristic.KData M hM).U G ∈
      u3NullSpan M hM := by
  let D := MultipleKhintchineCharacteristic.KData M hM
  let K : Submodule ℂ (Lp ℂ 2 M.μ) :=
    (u3NullSpan M hM).comap D.U.toLinearMap
  have hgen : u3NullGenerators M hM ⊆ K := by
    intro G hG
    change D.U G ∈ u3NullSpan M hM
    apply Submodule.subset_span
    simpa only [D] using u3NullGenerators_koopman M hM hG
  exact (Submodule.span_le.mpr hgen) hG

/-- The closed analytic nullspace `N₂` is forward-invariant. -/
lemma u3NullClosedSpan_koopman
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {G : Lp ℂ 2 M.μ} (hG : G ∈ u3NullClosedSpan M hM) :
    (MultipleKhintchineCharacteristic.KData M hM).U G ∈
      u3NullClosedSpan M hM := by
  let D := MultipleKhintchineCharacteristic.KData M hM
  let K : Submodule ℂ (Lp ℂ 2 M.μ) :=
    (u3NullClosedSpan M hM).comap D.U.toLinearMap
  have hspan : u3NullSpan M hM ≤ K := by
    intro F hF
    exact (u3NullSpan M hM).le_topologicalClosure
      (u3NullSpan_koopman M hM hF)
  have hKclosed : IsClosed (K : Set (Lp ℂ 2 M.μ)) := by
    change IsClosed
      (D.U ⁻¹' (u3NullClosedSpan M hM :
        Set (Lp ℂ 2 M.μ)))
    exact
      (u3NullSpan M hM).isClosed_topologicalClosure.preimage
        D.U.continuous
  exact
    (Submodule.topologicalClosure_minimal
      (u3NullSpan M hM) hspan hKclosed) hG

lemma isClosed_u3NullClosedSpan
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    IsClosed (u3NullClosedSpan M hM : Set (Lp ℂ 2 M.μ)) :=
  (u3NullSpan M hM).isClosed_topologicalClosure

lemma u3NullGenerator_mem_closedSpan
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {G : Lp ℂ 2 M.μ} (hG : G ∈ u3NullGenerators M hM) :
    G ∈ u3NullClosedSpan M hM := by
  exact (u3NullSpan M hM).le_topologicalClosure
    (Submodule.subset_span hG)

theorem u3NullClosedSpan_hasOrthogonalProjection
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    (u3NullClosedSpan M hM).HasOrthogonalProjection := by
  let S := u3NullClosedSpan M hM
  letI : IsClosed (S : Set (Lp ℂ 2 M.μ)) :=
    isClosed_u3NullClosedSpan M hM
  letI : CompleteSpace S := IsClosed.completeSpace_coe
  infer_instance

/-- The `N₂` component of an `L²` vector. -/
noncomputable def u3UnstructuredPart
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) :
    Lp ℂ 2 M.μ := by
  letI : (u3NullClosedSpan M hM).HasOrthogonalProjection :=
    u3NullClosedSpan_hasOrthogonalProjection M hM
  exact (u3NullClosedSpan M hM).starProjection F

/-- The component orthogonal to the closed `U³`-null span. -/
noncomputable def hostKraZ2Part
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) :
    Lp ℂ 2 M.μ :=
  F - u3UnstructuredPart M hM F

lemma u3UnstructuredPart_mem
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) :
    u3UnstructuredPart M hM F ∈ u3NullClosedSpan M hM := by
  letI : (u3NullClosedSpan M hM).HasOrthogonalProjection :=
    u3NullClosedSpan_hasOrthogonalProjection M hM
  exact (u3NullClosedSpan M hM).starProjection_apply_mem F

lemma hostKraZ2Part_mem
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) :
    hostKraZ2Part M hM F ∈ hostKraZ2Subspace M hM := by
  letI : (u3NullClosedSpan M hM).HasOrthogonalProjection :=
    u3NullClosedSpan_hasOrthogonalProjection M hM
  exact (u3NullClosedSpan M hM).sub_starProjection_mem_orthogonal F

lemma hostKraZ2Part_add_u3UnstructuredPart
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) :
    hostKraZ2Part M hM F + u3UnstructuredPart M hM F = F := by
  simp [hostKraZ2Part]

/-- A translated Cesàro average of the bilinear progression, regarded as a
function of its second `L²` input. -/
noncomputable def translatedBilinearCesaro
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (N i : ℕ) : Lp ℂ 2 M.μ :=
  (((N + 1 : ℕ) : ℂ)⁻¹) •
    ∑ n ∈ Finset.range (N + 1),
      MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F G hFtop (i + n)

lemma doubleKoopmanProduct_add_right
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F (G + H) hFtop n =
      MultipleKhintchineCharacteristic.doubleKoopmanProduct
          M hM F G hFtop n +
        MultipleKhintchineCharacteristic.doubleKoopmanProduct
          M hM F H hFtop n := by
  unfold MultipleKhintchineCharacteristic.doubleKoopmanProduct
  rw [AlmostPeriodic.iterate_add]
  exact MultipleKhintchineKronecker.lpPointwiseMul_add_right _ _ _ _

lemma doubleKoopmanProduct_smul_right
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (c : ℂ) (n : ℕ) :
    MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F (c • G) hFtop n =
      c • MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F G hFtop n := by
  unfold MultipleKhintchineCharacteristic.doubleKoopmanProduct
  rw [AlmostPeriodic.iterate_smul]
  exact MultipleKhintchineKronecker.lpPointwiseMul_smul_right _ _ _ _

lemma translatedBilinearCesaro_add
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (N i : ℕ) :
    translatedBilinearCesaro M hM F (G + H) hFtop N i =
      translatedBilinearCesaro M hM F G hFtop N i +
        translatedBilinearCesaro M hM F H hFtop N i := by
  simp only [translatedBilinearCesaro, doubleKoopmanProduct_add_right,
    Finset.sum_add_distrib, smul_add]

lemma translatedBilinearCesaro_smul
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (c : ℂ) (N i : ℕ) :
    translatedBilinearCesaro M hM F (c • G) hFtop N i =
      c • translatedBilinearCesaro M hM F G hFtop N i := by
  simp only [translatedBilinearCesaro, doubleKoopmanProduct_smul_right]
  rw [← Finset.smul_sum]
  simp only [smul_smul, mul_comm]

/-- Uniform translated Cesàro cancellation for the bilinear progression with
fixed first input `F`. -/
def HasUniformBilinearCesaroZero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) : Prop :=
  ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
    ‖translatedBilinearCesaro M hM F G hFtop N i‖ < ε

theorem generator_hasUniformBilinearCesaroZero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (hG : G ∈ u3NullGenerators M hM) :
    HasUniformBilinearCesaroZero M hM F G hFtop := by
  rcases hG with ⟨g, hg, hzero, rfl⟩
  simpa [HasUniformBilinearCesaroZero, translatedBilinearCesaro,
    boundedToLp] using
    (Chapter02.HostKraU3ProgressionDecay.doubleKoopmanProduct_uniform_cesaro_zero_of_hasZeroHostKraU3
        M hM hErg F g hFtop hg C hC hFbound hzero)

lemma hasUniformBilinearCesaroZero_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    HasUniformBilinearCesaroZero M hM F 0 hFtop := by
  intro ε hε
  filter_upwards [] with N i
  have h :=
    translatedBilinearCesaro_smul M hM F (0 : Lp ℂ 2 M.μ)
      hFtop 0 N i
  simp only [zero_smul] at h
  rw [h, norm_zero]
  exact hε

lemma HasUniformBilinearCesaroZero.add
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hG : HasUniformBilinearCesaroZero M hM F G hFtop)
    (hH : HasUniformBilinearCesaroZero M hM F H hFtop) :
    HasUniformBilinearCesaroZero M hM F (G + H) hFtop := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  filter_upwards [hG (ε / 2) hε2, hH (ε / 2) hε2] with N hGN hHN i
  rw [translatedBilinearCesaro_add]
  calc
    ‖translatedBilinearCesaro M hM F G hFtop N i +
        translatedBilinearCesaro M hM F H hFtop N i‖
        ≤ ‖translatedBilinearCesaro M hM F G hFtop N i‖ +
          ‖translatedBilinearCesaro M hM F H hFtop N i‖ :=
      norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hGN i) (hHN i)
    _ = ε := by ring

lemma HasUniformBilinearCesaroZero.smul
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hG : HasUniformBilinearCesaroZero M hM F G hFtop)
    (c : ℂ) :
    HasUniformBilinearCesaroZero M hM F (c • G) hFtop := by
  by_cases hc : c = 0
  · subst c
    simpa using hasUniformBilinearCesaroZero_zero M hM F hFtop
  · intro ε hε
    have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hquot : 0 < ε / ‖c‖ := div_pos hε hcnorm
    filter_upwards [hG (ε / ‖c‖) hquot] with N hN i
    rw [translatedBilinearCesaro_smul, norm_smul]
    have hmul := mul_lt_mul_of_pos_left (hN i) hcnorm
    calc
      ‖c‖ * ‖translatedBilinearCesaro M hM F G hFtop N i‖
          < ‖c‖ * (ε / ‖c‖) := hmul
      _ = ε := by field_simp

theorem span_hasUniformBilinearCesaroZero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (hG : G ∈ u3NullSpan M hM) :
    HasUniformBilinearCesaroZero M hM F G hFtop := by
  refine Submodule.span_induction
    (p := fun G _ ↦ HasUniformBilinearCesaroZero M hM F G hFtop)
    ?_ ?_ ?_ ?_ hG
  · intro G hG
    exact generator_hasUniformBilinearCesaroZero
      M hM hErg F G hFtop C hC hFbound hG
  · exact hasUniformBilinearCesaroZero_zero M hM F hFtop
  · intro G H _ _ hG hH
    exact hG.add M hM F G H hFtop hH
  · intro c G _ hG
    exact hG.smul M hM F G hFtop c

/-- The translated averages are uniformly Lipschitz in their second input.
This estimate is the analytic input for passage from the algebraic span to
its closure. -/
lemma norm_translatedBilinearCesaro_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (N i : ℕ) :
    ‖translatedBilinearCesaro M hM F G hFtop N i‖ ≤ C * ‖G‖ := by
  rw [translatedBilinearCesaro, norm_smul]
  calc
    ‖(((N + 1 : ℕ) : ℂ)⁻¹)‖ *
          ‖∑ n ∈ Finset.range (N + 1),
            MultipleKhintchineCharacteristic.doubleKoopmanProduct
              M hM F G hFtop (i + n)‖
        ≤ ‖(((N + 1 : ℕ) : ℂ)⁻¹)‖ *
          ∑ n ∈ Finset.range (N + 1),
            ‖MultipleKhintchineCharacteristic.doubleKoopmanProduct
              M hM F G hFtop (i + n)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖(((N + 1 : ℕ) : ℂ)⁻¹)‖ *
          ∑ _n ∈ Finset.range (N + 1), C * ‖G‖ := by
      gcongr with n hn
      exact MultipleKhintchineCharacteristic.norm_doubleKoopmanProduct_le
        M hM F G hFtop C hC hFbound (i + n)
    _ = C * ‖G‖ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        norm_inv, Complex.norm_natCast]
      have hpos : (0 : ℝ) < N + 1 := by positivity
      field_simp

/-- Every vector in the closed `U³`-null span is characteristic-null for the
bilinear progression. -/
theorem closedSpan_hasUniformBilinearCesaroZero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (hG : G ∈ u3NullClosedSpan M hM) :
    HasUniformBilinearCesaroZero M hM F G hFtop := by
  by_cases hC0 : C = 0
  · intro ε hε
    filter_upwards [] with N i
    have hbound :=
      norm_translatedBilinearCesaro_le
        M hM F G hFtop C hC hFbound N i
    rw [hC0, zero_mul] at hbound
    have hz :
        ‖translatedBilinearCesaro M hM F G hFtop N i‖ = 0 :=
      le_antisymm hbound (norm_nonneg _)
    rw [hz]
    exact hε
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    intro ε hε
    have hδ : 0 < ε / (2 * C) := div_pos hε (mul_pos two_pos hCpos)
    change G ∈ closure (u3NullSpan M hM : Set (Lp ℂ 2 M.μ)) at hG
    obtain ⟨H, hHspan, hHG⟩ :=
      SeminormedAddCommGroup.mem_closure_iff.1 hG (ε / (2 * C)) hδ
    have hHzero :=
      span_hasUniformBilinearCesaroZero
        M hM hErg F H hFtop C hC hFbound hHspan
    have hε2 : 0 < ε / 2 := half_pos hε
    filter_upwards [hHzero (ε / 2) hε2] with N hHN i
    have havg :
        translatedBilinearCesaro M hM F G hFtop N i =
          translatedBilinearCesaro M hM F H hFtop N i +
            translatedBilinearCesaro M hM F (G - H) hFtop N i := by
      rw [← translatedBilinearCesaro_add]
      congr 1
      abel
    rw [havg]
    calc
      ‖translatedBilinearCesaro M hM F H hFtop N i +
          translatedBilinearCesaro M hM F (G - H) hFtop N i‖
          ≤ ‖translatedBilinearCesaro M hM F H hFtop N i‖ +
            ‖translatedBilinearCesaro M hM F (G - H) hFtop N i‖ :=
        norm_add_le _ _
      _ ≤ ‖translatedBilinearCesaro M hM F H hFtop N i‖ +
            C * ‖G - H‖ := by
        gcongr
        exact norm_translatedBilinearCesaro_le
          M hM F (G - H) hFtop C hC hFbound N i
      _ < ε / 2 + C * (ε / (2 * C)) := by
        exact add_lt_add (hHN i)
          (mul_lt_mul_of_pos_left hHG hCpos)
      _ = ε := by
        field_simp
        ring

/-- The orthogonal-projection residual is invisible to every bounded first
factor in the bilinear progression.  This is the analytic `Z₂`
characteristicity statement obtained in this module. -/
theorem u3UnstructuredPart_hasUniformBilinearCesaroZero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C) :
    HasUniformBilinearCesaroZero M hM F
      (u3UnstructuredPart M hM G) hFtop := by
  exact closedSpan_hasUniformBilinearCesaroZero
    M hM hErg F (u3UnstructuredPart M hM G)
      hFtop C hC hFbound (u3UnstructuredPart_mem M hM G)

/-- The closed span of bounded `U³`-null vectors is contained in the
continuous-spectral complement of the almost-periodic Koopman subspace. -/
theorem u3NullClosedSpan_le_almostPeriodic_orthogonal
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M) :
    u3NullClosedSpan M hM ≤
      (AlmostPeriodicIsometry.almostPeriodicSubmodule
        (MultipleKhintchineCharacteristic.KData M hM))ᗮ := by
  let D := MultipleKhintchineCharacteristic.KData M hM
  let K : Submodule ℂ (Lp ℂ 2 M.μ) :=
    (AlmostPeriodicIsometry.almostPeriodicSubmodule D)ᗮ
  have hspan : u3NullSpan M hM ≤ K := by
    apply Submodule.span_le.mpr
    intro G hG
    rcases hG with ⟨g, hg, hzero, rfl⟩
    change boundedToLp M hM g hg ∈
      (AlmostPeriodicIsometry.almostPeriodicSubmodule D)ᗮ
    rw [Submodule.mem_orthogonal]
    intro Y hY
    have hcont :=
      Chapter02.HostKraU3ProgressionDecay.hasZeroHostKraU3_implies_continuous
        M hM hErg g hg hzero
    have horth :=
      AlmostPeriodicIsometry.continuous_inner_almostPeriodic_eq_zero
        D
        (fun X ↦
          (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map X)
        (boundedToLp M hM g hg) Y
        (by simpa [D, boundedToLp] using hcont) hY
    exact inner_eq_zero_symm.mpr horth
  exact Submodule.topologicalClosure_minimal
    (u3NullSpan M hM) hspan (Submodule.isClosed_orthogonal _)

/-- Every forward almost-periodic Koopman vector belongs to analytic `Z₂`.
This identifies the already constructed Kronecker factor as an unconditional
subfactor of the Host--Kra candidate, and is the compact base case for the
dual-function algebra construction. -/
theorem almostPeriodic_mem_hostKraZ2Subspace
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    {F : Lp ℂ 2 M.μ}
    (hF : IsAlmostPeriodicVector
      (MultipleKhintchineCharacteristic.KData M hM) F) :
    F ∈ hostKraZ2Subspace M hM := by
  rw [hostKraZ2Subspace, Submodule.mem_orthogonal]
  intro G hG
  have hGorth :=
    u3NullClosedSpan_le_almostPeriodic_orthogonal M hM hErg hG
  exact inner_eq_zero_symm.mpr (hGorth F hF)

/-- The constant-one `L²` vector belongs to the analytic `Z₂` subspace. -/
theorem oneLp_mem_hostKraZ2Subspace
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M) :
    CorrelationMean.oneLp M hM ∈ hostKraZ2Subspace M hM := by
  let D := MultipleKhintchineCharacteristic.KData M hM
  have honeAP :
      IsAlmostPeriodicVector D (CorrelationMean.oneLp M hM) := by
    apply AlmostPeriodicIsometry.eigenvector_almostPeriodic D
      (fun X ↦
        (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map X)
    refine ⟨?_, (1 : ℂ), ?_⟩
    · intro hzero
      have hself := WeakSpectrum.inner_oneLp_self M hM
      rw [hzero, inner_zero_left] at hself
      exact one_ne_zero hself.symm
    · have hfix := WeakSpectrum.koopmanData_iter_oneLp M hM 1
      simpa only [D, MultipleKhintchineCharacteristic.KData,
        MultipleKhintchineKronecker.koopmanData,
        Function.iterate_one, one_smul] using hfix
  rw [hostKraZ2Subspace, Submodule.mem_orthogonal]
  intro G hG
  have hGorth :=
    u3NullClosedSpan_le_almostPeriodic_orthogonal M hM hErg hG
  exact inner_eq_zero_symm.mpr
    (hGorth (CorrelationMean.oneLp M hM) honeAP)

lemma lpStar_zero
    (M : System.{u}) :
    ForwardKroneckerFactor.lpStar M (0 : Lp ℂ 2 M.μ) = 0 := by
  apply Lp.ext
  filter_upwards [
    ForwardKroneckerFactor.lpStar_coe M (0 : Lp ℂ 2 M.μ),
    Lp.coeFn_zero ℂ 2 M.μ] with x hstar hzero
  rw [hstar, hzero]
  change star (0 : ℂ) = 0
  exact star_zero ℂ

lemma lpStar_add
    (M : System.{u}) (F G : Lp ℂ 2 M.μ) :
    ForwardKroneckerFactor.lpStar M (F + G) =
      ForwardKroneckerFactor.lpStar M F +
        ForwardKroneckerFactor.lpStar M G := by
  apply Lp.ext
  filter_upwards [
    ForwardKroneckerFactor.lpStar_coe M (F + G),
    ForwardKroneckerFactor.lpStar_coe M F,
    ForwardKroneckerFactor.lpStar_coe M G,
    Lp.coeFn_add F G,
    Lp.coeFn_add (ForwardKroneckerFactor.lpStar M F)
      (ForwardKroneckerFactor.lpStar M G)] with x hsum hF hG hFG hout
  rw [hsum, hFG, hout]
  simp only [Pi.add_apply]
  rw [hF, hG, star_add]

lemma lpStar_smul
    (M : System.{u}) (c : ℂ) (F : Lp ℂ 2 M.μ) :
    ForwardKroneckerFactor.lpStar M (c • F) =
      star c • ForwardKroneckerFactor.lpStar M F := by
  apply Lp.ext
  filter_upwards [
    ForwardKroneckerFactor.lpStar_coe M (c • F),
    ForwardKroneckerFactor.lpStar_coe M F,
    Lp.coeFn_smul c F,
    Lp.coeFn_smul (star c)
      (ForwardKroneckerFactor.lpStar M F)] with x hstar hF hcin hcout
  rw [hstar, hcin, hcout]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hF, star_mul]
  ring

lemma lpStar_boundedToLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    ForwardKroneckerFactor.lpStar M (boundedToLp M hM f hf) =
      boundedToLp M hM (fun x ↦ star (f x)) hf.star := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let hf2 : MemLp f 2 M.μ := hf.mono_exponent (by simp)
  let hfs2 : MemLp (fun x ↦ star (f x)) 2 M.μ :=
    hf.star.mono_exponent (by simp)
  change ForwardKroneckerFactor.lpStar M (hf2.toLp f) =
    hfs2.toLp (fun x ↦ star (f x))
  apply Lp.ext
  filter_upwards [
    ForwardKroneckerFactor.lpStar_coe M (hf2.toLp f),
    hf2.coeFn_toLp, hfs2.coeFn_toLp] with x hstar hfX hfsX
  rw [hstar, hfX, hfsX]

/-- The algebraic `U³`-null span is stable under pointwise conjugation. -/
theorem lpStar_mem_u3NullSpan
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {F : Lp ℂ 2 M.μ} (hF : F ∈ u3NullSpan M hM) :
    ForwardKroneckerFactor.lpStar M F ∈ u3NullSpan M hM := by
  refine Submodule.span_induction
    (p := fun F _ ↦ ForwardKroneckerFactor.lpStar M F ∈
      u3NullSpan M hM) ?_ ?_ ?_ ?_ hF
  · intro F hF
    rcases hF with ⟨f, hf, hzero, rfl⟩
    rw [lpStar_boundedToLp]
    exact Submodule.subset_span
      ⟨fun x ↦ star (f x), hf.star,
        HostKraU3Nullspace.hasZeroHostKraU3_star M hM f hf hzero, rfl⟩
  · change ForwardKroneckerFactor.lpStar M 0 ∈ u3NullSpan M hM
    rw [lpStar_zero]
    exact (u3NullSpan M hM).zero_mem
  · intro F G _ _ hF hG
    rw [lpStar_add]
    exact (u3NullSpan M hM).add_mem hF hG
  · intro c F _ hF
    rw [lpStar_smul]
    exact (u3NullSpan M hM).smul_mem (star c) hF

/-- The closed `U³`-null span is stable under pointwise conjugation. -/
theorem lpStar_mem_u3NullClosedSpan
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {F : Lp ℂ 2 M.μ} (hF : F ∈ u3NullClosedSpan M hM) :
    ForwardKroneckerFactor.lpStar M F ∈ u3NullClosedSpan M hM := by
  change F ∈ closure (u3NullSpan M hM : Set (Lp ℂ 2 M.μ)) at hF
  change ForwardKroneckerFactor.lpStar M F ∈
    closure (u3NullSpan M hM : Set (Lp ℂ 2 M.μ))
  rw [Metric.mem_closure_iff] at hF ⊢
  intro ε hε
  obtain ⟨G, hGspan, hGF⟩ := hF ε hε
  refine ⟨ForwardKroneckerFactor.lpStar M G,
    lpStar_mem_u3NullSpan M hM hGspan, ?_⟩
  rw [dist_eq_norm, ← ForwardKroneckerFactor.lpStar_sub,
    ForwardKroneckerFactor.norm_lpStar, ← dist_eq_norm]
  exact hGF

/-- The analytic `Z₂` subspace is stable under pointwise conjugation. -/
theorem lpStar_mem_hostKraZ2Subspace
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {F : Lp ℂ 2 M.μ} (hF : F ∈ hostKraZ2Subspace M hM) :
    ForwardKroneckerFactor.lpStar M F ∈ hostKraZ2Subspace M hM := by
  rw [hostKraZ2Subspace, Submodule.mem_orthogonal] at hF ⊢
  intro G hG
  rw [HostKraU3Nullspace.inner_lpStar_right M G F,
    hF (ForwardKroneckerFactor.lpStar M G)
      (lpStar_mem_u3NullClosedSpan M hM hG),
    star_zero]

end Chapter02.HostKraZ2Characteristic
