import Chapter02.HallPetresco.HallPetrescoTwoStepGroup

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoNormalForm

open Chapter02.HallPetrescoTwoStepGroup

universe u v

/-- Reordering two factors introduces the commutator in the convention used
by Mathlib. -/
theorem mul_eq_commutatorElement_mul_swap
    {H : Type u} [Group H] (a b : H) :
    a * b = ⁅a, b⁆ * b * a := by
  simp [commutatorElement_def, mul_assoc]

/-- In a two-step group, moving a power past one factor produces the
corresponding power of the central commutator. -/
theorem pow_mul_eq_commutatorElement_pow_mul
    {H : Type u} [Group H] (a b : H)
    (hcentral : ⁅a, b⁆ ∈ Subgroup.center H) (n : ℕ) :
    a ^ n * b = ⁅a, b⁆ ^ n * b * a ^ n := by
  let c := ⁅a, b⁆
  have hab : a * b = c * b * a :=
    mul_eq_commutatorElement_mul_swap a b
  have hcomm (m : ℕ) : a ^ m * c = c * a ^ m :=
    Subgroup.mem_center_iff.mp hcentral (a ^ m)
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        a ^ (n + 1) * b = a ^ n * (a * b) := by
          rw [pow_succ]
          group
        _ = a ^ n * (c * b * a) := by rw [hab]
        _ = (a ^ n * c) * b * a := by group
        _ = (c * a ^ n) * b * a := by rw [hcomm]
        _ = c * (a ^ n * b) * a := by group
        _ = c * (c ^ n * b * a ^ n) * a := by
          rw [ih]
        _ = c ^ (n + 1) * b * a ^ (n + 1) := by
          rw [pow_succ, pow_succ]
          group

theorem mul_pow_two_eq_commutatorElement
    {H : Type u} [Group H] (a b : H)
    (hcentral : ⁅b, a⁆ ∈ Subgroup.center H) :
    (a * b) ^ 2 = ⁅b, a⁆ * a ^ 2 * b ^ 2 := by
  let c := ⁅b, a⁆
  have hba : b * a = c * a * b :=
    mul_eq_commutatorElement_mul_swap b a
  have hac : a * c = c * a :=
    Subgroup.mem_center_iff.mp hcentral a
  calc
    (a * b) ^ 2 = a * (b * a) * b := by
      rw [pow_two]
      group
    _ = a * (c * a * b) * b := by rw [hba]
    _ = (a * c) * a * b * b := by group
    _ = (c * a) * a * b * b := by rw [hac]
    _ = c * a ^ 2 * b ^ 2 := by simp [pow_two, mul_assoc]

theorem mul_pow_three_eq_commutatorElement
    {H : Type u} [Group H] (a b : H)
    (hcentral : ⁅b, a⁆ ∈ Subgroup.center H) :
    (a * b) ^ 3 = ⁅b, a⁆ ^ 3 * a ^ 3 * b ^ 3 := by
  let c := ⁅b, a⁆
  have hb2a : b ^ 2 * a = c ^ 2 * a * b ^ 2 :=
    pow_mul_eq_commutatorElement_pow_mul b a hcentral 2
  have ha2c2 : a ^ 2 * c ^ 2 = c ^ 2 * a ^ 2 := by
    exact Subgroup.mem_center_iff.mp ((Subgroup.center H).pow_mem hcentral 2) (a ^ 2)
  calc
    (a * b) ^ 3 = (a * b) ^ 2 * (a * b) := by
      rw [show (3 : ℕ) = 2 + 1 by omega, pow_succ]
    _ = (c * a ^ 2 * b ^ 2) * (a * b) := by
      rw [mul_pow_two_eq_commutatorElement a b hcentral]
    _ = c * a ^ 2 * ((b ^ 2 * a) * b) := by group
    _ = c * a ^ 2 * ((c ^ 2 * a * b ^ 2) * b) := by rw [hb2a]
    _ = c * (a ^ 2 * c ^ 2) * a * b ^ 2 * b := by group
    _ = c * (c ^ 2 * a ^ 2) * a * b ^ 2 * b := by rw [ha2c2]
    _ = c ^ 3 * a ^ 3 * b ^ 3 := by group

/-- Parameters `(g,a,z)` for a two-step Hall polynomial. -/
abbrev Parameters
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :=
  (H × H) × (Fin N.torusDim → Circle)

/-- The four-coordinate Hall polynomial
`j(g,a,z)_r = g a^r ι(z)^(choose r 2)`. -/
def hallTuple
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (p : Parameters N) : Vertex → H :=
  diagonal p.1.1 * linear p.1.2 *
    quadratic (N.centralHom p.2)

@[simp]
theorem hallTuple_apply
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (p : Parameters N) (j : Vertex) :
    hallTuple N p j =
      p.1.1 * p.1.2 ^ j.val *
        N.centralHom p.2 ^ j.val.choose 2 :=
  rfl

theorem continuous_hallTuple
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    Continuous (hallTuple N) := by
  rw [continuous_pi_iff]
  intro j
  simp only [hallTuple_apply]
  exact
    ((continuous_fst.comp continuous_fst).mul
      ((continuous_snd.comp continuous_fst).pow j.val)).mul
        ((N.continuous_centralHom.comp continuous_snd).pow
          (j.val.choose 2))

theorem diagonal_eq_hallTuple
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) (g : H) :
    diagonal g =
      hallTuple N ((g, 1), (1 : Fin N.torusDim → Circle)) := by
  funext j
  fin_cases j <;> simp [hallTuple]

theorem linear_eq_hallTuple
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) (a : H) :
    linear a =
      hallTuple N ((1, a), (1 : Fin N.torusDim → Circle)) := by
  funext j
  fin_cases j <;> simp [hallTuple]

theorem quadraticCentral_eq_hallTuple
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (z : Fin N.torusDim → Circle) :
    quadratic (N.centralHom z) =
      hallTuple N ((1, 1), z) := by
  funext j
  fin_cases j <;> simp [hallTuple]

theorem hallTuple_mem_subgroup
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (p : Parameters N) :
    hallTuple N p ∈ subgroup N := by
  exact (subgroup N).mul_mem
    ((subgroup N).mul_mem
      (diagonal_mem_subgroup N p.1.1)
      (linear_mem_subgroup N p.1.2))
    (quadratic_central_mem_subgroup N p.2)

private theorem commute_of_mem_center
    {H : Type u} [Group H] {c : H}
    (hc : c ∈ Subgroup.center H) (x : H) :
    Commute c x :=
  (Subgroup.mem_center_iff.mp hc x).symm

private theorem hall_coordinate_mul
    {H : Type u} [Group H]
    (g a h b u v c d e : H) (n k : ℕ)
    (hu : u ∈ Subgroup.center H)
    (hv : v ∈ Subgroup.center H)
    (hc : c ∈ Subgroup.center H)
    (he : e = v⁻¹ * c * d)
    (hah : a ^ n * h = u ^ n * h * a ^ n)
    (hab : (a * b) ^ n = v ^ k * a ^ n * b ^ n) :
    g * a ^ n * c ^ k * (h * b ^ n * d ^ k) =
      g * h * (u * a * b) ^ n * e ^ k := by
  have hcpow : c ^ k ∈ Subgroup.center H :=
    (Subgroup.center H).pow_mem hc k
  have hvpow : v ^ k ∈ Subgroup.center H :=
    (Subgroup.center H).pow_mem hv k
  have hvinv : v⁻¹ ∈ Subgroup.center H :=
    (Subgroup.center H).inv_mem hv
  have hmove_c :
      (g * a ^ n) * c ^ k * ((h * b ^ n) * d ^ k) =
        (g * a ^ n) * (h * b ^ n) * (c ^ k * d ^ k) := by
    calc
      (g * a ^ n) * c ^ k * ((h * b ^ n) * d ^ k) =
          (g * a ^ n) * (c ^ k * (h * b ^ n)) * d ^ k := by group
      _ = (g * a ^ n) * ((h * b ^ n) * c ^ k) * d ^ k := by
        rw [(commute_of_mem_center hcpow (h * b ^ n)).eq]
      _ = (g * a ^ n) * (h * b ^ n) * (c ^ k * d ^ k) := by group
  have hu_h : Commute (u ^ n) h :=
    commute_of_mem_center ((Subgroup.center H).pow_mem hu n) h
  have hu_ab : Commute u (a * b) :=
    commute_of_mem_center hu (a * b)
  have hv_ab : Commute (v ^ k) (a ^ n * b ^ n) :=
    commute_of_mem_center hvpow (a ^ n * b ^ n)
  have hvinv_cd : Commute v⁻¹ (c * d) :=
    commute_of_mem_center hvinv (c * d)
  have hc_d : Commute c d :=
    commute_of_mem_center hc d
  have hepow :
      e ^ k = (v⁻¹) ^ k * (c ^ k * d ^ k) := by
    rw [he]
    calc
      (v⁻¹ * c * d) ^ k = (v⁻¹ * (c * d)) ^ k := by
        congr 1
        group
      _ = (v⁻¹) ^ k * (c * d) ^ k := hvinv_cd.mul_pow k
      _ = (v⁻¹) ^ k * (c ^ k * d ^ k) := by rw [hc_d.mul_pow k]
  have hcancel :
      v ^ k * (a ^ n * b ^ n) * e ^ k =
        (a ^ n * b ^ n) * (c ^ k * d ^ k) := by
    rw [hepow, hv_ab.eq]
    simp only [inv_pow]
    group
  calc
    g * a ^ n * c ^ k * (h * b ^ n * d ^ k) =
        (g * a ^ n) * c ^ k * ((h * b ^ n) * d ^ k) := by group
    _ = (g * a ^ n) * (h * b ^ n) * (c ^ k * d ^ k) := hmove_c
    _ = g * (a ^ n * h) * b ^ n * (c ^ k * d ^ k) := by group
    _ = g * (u ^ n * h * a ^ n) * b ^ n * (c ^ k * d ^ k) := by
      rw [hah]
    _ = g * h * u ^ n * (a ^ n * b ^ n) * (c ^ k * d ^ k) := by
      rw [hu_h.eq]
      group
    _ = g * h * u ^ n *
        ((a ^ n * b ^ n) * (c ^ k * d ^ k)) := by group
    _ = g * h * u ^ n *
        (v ^ k * (a ^ n * b ^ n) * e ^ k) := by rw [hcancel]
    _ = g * h * u ^ n *
        (v ^ k * a ^ n * b ^ n) * e ^ k := by group
    _ = g * h * u ^ n * (a * b) ^ n * e ^ k := by rw [← hab]
    _ = g * h * (u ^ n * (a * b) ^ n) * e ^ k := by group
    _ = g * h * (u * (a * b)) ^ n * e ^ k := by
      rw [hu_ab.mul_pow n]
    _ = g * h * (u * a * b) ^ n * e ^ k := by group

/-- Explicit multiplication law for four-coordinate Hall polynomials. -/
theorem hallTuple_mul_eq
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (g a h b : H)
    (z w t : Fin N.torusDim → Circle)
    (ht : N.centralHom t =
      ⁅b, a⁆⁻¹ * N.centralHom z * N.centralHom w) :
    hallTuple N ((g, a), z) * hallTuple N ((h, b), w) =
      hallTuple N ((g * h, ⁅a, h⁆ * a * b), t) := by
  let u := ⁅a, h⁆
  let v := ⁅b, a⁆
  let c := N.centralHom z
  let d := N.centralHom w
  let e := v⁻¹ * c * d
  have ht' : N.centralHom t = e := by
    simpa [e, v, c, d] using ht
  have hu_commutator : u ∈ commutator H := by
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_top a) (Subgroup.mem_top h)
  have hv_commutator : v ∈ commutator H := by
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_top b) (Subgroup.mem_top a)
  have hu_center : u ∈ Subgroup.center H :=
    N.commutator_le_center hu_commutator
  have hv_center : v ∈ Subgroup.center H :=
    N.commutator_le_center hv_commutator
  have hc_center : c ∈ Subgroup.center H := by
    exact N.centralHom_mem_center z
  funext j
  fin_cases j
  · simp [hallTuple]
  · simpa [hallTuple, u, c, d, ht'] using
      hall_coordinate_mul g a h b u v c d e 1 0
        hu_center hv_center hc_center rfl
        (by simpa [u] using mul_eq_commutatorElement_mul_swap a h)
        (by simp)
  · simpa [hallTuple, u, v, c, d, ht'] using
      hall_coordinate_mul g a h b u v c d e 2 1
        hu_center hv_center hc_center rfl
        (pow_mul_eq_commutatorElement_pow_mul a h hu_center 2)
        (by simpa [v] using mul_pow_two_eq_commutatorElement a b hv_center)
  · simpa [hallTuple, u, v, c, d, ht'] using
      hall_coordinate_mul g a h b u v c d e 3 3
        hu_center hv_center hc_center rfl
        (pow_mul_eq_commutatorElement_pow_mul a h hu_center 3)
        (mul_pow_three_eq_commutatorElement a b hv_center)

/-- The four-coordinate Hall polynomials are closed under pointwise
multiplication.  The new quadratic coefficient absorbs the commutator
created when the two linear coefficients are multiplied. -/
theorem exists_hallTuple_mul
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (p q : Parameters N) :
    ∃ r : Parameters N, hallTuple N p * hallTuple N q = hallTuple N r := by
  rcases p with ⟨⟨g, a⟩, z⟩
  rcases q with ⟨⟨h, b⟩, w⟩
  let u := ⁅a, h⁆
  let v := ⁅b, a⁆
  let c := N.centralHom z
  let d := N.centralHom w
  let e := v⁻¹ * c * d
  have hu_commutator : u ∈ commutator H := by
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_top a) (Subgroup.mem_top h)
  have hv_commutator : v ∈ commutator H := by
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_top b) (Subgroup.mem_top a)
  have hc_commutator : c ∈ commutator H := by
    rw [← N.centralHom_range]
    exact ⟨z, rfl⟩
  have hd_commutator : d ∈ commutator H := by
    rw [← N.centralHom_range]
    exact ⟨w, rfl⟩
  have he_commutator : e ∈ commutator H := by
    exact (commutator H).mul_mem
      ((commutator H).mul_mem
        ((commutator H).inv_mem hv_commutator)
        hc_commutator)
      hd_commutator
  have he_range : e ∈ N.centralHom.range := by
    rw [N.centralHom_range]
    exact he_commutator
  rcases he_range with ⟨t, ht⟩
  refine ⟨((g * h, u * a * b), t), ?_⟩
  simpa [u, v, c, d, e] using hallTuple_mul_eq N g a h b z w t ht

/-- The pointwise inverse of a four-coordinate Hall polynomial is again
a four-coordinate Hall polynomial. -/
theorem exists_hallTuple_inv
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (p : Parameters N) :
    ∃ q : Parameters N, (hallTuple N p)⁻¹ = hallTuple N q := by
  rcases p with ⟨⟨g, a⟩, z⟩
  let c := N.centralHom z
  let u := ⁅a, g⁻¹⁆
  let b := (u * a)⁻¹
  let v := ⁅b, a⁆
  let d := c⁻¹ * v
  have hv_commutator : v ∈ commutator H := by
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_top b) (Subgroup.mem_top a)
  have hc_commutator : c ∈ commutator H := by
    rw [← N.centralHom_range]
    exact ⟨z, rfl⟩
  have hd_commutator : d ∈ commutator H := by
    exact (commutator H).mul_mem
      ((commutator H).inv_mem hc_commutator)
      hv_commutator
  have hd_range : d ∈ N.centralHom.range := by
    rw [N.centralHom_range]
    exact hd_commutator
  rcases hd_range with ⟨w, hw⟩
  have ht :
      N.centralHom (1 : Fin N.torusDim → Circle) =
        ⁅b, a⁆⁻¹ * N.centralHom z * N.centralHom w := by
    rw [map_one, hw]
    change (1 : H) = v⁻¹ * c * d
    dsimp [d]
    group
  have hub : u * a * b = 1 := by
    dsimp [b]
    group
  have hmul :=
    hallTuple_mul_eq N g a g⁻¹ b z w
      (1 : Fin N.torusDim → Circle) ht
  have hmul_one :
      hallTuple N ((g, a), z) * hallTuple N ((g⁻¹, b), w) = 1 := by
    calc
      hallTuple N ((g, a), z) * hallTuple N ((g⁻¹, b), w) =
          hallTuple N ((g * g⁻¹, u * a * b),
            (1 : Fin N.torusDim → Circle)) := by
        simpa [u] using hmul
      _ = 1 := by
        funext j
        fin_cases j <;> simp [hallTuple, hub]
  refine ⟨((g⁻¹, b), w), ?_⟩
  have hcancel := congrArg
    (fun F => (hallTuple N ((g, a), z))⁻¹ * F) hmul_one
  simpa [mul_assoc] using hcancel.symm

/-- The subgroup whose elements are exactly the four-coordinate Hall
polynomials. -/
def normalFormSubgroup
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    Subgroup (Vertex → H) where
  carrier := Set.range (hallTuple N)
  one_mem' := by
    refine ⟨((1, 1), (1 : Fin N.torusDim → Circle)), ?_⟩
    funext j
    simp [hallTuple]
  mul_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    rcases exists_hallTuple_mul N p q with ⟨r, hr⟩
    exact ⟨r, hr.symm⟩
  inv_mem' := by
    rintro _ ⟨p, rfl⟩
    rcases exists_hallTuple_inv N p with ⟨q, hq⟩
    exact ⟨q, hq.symm⟩

theorem hallTuple_mem_algebraicSubgroup
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (p : Parameters N) :
    hallTuple N p ∈ algebraicSubgroup N := by
  apply (algebraicSubgroup N).mul_mem
  · apply (algebraicSubgroup N).mul_mem
    · apply Subgroup.subset_closure
      exact Or.inl (Or.inl ⟨p.1.1, rfl⟩)
    · apply Subgroup.subset_closure
      exact Or.inl (Or.inr ⟨p.1.2, rfl⟩)
  · apply Subgroup.subset_closure
    exact Or.inr ⟨p.2, rfl⟩

/-- The algebraically generated Hall--Petresco subgroup has no additional
elements beyond the explicit Hall normal forms. -/
theorem algebraicSubgroup_eq_normalFormSubgroup
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    algebraicSubgroup N = normalFormSubgroup N := by
  apply le_antisymm
  · rw [algebraicSubgroup]
    apply (Subgroup.closure_le (normalFormSubgroup N)).2
    intro y hy
    rcases hy with hy | hz
    · rcases hy with hg | ha
      · rcases hg with ⟨g, rfl⟩
        exact ⟨((g, 1), (1 : Fin N.torusDim → Circle)),
          (diagonal_eq_hallTuple N g).symm⟩
      · rcases ha with ⟨a, rfl⟩
        exact ⟨((1, a), (1 : Fin N.torusDim → Circle)),
          (linear_eq_hallTuple N a).symm⟩
    · rcases hz with ⟨z, rfl⟩
      exact ⟨((1, 1), z), (quadraticCentral_eq_hallTuple N z).symm⟩
  · intro y hy
    rcases hy with ⟨p, rfl⟩
    exact hallTuple_mem_algebraicSubgroup N p

/-- Zeroth-coordinate coefficient extracted from a four-tuple. -/
def extractedBase
    {H : Type u} [Group H] (y : Vertex → H) : H :=
  y 0

/-- Linear coefficient extracted from the first two coordinates. -/
def extractedLinear
    {H : Type u} [Group H] (y : Vertex → H) : H :=
  (extractedBase y)⁻¹ * y 1

/-- Quadratic coefficient extracted from the first three coordinates. -/
def extractedQuadratic
    {H : Type u} [Group H] (y : Vertex → H) : H :=
  (extractedBase y * extractedLinear y ^ 2)⁻¹ * y 2

@[simp]
theorem extractedBase_hallTuple
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (p : Parameters N) :
    extractedBase (hallTuple N p) = p.1.1 := by
  simp [extractedBase, hallTuple]

@[simp]
theorem extractedLinear_hallTuple
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (p : Parameters N) :
    extractedLinear (hallTuple N p) = p.1.2 := by
  rw [extractedLinear, extractedBase_hallTuple]
  rw [hallTuple_apply]
  rw [show (1 : Vertex).val.choose 2 = 0 by decide,
    show (1 : Vertex).val = 1 by rfl, pow_one, pow_zero, mul_one]
  group

@[simp]
theorem extractedQuadratic_hallTuple
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (p : Parameters N) :
    extractedQuadratic (hallTuple N p) = N.centralHom p.2 := by
  rw [extractedQuadratic, extractedBase_hallTuple,
    extractedLinear_hallTuple]
  change (p.1.1 * p.1.2 ^ 2)⁻¹ * hallTuple N p 2 =
    N.centralHom p.2
  rw [hallTuple_apply]
  rw [show (2 : Vertex).val.choose 2 = 1 by decide,
    show (2 : Vertex).val = 2 by rfl, pow_one]
  group

/-- Closed coordinate conditions characterizing the explicit Hall normal
forms. -/
def IsNormalForm
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (y : Vertex → H) : Prop :=
  extractedQuadratic y ∈ N.centralHom.range ∧
    y 3 = extractedBase y * extractedLinear y ^ 3 *
      extractedQuadratic y ^ 3

/-- A four-tuple is a Hall normal form exactly when it satisfies the
closed coefficient conditions. -/
theorem mem_normalFormSubgroup_iff
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (y : Vertex → H) :
    y ∈ normalFormSubgroup N ↔ IsNormalForm N y := by
  constructor
  · rintro ⟨p, rfl⟩
    constructor
    · exact ⟨p.2, (extractedQuadratic_hallTuple N p).symm⟩
    · rw [extractedBase_hallTuple, extractedLinear_hallTuple,
        extractedQuadratic_hallTuple, hallTuple_apply]
      rw [show (3 : Vertex).val.choose 2 = 3 by decide,
        show (3 : Vertex).val = 3 by rfl]
  · rintro ⟨hquad, hlast⟩
    rcases hquad with ⟨z, hz⟩
    refine ⟨((extractedBase y, extractedLinear y), z), ?_⟩
    funext j
    fin_cases j
    · change extractedBase y * extractedLinear y ^ 0 *
          N.centralHom z ^ Nat.choose 0 2 = y 0
      rw [show Nat.choose 0 2 = 0 by decide]
      simp only [pow_zero, mul_one]
      exact rfl
    · simp only [hallTuple_apply]
      rw [show Nat.choose 1 2 = 0 by decide, pow_one, pow_zero, mul_one]
      change extractedBase y * extractedLinear y = y 1
      unfold extractedLinear extractedBase
      group
    · simp only [hallTuple_apply]
      rw [show Nat.choose 2 2 = 1 by decide, pow_one]
      change extractedBase y * extractedLinear y ^ 2 *
          N.centralHom z = y 2
      rw [hz]
      unfold extractedQuadratic
      group
    · simp only [hallTuple_apply]
      rw [show Nat.choose 3 2 = 3 by decide]
      change extractedBase y * extractedLinear y ^ 3 *
          N.centralHom z ^ 3 = y 3
      rw [hz]
      exact hlast.symm

theorem continuous_extractedBase
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Continuous (extractedBase : (Vertex → H) → H) :=
  continuous_apply 0

theorem continuous_extractedLinear
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Continuous (extractedLinear : (Vertex → H) → H) :=
  continuous_extractedBase.inv.mul (continuous_apply 1)

theorem continuous_extractedQuadratic
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Continuous (extractedQuadratic : (Vertex → H) → H) :=
  (continuous_extractedBase.mul (continuous_extractedLinear.pow 2)).inv.mul
    (continuous_apply 2)

/-- The coordinate conditions defining the Hall normal forms are closed. -/
theorem isClosed_isNormalForm
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    IsClosed {y : Vertex → H | IsNormalForm N y} := by
  letI : T2Space H := N.t2Ambient
  have hrange : IsClosed (N.centralHom.range : Set H) := by
    rw [N.centralHom_range]
    exact N.isClosed_commutator
  have hquadratic :
      IsClosed {y : Vertex → H |
        extractedQuadratic y ∈ N.centralHom.range} :=
    hrange.preimage continuous_extractedQuadratic
  have hlast :
      IsClosed {y : Vertex → H |
        y 3 = extractedBase y * extractedLinear y ^ 3 *
          extractedQuadratic y ^ 3} := by
    apply isClosed_eq (continuous_apply 3)
    exact (continuous_extractedBase.mul
      (continuous_extractedLinear.pow 3)).mul
        (continuous_extractedQuadratic.pow 3)
  exact hquadratic.inter hlast

instance normalFormSubgroup_isClosed
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    IsClosed (normalFormSubgroup N : Set (Vertex → H)) := by
  have heq :
      (normalFormSubgroup N : Set (Vertex → H)) =
        {y : Vertex → H | IsNormalForm N y} := by
    ext y
    exact mem_normalFormSubgroup_iff N y
  rw [heq]
  exact isClosed_isNormalForm N

/-- The topologically closed Hall--Petresco group is already the explicit
normal-form subgroup. -/
theorem subgroup_eq_normalFormSubgroup
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    subgroup N = normalFormSubgroup N := by
  rw [subgroup, algebraicSubgroup_eq_normalFormSubgroup]
  apply le_antisymm
  · exact Subgroup.topologicalClosure_minimal
      (normalFormSubgroup N) le_rfl (normalFormSubgroup_isClosed N)
  · exact Subgroup.le_topologicalClosure (normalFormSubgroup N)

end Chapter02.HallPetrescoNormalForm
