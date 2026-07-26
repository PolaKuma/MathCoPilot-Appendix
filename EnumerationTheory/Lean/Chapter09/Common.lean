import Chapter08.Section06

noncomputable section

open Classical Filter MeasureTheory
open scoped BigOperators ENNReal

set_option linter.unusedVariables false

namespace Chapter09

universe u v w

abbrev MeasurableSystem := Chapter08.MeasurableSystem
abbrev TopologicalSystem := Chapter08.TopologicalSystem
abbrev MeasureOn := Chapter08.MeasureOn
abbrev SetFamily (X : Type u) := Chapter00.SetFamily X

def IsCommutingFamily {ι : Type v} {X : Type u} (T : ι -> X -> X) : Prop :=
  ∀ i j, T i ∘ T j = T j ∘ T i

def HasSimultaneousTopologicalRecurrence (X : Type u) [TopologicalSpace X]
    (T : Fin n -> X -> X) : Prop :=
  ∃ x : X, ∃ r : ℕ -> ℕ, StrictMono r ∧
    ∀ j : Fin n, Tendsto (fun i : ℕ => ((T j)^[r i]) x) atTop (nhds x)

def IsHomogeneousSystem (S : TopologicalSystem.{u}) : Prop :=
  Chapter05.IsCompactTopologicalSystem S ∧ IsHomeomorph S.T ∧
  ∃ G : Type u, ∃ _ : Group G, ∃ act : G -> S.X ≃ₜ S.X,
    act 1 = Homeomorph.refl S.X ∧
    (∀ g h, act (g * h) = (act h).trans (act g)) ∧
    (∀ g : G, (act g : S.X -> S.X) ∘ S.T = S.T ∘ (act g : S.X -> S.X)) ∧
    ∀ x : S.X, closure {y | ∃ g : G, act g x = y} = Set.univ

def IsHomogeneousClosedSubset (S : TopologicalSystem.{u}) (A : Set S.X) : Prop :=
  Chapter05.IsCompactTopologicalSystem S ∧ IsHomeomorph S.T ∧
  IsClosed A ∧ A.Nonempty ∧
  ∃ G : Type u, ∃ _ : Group G, ∃ act : G -> S.X ≃ₜ S.X,
    act 1 = Homeomorph.refl S.X ∧
    (∀ g h, act (g * h) = (act h).trans (act g)) ∧
    (∀ g : G, (act g : S.X -> S.X) ∘ S.T = S.T ∘ (act g : S.X -> S.X)) ∧
    (∀ g : G, act g '' A = A) ∧
    ∀ x ∈ A, closure {y | ∃ g : G, act g x = y} = A

def HasApproximateReturnInSubset (S : TopologicalSystem.{u}) [PseudoMetricSpace S.X]
    (A : Set S.X) : Prop :=
  ∀ ε : ℝ, 0 < ε -> ∃ x ∈ A, ∃ y ∈ A, ∃ n : ℕ,
    0 < n ∧ dist ((S.T^[n]) x) y < ε

def HasRecurrentPointInSubset (S : TopologicalSystem.{u}) (A : Set S.X) : Prop :=
  ∃ x ∈ A, ∃ n : ℕ -> ℕ, StrictMono n ∧ Tendsto (fun k => (S.T^[n k]) x) atTop (nhds x)

def ContainsArbitrarilyLongArithmeticProgressions (E : Set ℕ) : Prop :=
  ∀ k : ℕ, 0 < k -> ∃ a b : ℕ, 0 < b ∧ ∀ i : Fin k, a + i.val * b ∈ E

def IsPositiveNaturalSet (R : Set ℕ) : Prop :=
  ∀ n ∈ R, 0 < n

def IsPoincareSequence (R : Set ℕ) : Prop :=
  IsPositiveNaturalSet R ∧
    ∀ M : MeasurableSystem.{0}, Chapter01.IsMeasurePreservingSystem M →
    ∀ A : Set M.X, A ∈ M.𝓧 -> 0 < M.μ A ->
      ∃ n ∈ R, 0 < M.μ (A ∩ (M.T^[n]) ⁻¹' A)

def IsSyndeticSet (A : Set ℕ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, ∃ a ∈ A, n ≤ a ∧ a ≤ n + N

def naturalDifferenceSet (E : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ E, ∃ b ∈ E, b < a ∧ n = a - b}

def HasPositiveUpperBanachDensity (E : Set ℕ) : Prop :=
  0 < Chapter00.upperBanachDensity E

def FurstenbergCorrespondencePrinciple : Prop :=
  (∀ E : Set ℕ, HasPositiveUpperBanachDensity E ->
    ∃ M : MeasurableSystem.{0}, ∃ A : Set M.X,
      Chapter01.IsMeasurePreservingSystem M ∧ MeasurableSet A ∧
      M.μ A = ENNReal.ofReal (Chapter00.upperBanachDensity E) ∧
      ∀ α : Finset ℕ,
        M.μ (⋂ n ∈ α, (M.T^[n]) ⁻¹' A) ≤
          ENNReal.ofReal (Chapter00.upperBanachDensity
            {m : ℕ | ∀ n ∈ α, m + n ∈ E})) ∧
  (∀ M : MeasurableSystem.{0}, Chapter01.IsMeasurePreservingSystem M ->
    ∀ A : Set M.X, MeasurableSet A -> 0 < M.μ A ->
      ∃ E : Set ℕ, (M.μ A).toReal ≤ Chapter00.upperAsymptoticDensity E ∧
        ∀ α : Finset ℕ,
          {m : ℕ | ∀ n ∈ α, m + n ∈ E}.Nonempty ->
            0 < M.μ (⋂ n ∈ α, (M.T^[n]) ⁻¹' A))

def MultipleRecurrenceAverageFromOne (M : MeasurableSystem.{u}) (k : ℕ)
    (A : Set M.X) (N : ℕ) : ℝ :=
  if N = 0 then 0 else
    (N : ℝ)⁻¹ * (Finset.range N).sum fun n =>
      (M.μ (⋂ i : Fin (k + 1), (M.T^[(n + 1) * i.val]) ⁻¹' A)).toReal

def MultipleRecurrenceAverage (M : MeasurableSystem.{u}) (k : ℕ)
    (A : Set M.X) (N : ℕ) : ℝ :=
  if N = 0 then 0 else
    (N : ℝ)⁻¹ * (Finset.range N).sum fun n =>
      (M.μ (⋂ i : Fin (k + 1), (M.T^[n * i.val]) ⁻¹' A)).toReal

def PositiveCesaroMultipleRecurrenceFromOne (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M →
    ∀ k : ℕ, 0 < k → ∀ A : Set M.X, MeasurableSet A -> 0 < M.μ A ->
      0 < Filter.liminf
        (fun N : ℕ => MultipleRecurrenceAverageFromOne M k A N) atTop

def HasSZProperty (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M →
    ∀ k : ℕ, 0 < k → ∀ A : Set M.X, MeasurableSet A -> 0 < M.μ A ->
      0 < Filter.liminf (fun N : ℕ => MultipleRecurrenceAverage M k A N) atTop

def MultiplePoincareRecurrenceStatement (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M →
    ∀ k : ℕ, 0 < k → ∀ A : Set M.X, MeasurableSet A -> 0 < M.μ A ->
      ∃ n : ℕ, 0 < n ∧
        0 < M.μ (⋂ i : Fin (k + 1), (M.T^[n * i.val]) ⁻¹' A)

def VdCStatement : Prop :=
  ∀ H : Type u, ∀ _ : NormedAddCommGroup H,
    ∀ _ : InnerProductSpace ℂ H, ∀ _ : CompleteSpace H, ∀ u : ℕ -> H,
      Bornology.IsBounded (Set.range u) ->
      Tendsto (fun H0 : ℕ => if H0 = 0 then 0 else (H0 : ℝ)⁻¹ *
        (Finset.range H0).sum fun h => Filter.limsup (fun N : ℕ =>
          if N = 0 then 0 else
            ((N : ℂ)⁻¹ * (Finset.range N).sum
              (fun n => inner ℂ (u (n + h)) (u n))).re) atTop)
        atTop (nhds 0) ->
      Tendsto (fun N : ℕ => if N = 0 then 0 else
        ‖(N : ℂ)⁻¹ • (Finset.range N).sum u‖) atTop (nhds 0)

def linearMultipleAverage (M : MeasurableSystem.{u}) (d N : ℕ)
    (f : Fin d -> M.X -> ℂ) (x : M.X) : ℂ :=
  if N = 0 then 0 else (N : ℂ)⁻¹ *
    (Finset.range N).sum fun n => Finset.univ.prod fun i : Fin d =>
      f i ((M.T^[(i.val + 1) * n]) x)

def MultipleErgodicAverageConvergesL2 (M : MeasurableSystem.{u}) (d : ℕ) : Prop :=
  Chapter01.IsMeasurePreservingSystem M -> 1 ≤ d ->
  ∀ f : Fin d -> M.X -> ℂ, (∀ i, M.lpMember ⊤ (f i)) ->
    ∃ limit : M.X -> ℂ, M.lpMember 2 limit ∧
      Tendsto (fun N : ℕ => M.lpNorm 2 (fun x =>
        linearMultipleAverage M d N f x - limit x)) atTop (nhds 0)

def commutingMultipleAverage (M : MeasurableSystem.{u}) (d N : ℕ)
    (T : Fin d -> M.X -> M.X) (f : Fin d -> M.X -> ℂ) (x : M.X) : ℂ :=
  if N = 0 then 0 else (N : ℂ)⁻¹ * (Finset.range N).sum fun n =>
    Finset.univ.prod fun i : Fin d => f i (((T i)^[n]) x)

def CommutingMultipleErgodicAverageConvergesL2
    (M : MeasurableSystem.{u}) (d : ℕ) : Prop :=
  IsProbabilityMeasure M.μ -> 1 ≤ d ->
  ∀ T : Fin d -> M.X -> M.X,
    (∀ i, MeasurePreserving (T i) M.μ M.μ) -> IsCommutingFamily T ->
    ∀ f : Fin d -> M.X -> ℂ, (∀ i, M.lpMember ⊤ (f i)) ->
      ∃ limit : M.X -> ℂ, M.lpMember 2 limit ∧
        Tendsto (fun N => M.lpNorm 2 (fun x =>
          commutingMultipleAverage M d N T f x - limit x)) atTop (nhds 0)

def WeakMixingMultipleAverageStatement (M : MeasurableSystem.{u}) (d : ℕ) : Prop :=
  ∀ f : Fin d -> M.X -> ℂ, (∀ i, M.lpMember ⊤ (f i)) ->
    Tendsto (fun N : ℕ => M.lpNorm 2 (fun x =>
      linearMultipleAverage M d N f x - Finset.univ.prod (fun i => M.integral (f i))))
      atTop (nhds 0)

structure IntegerActionData (M : MeasurableSystem.{u}) where
  act : ℤ -> M.X -> M.X
  zero_act : act 0 = id
  add_act : ∀ m n, act (m + n) = act m ∘ act n
  one_act : act 1 = M.T
  measure_preserving : ∀ n, MeasurePreserving (act n) M.μ M.μ

def PolynomialRecurrenceStatement (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M →
    Nonempty (IntegerActionData M) ->
    ∀ U : IntegerActionData M, ∀ p : Polynomial ℤ, p.eval 0 = 0 ->
      ∀ A : Set M.X, MeasurableSet A -> 0 < M.μ A ->
        ∃ n : ℕ, 0 < n ∧
          0 < M.μ (A ∩ (U.act (p.eval (n : ℤ))) ⁻¹' A)

def IsRationalKroneckerProjection (M : MeasurableSystem.{u})
    (P : (M.X -> ℂ) -> M.X -> ℂ) : Prop :=
  (∀ f, M.lpMember 2 f -> M.lpMember 2 (P f)) ∧
  (∀ f g, M.lpMember 2 f → M.lpMember 2 g → f =ᵐ[M.μ] g →
    P f =ᵐ[M.μ] P g) ∧
  (∀ f g, M.lpMember 2 f → M.lpMember 2 g → ∀ a b : ℂ,
    P (fun x => a * f x + b * g x) =ᵐ[M.μ]
      fun x => a * P f x + b * P g x) ∧
  (∀ f, M.lpMember 2 f -> P (P f) =ᵐ[M.μ] P f) ∧
  (∀ f, M.lpMember 2 f -> M.lpNorm 2 (P f) ≤ M.lpNorm 2 f) ∧
  (∀ f g, M.lpMember 2 f → M.lpMember 2 g →
    M.integral (fun x => P f x * starRingEnd ℂ (g x)) =
      M.integral (fun x => f x * starRingEnd ℂ (P g x))) ∧
  ∀ f, M.lpMember 2 f ->
    (P f =ᵐ[M.μ] f ↔ ∀ ε : ℝ, 0 < ε ->
      ∃ r : ℕ, ∃ g : Fin r -> M.X -> ℂ,
        (∀ i, M.lpMember 2 (g i) ∧ ∃ q : ℕ, 0 < q ∧
          (fun x => g i ((M.T^[q]) x)) =ᵐ[M.μ] g i) ∧
        M.lpNorm 2 (fun x => f x - Finset.univ.sum (fun i => g i x)) < ε)

def kroneckerSigmaAlgebra (M : MeasurableSystem.{u}) : Set (Set M.X) :=
  Chapter00.generatedSigmaAlgebra
    {A | ∃ f : M.X -> ℂ, ∃ lam : ℂ, ∃ B : Set ℂ,
      Chapter02.Eigenfunction M lam f ∧ MeasurableSet B ∧ A = f ⁻¹' B}

def IsComplexConditionalExpectationVersion (M : MeasurableSystem.{u})
    (f : M.X -> ℂ) (F : Set (Set M.X)) (g : M.X -> ℂ) : Prop :=
  Chapter00.IsMeasurableForFamily F g ∧
  MeasureTheory.Integrable f M.μ ∧ MeasureTheory.Integrable g M.μ ∧
  ∀ A ∈ F, MeasurableSet A ->
    ∫ x in A, g x ∂M.μ = ∫ x in A, f x ∂M.μ

def PolynomialCesaroCharacteristicStatement (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M →
    Nonempty (IntegerActionData M) ->
    ∀ U : IntegerActionData M, ∀ p : Polynomial ℤ,
      (∃ n : ℕ, 0 < n ∧ p.coeff n ≠ 0) -> ∀ f : M.X -> ℂ,
      M.lpMember ⊤ f ->
      ∃ P : (M.X -> ℂ) -> M.X -> ℂ, IsRationalKroneckerProjection M P ∧
        Tendsto (fun N : ℕ => M.lpNorm 2 (fun x =>
          if N = 0 then 0 else (N : ℂ)⁻¹ * (Finset.range N).sum fun n =>
            f (U.act (p.eval (n : ℤ)) x) - P f (U.act (p.eval (n : ℤ)) x)))
          atTop (nhds 0)

def RothAveragePositive (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M →
    ∀ A : Set M.X, MeasurableSet A -> 0 < M.μ A ->
      0 < Filter.liminf (fun N : ℕ => MultipleRecurrenceAverage M 2 A N) atTop

def ProductTelescopingIdentity : Prop :=
  ∀ k : ℕ, ∀ a b : Fin k -> ℂ,
    (Finset.univ.prod a - Finset.univ.prod b) =
      Finset.univ.sum (fun i : Fin k =>
        ((Finset.univ.filter fun j : Fin k => j.val < i.val).prod a) *
          (a i - b i) *
          ((Finset.univ.filter fun j : Fin k => i.val < j.val).prod b))

def CompactSelfAdjointCommutingOperatorStatement (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M →
  ∀ K : (M.X -> ℂ) -> M.X -> ℂ,
    (∀ f, M.lpMember 2 f → M.lpMember 2 (K f)) →
    (∀ f g, M.lpMember 2 f → M.lpMember 2 g → f =ᵐ[M.μ] g →
      K f =ᵐ[M.μ] K g) →
    (∀ a b : ℂ, ∀ f g, M.lpMember 2 f → M.lpMember 2 g →
      K (fun x => a * f x + b * g x) =ᵐ[M.μ]
        fun x => a * K f x + b * K g x) ->
    (∀ f g, M.lpMember 2 f -> M.lpMember 2 g ->
      M.integral (fun x => K f x * starRingEnd ℂ (g x)) =
      M.integral (fun x => f x * starRingEnd ℂ (K g x))) ->
    (∀ f : ℕ -> M.X -> ℂ, (∀ n, M.lpMember 2 (f n) ∧ M.lpNorm 2 (f n) ≤ 1) ->
      ∃ r : ℕ -> ℕ, StrictMono r ∧ ∃ g : M.X -> ℂ,
        M.lpMember 2 g ∧
        Tendsto (fun n => M.lpNorm 2 (fun x => K (f (r n)) x - g x)) atTop (nhds 0)) ->
    (∀ f, M.lpMember 2 f →
      K (fun x => f (M.T x)) =ᵐ[M.μ] fun x => K f (M.T x)) ->
    ∀ lam : ℝ, lam ≠ 0 ->
      ∃ r : ℕ, ∃ e : Fin r -> M.X -> ℂ,
        (∀ i, M.lpMember 2 (e i) ∧ ¬ e i =ᵐ[M.μ] 0 ∧
          K (e i) =ᵐ[M.μ] fun x => lam * e i x) ∧
        (∀ i, ∃ z : ℂ, ‖z‖ = 1 ∧
          (fun x => e i (M.T x)) =ᵐ[M.μ] fun x => z * e i x) ∧
        ∀ f, M.lpMember 2 f → K f =ᵐ[M.μ] (fun x => lam * f x) ->
          ∃ c : Fin r -> ℂ, f =ᵐ[M.μ] fun x => Finset.univ.sum (fun i => c i * e i x)

structure KroneckerRotationFactorData (M : MeasurableSystem.{u})
    (Z : Type u) [AddCommGroup Z] [TopologicalSpace Z] [MeasurableSpace Z] where
  haar : Measure Z
  rotation : Z
  factorMap : M.X -> Z
  borel : BorelSpace Z
  compact : IsCompact (Set.univ : Set Z)
  continuous_add : Continuous (fun p : Z × Z => p.1 + p.2)
  continuous_neg : Continuous (fun z : Z => -z)
  probability : IsProbabilityMeasure haar
  translation_invariant : ∀ z, MeasurePreserving (fun θ => z + θ) haar haar
  factor_preserving : MeasurePreserving factorMap M.μ haar
  intertwines : ∀ x, factorMap (M.T x) = rotation + factorMap x
  realizes_kronecker :
    {A : Set M.X | ∃ B : Set Z, MeasurableSet B ∧ A = factorMap ⁻¹' B} =
      kroneckerSigmaAlgebra M

def IsKroneckerFactorConditionalExpectation
    (M : MeasurableSystem.{u}) {Z : Type u} [AddCommGroup Z]
    [TopologicalSpace Z] [MeasurableSpace Z]
    (D : KroneckerRotationFactorData M Z)
    (f : M.X -> ℂ) (fZ : Z -> ℂ) : Prop :=
  MeasureTheory.Integrable f M.μ ∧ MeasureTheory.Integrable fZ D.haar ∧
  ∀ B : Set Z, MeasurableSet B ->
    ∫ x in D.factorMap ⁻¹' B, f x ∂M.μ = ∫ z in B, fZ z ∂D.haar

def KroneckerFactorControlsDoubleAverage
    (M : MeasurableSystem.{u}) (a b : ℤ) : Prop :=
  a ≠ 0 -> b ≠ 0 -> a ≠ b ->
  Nonempty (IntegerActionData M) ->
  ∀ U : IntegerActionData M, ∀ f g : M.X -> ℂ,
    M.lpMember ⊤ f -> M.lpMember ⊤ g ->
    ∃ Z : Type u, ∃ _ : AddCommGroup Z, ∃ _ : TopologicalSpace Z,
    ∃ _ : MeasurableSpace Z, ∃ D : KroneckerRotationFactorData M Z,
    ∃ fZ gZ : Z -> ℂ,
      IsKroneckerFactorConditionalExpectation M D f fZ ∧
      IsKroneckerFactorConditionalExpectation M D g gZ ∧
      Tendsto (fun N : ℕ => M.lpNorm 2 (fun x =>
        if N = 0 then 0 else (N : ℂ)⁻¹ * (Finset.range N).sum fun n =>
          f (U.act (a * n) x) * g (U.act (b * n) x) -
          fZ (D.factorMap (U.act (a * n) x)) *
            gZ (D.factorMap (U.act (b * n) x)))) atTop (nhds 0) ∧
      let limit := fun x => ∫ θ,
        fZ (D.factorMap x + a • θ) * gZ (D.factorMap x + b • θ) ∂D.haar
      M.lpMember 2 limit ∧ Tendsto (fun N : ℕ => M.lpNorm 2 (fun x =>
        (if N = 0 then 0 else (N : ℂ)⁻¹ * (Finset.range N).sum fun n =>
          f (U.act (a * n) x) * g (U.act (b * n) x)) - limit x)) atTop (nhds 0)

def IsKroneckerSystem (M : MeasurableSystem.{u}) : Prop :=
  Chapter02.IsErgodic M ∧ Chapter08.HasDiscreteSpectrumMeasureSystem M

def SeparatingSieve (M : MeasurableSystem.{u}) (A : ℕ -> Set M.X) : Prop :=
  (∀ n, MeasurableSet (A n) ∧ 0 < M.μ (A n)) ∧
  (∀ n, A (n + 1) ⊆ A n) ∧
  Tendsto (fun n => M.μ (A n)) atTop (nhds 0) ∧
  ∃ U : IntegerActionData M, ∃ X0 : Set M.X,
    MeasurableSet X0 ∧ M.μ X0 = 1 ∧
    ∀ x ∈ X0, ∀ x' ∈ X0,
      (∀ n, ∃ k : ℤ, U.act k x ∈ A n ∧ U.act k x' ∈ A n) -> x = x'

def IsPeriodicMeasureSystem (M : MeasurableSystem.{u}) : Prop :=
  Chapter02.IsErgodic M ∧ ∃ q : ℕ, 0 < q ∧ (M.T^[q]) = id

def IsParryMeasureDistal (M : MeasurableSystem.{u}) : Prop :=
  Chapter02.IsErgodic M ∧
    (IsPeriodicMeasureSystem M ∨ ∃ A : ℕ -> Set M.X, SeparatingSieve M A)

def IsMeasureDistal (M : MeasurableSystem.{u}) : Prop :=
  Chapter08.IsDistalMeasureSystem M

/-- A disintegration of `μ` over the factor `π`, used throughout §9.6–§9.7. -/
structure FiberMeasureData (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (π : M.X -> N.X) where
  fiberMeasure : N.X -> Measure M.X
  probability_and_support : ∀ᵐ y ∂N.μ,
    IsProbabilityMeasure (fiberMeasure y) ∧ fiberMeasure y (π ⁻¹' {y}) = 1
  measurable_kernel : ∀ A : Set M.X, MeasurableSet A ->
    AEMeasurable (fun y => fiberMeasure y A) N.μ
  disintegration : ∀ A : Set M.X, MeasurableSet A ->
    M.μ A = ∫⁻ y, fiberMeasure y A ∂N.μ

def fiberLpNorm (D : FiberMeasureData M N π) (y : N.X)
    (f : M.X -> ℂ) : ℝ :=
  (MeasureTheory.eLpNorm f 2 (D.fiberMeasure y)).toReal

def RelativelyAlmostPeriodicFunction
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X)
    (f : M.X -> ℂ) : Prop :=
  Chapter01.IsFactorMap M N π ∧ M.lpMember 2 f ∧
  ∃ U : IntegerActionData M, ∃ D : FiberMeasureData M N π,
    ∀ ε : ℝ, 0 < ε -> ∃ r : ℕ, ∃ g : Fin r -> M.X -> ℂ,
      (∀ j, M.lpMember 2 (g j)) ∧ ∀ n : ℤ, ∀ᵐ y ∂N.μ,
        ∃ j : Fin r, fiberLpNorm D y (fun x => f (U.act n x) - g j x) < ε

/-- A concrete realization of the relatively independent self-product
`M ×_N M`: its points are precisely pairs in a common fiber, and its cylinder
measure is obtained by averaging products of conditional fiber measures. -/
structure RelativeSelfProductData
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) where
  system : MeasurableSystem.{u}
  first : system.X -> M.X
  second : system.X -> M.X
  base : system.X -> N.X
  fiberMeasure : FiberMeasureData M N π
  common_base : ∀ z, base z = π (first z) ∧ base z = π (second z)
  realizes_fiber_pairs : ∀ x₁ x₂, π x₁ = π x₂ ->
    ∃ z, first z = x₁ ∧ second z = x₂
  first_factor : Chapter01.IsFactorMap system M first
  second_factor : Chapter01.IsFactorMap system M second
  base_factor : Chapter01.IsFactorMap system N base
  cylinder_measure : ∀ A B : Set M.X, MeasurableSet A -> MeasurableSet B ->
    system.μ {z | first z ∈ A ∧ second z ∈ B} =
      ∫⁻ y, fiberMeasure.fiberMeasure y A *
        fiberMeasure.fiberMeasure y B ∂N.μ

def IsRelativelyWeakMixingExtension
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) : Prop :=
  Chapter01.IsFactorMap M N π ∧
  ∃ P : RelativeSelfProductData M N π, Chapter02.IsErgodic P.system

def IsCompactExtension
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) : Prop :=
  Chapter01.IsFactorMap M N π ∧
  ∀ f : M.X -> ℂ, M.lpMember 2 f -> ∀ ε : ℝ, 0 < ε ->
    ∃ h : M.X -> ℂ, RelativelyAlmostPeriodicFunction M N π h ∧
      M.lpNorm 2 (fun x => f x - h x) < ε

def RelativeExtensionSpaceCharacterization
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (π : M.X -> N.X) : Prop :=
  (IsCompactExtension M N π ↔
    ∀ f : M.X -> ℂ, M.lpMember 2 f -> ∀ ε : ℝ, 0 < ε ->
      ∃ h, RelativelyAlmostPeriodicFunction M N π h ∧
        M.lpNorm 2 (fun x => f x - h x) < ε) ∧
  (IsRelativelyWeakMixingExtension M N π ↔
    ∀ f : M.X -> ℂ, RelativelyAlmostPeriodicFunction M N π f ->
      ∃ g : N.X -> ℂ, f =ᵐ[M.μ] g ∘ π)

def RelativeWeakMixingConditionalExpectationStatement
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (π : M.X -> N.X) : Prop :=
  IsRelativelyWeakMixingExtension M N π ->
  ∀ f g : M.X -> ℂ, M.lpMember ⊤ f -> M.lpMember ⊤ g ->
    ∃ Ef Eg : M.X -> ℂ, ∃ Efg : ℕ -> M.X -> ℂ,
      IsComplexConditionalExpectationVersion M f
        {A | ∃ B : Set N.X, MeasurableSet B ∧ A = π ⁻¹' B} Ef ∧
      IsComplexConditionalExpectationVersion M g
        {A | ∃ B : Set N.X, MeasurableSet B ∧ A = π ⁻¹' B} Eg ∧
      (∀ n, IsComplexConditionalExpectationVersion M
        (fun x => f x * g ((M.T^[n]) x))
        {A | ∃ B : Set N.X, MeasurableSet B ∧ A = π ⁻¹' B} (Efg n)) ∧
      Tendsto (fun N0 : ℕ => if N0 = 0 then 0 else (N0 : ℝ)⁻¹ *
        (Finset.range N0).sum fun n => M.lpNorm 2 (fun x =>
          Efg n x - Ef x * Eg ((M.T^[n]) x))) atTop (nhds 0)

def RelativeWeakMixingCharacteristicStatement
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (π : M.X -> N.X) : Prop :=
  IsRelativelyWeakMixingExtension M N π ->
  ∀ d : ℕ, 1 ≤ d -> ∀ f : Fin d -> M.X -> ℂ,
    (∀ i, M.lpMember ⊤ (f i)) ->
    ∃ Ef : Fin d -> M.X -> ℂ,
      (∀ i, IsComplexConditionalExpectationVersion M (f i)
        {A | ∃ B : Set N.X, MeasurableSet B ∧ A = π ⁻¹' B} (Ef i)) ∧
      Tendsto (fun N0 => M.lpNorm 2 (fun x =>
        linearMultipleAverage M d N0 f x - linearMultipleAverage M d N0 Ef x))
        atTop (nhds 0)

def FiberMultipleMixingError
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X)
    (D : FiberMeasureData M N π) (k n : ℕ)
    (B : Fin (k + 1) -> Set M.X) (y : N.X) : ℝ :=
  (D.fiberMeasure y (⋂ i : Fin (k + 1), (M.T^[n * i.val]) ⁻¹' B i)).toReal -
    Finset.univ.prod (fun i : Fin (k + 1) =>
      (D.fiberMeasure y ((M.T^[n * i.val]) ⁻¹' B i)).toReal)

def IsFurstenbergZimmerTower (M : MeasurableSystem.{u}) : Prop :=
  Chapter02.IsErgodic M ∧
  ∃ Z : MeasurableSystem.{u}, ∃ π : M.X -> Z.X,
    IsMeasureDistal Z ∧ Chapter01.IsFactorMap M Z π ∧
      IsRelativelyWeakMixingExtension M Z π

def RelativeStructureDichotomy
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) : Prop :=
  IsRelativelyWeakMixingExtension M N π ∨
    ∃ Z : MeasurableSystem.{u}, ∃ σ : M.X -> Z.X, ∃ ρ : Z.X -> N.X,
      Chapter01.IsFactorMap M Z σ ∧ IsCompactExtension Z N ρ ∧
      ¬ Chapter01.IsIsomorphicSystems Z N ∧ π = ρ ∘ σ

def CommutingMultipleRecurrenceStatement (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M →
    ∀ l : ℕ, 0 < l -> ∀ T : Fin l -> M.X -> M.X,
      (∀ i, MeasurePreserving (T i) M.μ M.μ) -> IsCommutingFamily T ->
          ∀ A : Set M.X, MeasurableSet A -> 0 < M.μ A ->
            0 < Filter.liminf (fun N : ℕ => if N = 0 then 0 else
                (N : ℝ)⁻¹ * (Finset.range N).sum fun n =>
                (M.μ (⋂ i : Fin l, ((T i)^[n]) ⁻¹' A)).toReal) atTop

def CommutingMultiplePoincareRecurrenceStatement (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M →
    ∀ l : ℕ, 0 < l -> ∀ T : Fin l -> M.X -> M.X,
      (∀ i, MeasurePreserving (T i) M.μ M.μ) -> IsCommutingFamily T ->
      ∀ A : Set M.X, MeasurableSet A -> 0 < M.μ A ->
        ∃ n : ℕ, 1 ≤ n ∧
          0 < M.μ (⋂ i : Fin l, ((T i)^[n]) ⁻¹' A)

structure GammaSystem (Γ : Type u) [Group Γ] where
  X : Type v
  measurableSpace : MeasurableSpace X
  μ : @Measure X measurableSpace
  action : Γ -> X -> X
  action_identity : action 1 = id
  action_mul : ∀ g h, action (g * h) = action g ∘ action h
  probability : IsProbabilityMeasure μ
  preserving : ∀ g, MeasurePreserving (action g) μ μ

attribute [instance] GammaSystem.measurableSpace

namespace GammaSystem

def integral {Γ : Type u} [Group Γ]
    (X : GammaSystem.{u, v} Γ) (f : X.X -> ℂ) : ℂ := ∫ x, f x ∂X.μ

def lpMember {Γ : Type u} [Group Γ]
    (X : GammaSystem.{u, v} Γ) (p : ENNReal) (f : X.X -> ℂ) : Prop :=
  MeasureTheory.MemLp f p X.μ

end GammaSystem

structure IdempotentClass (Γ : Type u) [Group Γ] where
  contains : GammaSystem.{u, v} Γ -> Prop

def IsGammaFactorMap {Γ : Type u} [Group Γ] (X Y : GammaSystem.{u, v} Γ)
    (π : X.X -> Y.X) : Prop :=
  Function.Surjective π ∧
  Measurable π ∧ MeasurePreserving π X.μ Y.μ ∧
  ∀ γ x, π (X.action γ x) = Y.action γ (π x)

def GammaSystemsIsomorphic {Γ : Type u} [Group Γ]
    (X Y : GammaSystem.{u, v} Γ) : Prop :=
  ∃ e : X.X ≃ Y.X, IsGammaFactorMap X Y e ∧ IsGammaFactorMap Y X e.symm

def IsIdempotentClass {Γ : Type u} [Group Γ]
    (C : IdempotentClass.{u, v} Γ) : Prop :=
  (∀ X Y : GammaSystem.{u, v} Γ,
    C.contains X -> GammaSystemsIsomorphic X Y -> C.contains Y) ∧
  (∀ X : GammaSystem.{u, v} Γ, Nonempty X.X -> Subsingleton X.X -> C.contains X) ∧
  ∀ X : ℕ -> GammaSystem.{u, v} Γ, (∀ n, C.contains (X n)) ->
    ∃ J : GammaSystem.{u, v} Γ, C.contains J ∧
      ∃ π : ∀ n, J.X -> (X n).X,
        (∀ n, IsGammaFactorMap J (X n) (π n)) ∧
        MeasurableSpace.generateFrom
          {A : Set J.X | ∃ n, ∃ B : Set (X n).X,
            MeasurableSet B ∧ A = (π n) ⁻¹' B} = J.measurableSpace

def IsHereditaryIdempotentClass {Γ : Type u} [Group Γ]
    (C : IdempotentClass.{u, v} Γ) : Prop :=
  IsIdempotentClass C ∧ ∀ X Y : GammaSystem.{u, v} Γ,
    C.contains X -> ∀ π : X.X -> Y.X, IsGammaFactorMap X Y π -> C.contains Y

def IsFolnerSequence {Γ : Type u} [Group Γ] (F : ℕ -> Finset Γ) : Prop :=
  (∀ n, (F n).Nonempty) ∧ ∀ g : Γ,
    Tendsto (fun n =>
      let gF := (F n).image (fun h => g * h)
      (((gF \ F n).card + (F n \ gF).card : ℕ) : ℝ) / (F n).card)
      atTop (nhds 0)

def IsFiniteMeasurablePartition {Γ : Type u} [Group Γ]
    (X : GammaSystem.{u, v} Γ) {k : ℕ} (P : Fin k -> Set X.X) : Prop :=
  (∀ i, MeasurableSet (P i)) ∧
  (∀ i j, i ≠ j -> Disjoint (P i) (P j)) ∧
  (⋃ i, P i) = Set.univ

def gammaJoinedPartitionEntropy {Γ : Type u} [Group Γ]
    (X : GammaSystem.{u, v} Γ) {k : ℕ} (P : Fin k -> Set X.X)
    (E : Finset Γ) : ℝ :=
  -(Finset.univ.sum fun a : (g : ↥E) -> Fin k =>
    let atom := ⋂ g : ↥E, (X.action g.val) ⁻¹' P (a g)
    let p := (X.μ atom).toReal
    if p = 0 then 0 else p * Real.log p)

def HasZeroGammaEntropy {Γ : Type u} [Group Γ]
    (X : GammaSystem.{u, v} Γ) : Prop :=
  ∀ F : ℕ -> Finset Γ, IsFolnerSequence F ->
  ∀ k : ℕ, ∀ P : Fin k -> Set X.X, IsFiniteMeasurablePartition X P ->
    Tendsto (fun n => gammaJoinedPartitionEntropy X P (F n) / (F n).card)
      atTop (nhds 0)

structure GammaCharacter (Γ : Type u) [Group Γ] where
  toFun : Γ -> ℂ
  map_one : toFun 1 = 1
  map_mul : ∀ g h, toFun (g * h) = toFun g * toFun h
  unit_norm : ∀ g, ‖toFun g‖ = 1

def IsGammaEigenfunction {Γ : Type u} [Group Γ]
    (X : GammaSystem.{u, v} Γ) (f : X.X -> ℂ) : Prop :=
  X.lpMember 2 f ∧ ¬ f =ᵐ[X.μ] 0 ∧
  ∃ χ : GammaCharacter Γ, ∀ γ,
    (fun x => f (X.action γ x)) =ᵐ[X.μ] fun x => χ.toFun γ * f x

def HasGammaDiscreteSpectrum {Γ : Type u} [Group Γ]
    (X : GammaSystem.{u, v} Γ) : Prop :=
  ∀ f : X.X -> ℂ, X.lpMember 2 f -> ∀ ε : ℝ, 0 < ε ->
    ∃ r : ℕ, ∃ e : Fin r -> X.X -> ℂ, ∃ c : Fin r -> ℂ,
      (∀ i, IsGammaEigenfunction X (e i)) ∧
      (MeasureTheory.eLpNorm
        (fun x => f x - Finset.univ.sum (fun i => c i * e i x)) 2 X.μ).toReal < ε

def IdempotentClassExamplesStatement : Prop :=
  ∀ Γ : Type u, ∀ _ : Group Γ, Countable Γ ->
    (∃ Czero Cdiscrete : IdempotentClass.{u, v} Γ,
      (∀ X, Czero.contains X ↔ HasZeroGammaEntropy X) ∧
      (∀ X, Cdiscrete.contains X ↔ HasGammaDiscreteSpectrum X) ∧
      IsHereditaryIdempotentClass Czero ∧
      IsHereditaryIdempotentClass Cdiscrete) ∧
    ∃ C : IdempotentClass.{u, v} Γ,
      IsIdempotentClass C ∧ ¬ IsHereditaryIdempotentClass C

def IsMaximalCfactor {Γ : Type u} [Group Γ]
    (C : IdempotentClass.{u, v} Γ) (X Y : GammaSystem.{u, v} Γ)
    (π : X.X -> Y.X) : Prop :=
  C.contains Y ∧ IsGammaFactorMap X Y π ∧
    ∀ Z : GammaSystem.{u, v} Γ, C.contains Z ->
    ∀ ρ : X.X -> Z.X, IsGammaFactorMap X Z ρ ->
      ∃ σ : Y.X -> Z.X, IsGammaFactorMap Y Z σ ∧ ρ = σ ∘ π

def IsCountablyGeneratedGammaSystem {Γ : Type u} [Group Γ]
    (X : GammaSystem.{u, v} Γ) : Prop :=
  ∃ C : Set (Set X.X), C.Countable ∧
    MeasurableSpace.generateFrom C = X.measurableSpace

def MaximalCfactorStatement {Γ : Type u} [Group Γ]
    (C : IdempotentClass.{u, v} Γ) (X : GammaSystem.{u, v} Γ) : Prop :=
  IsIdempotentClass C -> IsCountablyGeneratedGammaSystem X ->
    ∃ Y : GammaSystem.{u, v} Γ,
    ∃ π : X.X -> Y.X, IsMaximalCfactor C X Y π

def IsGammaJoining {Γ : Type u} [Group Γ]
    (X Y J : GammaSystem.{u, v} Γ) : Prop :=
  ∃ πX : J.X -> X.X, ∃ πY : J.X -> Y.X,
    IsGammaFactorMap J X πX ∧ IsGammaFactorMap J Y πY ∧
    MeasurableSpace.generateFrom
      ({A : Set J.X | ∃ B : Set X.X, MeasurableSet B ∧ A = πX ⁻¹' B} ∪
       {A : Set J.X | ∃ B : Set Y.X, MeasurableSet B ∧ A = πY ⁻¹' B}) =
      J.measurableSpace

def JoinIdempotentClasses {Γ : Type u} [Group Γ]
    (C D : IdempotentClass.{u, v} Γ) : IdempotentClass.{u, v} Γ :=
  { contains := fun X => ∃ Y Z J : GammaSystem.{u, v} Γ,
      C.contains Y ∧ D.contains Z ∧ IsGammaJoining Y Z J ∧
        GammaSystemsIsomorphic X J }

def IsGammaConditionalExpectationVersion {Γ : Type u} [Group Γ]
    (E W : GammaSystem.{u, v} Γ) (σ : E.X -> W.X)
    (f : E.X -> ℂ) (h : W.X -> ℂ) : Prop :=
  IsGammaFactorMap E W σ ∧ MeasureTheory.Integrable f E.μ ∧
  MeasureTheory.Integrable h W.μ ∧
  ∀ A : Set W.X, MeasurableSet A ->
    ∫ x in σ ⁻¹' A, f x ∂E.μ = ∫ w in A, h w ∂W.μ

def AreGammaFactorsRelativelyIndependent {Γ : Type u} [Group Γ]
    (E X Z W : GammaSystem.{u, v} Γ)
    (π : E.X -> X.X) (ρ : E.X -> Z.X)
    (σ : X.X -> W.X) (τ : Z.X -> W.X) : Prop :=
  IsGammaFactorMap E X π ∧ IsGammaFactorMap E Z ρ ∧
  IsGammaFactorMap X W σ ∧ IsGammaFactorMap Z W τ ∧ σ ∘ π = τ ∘ ρ ∧
  ∀ f : X.X -> ℂ, X.lpMember 2 f ->
  ∀ g : Z.X -> ℂ, Z.lpMember 2 g ->
    ∃ Pf Pg : W.X -> ℂ,
      IsGammaConditionalExpectationVersion X W σ f Pf ∧
      IsGammaConditionalExpectationVersion Z W τ g Pg ∧
      E.integral (fun e => f (π e) * g (ρ e)) =
        W.integral (fun w => Pf w * Pg w)

def IsSatedForClass {Γ : Type u} [Group Γ] (C : IdempotentClass.{u, v} Γ)
    (X : GammaSystem.{u, v} Γ) : Prop :=
  IsIdempotentClass C ∧
  ∃ XC : GammaSystem.{u, v} Γ, ∃ ξX : X.X -> XC.X,
    IsMaximalCfactor C X XC ξX ∧
    ∀ E : GammaSystem.{u, v} Γ, ∀ π : E.X -> X.X,
      IsGammaFactorMap E X π ->
      ∃ EC : GammaSystem.{u, v} Γ, ∃ ξE : E.X -> EC.X,
        IsMaximalCfactor C E EC ξE ∧
        ∃ Cπ : EC.X -> XC.X, IsGammaFactorMap EC XC Cπ ∧
          ξX ∘ π = Cπ ∘ ξE ∧
          AreGammaFactorsRelativelyIndependent E X EC XC π ξE ξX Cπ

def AustinSatedExtensionStatement : Prop :=
  ∀ Γ : Type u, ∀ _ : Group Γ,
  ∀ I : Type v, Countable I -> ∀ C : I -> IdempotentClass.{u, w} Γ,
    (∀ i, IsIdempotentClass (C i)) -> ∀ X0 : GammaSystem.{u, w} Γ,
      IsCountablyGeneratedGammaSystem X0 ->
      ∃ X : GammaSystem.{u, w} Γ, (∀ i, IsSatedForClass (C i) X) ∧
        ∃ π0 : X.X -> X0.X, IsGammaFactorMap X X0 π0 ∧
        ∃ XC : I -> GammaSystem.{u, w} Γ,
        ∃ πC : ∀ i, X.X -> (XC i).X,
          (∀ i, IsMaximalCfactor (C i) X (XC i) (πC i)) ∧
          MeasurableSpace.generateFrom
            ({A : Set X.X | ∃ B : Set X0.X, MeasurableSet B ∧ A = π0 ⁻¹' B} ∪
             {A : Set X.X | ∃ i, ∃ B : Set (XC i).X,
                MeasurableSet B ∧ A = πC i ⁻¹' B}) = X.measurableSpace

def IsGammaErgodicExtensionForElement {Γ : Type u} [Group Γ]
    (X Y : GammaSystem.{u, v} Γ) (π : X.X -> Y.X) (γ : Γ) : Prop :=
  IsGammaFactorMap X Y π ∧
  ∀ A : Set X.X, MeasurableSet A ->
    X.μ (Chapter00.symmDiff ((X.action γ) ⁻¹' A) A) = 0 ->
      ∃ B : Set Y.X, MeasurableSet B ∧
        X.μ (Chapter00.symmDiff A (π ⁻¹' B)) = 0

structure GammaFiberMeasureData {Γ : Type u} [Group Γ]
    (X Y : GammaSystem.{u, v} Γ) (π : X.X -> Y.X) where
  fiberMeasure : Y.X -> Measure X.X
  probability_and_support : ∀ᵐ y ∂Y.μ,
    IsProbabilityMeasure (fiberMeasure y) ∧ fiberMeasure y (π ⁻¹' {y}) = 1
  measurable_kernel : ∀ A : Set X.X, MeasurableSet A ->
    AEMeasurable (fun y => fiberMeasure y A) Y.μ
  disintegration : ∀ A : Set X.X, MeasurableSet A ->
    X.μ A = ∫⁻ y, fiberMeasure y A ∂Y.μ

def gammaFiberLpNorm {Γ : Type u} [Group Γ]
    {X Y : GammaSystem.{u, v} Γ} {π : X.X -> Y.X}
    (D : GammaFiberMeasureData X Y π) (y : Y.X) (f : X.X -> ℂ) : ℝ :=
  (MeasureTheory.eLpNorm f 2 (D.fiberMeasure y)).toReal

def IsGammaRelativelyAlmostPeriodicOnSubgroup {Γ : Type u} [Group Γ]
    (X Y : GammaSystem.{u, v} Γ) (π : X.X -> Y.X)
    (H : Subgroup Γ) (f : X.X -> ℂ) : Prop :=
  X.lpMember 2 f ∧ ∃ D : GammaFiberMeasureData X Y π,
    ∀ ε : ℝ, 0 < ε -> ∃ r : ℕ, ∃ g : Fin r -> X.X -> ℂ,
      (∀ j, X.lpMember 2 (g j)) ∧
      ∀ γ : Γ, γ ∈ H -> ∀ᵐ y ∂Y.μ, ∃ j : Fin r,
        gammaFiberLpNorm D y
          (fun x => f (X.action γ x) - g j x) < ε

def IsGammaCompactExtensionOnSubgroup {Γ : Type u} [Group Γ]
    (X Y : GammaSystem.{u, v} Γ) (π : X.X -> Y.X)
    (H : Subgroup Γ) : Prop :=
  IsGammaFactorMap X Y π ∧
  ∀ f : X.X -> ℂ, X.lpMember 2 f -> ∀ ε : ℝ, 0 < ε ->
    ∃ h : X.X -> ℂ, IsGammaRelativelyAlmostPeriodicOnSubgroup X Y π H h ∧
      (MeasureTheory.eLpNorm (fun x => f x - h x) 2 X.μ).toReal < ε

def IsGammaCompactExtension {Γ : Type u} [Group Γ]
    (X Y : GammaSystem.{u, v} Γ) (π : X.X -> Y.X) : Prop :=
  IsGammaCompactExtensionOnSubgroup X Y π ⊤

/-- The relatively independent square `X ×_Y X`, including its defining
conditional cylinder measure.  This prevents an arbitrary common extension
from being mistaken for the relative product in §9.6. -/
structure GammaRelativeSelfProductData {Γ : Type u} [Group Γ]
    (X Y : GammaSystem.{u, v} Γ) (π : X.X -> Y.X) where
  system : GammaSystem.{u, v} Γ
  first : system.X -> X.X
  second : system.X -> X.X
  base : system.X -> Y.X
  fiberMeasure : GammaFiberMeasureData X Y π
  common_base : ∀ z, base z = π (first z) ∧ base z = π (second z)
  realizes_fiber_pairs : ∀ x₁ x₂, π x₁ = π x₂ ->
    ∃ z, first z = x₁ ∧ second z = x₂
  first_factor : IsGammaFactorMap system X first
  second_factor : IsGammaFactorMap system X second
  base_factor : IsGammaFactorMap system Y base
  cylinder_measure : ∀ A B : Set X.X, MeasurableSet A -> MeasurableSet B ->
    system.μ {z | first z ∈ A ∧ second z ∈ B} =
      ∫⁻ y, fiberMeasure.fiberMeasure y A *
        fiberMeasure.fiberMeasure y B ∂Y.μ

def IsGammaWeakMixingExtensionForElement {Γ : Type u} [Group Γ]
    (X Y : GammaSystem.{u, v} Γ) (π : X.X -> Y.X) (γ : Γ) : Prop :=
  IsGammaFactorMap X Y π ∧
  ∃ P : GammaRelativeSelfProductData X Y π,
    IsGammaErgodicExtensionForElement P.system Y P.base γ

def IsGammaRelativelyWeakMixingExtension {Γ : Type u} [Group Γ]
    (X Y : GammaSystem.{u, v} Γ) (π : X.X -> Y.X) : Prop :=
  IsGammaFactorMap X Y π ∧
  ∃ P : GammaRelativeSelfProductData X Y π,
    ∀ A : Set P.system.X, MeasurableSet A ->
      (∀ γ, P.system.μ
        (Chapter00.symmDiff ((P.system.action γ) ⁻¹' A) A) = 0) ->
        P.system.μ A = 0 ∨ P.system.μ A = 1

def IsGammaWeakMixingExtensionOnSubgroup {Γ : Type u} [Group Γ]
    (X Y : GammaSystem.{u, v} Γ) (π : X.X -> Y.X)
    (H : Subgroup Γ) : Prop :=
  IsGammaFactorMap X Y π ∧
  ∀ γ : Γ, γ ∈ H -> γ ≠ 1 ->
    IsGammaWeakMixingExtensionForElement X Y π γ

def IsInternalDirectProductOfSubgroups {Γ : Type u} [Group Γ]
    (H K : Subgroup Γ) : Prop :=
  (∀ h : Γ, h ∈ H -> ∀ k : Γ, k ∈ K -> h * k = k * h) ∧
  (∀ g : Γ, ∃ h : Γ, h ∈ H ∧ ∃ k : Γ, k ∈ K ∧ g = h * k) ∧
  ∀ g : Γ, g ∈ H -> g ∈ K -> g = 1

def IsPrimitiveGammaExtension {Γ : Type u} [Group Γ]
    (X Y : GammaSystem.{u, v} Γ) (π : X.X -> Y.X) : Prop :=
  ∃ Γc Γw : Subgroup Γ, IsInternalDirectProductOfSubgroups Γc Γw ∧
    IsGammaCompactExtensionOnSubgroup X Y π Γc ∧
    IsGammaWeakMixingExtensionOnSubgroup X Y π Γw

def FiniteRankFreeAbelianFurstenbergZimmerStatement : Prop :=
  ∀ l : ℕ, ∀ X : GammaSystem.{0, 0} (Multiplicative (Fin l -> ℤ)),
    1 ≤ l -> IsCountablyGeneratedGammaSystem X ->
    ∃ η : Ordinal.{0},
    ∃ tower : Ordinal.{0} -> GammaSystem.{0, 0} (Multiplicative (Fin l -> ℤ)),
    ∃ factorMap : ∀ ξ ξ', (tower ξ').X -> (tower ξ).X,
      {ξ : Ordinal.{0} | ξ < η}.Countable ∧
      Subsingleton (tower 0).X ∧ GammaSystemsIsomorphic (tower η) X ∧
      (∀ ξ ξ', ξ ≤ ξ' -> ξ' ≤ η ->
        IsGammaFactorMap (tower ξ') (tower ξ) (factorMap ξ ξ')) ∧
      (∀ ξ, ξ ≤ η -> factorMap ξ ξ = id) ∧
      (∀ ξ ξ' ξ'', ξ ≤ ξ' -> ξ' ≤ ξ'' -> ξ'' ≤ η ->
        factorMap ξ ξ'' = factorMap ξ ξ' ∘ factorMap ξ' ξ'') ∧
      (∀ ξ, ξ < η -> ∃ π : (tower (ξ + 1)).X -> (tower ξ).X,
        π = factorMap ξ (ξ + 1) ∧
        IsPrimitiveGammaExtension (tower (ξ + 1)) (tower ξ) π) ∧
      (∀ ξ, ξ ≤ η -> ξ ≠ 0 ->
        (∀ γ, γ < ξ -> γ + 1 < ξ) ->
        MeasurableSpace.generateFrom
            {A : Set (tower ξ).X | ∃ γ, γ < ξ ∧
              ∃ B : Set (tower γ).X,
                MeasurableSet B ∧ A = (factorMap γ ξ) ⁻¹' B} =
          (tower ξ).measurableSpace) ∧
      (l = 1 -> ∃ η0 : Ordinal.{0}, η = η0 + 1 ∧
        ∀ ξ, ξ < η0 -> IsGammaCompactExtension
          (tower (ξ + 1)) (tower ξ) (factorMap ξ (ξ + 1)))

def NilpotentGroupOfStep (G : Type u) [Group G] (d : ℕ) : Prop :=
  1 ≤ d ∧ ∃ lowerCentral : ℕ -> Subgroup G,
    lowerCentral 1 = ⊤ ∧ lowerCentral (d + 1) = ⊥ ∧
    ∀ n, 1 ≤ n -> lowerCentral (n + 1) =
      Subgroup.closure {c : G | ∃ a : G, a ∈ lowerCentral n ∧
        ∃ b : G, c = a * b * a⁻¹ * b⁻¹}

/-- A concrete topological characterization of a finite-dimensional Lie
group: a second-countable Hausdorff topological group which is locally
Euclidean.  For topological groups this is equivalent to carrying a Lie-group
structure, and avoids hiding the geometric hypothesis behind a bare label. -/
def IsFiniteDimensionalLieGroup (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  T2Space G ∧ SecondCountableTopology G ∧
  Continuous (fun p : G × G => p.1 * p.2) ∧
  Continuous (fun g : G => g⁻¹) ∧
  ∃ n : ℕ, ∀ g : G, ∃ U : Set G,
    ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen U ∧ IsOpen V ∧ g ∈ U ∧ Nonempty (U ≃ₜ V)

/-- A discrete cocompact subgroup represented together with its left-coset
space.  The fiber equation says exactly that `Q` is `G / lattice`. -/
def IsLatticeQuotient (G Q : Type u) [Group G]
    [TopologicalSpace G] [TopologicalSpace Q]
    (lattice : Set G) (quotientMap : G -> Q) : Prop :=
  (1 : G) ∈ lattice ∧
  (∀ a ∈ lattice, ∀ b ∈ lattice, a * b ∈ lattice) ∧
  (∀ a ∈ lattice, a⁻¹ ∈ lattice) ∧
  (∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ U ∩ lattice = {1}) ∧
  IsCompact (Set.univ : Set Q) ∧ Continuous quotientMap ∧
  Function.Surjective quotientMap ∧
  (∀ V : Set Q, IsOpen V ↔ IsOpen (quotientMap ⁻¹' V)) ∧
  ∀ g h, quotientMap g = quotientMap h ↔ ∃ γ ∈ lattice, h = g * γ

def IsNilSystem (M : MeasurableSystem.{u}) (d : ℕ) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
  ∃ G : Type u, ∃ _ : Group G, ∃ _ : TopologicalSpace G,
    IsFiniteDimensionalLieGroup G ∧ NilpotentGroupOfStep G d ∧
    ∃ lattice : Set G, ∃ Q : Type u, ∃ _ : TopologicalSpace Q,
    ∃ _ : MeasurableSpace Q, ∃ _ : BorelSpace Q,
    ∃ quotientMap : G -> Q, IsLatticeQuotient G Q lattice quotientMap ∧
    ∃ action : G -> Q -> Q, ∃ μQ : Measure Q, ∃ τ : G, ∃ e : M.X ≃ Q,
      (∀ g h x, action (g * h) x = action g (action h x)) ∧
      (∀ x, action 1 x = x) ∧
      (∀ g h, action g (quotientMap h) = quotientMap (g * h)) ∧
      (∀ g, Continuous (action g)) ∧
      IsProbabilityMeasure μQ ∧
      (∀ g, MeasurePreserving (action g) μQ μQ) ∧
      MeasurePreserving e M.μ μQ ∧ MeasurePreserving e.symm μQ M.μ ∧
      ∀ x, e (M.T x) = action τ (e x)

def hostKraCubeMomentAverage (M : MeasurableSystem.{u}) (d N : ℕ)
    (f : (Fin d -> Bool) -> M.X -> ℂ) : ℂ :=
  if N = 0 then 0 else
    ((N : ℂ) ^ d)⁻¹ *
      Finset.univ.sum fun n : Fin d -> Fin N =>
        M.integral fun x => Finset.univ.prod fun e : Fin d -> Bool =>
          f e ((M.T^[Finset.univ.sum fun i : Fin d =>
            if e i then (n i).val else 0]) x)

/-- Moment characterization of the Host--Kra cube measure `μ^[d]`. -/
def IsHostKraCubeMeasure (M : MeasurableSystem.{u}) (d : ℕ)
    (μcube : Measure ((Fin d -> Bool) -> M.X)) : Prop :=
  IsProbabilityMeasure μcube ∧
  (∀ e : Fin d -> Bool, MeasurePreserving (fun q => q e) μcube M.μ) ∧
  ∀ f : (Fin d -> Bool) -> M.X -> ℂ,
    (∀ e, M.lpMember ⊤ (f e)) ->
    Tendsto (fun N => hostKraCubeMomentAverage M d N f -
      ∫ q, Finset.univ.prod (fun e : Fin d -> Bool => f e (q e)) ∂μcube)
      atTop (nhds 0)

def hostKraCubeCorrelation (M : MeasurableSystem.{u}) (d N : ℕ)
    (f : M.X -> ℂ) : ℝ :=
  if N = 0 then 0 else
    ((N : ℝ) ^ d)⁻¹ *
      (Finset.univ.sum fun n : Fin d -> Fin N =>
        (M.integral fun x => Finset.univ.prod fun s : Finset (Fin d) =>
          let z := f ((M.T^[s.sum fun i => (n i).val]) x)
          if Even s.card then z else starRingEnd ℂ z).re)

def HostKraSeminorm (M : MeasurableSystem.{u}) (d : ℕ) (f : M.X -> ℂ) : ℝ :=
  (max 0 (Filter.limsup (fun N => hostKraCubeCorrelation M d N f) atTop)) ^
    ((2 : ℝ) ^ d)⁻¹

structure HostKraOrderData (M : MeasurableSystem.{u}) (d : ℕ) where
  seminorm : (M.X -> ℂ) -> ℝ
  seminorm_eq : seminorm = HostKraSeminorm M d
  cubeMeasure : Measure ((Fin d -> Bool) -> M.X)
  is_cube_measure : IsHostKraCubeMeasure M d cubeMeasure
  characteristicFactor : MeasurableSystem.{u}
  factorMap : M.X -> characteristicFactor.X
  is_factor : Chapter01.IsFactorMap M characteristicFactor factorMap
  detects_factor : ∀ f : M.X -> ℂ, M.lpMember ⊤ f ->
    seminorm f = 0 ↔
      ∃ Ef : M.X -> ℂ,
        IsComplexConditionalExpectationVersion M f
          {A | ∃ B : Set characteristicFactor.X,
            MeasurableSet B ∧ A = factorMap ⁻¹' B} Ef ∧
        M.lpNorm 2 Ef = 0

def IsSystemOfOrder (M : MeasurableSystem.{u}) (d : ℕ) : Prop :=
  Chapter02.IsErgodic M ∧
  ∀ f : M.X -> ℂ, M.lpMember ⊤ f ->
    HostKraSeminorm M (d + 1) f = 0 -> M.lpNorm 2 f = 0

def CharacteristicFactorForLinearAverages
    (M : MeasurableSystem.{u}) (d : ℕ) (Z : MeasurableSystem.{v}) (π : M.X -> Z.X) : Prop :=
  Chapter01.IsFactorMap M Z π ∧
  ∀ f : Fin d -> M.X -> ℂ, (∀ i, M.lpMember ⊤ (f i)) ->
    ∃ Ef : Fin d -> M.X -> ℂ,
      (∀ i, IsComplexConditionalExpectationVersion M (f i)
        {A | ∃ B : Set Z.X, MeasurableSet B ∧ A = π ⁻¹' B} (Ef i)) ∧
      Tendsto (fun N : ℕ => M.lpNorm 2 (fun x =>
        linearMultipleAverage M d N f x - linearMultipleAverage M d N Ef x))
        atTop (nhds 0)

def applyFiniteIntegerActions {X : Type u} {d : ℕ}
    (T : Fin d -> ℤ -> X -> X) (powers : Fin d -> ℤ) (x : X) : X :=
  (List.ofFn fun i : Fin d => i).foldl
    (fun y i => T i (powers i) y) x

def TransformationsGenerateNilpotentAction {X : Type u} {d : ℕ}
    (T : Fin d -> ℤ -> X -> X) : Prop :=
  ∃ G : Type u, ∃ _ : Group G, ∃ step : ℕ, NilpotentGroupOfStep G step ∧
    ∃ gen : Fin d -> G, ∃ act : G -> X -> X,
      (∀ g h, act (g * h) = act g ∘ act h) ∧
      (∀ x, act 1 x = x) ∧ ∀ i n, T i n = act ((gen i) ^ n)

def WalshNilpotentPolynomialAverageStatement : Prop :=
  ∀ M : MeasurableSystem.{u}, ∀ d l : ℕ,
  IsProbabilityMeasure M.μ ->
  ∀ T : Fin d -> ℤ -> M.X -> M.X,
    TransformationsGenerateNilpotentAction T ->
    (∀ i n, MeasurePreserving (T i n) M.μ M.μ) ->
  ∀ p : Fin l -> Fin d -> Polynomial ℤ, ∀ f : Fin l -> M.X -> ℂ,
    (∀ j, M.lpMember ⊤ (f j)) -> ∃ limit : M.X -> ℂ,
    M.lpMember 2 limit ∧ Tendsto (fun N : ℕ => M.lpNorm 2 (fun x =>
      (if N = 0 then 0 else (N : ℂ)⁻¹ * (Finset.range N).sum fun n =>
        Finset.univ.prod fun j : Fin l =>
          f j (applyFiniteIntegerActions T
            (fun i => (p j i).eval ((n + 1 : ℕ) : ℤ)) x)) - limit x))
      atTop (nhds 0)

def NilpotentPolynomialPointwiseAverageStatement : Prop :=
  ∀ M : MeasurableSystem.{u}, ∀ d l : ℕ,
  IsProbabilityMeasure M.μ ->
  ∀ T : Fin d -> ℤ -> M.X -> M.X,
    TransformationsGenerateNilpotentAction T ->
    (∀ i n, MeasurePreserving (T i n) M.μ M.μ) ->
  ∀ p : Fin l -> Fin d -> Polynomial ℤ, ∀ f : Fin l -> M.X -> ℂ,
    (∀ j, M.lpMember ⊤ (f j)) ->
    ∃ E : Set M.X, M.μ Eᶜ = 0 ∧ ∀ x ∈ E, ∃ c : ℂ,
      Tendsto (fun N : ℕ => if N = 0 then 0 else
        (N : ℂ)⁻¹ * (Finset.range N).sum fun n =>
          Finset.univ.prod fun j : Fin l =>
            f j (applyFiniteIntegerActions T
              (fun i => (p j i).eval (n : ℤ)) x)) atTop (nhds c)

def NilpotentPolynomialAverageQuestionStatement : Prop :=
  WalshNilpotentPolynomialAverageStatement.{u} ∧
    NilpotentPolynomialPointwiseAverageStatement.{u}

def HostKraSeminormControlsAverages (M : MeasurableSystem.{u}) (d : ℕ) : Prop :=
  Chapter02.IsErgodic M -> 1 ≤ d ->
  ∀ f : Fin d -> M.X -> ℂ,
    (∀ i, M.lpMember ⊤ (f i) ∧ M.lpNorm ⊤ (f i) ≤ 1) ->
    ∀ j : Fin d, Filter.limsup (fun N : ℕ => M.lpNorm 2 (fun x =>
      if N = 0 then 0 else (N : ℂ)⁻¹ *
        (Finset.range N).sum fun n => Finset.univ.prod fun i : Fin d =>
          f i ((M.T^[(i.val + 1) * n]) x))) atTop ≤ HostKraSeminorm M d (f j)

def IsInverseLimitOfNilSystems (M : MeasurableSystem.{u}) (d : ℕ) : Prop :=
  ∃ Xn : ℕ -> MeasurableSystem.{u},
    (∀ n, IsNilSystem (Xn n) d) ∧
    ∃ D : Chapter01.InverseSequenceData.{u}, ∃ π : ∀ n, M.X -> (D.system n).X,
      D.system = Xn ∧ Chapter01.IsInverseLimitSystem D M π

def HostKraCubeReconstruction (M : MeasurableSystem.{u}) (d : ℕ) : Prop :=
  ∃ μcube : Measure ((Fin d -> Bool) -> M.X),
    IsHostKraCubeMeasure M d μcube ∧
    ∃ J : ((e : Fin d -> Bool) -> e ≠ (fun _ => false) -> M.X) -> M.X,
      ∀ᵐ x ∂μcube, x (fun _ => false) =
        J (fun e _ => x e)

def HostKraStructureEquivalence (M : MeasurableSystem.{u}) (d : ℕ) : Prop :=
  Chapter02.IsErgodic M -> 1 ≤ d ->
  IsSystemOfOrder M (d - 1) ↔
    (IsInverseLimitOfNilSystems M (d - 1) ∧
      (∀ f : M.X -> ℂ, M.lpMember ⊤ f ->
        HostKraSeminorm M d f = 0 -> M.lpNorm 2 f = 0) ∧
      HostKraCubeReconstruction M d)

structure TopologicalIntegerActionData (S : TopologicalSystem.{u}) where
  act : ℤ -> S.X ≃ₜ S.X
  zero_act : act 0 = Homeomorph.refl S.X
  add_act : ∀ m n, act (m + n) = (act n).trans (act m)
  one_act : (act 1 : S.X -> S.X) = S.T

abbrev CubeVertex (d : ℕ) := Fin d -> Bool

def cubeDot (n : Fin d -> ℤ) (e : CubeVertex d) : ℤ :=
  Finset.univ.sum fun i => if e i then n i else 0

def topologicalCubeSet (S : TopologicalSystem.{u}) (d : ℕ)
    (U : TopologicalIntegerActionData S) : Set (CubeVertex d -> S.X) :=
  closure {q | ∃ x : S.X, ∃ n : Fin d -> ℤ,
    q = fun e => U.act (cubeDot n e) x}

def cubeFaceTransform (S : TopologicalSystem.{u}) (d : ℕ)
    (U : TopologicalIntegerActionData S) (n : Fin d -> ℤ)
    (q : CubeVertex d -> S.X) : CubeVertex d -> S.X :=
  fun e => U.act (cubeDot n e) (q e)

def cubeGroupTransform (S : TopologicalSystem.{u}) (d : ℕ)
    (U : TopologicalIntegerActionData S) (m : ℤ) (n : Fin d -> ℤ)
    (q : CubeVertex d -> S.X) : CubeVertex d -> S.X :=
  fun e => U.act (m + cubeDot n e) (q e)

def measurableCubeGroupTransform (M : MeasurableSystem.{u}) (d : ℕ)
    (U : IntegerActionData M) (m : ℤ) (n : Fin d -> ℤ)
    (q : CubeVertex d -> M.X) : CubeVertex d -> M.X :=
  fun e => U.act (m + cubeDot n e) (q e)

/-- The invariant-factor system `(Ω_d, P_d, F^[d])` obtained from the
ergodic decomposition of the diagonal action on the Host--Kra cube. -/
structure CubeInvariantFactorData (M : MeasurableSystem.{u}) (d : ℕ)
    (U : IntegerActionData M) (μcube : Measure (CubeVertex d -> M.X)) where
  Ω : Type u
  measurableSpace : MeasurableSpace Ω
  P : @Measure Ω measurableSpace
  component : (CubeVertex d -> M.X) -> Ω
  probability : IsProbabilityMeasure P
  factor_map : MeasurePreserving component μcube P
  diagonal_invariant : ∀ m q,
    component (measurableCubeGroupTransform M d U m (fun _ => 0) q) = component q
  realizes_invariant_sigma : ∀ A : Set (CubeVertex d -> M.X), MeasurableSet A ->
    ((∀ m : ℤ, μcube (Chapter00.symmDiff
        ((measurableCubeGroupTransform M d U m (fun _ => 0)) ⁻¹' A) A) = 0) ↔
      ∃ B : Set Ω, @MeasurableSet Ω measurableSpace B ∧
        μcube (Chapter00.symmDiff A (component ⁻¹' B)) = 0)
  faceAction : (Fin d -> ℤ) -> Ω -> Ω
  face_zero : faceAction 0 = id
  face_add : ∀ n m, faceAction (n + m) = faceAction n ∘ faceAction m
  face_intertwines : ∀ n q,
    component (measurableCubeGroupTransform M d U 0 n q) = faceAction n (component q)
  face_preserving : ∀ n, MeasurePreserving (faceAction n) P P
  face_ergodic : ∀ A : Set Ω, @MeasurableSet Ω measurableSpace A ->
    (∀ n, P (Chapter00.symmDiff ((faceAction n) ⁻¹' A) A) = 0) ->
      P A = 0 ∨ P A = 1

def CubeMinimalityStatement (S : TopologicalSystem.{u}) (d : ℕ) : Prop :=
  Chapter05.IsCompactTopologicalSystem S -> IsHomeomorph S.T ->
  Chapter05.IsMinimalSystem S -> 1 ≤ d ->
  ∃ U : TopologicalIntegerActionData S,
    (∀ q ∈ topologicalCubeSet S d U,
      closure {q' | ∃ m : ℤ, ∃ n : Fin d -> ℤ,
        cubeGroupTransform S d U m n q = q'} = topologicalCubeSet S d U) ∧
    ∀ x : S.X,
      let Qx := closure {q | ∃ n : Fin d -> ℤ,
        cubeFaceTransform S d U n (fun _ => x) = q}
      ∀ q ∈ Qx, closure {q' | ∃ n : Fin d -> ℤ,
        cubeFaceTransform S d U n q = q'} = Qx

def ProgressionOrbitClosureMinimalityStatement
    (S : TopologicalSystem.{u}) (d : ℕ) : Prop :=
  Chapter05.IsCompactTopologicalSystem S -> IsHomeomorph S.T ->
  Chapter05.IsMinimalSystem S -> 1 ≤ d ->
  ∃ U : TopologicalIntegerActionData S,
    ∀ x : S.X,
      let Nd := closure {q : Fin d -> S.X | ∃ n m : ℤ,
        q = fun i => U.act (n + (i.val + 1) * m) x}
      ∀ q ∈ Nd, closure {q' | ∃ n m : ℤ,
        q' = fun i => U.act (n + (i.val + 1) * m) (q i)} = Nd

def IsStrictlyErgodicProgressionOrbitClosure
    (S : TopologicalSystem.{u}) (d : ℕ) : Prop :=
  ∃ _ : MeasurableSpace S.X, ∃ _ : BorelSpace S.X,
  ∃ U : TopologicalIntegerActionData S, ∃ Nd : Set (Fin d -> S.X),
    (∀ x : S.X, Nd = closure {q : Fin d -> S.X | ∃ n m : ℤ,
      q = fun i => U.act (n + (i.val + 1) * m) x}) ∧
    (∀ q ∈ Nd, closure {q' | ∃ n m : ℤ,
      q' = fun i => U.act (n + (i.val + 1) * m) (q i)} = Nd) ∧
    ∃! ν : Measure (Fin d -> S.X),
      IsProbabilityMeasure ν ∧ ν Nd = 1 ∧
      ∀ n m : ℤ, MeasurePreserving
        (fun (q : Fin d -> S.X) (i : Fin d) =>
          U.act (n + (i.val + 1) * m) (q i)) ν ν

def MeasurableCubeErgodicityStatement (M : MeasurableSystem.{u}) (d : ℕ) : Prop :=
  Chapter02.IsErgodic M -> Nonempty (IntegerActionData M) -> 1 ≤ d ->
  ∃ U : IntegerActionData M, ∃ μcube : Measure (CubeVertex d -> M.X),
    IsHostKraCubeMeasure M d μcube ∧
    (∀ m n, MeasurePreserving
      (measurableCubeGroupTransform M d U m n) μcube μcube) ∧
    (∀ A : Set (CubeVertex d -> M.X), MeasurableSet A ->
      (∀ m : ℤ, ∀ n : Fin d -> ℤ,
        μcube (Chapter00.symmDiff
          ((measurableCubeGroupTransform M d U m n) ⁻¹' A) A) = 0) ->
      μcube A = 0 ∨ μcube A = 1) ∧
    Nonempty (CubeInvariantFactorData M d U μcube)

def IsTopologicalNilSystem (S : TopologicalSystem.{u}) (d : ℕ) : Prop :=
  Chapter05.IsMinimalSystem S ∧
  ∃ G : Type u, ∃ _ : Group G, ∃ _ : TopologicalSpace G,
    IsFiniteDimensionalLieGroup G ∧ NilpotentGroupOfStep G d ∧
    ∃ lattice : Set G, ∃ Q : Type u, ∃ _ : TopologicalSpace Q,
    ∃ quotientMap : G -> Q, IsLatticeQuotient G Q lattice quotientMap ∧
    ∃ action : G -> Q -> Q, ∃ τ : G, ∃ e : S.X ≃ₜ Q,
      (∀ g h x, action (g * h) x = action g (action h x)) ∧
      (∀ x, action 1 x = x) ∧
      (∀ g h, action g (quotientMap h) = quotientMap (g * h)) ∧
      (∀ g, Continuous (action g)) ∧
      ∀ x, e (S.T x) = action τ (e x)

def IsTopologicalProNilSystem (S : TopologicalSystem.{u}) (d : ℕ) : Prop :=
  ∃ Xn : ℕ -> TopologicalSystem.{u},
    (∀ n, IsTopologicalNilSystem (Xn n) d) ∧
    ∃ bonding : ∀ n, (Xn (n + 1)).X -> (Xn n).X,
      (∀ n, Chapter05.IsFactorMap (Xn (n + 1)) (Xn n) (bonding n)) ∧
      ∃ π : ∀ n, S.X -> (Xn n).X,
        (∀ n, Chapter05.IsFactorMap S (Xn n) (π n)) ∧
        (∀ n, π n = bonding n ∘ π (n + 1)) ∧
        (∀ x y : S.X, x ≠ y -> ∃ n, π n x ≠ π n y) ∧
        ∀ thread : ∀ n, (Xn n).X,
          (∀ n, bonding n (thread (n + 1)) = thread n) ->
          ∃ x : S.X, ∀ n, π n x = thread n

def TopologicalProNilCharacterization (S : TopologicalSystem.{u}) (d : ℕ) : Prop :=
  Chapter05.IsCompactTopologicalSystem S -> IsHomeomorph S.T ->
  Chapter05.IsMinimalSystem S -> 2 ≤ d ->
  ∃ U : TopologicalIntegerActionData S,
    (IsTopologicalProNilSystem S (d - 1) ↔
      ((∀ x y : CubeVertex d -> S.X,
        x ∈ topologicalCubeSet S d U -> y ∈ topologicalCubeSet S d U ->
        (∃ e0, ∀ e, e ≠ e0 -> x e = y e) -> x = y) ∧
       ∀ x y : S.X,
        (Function.update (fun _ : CubeVertex d => y) (fun _ => false) x)
          ∈ topologicalCubeSet S d U -> x = y))

def RegionallyProximalOfOrder (S : TopologicalSystem.{u}) [PseudoMetricSpace S.X]
    (d : ℕ) (x y : S.X) : Prop :=
  ∃ U : TopologicalIntegerActionData S,
  ∀ δ : ℝ, 0 < δ -> ∃ x' y' : S.X, ∃ n : Fin d -> ℤ,
    dist x x' < δ ∧ dist y y' < δ ∧
    ∀ e : CubeVertex d, e ≠ (fun _ => false) ->
      dist (U.act (cubeDot n e) x') (U.act (cubeDot n e) y') < δ

def RegionallyProximalRelationStatement (S : TopologicalSystem.{u}) (d : ℕ) : Prop :=
  Chapter05.IsCompactTopologicalSystem S -> IsHomeomorph S.T ->
  Chapter05.IsMinimalSystem S -> 1 ≤ d ->
  ∃ _ : PseudoMetricSpace S.X,
    Equivalence (RegionallyProximalOfOrder S d) ∧
    IsClosed {p : S.X × S.X | RegionallyProximalOfOrder S d p.1 p.2} ∧
    (∀ Y : TopologicalSystem.{u}, ∀ _ : PseudoMetricSpace Y.X, ∀ π : S.X -> Y.X,
      Chapter05.IsFactorMap S Y π ->
      {p : Y.X × Y.X | RegionallyProximalOfOrder Y d p.1 p.2} =
        Prod.map π π '' {p : S.X × S.X | RegionallyProximalOfOrder S d p.1 p.2}) ∧
    ∃ Q : TopologicalSystem.{u}, ∃ π : S.X -> Q.X,
      Chapter05.IsFactorMap S Q π ∧ IsTopologicalProNilSystem Q d ∧
      (∀ x y, π x = π y ↔ RegionallyProximalOfOrder S d x y) ∧
      ∀ Y : TopologicalSystem.{u}, IsTopologicalProNilSystem Y d ->
      ∀ φ : S.X -> Y.X, Chapter05.IsFactorMap S Y φ ->
        ∃ ψ : Q.X -> Y.X, Chapter05.IsFactorMap Q Y ψ ∧ φ = ψ ∘ π

def BourgainPointwiseConvergenceStatement (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ->
  Nonempty (IntegerActionData M) ->
  (∀ U : IntegerActionData M, ∀ p : Polynomial ℤ, ∀ r : ℝ, 1 < r ->
    ∀ f : M.X -> ℂ, M.lpMember (ENNReal.ofReal r) f ->
      ∃ E : Set M.X, M.μ Eᶜ = 0 ∧ ∀ x ∈ E, ∃ c : ℂ,
        Tendsto (fun N : ℕ => if N = 0 then 0 else
          (N : ℂ)⁻¹ * (Finset.range N).sum fun n =>
            f (U.act (p.eval (n : ℤ)) x)) atTop (nhds c)) ∧
  (∀ U : IntegerActionData M, ∀ a b : ℤ,
    a ≠ 0 -> b ≠ 0 -> a ≠ b ->
    ∀ f g : M.X -> ℂ, M.lpMember ⊤ f -> M.lpMember ⊤ g ->
      ∃ E : Set M.X, M.μ Eᶜ = 0 ∧ ∀ x ∈ E, ∃ c : ℂ,
        Tendsto (fun N : ℕ => if N = 0 then 0 else
          (N : ℂ)⁻¹ * (Finset.range N).sum fun n =>
            f (U.act (a * n) x) * g (U.act (b * n) x)) atTop (nhds c))

def StrictlyErgodicModelForCubesStatement (M : MeasurableSystem.{u}) (d : ℕ) : Prop :=
  Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace ->
  Chapter02.IsErgodic M -> Nonempty (IntegerActionData M) -> 1 ≤ d ->
  ∃ D : Chapter06.TopologicalModelData M,
    Chapter06.IsTopologicalModel M D ∧
    Chapter06.IsStrictlyErgodic D.topologicalSystem ∧
    IsStrictlyErgodicProgressionOrbitClosure D.topologicalSystem d

def PointwiseMultipleAverageConvergenceStatement (M : MeasurableSystem.{u}) (d : ℕ) : Prop :=
  Chapter01.IsMeasurePreservingSystem M -> 1 ≤ d ->
  ∀ f : Fin d -> M.X -> ℂ, (∀ i, M.lpMember ⊤ (f i)) ->
    ∃ E : Set M.X, M.μ Eᶜ = 0 ∧ ∀ x ∈ E, ∃ c : ℂ,
      Tendsto (fun N : ℕ => if N = 0 then 0 else
        (N : ℂ)⁻¹ * (Finset.range N).sum fun n =>
          Finset.univ.prod fun i : Fin d => f i ((M.T^[(i.val + 1) * n]) x))
        atTop (nhds c)

def TwoParameterProgressionAverageConvergenceStatement
    (M : MeasurableSystem.{u}) (d : ℕ) : Prop :=
  Chapter02.IsErgodic M -> 1 ≤ d ->
  ∀ f : Fin d -> M.X -> ℂ, (∀ i, M.lpMember ⊤ (f i)) ->
    ∃ c : ℂ, ∃ E : Set M.X, M.μ Eᶜ = 0 ∧ ∀ x ∈ E,
      Tendsto (fun N : ℕ => if N = 0 then 0 else
        ((N : ℂ) ^ 2)⁻¹ * (Finset.range N).sum fun n =>
          (Finset.range N).sum fun m =>
            Finset.univ.prod fun i : Fin d =>
              f i ((M.T^[n + i.val * m]) x)) atTop (nhds c)

def IsPIDSystem (M : MeasurableSystem.{u}) : Prop :=
  ∀ d : ℕ, 3 ≤ d -> ∀ J : Chapter08.MultipleJoiningData (fun _ : Fin d => M),
    Chapter08.IsMultipleJoining (fun _ : Fin d => M) J ->
    (∀ i j : Fin d, i ≠ j -> ∀ A B : Set M.X, MeasurableSet A -> MeasurableSet B ->
      J {x | x i ∈ A ∧ x j ∈ B} = M.μ A * M.μ B) ->
    ∀ A : Fin d -> Set M.X, (∀ i, MeasurableSet (A i)) ->
      J {x | ∀ i, x i ∈ A i} = Finset.univ.prod fun i => M.μ (A i)

def CubeGroupAverageConvergenceStatement (M : MeasurableSystem.{u}) (d : ℕ) : Prop :=
  Chapter01.IsMeasurePreservingSystem M -> 1 ≤ d ->
  ∀ f : {e : CubeVertex d // e ≠ (fun _ => false)} -> M.X -> ℂ,
    (∀ e, M.lpMember ⊤ (f e)) ->
  ∃ limit : M.X -> ℂ, M.lpMember 2 limit ∧
  ∀ offset side : ℕ -> Fin d -> ℕ,
    (∀ i, Tendsto (fun k => side k i) atTop atTop) ->
    Tendsto (fun k : ℕ => M.lpNorm 2 (fun x =>
      (if (Finset.univ.prod fun i : Fin d => side k i) = 0 then 0 else
        ((Finset.univ.prod fun i : Fin d => side k i : ℕ) : ℂ)⁻¹ *
        Finset.univ.sum fun n : (i : Fin d) -> Fin (side k i) =>
          Finset.univ.prod fun e : {e : CubeVertex d // e ≠ (fun _ => false)} =>
            f e ((M.T^[Finset.univ.sum fun i : Fin d =>
              (offset k i + (n i).val) * (if e.val i then 1 else 0)]) x)) - limit x))
      atTop (nhds 0)

end Chapter09
