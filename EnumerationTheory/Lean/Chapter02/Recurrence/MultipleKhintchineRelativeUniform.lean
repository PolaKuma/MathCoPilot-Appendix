import Chapter02.HostKra.HostKraRelativeMean
import Chapter02.HostKra.HostKraCartesianCube
import Chapter02.Recurrence.MultipleKhintchineProductInvariant
import Chapter02.Ergodic.VanDerCorputPairLimits

open Classical Filter MeasureTheory
open scoped BigOperators

noncomputable section

namespace Chapter02.MultipleKhintchineRelativeUniform

universe u

/-- Cartesian tensor squaring intertwines every forward Koopman iterate
with the diagonal iterate on the Cartesian-square system. -/
lemma koopman_iter_cartesianSquareLp_ae
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) (n : ℕ) :
    let P := MultipleKhintchineCartesian.productSystem M M
    let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
    let Y := HostKraCartesianCube.cartesianSquareLp M hM F
    (fun p ↦
      (show Lp ℂ 2 P.μ from
        ((MultipleKhintchineCharacteristic.KData P hP).U^[n]) Y) p)
      =ᵐ[P.μ]
    fun p : M.X × M.X ↦
      (show Lp ℂ 2 M.μ from
        ((MultipleKhintchineCharacteristic.KData M hM).U^[n]) F) p.1 *
      star
        ((show Lp ℂ 2 M.μ from
          ((MultipleKhintchineCharacteristic.KData M hM).U^[n]) F) p.2) := by
  dsimp only
  let P := MultipleKhintchineCartesian.productSystem M M
  let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
  let Y := HostKraCartesianCube.cartesianSquareLp M hM F
  have hiterP :=
    MultipleKhintchineKronecker.koopmanData_iter_ae P hP n Y
  have hY := HostKraCartesianCube.cartesianSquareLp_coe M hM F
  have hYshift :=
    (hP.2.iterate n).quasiMeasurePreserving.ae_eq_comp hY
  have hiter :=
    MultipleKhintchineKronecker.koopmanData_iter_ae M hM n F
  have hiterFst :=
    (Measure.quasiMeasurePreserving_fst
      (μ := M.μ) (ν := M.μ)).ae_eq hiter
  have hiterSnd :=
    (Measure.quasiMeasurePreserving_snd
      (μ := M.μ) (ν := M.μ)).ae_eq hiter
  filter_upwards [hiterP, hYshift, hiterFst, hiterSnd] with
      p hp hYp hfst hsnd
  rw [hp]
  have hYp' :
      Y ((P.T^[n]) p) =
        MultipleKhintchineCartesian.cartesianSquare
          (fun x ↦ F x) ((P.T^[n]) p) := by
    simpa only [Function.comp_apply] using hYp
  rw [hYp', MultipleKhintchineCartesian.product_iter M M n p]
  change
    F ((M.T^[n]) p.1) * star (F ((M.T^[n]) p.2)) =
      (show Lp ℂ 2 M.μ from
        ((MultipleKhintchineCharacteristic.KData M hM).U^[n]) F) p.1 *
      star
        ((show Lp ℂ 2 M.μ from
          ((MultipleKhintchineCharacteristic.KData M hM).U^[n]) F) p.2)
  have hfst' :
      (show Lp ℂ 2 M.μ from
        ((MultipleKhintchineCharacteristic.KData M hM).U^[n]) F) p.1 =
        F ((M.T^[n]) p.1) := by
    simpa only [Function.comp_apply] using hfst
  have hsnd' :
      (show Lp ℂ 2 M.μ from
        ((MultipleKhintchineCharacteristic.KData M hM).U^[n]) F) p.2 =
        F ((M.T^[n]) p.2) := by
    simpa only [Function.comp_apply] using hsnd
  rw [hfst', hsnd']

/-- The right van der Corput pair function of a tensor square is the tensor
square of the corresponding right pair function on the base system. -/
lemma rightPairFunction_cartesianSquareLp_ae
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (G : Lp ℂ 2 M.μ) (h k : ℕ) :
    let P := MultipleKhintchineCartesian.productSystem M M
    let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
    let Y := HostKraCartesianCube.cartesianSquareLp M hM G
    MultipleKhintchineCharacteristic.rightPairFunction P hP Y h k
      =ᵐ[P.μ]
    MultipleKhintchineCartesian.cartesianSquare
      (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k) := by
  dsimp only
  let P := MultipleKhintchineCartesian.productSystem M M
  let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
  let Y := HostKraCartesianCube.cartesianSquareLp M hM G
  have hh := koopman_iter_cartesianSquareLp_ae M hM G (2 * h)
  have hk := koopman_iter_cartesianSquareLp_ae M hM G (2 * k)
  filter_upwards [hh, hk] with p hhp hkp
  simp only [MultipleKhintchineCharacteristic.rightPairFunction]
  rw [hhp, hkp]
  simp only [MultipleKhintchineCartesian.cartesianSquare,
    MultipleKhintchineCharacteristic.rightPairFunction,
    Nat.mul_comm,
    starRingEnd_apply, star_mul, star_star]
  ring

/-- The left van der Corput pair function of a tensor square is the tensor
square of the corresponding left pair function on the base system. -/
lemma leftPairFunction_cartesianSquareLp_ae
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) (h k : ℕ) :
    let P := MultipleKhintchineCartesian.productSystem M M
    let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
    let Y := HostKraCartesianCube.cartesianSquareLp M hM F
    MultipleKhintchineCharacteristic.leftPairFunction P hP Y h k
      =ᵐ[P.μ]
    MultipleKhintchineCartesian.cartesianSquare
      (MultipleKhintchineCharacteristic.leftPairFunction M hM F h k) := by
  dsimp only
  let P := MultipleKhintchineCartesian.productSystem M M
  let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
  let Y := HostKraCartesianCube.cartesianSquareLp M hM F
  have hh := koopman_iter_cartesianSquareLp_ae M hM F h
  have hk := koopman_iter_cartesianSquareLp_ae M hM F k
  filter_upwards [hh, hk] with p hhp hkp
  simp only [MultipleKhintchineCharacteristic.leftPairFunction]
  rw [hhp, hkp]
  simp only [MultipleKhintchineCartesian.cartesianSquare,
    MultipleKhintchineCharacteristic.leftPairFunction,
    starRingEnd_apply, star_mul, star_star]
  ring

/-- A raw tensor square, converted to `L²`, is the separated product of
the underlying vector and its `L²` conjugate. -/
lemma tensorSquare_toLp_eq_separatedProductLp
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f 2 M.μ) :
    (HilbertSchmidtInvariant.tensorSquare_memLp M hM f hf).toLp
        (TensorSquare M f) =
      MultipleKhintchineProductInvariant.separatedProductLp M hM
        (hf.toLp f)
        (ForwardKroneckerFactor.lpStar M (hf.toLp f)) := by
  have hfFst :=
    (Measure.quasiMeasurePreserving_fst
      (μ := M.μ) (ν := M.μ)).ae_eq hf.coeFn_toLp
  have hfSnd :=
    (Measure.quasiMeasurePreserving_snd
      (μ := M.μ) (ν := M.μ)).ae_eq hf.coeFn_toLp
  have hstarSnd :=
    (Measure.quasiMeasurePreserving_snd
      (μ := M.μ) (ν := M.μ)).ae_eq
        (ForwardKroneckerFactor.lpStar_coe M (hf.toLp f))
  apply Lp.ext
  filter_upwards [
    (HilbertSchmidtInvariant.tensorSquare_memLp M hM f hf).coeFn_toLp,
    MultipleKhintchineProductInvariant.separatedProductLp_coe M hM
      (hf.toLp f) (ForwardKroneckerFactor.lpStar M (hf.toLp f)),
    hfFst, hfSnd, hstarSnd] with
      p hleft hright hf₁ hf₂ hstar
  have hf₁' : (hf.toLp f) p.1 = f p.1 := by
    simpa only [Function.comp_apply] using hf₁
  have hf₂' : (hf.toLp f) p.2 = f p.2 := by
    simpa only [Function.comp_apply] using hf₂
  have hstar' :
      ForwardKroneckerFactor.lpStar M (hf.toLp f) p.2 =
        star ((hf.toLp f) p.2) := by
    simpa only [Function.comp_apply] using hstar
  rw [hleft, hright, hf₁', hstar', hf₂']
  rfl

/-- Conjugating a raw tensor square interchanges its two separated
factors. -/
lemma star_tensorSquare_toLp_eq_separatedProductLp
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f 2 M.μ) :
    ((HilbertSchmidtInvariant.tensorSquare_memLp M hM f hf).star).toLp
        (star (TensorSquare M f)) =
      MultipleKhintchineProductInvariant.separatedProductLp M hM
        (ForwardKroneckerFactor.lpStar M (hf.toLp f))
        (hf.toLp f) := by
  have hfFst :=
    (Measure.quasiMeasurePreserving_fst
      (μ := M.μ) (ν := M.μ)).ae_eq hf.coeFn_toLp
  have hfSnd :=
    (Measure.quasiMeasurePreserving_snd
      (μ := M.μ) (ν := M.μ)).ae_eq hf.coeFn_toLp
  have hstarFst :=
    (Measure.quasiMeasurePreserving_fst
      (μ := M.μ) (ν := M.μ)).ae_eq
        (ForwardKroneckerFactor.lpStar_coe M (hf.toLp f))
  apply Lp.ext
  filter_upwards [
    ((HilbertSchmidtInvariant.tensorSquare_memLp M hM f hf).star).coeFn_toLp,
    MultipleKhintchineProductInvariant.separatedProductLp_coe M hM
      (ForwardKroneckerFactor.lpStar M (hf.toLp f)) (hf.toLp f),
    hfFst, hfSnd, hstarFst] with
      p hleft hright hf₁ hf₂ hstar
  have hf₁' : (hf.toLp f) p.1 = f p.1 := by
    simpa only [Function.comp_apply] using hf₁
  have hf₂' : (hf.toLp f) p.2 = f p.2 := by
    simpa only [Function.comp_apply] using hf₂
  have hstar' :
      ForwardKroneckerFactor.lpStar M (hf.toLp f) p.1 =
        star ((hf.toLp f) p.1) := by
    simpa only [Function.comp_apply] using hstar
  rw [hleft, hright, hstar', hf₁', hf₂']
  change star (f p.1 * star (f p.2)) = star (f p.1) * f p.2
  rw [star_mul, star_star, mul_comm]

/-- Pointwise conjugation on `L²` is involutive. -/
lemma lpStar_lpStar
    (M : System.{u}) (F : Lp ℂ 2 M.μ) :
    ForwardKroneckerFactor.lpStar M
        (ForwardKroneckerFactor.lpStar M F) = F := by
  apply Lp.ext
  filter_upwards [
    ForwardKroneckerFactor.lpStar_coe M
      (ForwardKroneckerFactor.lpStar M F),
    ForwardKroneckerFactor.lpStar_coe M F] with x hss hs
  rw [hss, hs, star_star]

/-- On a Cartesian square, the relative invariant mean is the same
orthogonal projection as the product-invariant projection used by the cube
pairing formalism. -/
theorem product_invariantMeanLp_eq_productInvariantProjectionCLM
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X × M.X → ℂ)
    (hf : MemLp f 2 (M.μ.prod M.μ)) :
    let P := MultipleKhintchineCartesian.productSystem M M
    let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
    HostKraRelativeMean.invariantMeanLp P hP f hf =
      MultipleKhintchineProductInvariant.productInvariantProjectionCLM
        M hM (hf.toLp f) := by
  dsimp only
  rw [HostKraRelativeMean.invariantMeanLp_eq_fixedProjection]
  rfl

/-- Pairing against a Cartesian invariant projection is unchanged if the
first vector is projected as well. -/
theorem inner_productInvariantProjection_eq_inner_projections
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 (M.μ.prod M.μ)) :
    @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
        F
        (MultipleKhintchineProductInvariant.productInvariantProjectionCLM
          M hM G) =
      @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
        (MultipleKhintchineProductInvariant.productInvariantProjectionCLM
          M hM F)
        (MultipleKhintchineProductInvariant.productInvariantProjectionCLM
          M hM G) := by
  let P := MultipleKhintchineCartesian.productSystem M M
  let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
  let Uiso : Lp ℂ 2 P.μ →ₗᵢ[ℂ] Lp ℂ 2 P.μ :=
    Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2
  let U : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ :=
    Uiso.toContinuousLinearMap
  let S : Submodule ℂ (Lp ℂ 2 P.μ) :=
    LinearMap.eqLocus U (1 : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ)
  let F' : Lp ℂ 2 P.μ := F
  let G' : Lp ℂ 2 P.μ := G
  let PF : Lp ℂ 2 P.μ := (S.orthogonalProjection F' : Lp ℂ 2 P.μ)
  let PG : Lp ℂ 2 P.μ := (S.orthogonalProjection G' : Lp ℂ 2 P.μ)
  have hPGmem : PG ∈ S := (S.orthogonalProjection G').property
  have horth : F' - PF ∈ Sᗮ :=
    S.sub_starProjection_mem_orthogonal F'
  have hz : @inner ℂ (Lp ℂ 2 P.μ) _ (F' - PF) PG = 0 :=
    S.inner_left_of_mem_orthogonal hPGmem horth
  change
    @inner ℂ (Lp ℂ 2 P.μ) _ F' PG =
      @inner ℂ (Lp ℂ 2 P.μ) _ PF PG
  calc
    @inner ℂ (Lp ℂ 2 P.μ) _ F' PG =
        @inner ℂ (Lp ℂ 2 P.μ) _ ((F' - PF) + PF) PG := by
          congr 1
          abel
    _ = @inner ℂ (Lp ℂ 2 P.μ) _ (F' - PF) PG +
        @inner ℂ (Lp ℂ 2 P.μ) _ PF PG := inner_add_left _ _ _
    _ = _ := by rw [hz, zero_add]

/-- The base-system right van der Corput pair, as a canonical `L²`
vector. -/
def rightPairLp
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (G : Lp ℂ 2 M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (h k : ℕ) : Lp ℂ 2 M.μ :=
  (MultipleKhintchineCharacteristic.rightPairFunction_memLp
    M hM G hGtop h k).toLp
      (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)

/-- The base-system left van der Corput pair, as a canonical `L²`
vector. -/
def leftPairLp
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (h k : ℕ) : Lp ℂ 2 M.μ :=
  (MultipleKhintchineCharacteristic.leftPairFunction_memLp
    M hM F hFtop h k).toLp
      (MultipleKhintchineCharacteristic.leftPairFunction M hM F h k)

/-- The fixed pair limit for a bilinear progression on a not necessarily
ergodic system.  The ordinary product of means is replaced by the pairing
with the invariant projection. -/
def relativeDoubleKoopmanPairLimit
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (h k : ℕ) : ℝ :=
  (@inner ℂ (Lp ℂ 2 M.μ) _
    ((MultipleKhintchineCharacteristic.star_leftPairFunction_memLp
      M hM F hFtop h k).toLp
      (fun x ↦ star
        (MultipleKhintchineCharacteristic.leftPairFunction
          M hM F h k x)))
    (HostKraRelativeMean.invariantMeanLp M hM
      (MultipleKhintchineCharacteristic.rightPairFunction
        M hM G h k)
      (MultipleKhintchineCharacteristic.rightPairFunction_memLp
        M hM G hGtop h k))).re

/-- On a Cartesian-square system, every relative bilinear pair limit is
exactly a pairing of the two Cartesian invariant projections.  This is the
entry point for applying cube transposition to nonergodic product-system
averages. -/
theorem relativeDoubleKoopmanPairLimit_product_eq_re_inner_projections
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G :
      Lp ℂ 2
        (MultipleKhintchineCartesian.productSystem M M).μ)
    (hFtop :
      MemLp (fun p ↦ F p) ⊤
        (MultipleKhintchineCartesian.productSystem M M).μ)
    (hGtop :
      MemLp (fun p ↦ G p) ⊤
        (MultipleKhintchineCartesian.productSystem M M).μ)
    (h k : ℕ) :
    let P := MultipleKhintchineCartesian.productSystem M M
    let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
    let f : P.X → ℂ :=
      MultipleKhintchineCharacteristic.rightPairFunction P hP G h k
    let g : P.X → ℂ := fun p ↦ star
      (MultipleKhintchineCharacteristic.leftPairFunction P hP F h k p)
    let hf : MemLp f 2 P.μ :=
      MultipleKhintchineCharacteristic.rightPairFunction_memLp
        P hP G hGtop h k
    let hg : MemLp g 2 P.μ :=
      MultipleKhintchineCharacteristic.star_leftPairFunction_memLp
        P hP F hFtop h k
    relativeDoubleKoopmanPairLimit
        P hP F G hFtop hGtop h k =
      (@inner ℂ (Lp ℂ 2 P.μ) _
        (MultipleKhintchineProductInvariant.productInvariantProjectionCLM
          M hM (hg.toLp g))
        (MultipleKhintchineProductInvariant.productInvariantProjectionCLM
          M hM (hf.toLp f))).re := by
  dsimp only
  unfold relativeDoubleKoopmanPairLimit
  rw [product_invariantMeanLp_eq_productInvariantProjectionCLM]
  rw [inner_productInvariantProjection_eq_inner_projections]

/-- For tensor-square inputs, the relative pair limit on the Cartesian
square is the row-oriented invariant-projection pairing of the two
base-system van der Corput pairs. -/
theorem relativeDoubleKoopmanPairLimit_cartesianSquare_eq_rowProjectionPairing
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Lp ℂ 2 M.μ)
    (hAtop : MemLp (fun x ↦ A x) ⊤ M.μ)
    (hBtop : MemLp (fun x ↦ B x) ⊤ M.μ)
    (h k : ℕ) :
    let P := MultipleKhintchineCartesian.productSystem M M
    let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
    let YA := HostKraCartesianCube.cartesianSquareLp M hM A
    let YB := HostKraCartesianCube.cartesianSquareLp M hM B
    let hYAtop :=
      HostKraCartesianCube.cartesianSquareLp_memLp_top M hM A hAtop
    let hYBtop :=
      HostKraCartesianCube.cartesianSquareLp_memLp_top M hM B hBtop
    let R := rightPairLp M hM B hBtop h k
    let L := leftPairLp M hM A hAtop h k
    relativeDoubleKoopmanPairLimit
        P hP YA YB hYAtop hYBtop h k =
      (@inner ℂ (Lp ℂ 2 P.μ) _
        (MultipleKhintchineProductInvariant.productInvariantProjectionCLM
          M hM
          (MultipleKhintchineProductInvariant.separatedProductLp M hM
            (ForwardKroneckerFactor.lpStar M L) L))
        (MultipleKhintchineProductInvariant.productInvariantProjectionCLM
          M hM
          (MultipleKhintchineProductInvariant.separatedProductLp M hM
            R (ForwardKroneckerFactor.lpStar M R)))).re := by
  dsimp only
  let P := MultipleKhintchineCartesian.productSystem M M
  let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
  let YA := HostKraCartesianCube.cartesianSquareLp M hM A
  let YB := HostKraCartesianCube.cartesianSquareLp M hM B
  let hYAtop :=
    HostKraCartesianCube.cartesianSquareLp_memLp_top M hM A hAtop
  let hYBtop :=
    HostKraCartesianCube.cartesianSquareLp_memLp_top M hM B hBtop
  let r : M.X → ℂ :=
    MultipleKhintchineCharacteristic.rightPairFunction M hM B h k
  let l : M.X → ℂ :=
    MultipleKhintchineCharacteristic.leftPairFunction M hM A h k
  let hr : MemLp r 2 M.μ :=
    MultipleKhintchineCharacteristic.rightPairFunction_memLp
      M hM B hBtop h k
  let hl : MemLp l 2 M.μ :=
    MultipleKhintchineCharacteristic.leftPairFunction_memLp
      M hM A hAtop h k
  let f : P.X → ℂ :=
    MultipleKhintchineCharacteristic.rightPairFunction P hP YB h k
  let g : P.X → ℂ := fun p ↦ star
    (MultipleKhintchineCharacteristic.leftPairFunction P hP YA h k p)
  let hf : MemLp f 2 P.μ :=
    MultipleKhintchineCharacteristic.rightPairFunction_memLp
      P hP YB hYBtop h k
  let hg : MemLp g 2 P.μ :=
    MultipleKhintchineCharacteristic.star_leftPairFunction_memLp
      P hP YA hYAtop h k
  have hright :
      hf.toLp f =
        MultipleKhintchineProductInvariant.separatedProductLp M hM
          (hr.toLp r)
          (ForwardKroneckerFactor.lpStar M (hr.toLp r)) := by
    have hae :
        f =ᵐ[P.μ] TensorSquare M r := by
      simpa only [P, hP, YB, f, r,
        MultipleKhintchineCartesian.cartesianSquare] using
          rightPairFunction_cartesianSquareLp_ae M hM B h k
    calc
      hf.toLp f =
          (HilbertSchmidtInvariant.tensorSquare_memLp M hM r hr).toLp
            (TensorSquare M r) :=
        MemLp.toLp_congr hf
          (HilbertSchmidtInvariant.tensorSquare_memLp M hM r hr) hae
      _ = _ := tensorSquare_toLp_eq_separatedProductLp M hM r hr
  have hleft :
      hg.toLp g =
        MultipleKhintchineProductInvariant.separatedProductLp M hM
          (ForwardKroneckerFactor.lpStar M (hl.toLp l))
          (hl.toLp l) := by
    have hraw :=
      leftPairFunction_cartesianSquareLp_ae M hM A h k
    have hae :
        g =ᵐ[P.μ] star (TensorSquare M l) := by
      filter_upwards [hraw] with p hp
      change star
          (MultipleKhintchineCharacteristic.leftPairFunction
            P hP YA h k p) =
        star (TensorSquare M l p)
      rw [hp]
      simp only [MultipleKhintchineCartesian.cartesianSquare,
        TensorSquare, l, starRingEnd_apply]
    calc
      hg.toLp g =
          ((HilbertSchmidtInvariant.tensorSquare_memLp M hM l hl).star).toLp
            (star (TensorSquare M l)) :=
        MemLp.toLp_congr hg
          (HilbertSchmidtInvariant.tensorSquare_memLp M hM l hl).star hae
      _ = _ := star_tensorSquare_toLp_eq_separatedProductLp M hM l hl
  rw [
    relativeDoubleKoopmanPairLimit_product_eq_re_inner_projections
      M hM YA YB hYAtop hYBtop h k,
    hleft, hright]
  rfl

/-- Cube transposition turns every tensor-square relative pair limit into
a nonnegative squared product-invariant energy on the base Cartesian
square. -/
theorem relativeDoubleKoopmanPairLimit_cartesianSquare_eq_projection_norm_sq
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (A B : Lp ℂ 2 M.μ)
    (hAtop : MemLp (fun x ↦ A x) ⊤ M.μ)
    (hBtop : MemLp (fun x ↦ B x) ⊤ M.μ)
    (h k : ℕ) :
    let P := MultipleKhintchineCartesian.productSystem M M
    let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
    let YA := HostKraCartesianCube.cartesianSquareLp M hM A
    let YB := HostKraCartesianCube.cartesianSquareLp M hM B
    let hYAtop :=
      HostKraCartesianCube.cartesianSquareLp_memLp_top M hM A hAtop
    let hYBtop :=
      HostKraCartesianCube.cartesianSquareLp_memLp_top M hM B hBtop
    let R := rightPairLp M hM B hBtop h k
    let L := leftPairLp M hM A hAtop h k
    let E :=
      MultipleKhintchineProductInvariant.productInvariantProjectionCLM
        M hM
        (MultipleKhintchineProductInvariant.separatedProductLp M hM R L)
    relativeDoubleKoopmanPairLimit
        P hP YA YB hYAtop hYBtop h k = ‖E‖ ^ 2 := by
  dsimp only
  let P := MultipleKhintchineCartesian.productSystem M M
  let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
  let YA := HostKraCartesianCube.cartesianSquareLp M hM A
  let YB := HostKraCartesianCube.cartesianSquareLp M hM B
  let hYAtop :=
    HostKraCartesianCube.cartesianSquareLp_memLp_top M hM A hAtop
  let hYBtop :=
    HostKraCartesianCube.cartesianSquareLp_memLp_top M hM B hBtop
  let R := rightPairLp M hM B hBtop h k
  let L := leftPairLp M hM A hAtop h k
  let E :=
    MultipleKhintchineProductInvariant.productInvariantProjectionCLM
      M hM
      (MultipleKhintchineProductInvariant.separatedProductLp M hM R L)
  have hprojection :=
    relativeDoubleKoopmanPairLimit_cartesianSquare_eq_rowProjectionPairing
      M hM A B hAtop hBtop h k
  have hrow :
      relativeDoubleKoopmanPairLimit
          P hP YA YB hYAtop hYBtop h k =
        (MultipleKhintchineProductInvariant.rowCubePairing M hM
          R (ForwardKroneckerFactor.lpStar M R)
          L (ForwardKroneckerFactor.lpStar M L)).re := by
    simpa only [P, hP, YA, YB, hYAtop, hYBtop, R, L,
      MultipleKhintchineProductInvariant.rowCubePairing,
      lpStar_lpStar] using hprojection
  have hdefect :=
    MultipleKhintchineProductInvariant.cubePairingDefect_eq_zero
      M hM hErg R (ForwardKroneckerFactor.lpStar M R)
        L (ForwardKroneckerFactor.lpStar M L)
  have htranspose :
      MultipleKhintchineProductInvariant.rowCubePairing M hM
          R (ForwardKroneckerFactor.lpStar M R)
          L (ForwardKroneckerFactor.lpStar M L) =
        MultipleKhintchineProductInvariant.columnCubePairing M hM
          R (ForwardKroneckerFactor.lpStar M R)
          L (ForwardKroneckerFactor.lpStar M L) := by
    exact sub_eq_zero.mp hdefect
  calc
    relativeDoubleKoopmanPairLimit
        P hP YA YB hYAtop hYBtop h k =
        (MultipleKhintchineProductInvariant.rowCubePairing M hM
          R (ForwardKroneckerFactor.lpStar M R)
          L (ForwardKroneckerFactor.lpStar M L)).re := hrow
    _ =
        (MultipleKhintchineProductInvariant.columnCubePairing M hM
          R (ForwardKroneckerFactor.lpStar M R)
          L (ForwardKroneckerFactor.lpStar M L)).re := by rw [htranspose]
    _ = ‖E‖ ^ 2 := by
      simp only [MultipleKhintchineProductInvariant.columnCubePairing,
        lpStar_lpStar, E]
      rw [inner_self_eq_norm_sq_to_K]
      change ((‖E‖ : ℂ) ^ 2).re = ‖E‖ ^ 2
      have hpow :
          ((‖E‖ ^ 2 : ℝ) : ℂ) = ((‖E‖ : ℂ) ^ 2) := by
        norm_cast
      rw [← hpow]
      exact Complex.ofReal_re _

/-- Relative, translated-uniform pair limits for the bilinear progression.
This is the nonergodic counterpart of
`uniform_shifted_cesaro_re_inner_doubleKoopmanProduct`. -/
theorem uniform_shifted_cesaro_re_inner_doubleKoopmanProduct_invariantMean
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (h k : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        |cesaroAverage
            (fun n ↦
              (@inner ℂ (Lp ℂ 2 M.μ) _
                (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                  M hM F G hFtop (i + (n + k)))
                (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                  M hM F G hFtop (i + (n + h)))).re) N -
          relativeDoubleKoopmanPairLimit
            M hM F G hFtop hGtop h k| < ε := by
  intro ε hε
  let f : M.X → ℂ :=
    MultipleKhintchineCharacteristic.rightPairFunction M hM G h k
  let g : M.X → ℂ := fun x ↦ star
    (MultipleKhintchineCharacteristic.leftPairFunction M hM F h k x)
  let hf : M.lpMember 2 f :=
    MultipleKhintchineCharacteristic.rightPairFunction_memLp
      M hM G hGtop h k
  let hg : M.lpMember 2 g :=
    MultipleKhintchineCharacteristic.star_leftPairFunction_memLp
      M hM F hFtop h k
  let L : ℂ :=
    @inner ℂ (Lp ℂ 2 M.μ) _
      (hg.toLp g) (HostKraRelativeMean.invariantMeanLp M hM f hf)
  have hu :=
    HostKraRelativeMean.uniform_shifted_cesaroFunctionCorrelations_invariantMean
      M hM f g hf hg ε hε
  have hu' := (tendsto_add_atTop_nat 1).eventually hu
  filter_upwards [hu'] with N hN
  intro i
  have hc := hN i
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false] at hc
  let b : ℕ → ℂ := fun n ↦
    @inner ℂ (Lp ℂ 2 M.μ) _
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F G hFtop (i + (n + k)))
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F G hFtop (i + (n + h)))
  have hb (n : ℕ) :
      b n = functionCorrelation M f g (i + n) := by
    dsimp only [b, f, g]
    rw [show i + (n + k) = (i + n) + k by omega,
      show i + (n + h) = (i + n) + h by omega,
      MultipleKhintchineCharacteristic.inner_doubleKoopmanProduct_add
        M hM F G hFtop (i + n) h k,
      MultipleKhintchineCharacteristic.inner_shiftedProducts_eq_functionCorrelation
        M hM F G hFtop (i + n) h k]
  have hcomplex :
      (((N + 1 : ℕ) : ℂ)⁻¹) *
          ∑ n ∈ Finset.range (N + 1), b n =
        (((N + 1 : ℕ) : ℂ)⁻¹) *
          ∑ n ∈ Finset.range (N + 1),
            functionCorrelation M f g (i + n) := by
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    exact hb n
  change
    |cesaroAverage (fun n ↦ (b n).re) N -
      relativeDoubleKoopmanPairLimit
        M hM F G hFtop hGtop h k| < ε
  have hlimit :
      relativeDoubleKoopmanPairLimit
        M hM F G hFtop hGtop h k = L.re := by
    simp only [relativeDoubleKoopmanPairLimit, L, f, g]
  rw [hlimit]
  calc
    |cesaroAverage (fun n ↦ (b n).re) N - L.re| =
        |(((((N + 1 : ℕ) : ℂ)⁻¹) *
          ∑ n ∈ Finset.range (N + 1), b n) - L).re| := by
            rw [MultipleKhintchineUniform.cesaroAverage_re_eq,
              Complex.sub_re]
    _ ≤ ‖((((N + 1 : ℕ) : ℂ)⁻¹) *
          ∑ n ∈ Finset.range (N + 1), b n) - L‖ :=
      Complex.abs_re_le_norm _
    _ < ε := by
      rw [hcomplex, ← dist_eq_norm]
      exact hc

/-- The preceding explicit relative limits package as uniform pair limits
for the abstract van der Corput criterion. -/
theorem doubleKoopmanProduct_hasUniformRelativePairLimits
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ) :
    VanDerCorput.HasUniformPairLimits
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F G hFtop)
      (relativeDoubleKoopmanPairLimit M hM F G hFtop hGtop) := by
  intro h k ρ hρ
  exact
    uniform_shifted_cesaro_re_inner_doubleKoopmanProduct_invariantMean
      M hM F G hFtop hGtop h k ρ hρ

end Chapter02.MultipleKhintchineRelativeUniform
