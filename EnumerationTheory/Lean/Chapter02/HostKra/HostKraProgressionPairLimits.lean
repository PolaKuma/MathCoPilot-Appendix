import Chapter02.HostKra.HostKraCubeSeminormRecursion
import Chapter02.Ergodic.VanDerCorputPairLimits

open Classical Filter MeasureTheory
open scoped BigOperators

noncomputable section

namespace Chapter02.HostKraProgressionPairLimits

universe u

/-- The fixed real pair-limit array of the bilinear progression
`(T^n F) (T^(2n) G)`. -/
def doubleKoopmanPairLimit
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ) (h k : ℕ) : ℝ :=
  (productOfMeans M
    (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)
    (fun x ↦ star
      (MultipleKhintchineCharacteristic.leftPairFunction
        M hM F h k x))).re

/-- The bilinear progression has the explicit fixed pair limits above,
uniformly over every translated averaging interval. -/
theorem doubleKoopmanProduct_hasUniformPairLimits
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (hErg : IsErgodic M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ) :
    VanDerCorput.HasUniformPairLimits
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F G hFtop)
      (doubleKoopmanPairLimit M hM F G) := by
  intro h k ρ hρ
  simpa only [doubleKoopmanPairLimit] using
    (MultipleKhintchineUniform.uniform_shifted_cesaro_re_inner_doubleKoopmanProduct
      M hM hErg F G hFtop hGtop h k ρ hρ)

/-- Once the concrete Host--Kra/Gowers finite-block estimate is available,
the existing uniform van der Corput criterion applies to the actual
bilinear progression. -/
theorem doubleKoopmanProduct_hasUniformBlockDecay_of_smallPairLimitBlocks
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (hErg : IsErgodic M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (hsmall : VanDerCorput.HasSmallPairLimitBlocks
      (doubleKoopmanPairLimit M hM F G)) :
    VanDerCorput.HasUniformVanDerCorputBlockDecay
      (MultipleKhintchineCharacteristic.doubleKoopmanProduct
        M hM F G hFtop) := by
  exact VanDerCorput.hasUniformVanDerCorputBlockDecay_of_pairLimits
    (MultipleKhintchineCharacteristic.doubleKoopmanProduct
      M hM F G hFtop)
    (doubleKoopmanPairLimit M hM F G)
    (doubleKoopmanProduct_hasUniformPairLimits
      M hM hErg F G hFtop hGtop)
    hsmall

/-- Concrete generalized-von-Neumann reduction for the bilinear
progression: the only remaining input is smallness of its explicit
pair-limit blocks. -/
theorem doubleKoopmanProduct_uniform_cesaro_zero_of_smallPairLimitBlocks
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (hErg : IsErgodic M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (hsmall : VanDerCorput.HasSmallPairLimitBlocks
      (doubleKoopmanPairLimit M hM F G)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1),
            MultipleKhintchineCharacteristic.doubleKoopmanProduct
              M hM F G hFtop (i + n)‖ < ε := by
  exact VanDerCorput.vectorCesaro_uniform_tendsto_zero_of_blockDecay
    (MultipleKhintchineCharacteristic.doubleKoopmanProduct
      M hM F G hFtop)
    (C * ‖G‖)
    (MultipleKhintchineCharacteristic.norm_doubleKoopmanProduct_le
      M hM F G hFtop C hC hFbound)
    (doubleKoopmanProduct_hasUniformBlockDecay_of_smallPairLimitBlocks
      M hM hErg F G hFtop hGtop hsmall)

end Chapter02.HostKraProgressionPairLimits
