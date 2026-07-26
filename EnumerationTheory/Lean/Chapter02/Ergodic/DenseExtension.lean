import Chapter02.Common

open Filter

namespace Chapter02.DenseExtension

/-- A uniformly Lipschitz family that converges on a dense set converges
everywhere. -/
lemma tendsto_of_dense_of_uniform_dist {X Y ι : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {l : Filter ι} {S : Set X} (hS : Dense S)
    (F : ι → X → Y) (G : X → Y) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ i x y, dist (F i x) (F i y) ≤ C * dist x y)
    (hG : ∀ x y, dist (G x) (G y) ≤ C * dist x y)
    (hlim : ∀ x ∈ S, Tendsto (fun i => F i x) l (nhds (G x))) :
    ∀ x, Tendsto (fun i => F i x) l (nhds (G x)) := by
  intro x
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / (8 * (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hC1)
  obtain ⟨y, hyS, hxy⟩ := hS.exists_dist_lt x hδ
  have hev := (Metric.tendsto_nhds.mp (hlim y hyS)) (ε / 2) (by positivity)
  filter_upwards [hev] with i hi
  calc
    dist (F i x) (G x) ≤
        dist (F i x) (F i y) + dist (F i y) (G y) + dist (G y) (G x) := by
      exact (dist_triangle _ _ _).trans
        (add_le_add_left (dist_triangle _ _ _) _)
    _ < C * δ + ε / 2 + C * δ := by
      have hyx : dist y x < δ := by simpa [dist_comm] using hxy
      have h1 : dist (F i x) (F i y) ≤ C * δ :=
        (hF i x y).trans (mul_le_mul_of_nonneg_left hxy.le hC)
      have h3 : dist (G y) (G x) ≤ C * δ :=
        (hG y x).trans (mul_le_mul_of_nonneg_left hyx.le hC)
      nlinarith
    _ < ε := by
      dsimp [δ]
      have hden : 0 < 8 * (C + 1) := mul_pos (by norm_num) hC1
      field_simp
      nlinarith

end Chapter02.DenseExtension
