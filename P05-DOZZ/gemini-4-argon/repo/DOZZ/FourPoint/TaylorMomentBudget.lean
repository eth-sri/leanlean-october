/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TwoRootedExponents

/-! Strict positive-moment and spatial margins in the intermediate Taylor region. -/

@[expose] public section
open Set
namespace DOZZ.Proofs

/-- The optimized intermediate-region order lies strictly below both GMC thresholds.
The reduced order is below 2, so the interpolation of the square in the proof of
[KRV, (fundest)] is legitimate. -/
theorem twoRooted_optimized_order γ α q
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγsq : 2 < γ ^ 2)
    (hα : γ / 2 < α) (hα2 : α < 2 / γ) (hq : 1 < q) :
    let r := (γ / 2 + Q γ - α) / (γ * q)
    0 < r ∧ r < 2 ∧
      q * r < min (4 / γ ^ 2) (2 / γ * (Q γ - α)) ∧
        γ * (Q γ - α + γ / 2) * r - γ ^ 2 * q * r ^ 2 / 2 =
          (γ / 2 + Q γ - α) ^ 2 / (2 * q) := by
  have hQmult : γ * Q γ = 2 + γ ^ 2 / 2 := by unfold Q; field_simp
  have hαmult : γ * α > γ ^ 2 / 2 := by
    nlinarith only [(mul_lt_mul_of_pos_left hα hγ)]
  have hrpos : 0 < (γ / 2 + Q γ - α) / (γ * q) := div_pos (by unfold Q; linarith only [hα2, hγ]) (mul_pos hγ (zero_lt_one.trans hq))
  have horder : q * ((γ / 2 + Q γ - α) / (γ * q)) = (γ / 2 + Q γ - α) / γ := by
    field_simp
  refine ⟨hrpos, ?_, ?_, ?_⟩
  · have hh : (γ / 2 + Q γ - α) / (γ * q) < q * ((γ / 2 + Q γ - α) / (γ * q)) := by
      exact lt_mul_of_one_lt_left hrpos hq
    rw [horder] at hh
    exact hh.trans (by apply (div_lt_iff₀ hγ).mpr; simpa only [mul_comm] using (by apply (mul_lt_mul_iff_right₀ hγ).mp; nlinarith only [hQmult, hαmult, hγsq]))
  · rw [horder]
    exact lt_min (by apply (div_lt_div_iff₀ hγ (sq_pos_of_pos hγ)).mpr; nlinarith only [hQmult, hαmult, hγ, hγ2]) (by rw [div_mul_eq_mul_div]; apply (div_lt_div_iff_of_pos_right hγ).mpr; unfold Q; linarith only [hα2])
  · field_simp
    ring

/-- Choose Holder, radial cutoff and near-root margins together, before any spatial scale. -/
theorem taylor_region_margins κ W d n
    (hκ : 0 < κ) (hκ2 : κ < 2) (hW : 2 * κ < W) (hd : 0 < d) (hn : 0 < n) :
    ∃ q δ ε η : ℝ, 1 < q ∧ 0 < δ ∧ δ < 1 ∧ 0 < ε ∧ 0 < η ∧ η < 2 - κ ∧
      η ≤ δ * d ∧ η ≤ n ∧
        κ - 2 + η ≤ -2 - 2 * ε + (1 - δ) * W / (2 * q) := by
  let q := (W + 2 * κ) / (4 * κ)
  have hq : 1 < q := by
    dsimp only [q]
    apply (lt_div_iff₀ (by positivity : 0 < 4 * κ)).mpr
    linarith only [hW]
  have hqpos := zero_lt_one.trans hq
  let E := W / (2 * q)
  have hE : κ < E := by
    apply (lt_div_iff₀ (mul_pos (by norm_num) hqpos)).mpr
    rw [(show κ * (2 * q) = (W + 2 * κ) / 2 by dsimp only [q]; field_simp; ring)]
    linarith only [hW]
  have hEpos := hκ.trans hE
  let g := E - κ
  have hg := sub_pos.mpr hE
  let δ : ℝ := min (1 / 2) (g / (4 * E))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hg (by positivity))
  have hδE := (mul_le_mul_of_nonneg_right (min_le_right (1 / 2 : ℝ) (g / (4 * E))) hEpos.le).trans_eq (show g / (4 * E) * E = g / 4 by field_simp)
  let ε : ℝ := g / 8
  let η : ℝ := min (g / 4) (min (δ * d / 2) (min (n / 2) ((2 - κ) / 2)))
  have hηg : η ≤ g / 4 := min_le_left _ _
  refine ⟨q, δ, ε, η, hq, hδ, ((min_le_left _ _).trans_lt (by norm_num)), (div_pos hg (by norm_num)), (lt_min (div_pos hg (by norm_num)) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))), ?_, ?_, ?_, ?_⟩
  · linarith only [(((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _) : η ≤ (2 - κ) / 2), hκ2]
  · have hh : 0 < δ * d := mul_pos hδ hd
    linarith only [((min_le_right _ _).trans (min_le_left _ _) : η ≤ δ * d / 2), hh]
  · linarith only [(((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _) : η ≤ n / 2), hn]
  · have heq : (1 - δ) * W / (2 * q) = E - δ * E := by dsimp only [E]; ring
    rw [heq]
    dsimp only [ε, g] at hηg hδE ⊢
    linarith only [hηg, hδE, hE]

end DOZZ.Proofs
