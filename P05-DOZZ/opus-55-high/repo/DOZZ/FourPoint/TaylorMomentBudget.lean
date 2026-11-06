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
theorem twoRooted_optimized_order (γ α q : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγsq : 2 < γ ^ 2)
    (hα : γ / 2 < α) (hα2 : α < 2 / γ) (hq : 1 < q) :
    let r := (γ / 2 + Q γ - α) / (γ * q)
    0 < r ∧ r < 2 ∧
      q * r < min (4 / γ ^ 2) (2 / γ * (Q γ - α)) ∧
        γ * (Q γ - α + γ / 2) * r - γ ^ 2 * q * r ^ 2 / 2 =
          (γ / 2 + Q γ - α) ^ 2 / (2 * q) := by
  have hQmult : γ * Q γ = 2 + γ ^ 2 / 2 := by unfold Q; field_simp
  have hαmult : γ * α > γ ^ 2 / 2 := by
    nlinarith
  have hαupper : γ * α < 2 := by simpa only [mul_comm] using (lt_div_iff₀ hγ).mp hα2
  have ha : 0 < γ / 2 + Q γ - α := by nlinarith
  have hrpos := div_pos ha (mul_pos hγ (zero_lt_one.trans hq))
  have horder : q * ((γ / 2 + Q γ - α) / (γ * q)) = (γ / 2 + Q γ - α) / γ := by
    field_simp
  have hbulk : (γ / 2 + Q γ - α) / γ < 4 / γ ^ 2 := by
    apply (div_lt_div_iff₀ hγ (sq_pos_of_pos hγ)).mpr
    nlinarith only [hQmult, hαmult, hγ, hγ2]
  have hinsertion : (γ / 2 + Q γ - α) / γ < 2 / γ * (Q γ - α) := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_div_iff_of_pos_right hγ).mpr
    unfold Q
    linarith only [hα2]
  have hsmall : (γ / 2 + Q γ - α) / γ < 2 := by
    apply (div_lt_iff₀ hγ).mpr
    have hh : γ / 2 + Q γ - α < 2 * γ := by
      apply (mul_lt_mul_iff_right₀ hγ).mp
      nlinarith only [hQmult, hαmult, hγsq]
    simpa using hh
  refine ⟨hrpos, ?_, ?_, ?_⟩
  · have hh : (γ / 2 + Q γ - α) / (γ * q) < q * ((γ / 2 + Q γ - α) / (γ * q)) := lt_mul_of_one_lt_left hrpos hq
    linarith
  · simp_all
  · field_simp
    ring

/-- Choose Holder, radial cutoff and near-root margins together, before any spatial scale. -/
theorem taylor_region_margins (κ W d n : ℝ)
    (hκ : 0 < κ) (hκ2 : κ < 2) (hW : 2 * κ < W) (hd : 0 < d) (hn : 0 < n) :
    ∃ q δ ε η : ℝ, 1 < q ∧ 0 < δ ∧ δ < 1 ∧ 0 < ε ∧ 0 < η ∧ η < 2 - κ ∧
      η ≤ δ * d ∧ η ≤ n ∧
        κ - 2 + η ≤ -2 - 2 * ε + (1 - δ) * W / (2 * q) := by
  let q := (W + 2 * κ) / (4 * κ)
  have hq : 1 < q := by
    bound
  have hqpos : 0 < q := zero_lt_one.trans hq
  let E := W / (2 * q)
  have hE : κ < E := by
    apply (lt_div_iff₀ (mul_pos (by norm_num) hqpos)).mpr
    have heq : κ * (2 * q) = (W + 2 * κ) / 2 := by grind
    rw [heq]
    linarith only [hW]
  have hEpos : 0 < E := hκ.trans hE
  let g := E - κ
  have hg : 0 < g := sub_pos.mpr hE
  let δ := min (1 / 2) (g / (4 * E))
  have hδ : 0 < δ := by positivity
  have hδ1 : δ < 1 := by bound
  have hδE : δ * E ≤ g / 4 := by
    have heq : g / (4 * E) * E = g / 4 := by field_simp
    exact (mul_le_mul_of_nonneg_right (min_le_right (1 / 2 : ℝ) _) hEpos.le).trans_eq heq
  let ε := g / 8
  have hε : 0 < ε := by positivity
  let η := min (g / 4) (min (δ * d / 2) (min (n / 2) ((2 - κ) / 2)))
  have hη : 0 < η := by positivity
  have hηg : η ≤ g / 4 := min_le_left ..
  have hηd : η ≤ δ * d / 2 := by grind
  have hηn : η ≤ n / 2 := by grind
  have hηκ : η ≤ (2 - κ) / 2 :=
    by grind
  refine ⟨q, δ, ε, η, hq, hδ, hδ1, hε, hη, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · grind

end DOZZ.Proofs
