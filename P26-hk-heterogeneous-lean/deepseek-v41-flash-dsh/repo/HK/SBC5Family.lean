module

public import HK.SBC5

/-!
# Perpetual SBC oscillation with arbitrarily small radius spread

For `0 < δ ≤ 1`, the five-agent system with initial state `sbc5_lim + δ sbc5_v` and radii
`(6-3δ, 6+3δ, 6+3δ, 6+3δ, 6-3δ)` has the constant table of `sbc5_T` and offset `sbc5Rate^t δ sbc5_v`.
Thus the radius ratio can be arbitrarily close to one while the three interior agents continue
crossing their limits forever.
-/

@[expose] public section

namespace HK

open Filter Topology

-- No positive bound on relative radius spread restores eventual pseudo-stability, even for a
-- constant-digraph SBC system on five agents: the largest radius over the smallest is below `1+ε`.
chall sbc5_near_homogeneous "let δ : ℝ := min (1 / 2) (ε / 4)
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  have hδ1 : δ ≤ 1 := by linarith
  have hεδ := mul_le_mul_of_nonneg_left hδhalf hε.le
  have hspread : 6 + 3 * δ < (1 + ε) * (6 - 3 * δ) := by nlinarith
  have hdc : ∀ t, proximityDigraph .sbc (sbc5Family_r δ) (traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) t) = proximityDigraph .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) :=
    digraph_constant_of_table _ _ _ _ (sbc5Family_neighbors_internal δ hδ0 hδ1)
  have hte : Tendsto (traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ)) atTop (𝓝 sbc5_lim) :=
    tendsto_of_geom _ _ _ _ (tendsto_pow_mul_of_neg sbc5Rate_mem.1 sbc5Rate_mem.2 δ) (sbc5Family_closed_form_internal δ hδ0 hδ1)
  have hnf : ∀ τ, ¬ FixedFrom (traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ)) τ := fun τ =>
    not_fixedFrom_of_geom _ sbc5_lim sbc5_v (fun t => sbc5Rate ^ t * δ) (sbc5Family_closed_form_internal δ hδ0 hδ1) (alternating sbc5Rate δ sbc5Rate_mem.2 hδ0.ne') 1 (by simp [sbc5_v]) τ
  have hnp : ∀ xinf τ, ¬ PseudoStableAfter (traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ)) xinf τ := fun xinf τ =>
    not_pseudoStable_of_geom _ sbc5_lim sbc5_v (fun t => sbc5Rate ^ t * δ) (tendsto_pow_mul_of_neg sbc5Rate_mem.1 sbc5Rate_mem.2 δ) (sbc5Family_closed_form_internal δ hδ0 hδ1) (alternating sbc5Rate δ sbc5Rate_mem.2 hδ0.ne') xinf τ
  refine ⟨sbc5Family_r δ, sbc5Family_x0 δ, sbc5Family_r_pos δ hδ0 hδ1, ?_, sbc5Family_r_strict δ hδ0, hdc, hte, hnf, hnp⟩
  intro i j
  have hi : sbc5Family_r δ i ≤ 6 + 3 * δ := by fin_cases i <;> simp [sbc5Family_r] <;> linarith
  have hj : 6 - 3 * δ ≤ sbc5Family_r δ j := by fin_cases j <;> simp [sbc5Family_r] <;> linarith
  exact lt_of_le_of_lt hi (lt_of_lt_of_le hspread (mul_le_mul_of_nonneg_left hj (show 0 ≤ 1 + ε by linarith)))"

end HK
