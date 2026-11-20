module

public import HK.Basic

/-!
# Perpetual SBC oscillation with arbitrarily small radius spread

For `0 < δ ≤ 1`, the five-agent system has initial state `sbc5_lim + δ • sbc5_v`
and radii `(6-3δ, 6+3δ, 6+3δ, 6+3δ, 6-3δ)`. Its constant neighborhood table is
the same as that of `sbc5_x0`, and its offset at time `t` is `sbc5Rate^t * δ • sbc5_v`.
Thus the radius ratio can be arbitrarily close to one while the three interior agents
continue crossing their limits forever.
-/

public section

namespace HK

scoped notation "fiveRows" => rows![{0}, 0⋯2, 1⋯3, 2⋯4, {4}]

section
variable (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
include hδ0 hδ1

theorem familyMode : Mode .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) sbc5_lim (δ • sbc5_v)
    sbc5Rate (fun _ => fiveRows) := by
  radical 2
  constructor
  case' rows =>
    rintro t u ⟨h,-⟩
    rw [smul_smul]
    have := (monotone_mul_right_of_nonneg hδ0.le).mapsTo_Icc h
  all_goals finite_check

corollary sbc5Family_closed_form := (familyMode δ hδ0 hδ1).form fun t i => (sbc5Rate ^ t * δ) * sbc5_v i

corollary sbc5Family_neighbors := (familyMode δ hδ0 hδ1).orbit.table

end

/-- No positive bound on relative radius spread restores eventual pseudo-stability, even
for a constant-digraph SBC system on five agents. The pairwise inequalities express that
the largest radius divided by the smallest is strictly below `1+ε`. -/
theorem sbc5_near_homogeneous (ε : ℝ) (hε : 0 < ε) :
    ∃ r x₀ : State 5,
      PositiveRadii r ∧
      (∀ i j, r i < (1 + ε) * r j) ∧
      r 0 < r 1 ∧
      (∀ t, proximityDigraph .sbc r (traj .sbc r x₀ t) =
        proximityDigraph .sbc r x₀) ∧
      Converges (traj .sbc r x₀) sbc5_lim ∧
      Unstable (traj .sbc r x₀) := by
  have h := familyMode (min 1 (ε / 4)) (by positivity) (min_le_left ..)
  refine ⟨_, _, h.positive, ?_, ?_, h.orbit.constant, h.conv, h.unstable⟩ <;>
    simp only [min_def] <;> finite_check

end HK
