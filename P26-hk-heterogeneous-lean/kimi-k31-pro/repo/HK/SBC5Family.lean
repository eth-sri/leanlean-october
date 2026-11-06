module

public import HK.SBC5

/-!
# Perpetual SBC oscillation with arbitrarily small radius spread

For `0 < δ ≤ 1`, the five-agent system has initial state `sbc5_lim + δ • sbc5_v`
and radii `(6-3δ, 6+3δ, 6+3δ, 6+3δ, 6-3δ)`. Its constant neighborhood table is
the same as that of `sbc5_x0`, and its offset at time `t` is `sbc5Rate^t * δ • sbc5_v`.
Thus the radius ratio can be arbitrarily close to one while the three interior agents
continue crossing their limits forever.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- The fixed table holds throughout the whole interval `-δ ≤ u ≤ δ`. -/
theorem sbc5Family_table (δ u : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hu0 : -δ ≤ u) (hu1 : u ≤ δ) :
    neighbors .sbc (sbc5Family_r δ) (fun i => sbc5_lim i + u * sbc5_v i) =
      ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}] := by
  obtain ⟨hs1, hs2⟩ := sbc_sqrt_two_bounds
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hmul0 := mul_le_mul_of_nonneg_right hu0 hs0
  have hmul1 := mul_le_mul_of_nonneg_right hu1 hs0
  have hδs := mul_le_mul_of_nonneg_left hs2.le hδ0.le
  have hp0 : -(3 / 2) * δ ≤ u * Real.sqrt 2 := by nlinarith
  have hp1 : u * Real.sqrt 2 ≤ (3 / 2) * δ := by nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbc5Family_r, sbc5_lim, sbc5_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem sbc5Family_step (δ u : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hu0 : -δ ≤ u) (hu1 : u ≤ δ) :
    step .sbc (sbc5Family_r δ) (fun i => sbc5_lim i + u * sbc5_v i) =
      fun i => sbc5_lim i + (sbc5Rate * u) * sbc5_v i := by
  have h2 := sbc_sqrt_two_sq
  have h2u := congrArg (fun x : ℝ => u * x) h2
  funext i
  rw [step_apply, sbc5Family_table δ u hδ0 hδ1 hu0 hu1]
  fin_cases i <;> simp [Finset.sum_insert, sbc5_lim, sbc5_v, sbc5Rate] <;> nlinarith [h2u]

theorem sbc5Family_pow_bounds (δ : ℝ) (hδ0 : 0 < δ) (t : ℕ) :
    -δ ≤ sbc5Rate ^ t * δ ∧ sbc5Rate ^ t * δ ≤ δ := by
  obtain ⟨h0, h1⟩ := sbc_pow_bounds t
  have hr := sbc_rate_gt
  constructor <;> nlinarith

theorem sbc5Family_closed_form (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (t : ℕ) :
    traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) t =
      fun i => sbc5_lim i + (sbc5Rate ^ t * δ) * sbc5_v i := by
  induction t with
  | zero =>
    funext i
    simp [traj, sbc5Family_x0]
  | succ t ih =>
    obtain ⟨h0, h1⟩ := sbc5Family_pow_bounds δ hδ0 t
    rw [traj_succ, ih, sbc5Family_step δ _ hδ0 hδ1 h0 h1]
    funext i
    rw [pow_succ]
    ring

theorem sbc5Family_neighbors (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (t : ℕ) :
    neighbors .sbc (sbc5Family_r δ)
      (traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) t) =
      ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}] := by
  obtain ⟨h0, h1⟩ := sbc5Family_pow_bounds δ hδ0 t
  rw [sbc5Family_closed_form δ hδ0 hδ1,
    sbc5Family_table δ _ hδ0 hδ1 h0 h1]

theorem sbc5Family_rate_tendsto (δ : ℝ) :
    Tendsto (fun t : ℕ => sbc5Rate ^ t * δ) atTop (𝓝 0) := by
  simpa using
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one abs_sbc5Rate_lt_one).mul_const δ

/-- No positive bound on relative radius spread restores eventual pseudo-stability, even
for a constant-digraph SBC system on five agents. The pairwise inequalities express that
the largest radius divided by the smallest is strictly below `1+ε`. -/
theorem sbc5_near_homogeneous (ε : ℝ) (hε : 0 < ε) :
    ∃ r x₀ : Fin 5 → ℝ,
      (∀ i, 0 < r i) ∧
      (∀ i j, r i < (1 + ε) * r j) ∧
      r 0 < r 1 ∧
      (∀ t, proximityDigraph .sbc r (traj .sbc r x₀ t) =
        proximityDigraph .sbc r x₀) ∧
      Tendsto (traj .sbc r x₀) atTop (𝓝 sbc5_lim) ∧
      (∀ τ, ¬ FixedFrom (traj .sbc r x₀) τ) ∧
      (∀ xinf τ, ¬ PseudoStableAfter (traj .sbc r x₀) xinf τ) := by
  let δ : ℝ := min (1 / 2) (ε / 4)
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  have hδ1 : δ ≤ 1 := by linarith
  have hεδ := mul_le_mul_of_nonneg_left hδhalf hε.le
  have hspread : 6 + 3 * δ < (1 + ε) * (6 - 3 * δ) := by nlinarith
  refine ⟨sbc5Family_r δ, sbc5Family_x0 δ, (by
    intro i
    fin_cases i <;> simp [sbc5Family_r] <;> linarith), ?_, (by
    simp only [sbc5Family_r, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith),
    digraph_constant_of_neighbors _ _ _ _ (sbc5Family_neighbors δ hδ0 hδ1),
    tendsto_of_closed_form _ _ sbc5_v _ (sbc5Family_rate_tendsto δ)
      (sbc5Family_closed_form δ hδ0 hδ1),
    not_fixedFrom_of_closed_form _ _ sbc5_v _ (sbc5Family_closed_form δ hδ0 hδ1)
      (alternating _ _ sbc5Rate_neg hδ0.ne') 1 (by simp [sbc5_v]),
    not_pseudoStable_of_closed_form _ _ sbc5_v _ (sbc5Family_rate_tendsto δ)
      (sbc5Family_closed_form δ hδ0 hδ1) (alternating _ _ sbc5Rate_neg hδ0.ne')⟩
  intro i j
  have hi : sbc5Family_r δ i ≤ 6 + 3 * δ := by
    fin_cases i <;> simp [sbc5Family_r] <;> linarith
  have hj : 6 - 3 * δ ≤ sbc5Family_r δ j := by
    fin_cases j <;> simp [sbc5Family_r] <;> linarith
  have hm := mul_le_mul_of_nonneg_left hj (show 0 ≤ 1 + ε by linarith)
  exact lt_of_le_of_lt hi (lt_of_lt_of_le hspread hm)

end HK
