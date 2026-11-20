module

public import HK.Basic

/-!
# The 8-agent SBI spectator system (Hegarty–Ognissanti–Wedin §5)

The seven agents of §5 with a spectator at `60` (`r = 1`), which becomes index 1 when the opinions
are listed increasingly; for all `t` the other agents evolve as in §5 and
`x₁(t) = 60 + φ⁻¹ ((1/4)ᵗ − λᵗ)`, so it is strictly right of `60` for every `t ≥ 1`; the
neighbourhood table is the same at every `t`. The table is verified from `−1/4 ≤ λᵗ ≤ 1`,
`0 ≤ (1/4)ᵗ ≤ 1`, and `0 < φ < 2`, without a parity split.
-/

@[expose] public section

namespace HK

local notation "X" => traj Model.sbi sbi8_r sbi8_x0
local notation "p" => (1 / 4 : ℝ)
local notation "φ" => Real.goldenRatio
local notation "V[" u "," w "]" =>
  ![0, 60 + φ⁻¹ * (w - u), 70 + u, 100 - φ * u, 110, 120 + φ * u, 150 - u, 220]
local notation "N" => ![{0}, {0, 1, 2, 4}, {0, 2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5}, {3, 4, 5, 6}, {4, 5, 6, 7}, {7}]

private theorem phi_inv : φ⁻¹ = φ - 1 :=
  inv_eq_of_mul_eq_one_right (by linear_combination Real.goldenRatio_sq)

private theorem table (t : ℕ) : neighbors .sbi sbi8_r V[sbiRate ^ t, p ^ t] = N := by
  obtain ⟨_, _⟩ := sbiRate_pow_bounds t
  have := Real.goldenRatio_pos
  have := Real.goldenRatio_lt_two
  have hp : p ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hw : 0 ≤ p ^ t := by positivity
  simp only [phi_inv]
  generalize p ^ t = w at *
  check_neighbors [sbi8_r]

theorem sbi8_closed_form (t : ℕ) : X t = V[sbiRate ^ t, p ^ t] :=
  traj_of_average table (fun _ => by simp only [pow_succ', phi_inv]; check_rows [sbiRate_eq])
    (by check_rows [sbi8_x0]) t

theorem sbi8_neighbors (t : ℕ) : neighbors .sbi sbi8_r (X t) = N := by
  rw [sbi8_closed_form, table]

theorem sbi8_spectator_gt (t : ℕ) (ht : 1 ≤ t) : 60 < X t 1 := by
  rw [sbi8_closed_form]
  exact lt_add_of_pos_right _ (mul_pos (by positivity) (sub_pos.mpr (pow_lt_of_abs_lt sbiRate_abs_lt_quarter ht)))

end HK
