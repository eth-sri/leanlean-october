module

public import HK.Basic

/-!
# The 9-agent SBC spectator system (Hegarty–Ognissanti–Wedin §4)

The six agents of §4 with a spectator at `210` (`r = 100`) and two beacons at `280` and `300`
(`r = 10`); for all `t`, agents 0–5 evolve as in §4, the beacons are fixed, and the spectator (index 6)
satisfies `x₆(t) = 210 + (12/11) ((−1/6)ᵗ − (1/5)ᵗ)`, so it is strictly left of `210` for every
`t ≥ 1`; the neighbourhood table is the same at every `t`. Two atoms: `u = (−1/6)ᵗ ∈ [−1/6, 1]` and
`w = (1/5)ᵗ ∈ (0, 1]`; the table is verified from these bounds without a parity split.
-/

@[expose] public section

namespace HK

local notation "X" => traj Model.sbc sbc9_r sbc9_x0
local notation "q" => (-1 / 6 : ℝ)
local notation "p" => (1 / 5 : ℝ)
local notation "V[" u "," w "]" =>
  ![0, 20 + 2 * u, 40 - 3 * u, 100 + 3 * u, 120 - 2 * u, 140, 210 + 12 / 11 * (u - w), 280, 300]
local notation "N" => ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}, {4, 5, 6, 7, 8}, {7}, {8}]

private theorem table (t : ℕ) : neighbors .sbc sbc9_r V[q ^ t, p ^ t] = N := by
  obtain ⟨_, _⟩ := sixth_pow_bounds t
  have h₀ : 0 ≤ p ^ t := by positivity
  have h₁ : p ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  generalize p ^ t = w at *
  check_neighbors [sbc9_r]

theorem sbc9_closed_form (t : ℕ) : X t = V[q ^ t, p ^ t] :=
  traj_of_average table (fun _ => by simp only [pow_succ']; check_rows []) (by check_rows [sbc9_x0]) t

theorem sbc9_neighbors (t : ℕ) : neighbors .sbc sbc9_r (X t) = N := by
  rw [sbc9_closed_form, table]

theorem sbc9_spectator_lt (t : ℕ) (ht : 1 ≤ t) : X t 6 < 210 := by
  rw [sbc9_closed_form]
  exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg (by norm_num)
    (sub_neg.mpr (pow_lt_of_abs_lt (by norm_num : |q| < p) ht)))

end HK
