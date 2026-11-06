module

public import HK.Basic

/-!
# The 9-agent SBC spectator system (Hegarty–Ognissanti–Wedin §4)

The six agents of §4 with a spectator at `210` (`r = 100`) and two beacons at `280` and `300`
(`r = 10`); for all `t`, agents 0–5 evolve as in §4, the beacons are fixed, and the spectator (index 6)
satisfies `x₆(t) = 210 + (12/11) ((−1/6)ᵗ − (1/5)ᵗ)`, so it is strictly left of `210` for every
`t ≥ 1`; the neighbourhood table is the same at every `t`.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- The SBC-9 opinion vector at the atoms `u` (the `(−1/6)ᵗ` offset) and `w` (the `(1/5)ᵗ` offset). -/
noncomputable def spe_sbc9_vec (u w : ℝ) : Fin 9 → ℝ :=
  ![0, 20 + 2 * u, 40 - 3 * u, 100 + 3 * u, 120 - 2 * u, 140, 210 + 12 / 11 * (u - w), 280, 300]

/-- The table on the box `-1/6 ≤ u ≤ 1`, `0 ≤ w ≤ 1`. -/
theorem spe_sbc9_table (u w : ℝ) (h0 : -1 / 6 ≤ u) (h1 : u ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    neighbors .sbc sbc9_r (spe_sbc9_vec u w) =
      ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}, {4, 5, 6, 7, 8}, {7}, {8}] := by
  tabn sbc9_r, spe_sbc9_vec

theorem spe_sbc9_step (u w : ℝ) (h0 : -1 / 6 ≤ u) (h1 : u ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    step .sbc sbc9_r (spe_sbc9_vec u w) = spe_sbc9_vec (-1 / 6 * u) (1 / 5 * w) := by
  funext i
  rw [step_apply, spe_sbc9_table u w h0 h1 hw0 hw1]
  fin_cases i <;> simp [Finset.sum_insert, spe_sbc9_vec] <;> ring

theorem sbc9_traj (t : ℕ) :
    traj .sbc sbc9_r sbc9_x0 t = spe_sbc9_vec ((-1 / 6 : ℝ) ^ t) ((1 / 5 : ℝ) ^ t) :=
  traj_geom2 .sbc sbc9_r sbc9_x0 spe_sbc9_vec (-1 / 6) (1 / 5) (-1 / 6) 1
    (fun u w h0 h1 hw0 hw1 => spe_sbc9_step u w h0 h1 hw0 hw1)
    (by funext i; fin_cases i <;> simp [sbc9_x0, spe_sbc9_vec] <;> norm_num)
    (fun t => pow_bounds_of_neg (by norm_num) (by norm_num) t)
    (fun t => pos_pow_bounds (by norm_num) (by norm_num) t) t

chall sbc9_closed_form "  rw [sbc9_traj]
  rfl"

chall sbc9_neighbors "  obtain ⟨h0, h1⟩ := pow_bounds_of_neg (by norm_num : -1 < (-1 / 6 : ℝ)) (by norm_num) t
  rw [sbc9_traj, spe_sbc9_table _ _ h0 h1 (pow_nonneg (by norm_num) t)
    (pow_le_one₀ (by norm_num) (by norm_num) (n := t))]"

chall sbc9_spectator_lt "  have ht0 : t ≠ 0 := by omega
  have habs : |(-1 / 6 : ℝ) ^ t| < (1 / 5 : ℝ) ^ t := by
    rw [abs_pow, abs_of_neg (by norm_num : (-1 / 6 : ℝ) < 0)]
    exact pow_lt_pow_left₀ (by norm_num) (by norm_num) ht0
  have hle := le_abs_self ((-1 / 6 : ℝ) ^ t)
  have h6 : spe_sbc9_vec ((-1 / 6 : ℝ) ^ t) ((1 / 5 : ℝ) ^ t) 6 =
      210 + 12 / 11 * ((-1 / 6 : ℝ) ^ t - (1 / 5 : ℝ) ^ t) := rfl
  rw [sbc9_traj, h6]
  linarith"

end HK
