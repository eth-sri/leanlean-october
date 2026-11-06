module

public import HK.Basic

/-!
# The 9-agent SBC spectator system (Hegarty–Ognissanti–Wedin §4)

The six agents of §4 with a spectator at `210` (`r = 100`) and two beacons at `280` and `300`
(`r = 10`); for all `t`, agents 0–5 evolve as in §4, the beacons are fixed, and the spectator (index 6)
satisfies `x₆(t) = 210 + (12/11) ((−1/6)ᵗ − (1/5)ᵗ)`, so it is strictly left of `210` for every
`t ≥ 1`; the neighbourhood table is the same at every `t`. Two atoms: `u = (−1/6)ᵗ ∈ [−1/6, 1]` and
`w = (1/5)ᵗ ∈ (0, 1]`; the table holds on the closed box `|u| ≤ 1`, `0 ≤ w ≤ 1` with no parity split.
-/

@[expose] public section

namespace HK

local notation "sbc9_N" =>
  ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5},
    {4, 5, 6, 7, 8}, {7}, {8}]

local notation "sbc9_f" t =>
  ![0, 20 + 2 * sbcRate ^ t, 40 - 3 * sbcRate ^ t, 100 + 3 * sbcRate ^ t,
    120 - 2 * sbcRate ^ t, 140, 210 + 12 / 11 * (sbcRate ^ t - (1 / 5) ^ t),
    280, 300]

/-- The SBC-9 table at time `t`. -/
theorem spe_sbc9_table t : nbc sbc9_r (sbc9_f t) = sbc9_N := by
  have := unit_pow (1 / 5) t
  hk_table

theorem sbc9_closed_form t : tr9 t = sbc9_f t := by
  hk_traj funext i; fin_cases i <;> norm_num =>
    rw [spe_sbc9_table]; hk_avg

theorem sbc9_neighbors t : nbc sbc9_r (tr9 t) = sbc9_N := by
  rw [sbc9_closed_form, spe_sbc9_table]

theorem sbc9_spectator_lt t (ht : 1 ≤ t) : tr9 t 6 < 210 := by
  rw [sbc9_closed_form]; dsimp; linarith [pow_lt sbcRate (1 / 5) ht]

end HK
