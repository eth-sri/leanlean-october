module

public import HK.Basic

/-!
# The 9-agent SBC spectator system (Hegarty–Ognissanti–Wedin §4)

The six agents of §4 with a spectator at `210` (`r = 100`) and two beacons at `280` and `300`
(`r = 10`); for all `t`, agents 0–5 evolve as in §4, the beacons are fixed, and the spectator (index 6)
satisfies `x₆(t) = 210 + (12/11) ((−1/6)ᵗ − (1/5)ᵗ)`, so it is strictly left of `210` for every
`t ≥ 1`; the neighbourhood table is the same at every `t`. The table check uses just
`−1/6 ≤ (−1/6)ᵗ ≤ 1` and `0 ≤ (1/5)ᵗ ≤ 1`, with no parity split.
-/

public section

namespace HK

theorem sbc9Orbit : Orbit .sbc sbc9_r sbc9_x0
    (powers sbcRate (1 / 5) fun u w =>
      ![0, 20 + 2 * u, 40 - 3 * u, 100 + 3 * u, 120 - 2 * u, 140, 210 + 12 / 11 * (u - w), 280, 300])
    (fun _ => rows![{0}, 0⋯2, 0⋯3, 2⋯5, 3⋯5, {5}, 4⋯8, {7}, {8}]) := by
  check_powers sbcRate and 1 / 5

corollary sbc9_closed_form := sbc9Orbit.form

corollary sbc9_neighbors := sbc9Orbit.table

theorem sbc9_spectator_lt (t : ℕ) (ht : 1 ≤ t) : traj .sbc sbc9_r sbc9_x0 t 6 < 210 := by
  have h := faster_power sbcRate (1 / 5) ht
  simp [sbc9_closed_form] at *
  linarith

end HK
