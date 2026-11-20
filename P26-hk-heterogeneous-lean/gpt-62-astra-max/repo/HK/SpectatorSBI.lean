module

public import HK.Basic

/-!
# The 8-agent SBI spectator system (Hegarty–Ognissanti–Wedin §5)

The seven agents of §5 with a spectator at `60` (`r = 1`), which becomes index 1 when the opinions
are listed increasingly; for all `t` the other agents evolve as in §5 and
`x₁(t) = 60 + φ⁻¹ ((1/4)ᵗ − λᵗ)`, so it is strictly right of `60` for every `t ≥ 1`; the
neighbourhood table is the same at every `t`. The proof bounds the two powers by
`λ ≤ λᵗ ≤ 1` and `0 ≤ (1/4)ᵗ ≤ 1` and checks the averaging identity in those coordinates.
-/

public section

namespace HK
open scoped goldenRatio

theorem sbi8Orbit : Orbit .sbi sbi8_r sbi8_x0
    (powers sbiRate (1 / 4) fun u w =>
      ![0, 60 + φ⁻¹ * (w - u), 70 + u, 100 - φ * u, 110, 120 + φ * u, 150 - u, 220])
    (fun _ => rows![{0}, {0, 1, 2, 4}, {0, 2, 3, 4}, 2⋯5, 3⋯5, 3⋯6, 4⋯7, {7}]) := by
  radical 5
  check_powers sbiRate and 1 / 4

corollary sbi8_closed_form := sbi8Orbit.form

corollary sbi8_neighbors := sbi8Orbit.table

theorem sbi8_spectator_gt (t : ℕ) (ht : 1 ≤ t) : 60 < traj .sbi sbi8_r sbi8_x0 t 1 := by
  radical 5
  have := sub_pos.mpr (faster_power sbiRate (1 / 4) ht)
  rw [sbi8_closed_form]
  exact lt_add_of_pos_right _ (by positivity)

end HK
