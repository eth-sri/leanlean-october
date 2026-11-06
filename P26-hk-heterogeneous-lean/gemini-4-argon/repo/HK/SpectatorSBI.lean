module

public import HK.Basic

/-!
# The 8-agent SBI spectator system (Hegarty–Ognissanti–Wedin §5)

The seven agents of §5 with a spectator at `60` (`r = 1`), which becomes index 1 when the opinions
are listed increasingly; for all `t` the other agents evolve as in §5 and
`x₁(t) = 60 + φ⁻¹ ((1/4)ᵗ − λᵗ)`, so it is strictly right of `60` for every `t ≥ 1`; the
neighbourhood table is the same at every `t`. Two atoms: `u = λᵗ ∈ [λ, 1]` and `w = (1/4)ᵗ ∈ (0, 1]`;
the table holds on the closed box `|u| ≤ 1`, `0 ≤ w ≤ 1` with no parity split (the product atom
`u φ` needs its own bounds, as in `HK/SBI7.lean`).
-/

@[expose] public section

namespace HK

local notation "sbi8_N" =>
  ![{0}, {0, 1, 2, 4}, {0, 2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5}, {3, 4, 5, 6},
    {4, 5, 6, 7}, {7}]

local notation "sbi8_f" t =>
  ![0, 60 + Real.goldenRatio⁻¹ * ((1 / 4) ^ t - sbiRate ^ t), 70 + sbiRate ^ t,
    100 - Real.goldenRatio * sbiRate ^ t, 110, 120 + Real.goldenRatio * sbiRate ^ t,
    150 - sbiRate ^ t, 220]

theorem spe_inv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 :=
  inv_eq_of_mul_eq_one_right (by linear_combination Real.goldenRatio_sq)

/-- The table on the closed box `(1 − φ)/4 ≤ u ≤ 1`, `0 ≤ w ≤ 1`. -/
theorem spe_table t : nbi sbi8_r (sbi8_f t) = sbi8_N := by
  have := unit_pow (1 / 4) t
  have : 0 ≤ (%1 / 4) ^ t * Real.goldenRatio := by positivity
  have : (%1 / 4) ^ t * Real.goldenRatio ≤ 2 := by nlinarith [Real.goldenRatio_lt_two]
  rw [spe_inv]
  hk_table

theorem sbi8_closed_form t : tr8 t = sbi8_f t := by
  hk_traj funext i; fin_cases i <;> simp <;> ring =>
    rw [spe_table, spe_inv]; hk_avg

theorem sbi8_neighbors t : nbi sbi8_r (tr8 t) = sbi8_N := by
  rw [sbi8_closed_form, spe_table]

theorem sbi8_spectator_gt t (ht : 1 ≤ t) : 60 < tr8 t 1 := by
  rw [sbi8_closed_form]; dsimp
  nlinarith [pow_lt sbiRate (1 / 4) ht, Real.one_lt_goldenRatio, spe_inv]

end HK
