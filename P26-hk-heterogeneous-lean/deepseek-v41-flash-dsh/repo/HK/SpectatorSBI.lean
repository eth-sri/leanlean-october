module

public import HK.Basic

/-!
# The 8-agent SBI spectator system (Hegarty–Ognissanti–Wedin §5)

The seven agents of §5 with a spectator at `60` (`r = 1`), which becomes index 1 when the opinions
are listed increasingly; for all `t` the other agents evolve as in §5 and
`x₁(t) = 60 + φ⁻¹ ((1/4)ᵗ − λᵗ)`, so it is strictly right of `60` for every `t ≥ 1`; the
neighbourhood table is the same at every `t`.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- The state on the box: `u = λᵗ`, `w = (1/4)ᵗ`. -/
noncomputable def spe_x (u w : ℝ) : Fin 8 → ℝ :=
  ![0, 60 + (Real.goldenRatio - 1) * (w - u), 70 + u, 100 - Real.goldenRatio * u, 110,
    120 + Real.goldenRatio * u, 150 - u, 220]

theorem spe_inv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 :=
  inv_eq_of_mul_eq_one_right (by linear_combination Real.goldenRatio_sq)

/-- The table on the closed box `(1 − φ)/4 ≤ u ≤ 1`, `0 ≤ w ≤ 1`. -/
theorem spe_table (u w : ℝ) (hu0 : (1 - Real.goldenRatio) / 4 ≤ u) (hu1 : u ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    neighbors .sbi sbi8_r (spe_x u w) =
      ![{0}, {0, 1, 2, 4}, {0, 2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5}, {3, 4, 5, 6}, {4, 5, 6, 7}, {7}] := by
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have hsq := Real.goldenRatio_sq
  have hφ0 : 0 ≤ Real.goldenRatio := by linarith
  have hm0 := mul_le_mul_of_nonneg_right hu0 hφ0
  have hm1 := mul_le_mul_of_nonneg_right hu1 hφ0
  have hp0 : -1 / 4 ≤ u * Real.goldenRatio := by nlinarith
  have hp1 : u * Real.goldenRatio ≤ 2 := by nlinarith
  have hq0 : 0 ≤ w * Real.goldenRatio := mul_nonneg hw0 hφ0
  have hq1 : w * Real.goldenRatio ≤ 2 := by nlinarith
  tab sbi8_r, spe_x

theorem spe_step (u w : ℝ) (hu0 : (1 - Real.goldenRatio) / 4 ≤ u) (hu1 : u ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    step .sbi sbi8_r (spe_x u w) = spe_x (sbiRate * u) (1 / 4 * w) := by
  funext i
  rw [step_apply, spe_table u w hu0 hu1 hw0 hw1, sbiRate_eq]
  fin_cases i <;> simp [Finset.sum_insert, spe_x] <;> sq 5

theorem spe_closed (t : ℕ) :
    traj .sbi sbi8_r sbi8_x0 t = spe_x (sbiRate ^ t) ((1 / 4 : ℝ) ^ t) :=
  traj_geom2 .sbi sbi8_r sbi8_x0 spe_x sbiRate (1 / 4) ((1 - Real.goldenRatio) / 4) 1
    (fun u w h0 h1 hw0 hw1 => spe_step u w h0 h1 hw0 hw1)
    (by funext i; fin_cases i <;> simp [sbi8_x0, spe_x] <;> ring_nf)
    (fun t => by
      rw [← sbiRate_eq]
      exact pow_bounds_of_neg sbiRate_mem.1 sbiRate_mem.2 t)
    (fun t => pos_pow_bounds (by norm_num) (by norm_num) t) t

chall sbi8_closed_form "  rw [spe_closed, spe_inv]
  rfl"

chall sbi8_neighbors "  obtain ⟨h0, h1⟩ := pow_bounds_of_neg sbiRate_mem.1 sbiRate_mem.2 t
  rw [spe_closed,
    spe_table _ _ (by rw [← sbiRate_eq]; exact h0) h1 (pow_nonneg (by norm_num) t)
      (pow_le_one₀ (by norm_num) (by norm_num) (n := t))]"

chall sbi8_spectator_gt "  rw [spe_closed]
  have h0 : spe_x (sbiRate ^ t) ((1 / 4 : ℝ) ^ t) 1 =
      60 + (Real.goldenRatio - 1) * ((1 / 4 : ℝ) ^ t - sbiRate ^ t) := rfl
  rw [h0, ← spe_inv]
  have h1 : |sbiRate| ^ t < (1 / 4 : ℝ) ^ t :=
    pow_lt_pow_left₀ sbiRate_abs_lt_quarter (abs_nonneg _) (by omega)
  have h2 : sbiRate ^ t ≤ |sbiRate| ^ t := by
    rw [← abs_pow]
    exact le_abs_self _
  have h3 : 0 < Real.goldenRatio⁻¹ := inv_pos.mpr Real.goldenRatio_pos
  have h4 : 0 < (1 / 4 : ℝ) ^ t - sbiRate ^ t := by linarith
  have := mul_pos h3 h4
  linarith"

end HK
