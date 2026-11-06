module

public import HK.Basic

/-!
# The second 7-agent SBI system (Hegarty–Ognissanti–Wedin §5)

`x(0) = (0, 71, 100 − φ, 110, 120 + φ, 149, 220)`, `r = (85, 35, 35, 75, 35, 35, 85)`,
`λ = (1 − √5)/8`; `x(t) = (0, 70, 100, 110, 120, 150, 220) + λᵗ (0, 1, −φ, 0, φ, −1, 0)`. The
neighbourhood table is the same at every `t`, yet agents 1, 2, 4, 5 alternate sides of their limits;
their per-step convergence factor is `λ` at every `t`.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- The neighbourhood table of the system. -/
noncomputable def sbi7b_T : Fin 7 → Finset (Fin 7) :=
  ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}]

/-- The table for every offset `λ ≤ w ≤ 1`. -/
theorem sbi7b_table (w : ℝ) (h0 : sbiRate ≤ w) (h1 : w ≤ 1) :
    neighbors .sbi sbi7b_r (fun i => sbi7b_lim i + w * sbi_v i) = sbi7b_T := by
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have hsq := Real.goldenRatio_sq
  rw [sbiRate_eq] at h0
  have hφ0 : 0 ≤ Real.goldenRatio := by linarith
  have hm0 := mul_le_mul_of_nonneg_right h0 hφ0
  have hm1 := mul_le_mul_of_nonneg_right h1 hφ0
  have hp0 : -1 / 4 ≤ w * Real.goldenRatio := by nlinarith
  have hp1 : w * Real.goldenRatio ≤ 2 := by nlinarith
  tab sbi7b_r, sbi7b_lim, sbi_v, sbi7b_T

theorem sbi7b_step (w : ℝ) (h0 : sbiRate ≤ w) (h1 : w ≤ 1) :
    step .sbi sbi7b_r (fun i => sbi7b_lim i + w * sbi_v i) =
      fun i => sbi7b_lim i + (sbiRate * w) * sbi_v i := by
  have hsq := Real.goldenRatio_sq
  funext i
  rw [step_apply, sbi7b_table w h0 h1, sbiRate_eq]
  fin_cases i
  · simp [sbi7b_lim, sbi_v, sbi7b_T]
  · simp [Finset.sum_insert, sbi7b_lim, sbi_v, sbi7b_T]; ring
  · simp [Finset.sum_insert, sbi7b_lim, sbi_v, sbi7b_T]
    linear_combination (-w / 4) * hsq
  · simp [Finset.sum_insert, sbi7b_lim, sbi_v, sbi7b_T]; ring
  · simp [Finset.sum_insert, sbi7b_lim, sbi_v, sbi7b_T]
    linear_combination (w / 4) * hsq
  · simp [Finset.sum_insert, sbi7b_lim, sbi_v, sbi7b_T]; ring
  · simp [sbi7b_lim, sbi_v, sbi7b_T]

theorem sbi7b_bounds (t : ℕ) : sbiRate ≤ sbiRate ^ t ∧ sbiRate ^ t ≤ 1 :=
  pow_bounds_of_neg sbiRate_mem.1 sbiRate_mem.2 t

chall sbi7b_closed_form "exact traj_geom1 .sbi sbi7b_r sbi7b_x0 sbi7b_lim sbi_v sbiRate sbiRate 1 (fun u h0 h1 => sbi7b_step u h0 h1) (by init sbi7b_x0, sbi7b_lim, sbi_v) sbi7b_bounds t"
  sbi7b_neighbors "obtain ⟨h0, h1⟩ := sbi7b_bounds t; rw [sbi7b_closed_form_internal, sbi7b_table _ h0 h1]; rfl"
  sbi7b_digraph_constant "exact digraph_constant_of_table _ _ _ _ sbi7b_neighbors_internal t"
  sbi7b_fvct "exact fvct_of_step _ _ _ _ _ sbiRate (sbiRate ^ t) sbiRate 1 (sbi7b_closed_form_internal t) (fun u h0 h1 => by rw [sbi7b_table u h0 h1, sbi7b_neighbors_internal]; rfl) (fun u h0 h1 => sbi7b_step u h0 h1) (fun k => by rw [← pow_add]; exact sbi7b_bounds (k + t)) (abs_lt.mpr ⟨sbiRate_mem.1, by linarith [sbiRate_mem.2]⟩)"
  sbi7b_perStepFactor "refine perStepFactor_geom1 _ _ (traj .sbi sbi7b_r sbi7b_x0) sbi7b_lim sbi_v sbiRate sbiRate_mem.2.ne sbi7b_closed_form_internal sbi7b_fvct_internal i ?_ t; have h0 := Real.goldenRatio_pos; fin_cases i <;> simp_all [sbi_v] <;> linarith"
  sbi7b_perStepFactor_not_tendsto "exact perStepFactor_not_tendsto _ _ _ i sbiRate sbiRate_mem.2 (fun t => sbi7b_perStepFactor_internal t i hi) ρ hρ"

theorem sbi7b_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbi sbi7b_r sbi7b_x0) τ :=
  not_fixedFrom_of_geom1 _ sbi7b_lim sbi_v sbiRate sbiRate_mem.2 sbi7b_closed_form_internal 1
    (by simp [sbi_v]) τ

theorem sbi7b_not_pseudoStableAfter (xinf : Fin 7 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbi sbi7b_r sbi7b_x0) xinf τ :=
  not_pseudoStable_of_geom1 _ sbi7b_lim sbi_v sbiRate sbiRate_mem.1 sbiRate_mem.2
    sbi7b_closed_form_internal xinf τ

theorem sbi7b_r_pos : ∀ i, 0 < sbi7b_r i := by
  intro i
  fin_cases i <;> simp [sbi7b_r]

end HK
