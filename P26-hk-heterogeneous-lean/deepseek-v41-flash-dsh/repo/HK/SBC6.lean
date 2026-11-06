module

public import HK.Basic

/-!
# The 6-agent SBC system (Hegarty–Ognissanti–Wedin §4)

`x(0) = (0, 22, 37, 103, 118, 140)`, `r = (10, 70, 70, 70, 70, 10)`;
`x(t) = (0, 20, 40, 100, 120, 140) + (−1/6)ᵗ (0, 2, −3, 3, −2, 0)`. The neighbourhood table is the
same at every `t` (so the proximity digraph is constant), yet agents 1–4 alternate sides of their
limits; their per-step convergence factor is `−1/6` at every `t`.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- The neighbourhood table of the system. -/
noncomputable def sbc6_T : Fin 6 → Finset (Fin 6) :=
  ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}]

/-- The table for every offset `-1/6 ≤ u ≤ 1`. -/
theorem sbc6_table (u : ℝ) (h0 : -1 / 6 ≤ u) (h1 : u ≤ 1) :
    neighbors .sbc sbc6_r (fun i => sbc6_lim i + u * sbc6_v i) = sbc6_T := by
  tab sbc6_r, sbc6_lim, sbc6_v, sbc6_T

theorem sbc6_step (u : ℝ) (h0 : -1 / 6 ≤ u) (h1 : u ≤ 1) :
    step .sbc sbc6_r (fun i => sbc6_lim i + u * sbc6_v i) =
      fun i => sbc6_lim i + (-1 / 6 * u) * sbc6_v i := by
  stp sbc6_table u h0 h1 | sbc6_lim, sbc6_v, sbc6_T

theorem sbc6_rate : -1 < (-1 / 6 : ℝ) ∧ (-1 / 6 : ℝ) < 0 := ⟨by norm_num, by norm_num⟩

theorem sbc6_bounds (t : ℕ) : -1 / 6 ≤ (-1 / 6 : ℝ) ^ t ∧ (-1 / 6 : ℝ) ^ t ≤ 1 :=
  pow_bounds_of_neg sbc6_rate.1 sbc6_rate.2 t

chall sbc6_closed_form "exact traj_geom1 .sbc sbc6_r sbc6_x0 sbc6_lim sbc6_v (-1 / 6) (-1 / 6) 1 (fun u h0 h1 => sbc6_step u h0 h1) (by init sbc6_x0, sbc6_lim, sbc6_v) sbc6_bounds t"
  sbc6_neighbors "obtain ⟨h0, h1⟩ := sbc6_bounds t; rw [sbc6_closed_form_internal, sbc6_table _ h0 h1]; rfl"
  sbc6_digraph_constant "exact digraph_constant_of_table _ _ _ _ sbc6_neighbors_internal t"
  sbc6_fvct "exact fvct_of_step _ _ _ _ _ (-1 / 6) ((-1 / 6 : ℝ) ^ t) (-1 / 6) 1 (sbc6_closed_form_internal t) (fun u h0 h1 => by rw [sbc6_table u h0 h1, sbc6_neighbors_internal t]; rfl) (fun u h0 h1 => sbc6_step u h0 h1) (fun k => by rw [← pow_add]; exact sbc6_bounds (k + t)) (by norm_num)"
  sbc6_perStepFactor "exact perStepFactor_geom1 _ _ (traj .sbc sbc6_r sbc6_x0) sbc6_lim sbc6_v (-1 / 6) (by norm_num) sbc6_closed_form_internal sbc6_fvct_internal i (by fin_cases i <;> simp_all [sbc6_v]) t"
  sbc6_perStepFactor_not_tendsto "exact perStepFactor_not_tendsto _ _ _ i (-1 / 6) (by norm_num) (fun t => sbc6_perStepFactor_internal t i hi) ρ hρ"

theorem sbc6_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbc sbc6_r sbc6_x0) τ :=
  not_fixedFrom_of_geom1 _ sbc6_lim sbc6_v (-1 / 6) (by norm_num) (fun t => sbc6_closed_form_internal t)
    1 (by simp [sbc6_v]) τ

theorem sbc6_not_pseudoStableAfter (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc6_r sbc6_x0) yinf τ :=
  not_pseudoStable_of_geom1 _ sbc6_lim sbc6_v (-1 / 6) (by norm_num) (by norm_num)
    (fun t => sbc6_closed_form_internal t) yinf τ

theorem sbc6_r_pos : ∀ i, 0 < sbc6_r i := by
  intro i
  fin_cases i <;> simp [sbc6_r]

end HK
