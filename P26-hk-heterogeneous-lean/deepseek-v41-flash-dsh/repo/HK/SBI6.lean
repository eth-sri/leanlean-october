module

public import HK.Basic

/-!
# Six SBI agents with a constant digraph and oscillating convergence

`x_∞ = (0, 25, 31, 44, 55, 90)`, `v = (0, 10, −5 − √249, 8, 10, 0)/16`,
`r = (45, 18, 27, 45/2, 27, 54)`, `x(0) = x_∞ + v`, `x(t) = x_∞ + ((13 − √249)/40)ᵗ v`. The
neighbourhood table `{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}` is the
same at every `t`, yet agents 1–4 alternate sides of their limits.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- The neighbourhood table of the system. -/
noncomputable def sbi6_T : Fin 6 → Finset (Fin 6) :=
  ![{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}]

/-- The table for every offset `λ ≤ u ≤ 1`. -/
theorem sbi6_table (u : ℝ) (h0 : sbi6Rate ≤ u) (h1 : u ≤ 1) :
    neighbors .sbi sbi6_r (fun i => sbi6_lim i + u * sbi6_v i) = sbi6_T := by
  obtain ⟨hs0, hs1⟩ := sqrt249_bounds
  have hsq := sqrt249_sq
  have hs : 0 ≤ Real.sqrt 249 := Real.sqrt_nonneg _
  have hm0 := mul_le_mul_of_nonneg_right h0 hs
  have hm1 := mul_le_mul_of_nonneg_right h1 hs
  have hl : sbi6Rate * Real.sqrt 249 = (13 * Real.sqrt 249 - 249) / 40 := by
    unfold sbi6Rate
    linear_combination (-1 / 40 : ℝ) * hsq
  have hp0 : -27 / 20 ≤ u * Real.sqrt 249 := by nlinarith
  have hp1 : u * Real.sqrt 249 ≤ 16 := by nlinarith
  have hu0 : -3 / 40 ≤ u := by nlinarith
  tab sbi6_r, sbi6_lim, sbi6_v, sbi6_T

theorem sbi6_step (u : ℝ) (h0 : sbi6Rate ≤ u) (h1 : u ≤ 1) :
    step .sbi sbi6_r (fun i => sbi6_lim i + u * sbi6_v i) =
      fun i => sbi6_lim i + (sbi6Rate * u) * sbi6_v i := by
  have hsq := sqrt249_sq
  funext i
  rw [step_apply, sbi6_table u h0 h1]
  unfold sbi6Rate
  fin_cases i
  · simp [sbi6_lim, sbi6_v, sbi6_T]
  · simp [Finset.sum_insert, sbi6_lim, sbi6_v, sbi6_T]; ring
  · simp [Finset.sum_insert, sbi6_lim, sbi6_v, sbi6_T]
    linear_combination (-u / 640) * hsq
  · simp [Finset.sum_insert, sbi6_lim, sbi6_v, sbi6_T]; ring
  · simp [Finset.sum_insert, sbi6_lim, sbi6_v, sbi6_T]; ring
  · simp [sbi6_lim, sbi6_v, sbi6_T]

theorem sbi6_bounds (t : ℕ) : sbi6Rate ≤ sbi6Rate ^ t ∧ sbi6Rate ^ t ≤ 1 :=
  pow_bounds_of_neg sbi6Rate_mem.1 sbi6Rate_mem.2 t

chall sbi6_closed_form "exact traj_geom1 .sbi sbi6_r sbi6_x0 sbi6_lim sbi6_v sbi6Rate sbi6Rate 1 (fun u h0 h1 => sbi6_step u h0 h1) (by init sbi6_x0, sbi6_lim, sbi6_v) sbi6_bounds t"
  sbi6_neighbors "obtain ⟨h0, h1⟩ := sbi6_bounds t; rw [sbi6_closed_form_internal, sbi6_table _ h0 h1]; rfl"

theorem sbi6_digraph_constant (t : ℕ) :
    proximityDigraph .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) =
      proximityDigraph .sbi sbi6_r sbi6_x0 :=
  digraph_constant_of_table _ _ _ _ sbi6_neighbors_internal t

chall sbi6_fvct "exact fvct_of_step _ _ _ _ _ sbi6Rate (sbi6Rate ^ t) sbi6Rate 1 (sbi6_closed_form_internal t) (fun u h0 h1 => by rw [sbi6_table u h0 h1, sbi6_neighbors_internal]; rfl) (fun u h0 h1 => sbi6_step u h0 h1) (fun k => by rw [← pow_add]; exact sbi6_bounds (k + t)) (abs_lt.mpr ⟨sbi6Rate_mem.1, by linarith [sbi6Rate_mem.2]⟩)"
  sbi6_perStepFactor "refine perStepFactor_geom1 _ _ (traj .sbi sbi6_r sbi6_x0) sbi6_lim sbi6_v sbi6Rate sbi6Rate_mem.2.ne sbi6_closed_form_internal sbi6_fvct_internal i ?_ t; have hs : (0 : ℝ) ≤ Real.sqrt 249 := Real.sqrt_nonneg _; simp only [Finset.mem_insert, Finset.mem_singleton] at hi; rcases hi with rfl | rfl | rfl | rfl <;> simp [sbi6_v] <;> (intro h; linarith)"

theorem sbi6_tendsto : Tendsto (traj .sbi sbi6_r sbi6_x0) atTop (𝓝 sbi6_lim) :=
  tendsto_of_geom1 _ sbi6_lim sbi6_v sbi6Rate sbi6Rate_mem.1 sbi6Rate_mem.2 sbi6_closed_form_internal

theorem sbi6_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbi sbi6_r sbi6_x0) τ :=
  not_fixedFrom_of_geom1 _ sbi6_lim sbi6_v sbi6Rate sbi6Rate_mem.2 sbi6_closed_form_internal 1
    (by simp [sbi6_v]) τ

theorem sbi6_not_pseudoStableAfter (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbi sbi6_r sbi6_x0) yinf τ :=
  not_pseudoStable_of_geom1 _ sbi6_lim sbi6_v sbi6Rate sbi6Rate_mem.1 sbi6Rate_mem.2
    sbi6_closed_form_internal yinf τ

theorem sbi6_r_pos : ∀ i, 0 < sbi6_r i := by
  intro i
  fin_cases i <;> simp [sbi6_r] <;> norm_num

theorem not_conjecture23_sbi_six_internal : ¬ Conjecture23ForAgents .sbi 6 := by
  intro h
  obtain ⟨τ, hf | ⟨xinf, hps⟩⟩ := h sbi6_r sbi6_x0 sbi6_r_pos
  · exact sbi6_not_fixedFrom τ hf
  · exact sbi6_not_pseudoStableAfter xinf τ hps

theorem not_theorem64iv_sbi_six_internal : ¬ Theorem64ivForAgents .sbi 6 := by
  intro h
  obtain ⟨t₂, -, hf | ⟨xinf, hps⟩⟩ := h sbi6_r sbi6_x0 sbi6_r_pos 0
    (fun t _ => by simp only [proximityDigraph, sbi6_neighbors_internal])
  · exact sbi6_not_fixedFrom t₂ hf
  · exact sbi6_not_pseudoStableAfter xinf t₂ hps

end HK
