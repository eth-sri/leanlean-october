module

public import HK.Basic

/-!
# Five SBC agents: a constant digraph with oscillating convergence, with arbitrary spread

`x(0) = (0, 7, 12 − √2, 19, 24)`, `r = (3, 9, 9, 9, 3)`;
`x(t) = (0, 6, 12, 18, 24) + ((1 − √2)/3)ᵗ (0, 1, −√2, 1, 0)`. The neighbourhood table
`{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}` is the same at every `t`, yet agents 1, 2, 3 alternate
sides of their limits; the same holds for the whole family `sbc5_lim + δ sbc5_v` with bounds
`(6 − 3δ, 6 + 3δ, 6 + 3δ, 6 + 3δ, 6 − 3δ)`, whose radius ratio is below `1 + ε`.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- The neighbourhood table of the systems. -/
noncomputable def sbc5_T : Fin 5 → Finset (Fin 5) := ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}]

/-! ### The family `sbc5_lim + δ sbc5_v` -/

theorem sbc5Family_r_pos (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ i, 0 < sbc5Family_r δ i := by
  intro i
  fin_cases i <;> simp [sbc5Family_r] <;> linarith

/-- The family is genuinely heterogeneous whenever the amplitude is positive. -/
theorem sbc5Family_r_strict (δ : ℝ) (hδ0 : 0 < δ) : sbc5Family_r δ 0 < sbc5Family_r δ 1 := by
  simp only [sbc5Family_r, Matrix.cons_val_zero, Matrix.cons_val_one]
  linarith

/-- The fixed table holds throughout `-δ ≤ u ≤ δ`. -/
theorem sbc5Family_table (δ u : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hu0 : -δ ≤ u) (hu1 : u ≤ δ) :
    neighbors .sbc (sbc5Family_r δ) (fun i => sbc5_lim i + u * sbc5_v i) = sbc5_T := by
  have hs := sqrt_two_bounds
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  tabn sbc5Family_r, sbc5_lim, sbc5_v, sbc5_T

theorem sbc5Family_step (δ u : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hu0 : -δ ≤ u) (hu1 : u ≤ δ) :
    step .sbc (sbc5Family_r δ) (fun i => sbc5_lim i + u * sbc5_v i) =
      fun i => sbc5_lim i + (sbc5Rate * u) * sbc5_v i := by
  funext i
  rw [step_apply, sbc5Family_table δ u hδ0 hδ1 hu0 hu1]
  fin_cases i <;> simp [Finset.sum_insert, sbc5_lim, sbc5_v, sbc5_T, sbc5Rate] <;> sq 2

theorem sbc5Family_bounds (δ : ℝ) (hδ0 : 0 < δ) (t : ℕ) :
    -δ ≤ sbc5Rate ^ t * δ ∧ sbc5Rate ^ t * δ ≤ δ := by
  obtain ⟨h0, h1⟩ := pow_bounds_of_neg sbc5Rate_mem.1 sbc5Rate_mem.2 t
  have h2 : -1 ≤ sbc5Rate ^ t := by linarith [sbc5Rate_mem.1]
  constructor <;> nlinarith

chall sbc5Family_closed_form "exact traj_geom .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) sbc5_lim sbc5_v sbc5Rate δ (-δ) δ (fun u h0 h1 => sbc5Family_step δ u hδ0 hδ1 h0 h1) (by init sbc5Family_x0, sbc5_lim, sbc5_v) (sbc5Family_bounds δ hδ0) t"

chall sbc5Family_neighbors "obtain ⟨h0, h1⟩ := sbc5Family_bounds δ hδ0 t
  rw [sbc5Family_closed_form_internal δ hδ0 hδ1, sbc5Family_table δ _ hδ0 hδ1 h0 h1]
  rfl"





/-! ### The system at `δ = 1` -/

theorem sbc5_r_eq : sbc5_r = sbc5Family_r 1 := by
  funext i
  fin_cases i <;> simp [sbc5_r, sbc5Family_r] <;> norm_num

theorem sbc5_x0_eq : sbc5_x0 = sbc5Family_x0 1 := by
  funext i
  fin_cases i <;> simp [sbc5_x0, sbc5Family_x0, sbc5_lim, sbc5_v] <;> ring_nf

theorem sbc5_r_pos : ∀ i, 0 < sbc5_r i := by
  rw [sbc5_r_eq]
  exact sbc5Family_r_pos 1 one_pos le_rfl

chall sbc5_closed_form "rw [sbc5_r_eq, sbc5_x0_eq]
  simpa using sbc5Family_closed_form_internal 1 one_pos le_rfl t"

chall sbc5_neighbors "rw [sbc5_r_eq, sbc5_x0_eq]
  exact sbc5Family_neighbors_internal 1 one_pos le_rfl t"



theorem sbc5_digraph_constant (t : ℕ) :
    proximityDigraph .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) =
      proximityDigraph .sbc sbc5_r sbc5_x0 :=
  digraph_constant_of_table _ _ _ _ sbc5_neighbors_internal t

theorem sbc5_tendsto : Tendsto (traj .sbc sbc5_r sbc5_x0) atTop (𝓝 sbc5_lim) :=
  tendsto_of_geom1 _ sbc5_lim sbc5_v sbc5Rate sbc5Rate_mem.1 sbc5Rate_mem.2 sbc5_closed_form_internal

theorem sbc5_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbc sbc5_r sbc5_x0) τ :=
  not_fixedFrom_of_geom1 _ sbc5_lim sbc5_v sbc5Rate sbc5Rate_mem.2 sbc5_closed_form_internal 1
    (by simp [sbc5_v]) τ

theorem sbc5_not_pseudoStableAfter (xinf : Fin 5 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc5_r sbc5_x0) xinf τ :=
  not_pseudoStable_of_geom1 _ sbc5_lim sbc5_v sbc5Rate sbc5Rate_mem.1 sbc5Rate_mem.2
    sbc5_closed_form_internal xinf τ

chall sbc5_fvct "exact fvct_of_step _ _ _ _ _ sbc5Rate (sbc5Rate ^ t) sbc5Rate 1 (sbc5_closed_form_internal t) (fun u h0 h1 => by rw [sbc5_r_eq, sbc5Family_table 1 u one_pos le_rfl (by linarith [sbc5Rate_mem.1]) h1]; rw [← sbc5_r_eq]; rw [sbc5_neighbors_internal]; rfl) (fun u h0 h1 => by rw [sbc5_r_eq]; exact sbc5Family_step 1 u one_pos le_rfl (by linarith [sbc5Rate_mem.1]) h1) (fun k => by rw [← pow_add]; exact pow_bounds_of_neg sbc5Rate_mem.1 sbc5Rate_mem.2 (k + t)) (abs_lt.mpr ⟨sbc5Rate_mem.1, by linarith [sbc5Rate_mem.2]⟩)"

chall sbc5_perStepFactor "have hv : sbc5_v i ≠ 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> simp [sbc5_v] <;> linarith [sqrt_two_bounds.1]
  exact perStepFactor_geom1 _ _ (traj .sbc sbc5_r sbc5_x0) sbc5_lim sbc5_v sbc5Rate sbc5Rate_mem.2.ne sbc5_closed_form_internal
    sbc5_fvct_internal i hv t"

theorem not_conjecture23_sbc_five_internal : ¬ Conjecture23ForAgents .sbc 5 := by
  intro h
  obtain ⟨τ, hf | ⟨xinf, hps⟩⟩ := h sbc5_r sbc5_x0 sbc5_r_pos
  · exact sbc5_not_fixedFrom τ hf
  · exact sbc5_not_pseudoStableAfter xinf τ hps

theorem not_theorem64iv_sbc_five_internal : ¬ Theorem64ivForAgents .sbc 5 := by
  intro h
  obtain ⟨t₂, -, hf | ⟨xinf, hps⟩⟩ := h sbc5_r sbc5_x0 sbc5_r_pos 0
    (fun t _ => by simp only [proximityDigraph, sbc5_neighbors_internal])
  · exact sbc5_not_fixedFrom t₂ hf
  · exact sbc5_not_pseudoStableAfter xinf t₂ hps

end HK
