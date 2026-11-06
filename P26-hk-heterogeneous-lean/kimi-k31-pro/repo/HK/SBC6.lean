module

public import HK.Basic

@[expose] public section

namespace HK

open Filter Topology

theorem sbc6_table (u : ℝ) (h0 : -1 / 6 ≤ u) (h1 : u ≤ 1) :
    neighbors .sbc sbc6_r (fun i => sbc6_lim i + u * sbc6_v i) =
      ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbc6_r, sbc6_lim, sbc6_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem sbc6_step (u : ℝ) (h0 : -1 / 6 ≤ u) (h1 : u ≤ 1) :
    step .sbc sbc6_r (fun i => sbc6_lim i + u * sbc6_v i) =
      fun i => sbc6_lim i + (-1 / 6 * u) * sbc6_v i := by
  funext i
  rw [step_apply, sbc6_table u h0 h1]
  fin_cases i <;> simp [Finset.sum_insert, sbc6_lim, sbc6_v] <;> ring

theorem sbc6_closed_form (t : ℕ) :
    traj .sbc sbc6_r sbc6_x0 t = fun i => sbc6_lim i + (-1 / 6 : ℝ) ^ t * sbc6_v i := by
  induction t with
  | zero =>
    funext i
    fin_cases i <;> simp [traj, sbc6_x0, sbc6_lim, sbc6_v] <;> norm_num
  | succ t ih =>
    obtain ⟨h0, h1⟩ := pow_bounds t
    rw [traj_succ, ih, sbc6_step _ h0 h1]
    funext i
    rw [pow_succ]
    ring

theorem sbc6_neighbors (t : ℕ) :
    neighbors .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) =
      ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}] := by
  obtain ⟨h0, h1⟩ := pow_bounds t
  rw [sbc6_closed_form, sbc6_table _ h0 h1]

theorem sbc6_digraph_constant (t : ℕ) :
    proximityDigraph .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) =
      proximityDigraph .sbc sbc6_r sbc6_x0 :=
  digraph_constant_of_neighbors _ _ _ _ sbc6_neighbors t

theorem sbc6_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbc sbc6_r sbc6_x0) τ :=
  not_fixedFrom_of_pow _ _ sbc6_v _ sbc6_closed_form (by norm_num)
    1 (by simp [sbc6_v]) τ

theorem sbc6_not_pseudoStableAfter (xinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc6_r sbc6_x0) xinf τ :=
  not_pseudoStable_of_pow _ _ sbc6_v _ abs_negSixth sbc6_closed_form (by norm_num) xinf τ

theorem sbc6_fvct (t : ℕ) : fvct .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) = sbc6_lim := by
  refine fvct_of_eigen _ _ _ _ sbc6_v _ ((-1 / 6 : ℝ) ^ t) ?_ (by
    funext i
    rw [adj_mulVec, sbc6_neighbors]
    fin_cases i <;> simp [Finset.sum_insert, sbc6_lim] <;> norm_num) (by
    funext i
    rw [adj_mulVec, sbc6_neighbors]
    fin_cases i <;> simp [Finset.sum_insert, sbc6_v] <;> norm_num) abs_negSixth
  rw [sbc6_closed_form]
  funext i
  simp

theorem sbc6_perStepFactor (t : ℕ) (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6))) :
    perStepFactor .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0) i t = -1 / 6 := by
  apply perStepFactor_of_closed_form _ _ _ _ _ _ _ _ (sbc6_fvct t)
    sbc6_closed_form (by norm_num)
  fin_cases i <;> simp_all [sbc6_v]

theorem sbc6_perStepFactor_not_tendsto (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => perStepFactor .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0) i t) atTop (𝓝 ρ) := by
  intro h
  simp only [sbc6_perStepFactor _ i hi] at h
  have := tendsto_nhds_unique h tendsto_const_nhds
  linarith

end HK
