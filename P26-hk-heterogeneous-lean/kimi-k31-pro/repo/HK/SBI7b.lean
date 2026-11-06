module

public import HK.Basic

@[expose] public section

namespace HK

open Filter Topology

theorem sbi7b_table (w : ℝ) (hw0 : (1 - Real.goldenRatio) / 4 ≤ w) (hw1 : w ≤ 1) :
    neighbors .sbi sbi7b_r (fun i => sbi7b_lim i + w * sbi_v i) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := by
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have hsq := Real.goldenRatio_sq
  have hφ0 : 0 ≤ Real.goldenRatio := by linarith
  have hm0 := mul_le_mul_of_nonneg_right hw0 hφ0
  have hm1 := mul_le_mul_of_nonneg_right hw1 hφ0
  have hp0 : -1 / 4 ≤ w * Real.goldenRatio := by nlinarith
  have hp1 : w * Real.goldenRatio ≤ 2 := by nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbi7b_r, sbi7b_lim, sbi_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem sbi7b_step (w : ℝ) (hw0 : (1 - Real.goldenRatio) / 4 ≤ w) (hw1 : w ≤ 1) :
    step .sbi sbi7b_r (fun i => sbi7b_lim i + w * sbi_v i) =
      fun i => sbi7b_lim i + ((1 - Real.goldenRatio) / 4 * w) * sbi_v i := by
  have hsq := Real.goldenRatio_sq
  have hsqw := congrArg (fun x : ℝ => w * x) hsq
  funext i
  rw [step_apply, sbi7b_table w hw0 hw1]
  fin_cases i <;> simp [Finset.sum_insert, sbi7b_lim, sbi_v] <;> nlinarith [hsqw]

theorem sbi7b_closed_form (t : ℕ) :
    traj .sbi sbi7b_r sbi7b_x0 t = fun i => sbi7b_lim i + sbiRate ^ t * sbi_v i := by
  induction t with
  | zero =>
    funext i
    fin_cases i <;> simp [traj, sbi7b_x0, sbi7b_lim, sbi_v] <;> ring
  | succ t ih =>
    obtain ⟨h0, h1⟩ := sbiRate_pow_bounds t
    rw [traj_succ, ih, sbi7b_step _ h0 h1]
    funext i
    rw [pow_succ, sbiRate_eq]
    ring

theorem sbi7b_neighbors (t : ℕ) :
    neighbors .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := by
  obtain ⟨h0, h1⟩ := sbiRate_pow_bounds t
  rw [sbi7b_closed_form, sbi7b_table _ h0 h1]

theorem sbi7b_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbi sbi7b_r sbi7b_x0) τ :=
  not_fixedFrom_of_pow _ _ sbi_v _ sbi7b_closed_form sbiRate_neg
    1 (by simp [sbi_v]) τ

theorem sbi7b_not_pseudoStableAfter (xinf : Fin 7 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbi sbi7b_r sbi7b_x0) xinf τ :=
  not_pseudoStable_of_pow _ _ sbi_v _ sbiRate_abs_lt_one sbi7b_closed_form
    sbiRate_neg xinf τ

theorem sbi7b_fvct (t : ℕ) : fvct .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) = sbi7b_lim := by
  refine fvct_of_eigen _ _ _ _ sbi_v _ (sbiRate ^ t) ?_ (by
    funext i
    rw [adj_mulVec, sbi7b_neighbors]
    fin_cases i <;> simp [Finset.sum_insert, sbi7b_lim] <;> norm_num) (by
    have hsq := Real.goldenRatio_sq
    funext i
    rw [adj_mulVec, sbi7b_neighbors, sbiRate_eq]
    fin_cases i <;> simp [Finset.sum_insert, sbi_v] <;> nlinarith [hsq]) sbiRate_abs_lt_one
  rw [sbi7b_closed_form]
  funext i
  simp

theorem sbi7b_perStepFactor (t : ℕ) (i : Fin 7) (hi : i ∈ ({1, 2, 4, 5} : Finset (Fin 7))) :
    perStepFactor .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0) i t = sbiRate := by
  apply perStepFactor_of_closed_form _ _ _ _ _ _ _ _ (sbi7b_fvct t)
    sbi7b_closed_form sbiRate_neg.ne
  have := Real.goldenRatio_pos.ne'
  fin_cases i <;> simp_all [sbi_v]

theorem sbi7b_perStepFactor_not_tendsto (i : Fin 7) (hi : i ∈ ({1, 2, 4, 5} : Finset (Fin 7)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => perStepFactor .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0) i t) atTop
      (𝓝 ρ) := by
  intro h
  simp only [sbi7b_perStepFactor _ i hi] at h
  have := tendsto_nhds_unique h tendsto_const_nhds
  linarith [sbiRate_neg]

theorem sbi7b_digraph_constant (t : ℕ) :
    proximityDigraph .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) =
      proximityDigraph .sbi sbi7b_r sbi7b_x0 :=
  digraph_constant_of_neighbors _ _ _ _ sbi7b_neighbors t

end HK
