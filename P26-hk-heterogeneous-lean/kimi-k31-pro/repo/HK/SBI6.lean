module

public import HK.Basic

@[expose] public section

namespace HK

theorem sbi_sqrt249_bounds : 15 < Real.sqrt 249 ∧ Real.sqrt 249 < 16 := by
  constructor <;> norm_num [Real.lt_sqrt, Real.sqrt_lt']

theorem sbi_sqrt249_sq : Real.sqrt 249 ^ 2 = 249 := Real.sq_sqrt (by norm_num)

theorem sbi_sbi6Rate_bounds : -3 / 40 < sbi6Rate ∧ sbi6Rate < -1 / 20 := by
  unfold sbi6Rate
  constructor <;> linarith [sbi_sqrt249_bounds.1, sbi_sqrt249_bounds.2]

theorem sbi6_r_pos : ∀ i, 0 < sbi6_r i := by
  intro i
  fin_cases i <;> simp [sbi6_r]

theorem sbi6Rate_neg : sbi6Rate < 0 := by
  linarith [sbi_sbi6Rate_bounds.2]

theorem abs_sbi6Rate_lt_one : |sbi6Rate| < 1 := by
  rw [abs_lt]
  constructor <;> linarith [sbi_sbi6Rate_bounds.1, sbi_sbi6Rate_bounds.2]

theorem si_pow_bounds (t : ℕ) : sbi6Rate ≤ sbi6Rate ^ t ∧ sbi6Rate ^ t ≤ 1 :=
  pow_bounds_of_neg (by linarith [sbi_sbi6Rate_bounds.1]) sbi6Rate_neg t

theorem sbi_sbi6_table (u : ℝ) (h0 : sbi6Rate ≤ u) (h1 : u ≤ 1) :
    neighbors .sbi sbi6_r (fun i => sbi6_lim i + u * sbi6_v i) =
      ![{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}] := by
  obtain ⟨hs0, hs1⟩ := sbi_sqrt249_bounds
  obtain ⟨hl0, hl1⟩ := sbi_sbi6Rate_bounds
  have hsq := sbi_sqrt249_sq
  have hs : 0 ≤ Real.sqrt 249 := Real.sqrt_nonneg _
  have hm0 := mul_le_mul_of_nonneg_right h0 hs
  have hm1 := mul_le_mul_of_nonneg_right h1 hs
  have hl : sbi6Rate * Real.sqrt 249 = (13 * Real.sqrt 249 - 249) / 40 := by
    unfold sbi6Rate
    linear_combination (-1 / 40 : ℝ) * hsq
  have hp0 : -27 / 20 ≤ u * Real.sqrt 249 := by nlinarith
  have hp1 : u * Real.sqrt 249 ≤ 16 := by nlinarith
  have hu0 : -3 / 40 ≤ u := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbi6_r, sbi6_lim, sbi6_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem sbi_sbi6_step (u : ℝ) (h0 : sbi6Rate ≤ u) (h1 : u ≤ 1) :
    step .sbi sbi6_r (fun i => sbi6_lim i + u * sbi6_v i) =
      fun i => sbi6_lim i + (sbi6Rate * u) * sbi6_v i := by
  have hsq := sbi_sqrt249_sq
  have hsqu := congrArg (fun x : ℝ => u * x) hsq
  funext i
  rw [step_apply, sbi_sbi6_table u h0 h1]
  unfold sbi6Rate
  fin_cases i <;> simp [Finset.sum_insert, sbi6_lim, sbi6_v] <;> nlinarith [hsqu]

theorem sbi6_closed_form (t : ℕ) :
    traj .sbi sbi6_r sbi6_x0 t = fun i => sbi6_lim i + sbi6Rate ^ t * sbi6_v i := by
  induction t with
  | zero =>
    funext i
    fin_cases i <;> simp [traj, sbi6_x0, sbi6_lim, sbi6_v]
  | succ t ih =>
    obtain ⟨h0, h1⟩ := si_pow_bounds t
    rw [traj_succ, ih, sbi_sbi6_step _ h0 h1]
    funext i
    rw [pow_succ]
    ring

theorem sbi6_neighbors (t : ℕ) :
    neighbors .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) =
      ![{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}] := by
  obtain ⟨h0, h1⟩ := si_pow_bounds t
  rw [sbi6_closed_form, sbi_sbi6_table _ h0 h1]

theorem sbi6_digraph_constant (t : ℕ) :
    proximityDigraph .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) =
      proximityDigraph .sbi sbi6_r sbi6_x0 :=
  digraph_constant_of_neighbors _ _ _ _ sbi6_neighbors t

theorem sbi6_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbi sbi6_r sbi6_x0) τ :=
  not_fixedFrom_of_pow _ _ sbi6_v _ sbi6_closed_form sbi6Rate_neg
    1 (by simp [sbi6_v]) τ

theorem sbi6_not_pseudoStableAfter (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbi sbi6_r sbi6_x0) yinf τ :=
  not_pseudoStable_of_pow _ _ sbi6_v _ abs_sbi6Rate_lt_one sbi6_closed_form
    sbi6Rate_neg yinf τ

theorem not_conjecture23_sbi_six : ¬ Conjecture23ForAgents .sbi 6 :=
  not_conjecture23_of .sbi sbi6_r sbi6_x0 sbi6_r_pos sbi6_not_fixedFrom
    sbi6_not_pseudoStableAfter

theorem not_theorem64iv_sbi_six : ¬ Theorem64ivForAgents .sbi 6 :=
  not_theorem64iv_of .sbi sbi6_r sbi6_x0 sbi6_r_pos sbi6_digraph_constant
    sbi6_not_fixedFrom sbi6_not_pseudoStableAfter

theorem sbi6_fvct (t : ℕ) : fvct .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) = sbi6_lim := by
  refine fvct_of_eigen _ _ _ _ sbi6_v _ (sbi6Rate ^ t) ?_ (by
    funext i
    rw [adj_mulVec, sbi6_neighbors]
    fin_cases i <;> simp [Finset.sum_insert, sbi6_lim] <;> norm_num) (by
    have hsq := sbi_sqrt249_sq
    funext i
    rw [adj_mulVec, sbi6_neighbors]
    unfold sbi6Rate
    fin_cases i <;> simp [Finset.sum_insert, sbi6_v] <;> nlinarith [hsq]) abs_sbi6Rate_lt_one
  rw [sbi6_closed_form]
  funext i
  simp

theorem sbi6_perStepFactor (t : ℕ) (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6))) :
    perStepFactor .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0) i t = sbi6Rate := by
  apply perStepFactor_of_closed_form _ _ _ _ _ _ _ _ (sbi6_fvct t)
    sbi6_closed_form sbi6Rate_neg.ne
  have hs : (0 : ℝ) ≤ Real.sqrt 249 := Real.sqrt_nonneg _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp [sbi6_v]
  all_goals (intro h; linarith)

end HK
