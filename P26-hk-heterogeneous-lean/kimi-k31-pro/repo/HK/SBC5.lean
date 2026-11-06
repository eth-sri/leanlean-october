module

public import HK.Basic

@[expose] public section

namespace HK

theorem sbc5_r_pos : ∀ i, 0 < sbc5_r i := by
  intro i
  fin_cases i <;> simp [sbc5_r]

theorem sbc_sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem sbc_sqrt_two_bounds : 1.4 < Real.sqrt 2 ∧ Real.sqrt 2 < 1.5 := by
  constructor <;> norm_num [Real.lt_sqrt, Real.sqrt_lt']

theorem sbc5Rate_neg : sbc5Rate < 0 := by
  unfold sbc5Rate
  linarith [sbc_sqrt_two_bounds.1]

theorem abs_sbc5Rate_lt_one : |sbc5Rate| < 1 := by
  unfold sbc5Rate
  rw [abs_lt]
  constructor <;> linarith [sbc_sqrt_two_bounds.1, sbc_sqrt_two_bounds.2]

theorem sbc_rate_gt : -1 / 6 < sbc5Rate := by
  unfold sbc5Rate
  linarith [sbc_sqrt_two_bounds.2]

theorem sbc_pow_bounds (t : ℕ) : sbc5Rate ≤ sbc5Rate ^ t ∧ sbc5Rate ^ t ≤ 1 :=
  pow_bounds_of_neg (by linarith [sbc_rate_gt]) sbc5Rate_neg t

theorem sbc_table (u : ℝ) (hu0 : sbc5Rate ≤ u) (hu1 : u ≤ 1) :
    neighbors .sbc sbc5_r (fun i => sbc5_lim i + u * sbc5_v i) =
      ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}] := by
  obtain ⟨hs1, hs2⟩ := sbc_sqrt_two_bounds
  have hr := sbc_rate_gt
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hp0 : -1 / 2 ≤ u * Real.sqrt 2 := by nlinarith
  have hp1 : u * Real.sqrt 2 ≤ 3 / 2 := by nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbc5_r, sbc5_lim, sbc5_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem sbc_step (u : ℝ) (hu0 : sbc5Rate ≤ u) (hu1 : u ≤ 1) :
    step .sbc sbc5_r (fun i => sbc5_lim i + u * sbc5_v i) =
      fun i => sbc5_lim i + (sbc5Rate * u) * sbc5_v i := by
  have h2 := sbc_sqrt_two_sq
  have h2u := congrArg (fun x : ℝ => u * x) h2
  funext i
  rw [step_apply, sbc_table u hu0 hu1]
  fin_cases i <;> simp [Finset.sum_insert, sbc5_lim, sbc5_v, sbc5Rate] <;> nlinarith [h2u]

theorem sbc5_closed_form (t : ℕ) :
    traj .sbc sbc5_r sbc5_x0 t = fun i => sbc5_lim i + sbc5Rate ^ t * sbc5_v i := by
  induction t with
  | zero =>
    funext i
    fin_cases i <;> simp [traj, sbc5_x0, sbc5_lim, sbc5_v] <;> ring
  | succ t ih =>
    obtain ⟨h0, h1⟩ := sbc_pow_bounds t
    rw [traj_succ, ih, sbc_step _ h0 h1]
    funext i
    rw [pow_succ]
    ring

theorem sbc5_neighbors (t : ℕ) :
    neighbors .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) =
      ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}] := by
  obtain ⟨h0, h1⟩ := sbc_pow_bounds t
  rw [sbc5_closed_form, sbc_table _ h0 h1]

theorem sbc5_digraph_constant (t : ℕ) :
    proximityDigraph .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) =
      proximityDigraph .sbc sbc5_r sbc5_x0 :=
  digraph_constant_of_neighbors _ _ _ _ sbc5_neighbors t

theorem sbc5_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbc sbc5_r sbc5_x0) τ :=
  not_fixedFrom_of_pow _ _ sbc5_v _ sbc5_closed_form sbc5Rate_neg
    1 (by simp [sbc5_v]) τ

theorem sbc5_not_pseudoStableAfter (xinf : Fin 5 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc5_r sbc5_x0) xinf τ :=
  not_pseudoStable_of_pow _ _ sbc5_v _ abs_sbc5Rate_lt_one sbc5_closed_form
    sbc5Rate_neg xinf τ

theorem not_conjecture23_sbc_five : ¬ Conjecture23ForAgents .sbc 5 :=
  not_conjecture23_of .sbc sbc5_r sbc5_x0 sbc5_r_pos sbc5_not_fixedFrom
    sbc5_not_pseudoStableAfter

theorem not_theorem64iv_sbc_five : ¬ Theorem64ivForAgents .sbc 5 :=
  not_theorem64iv_of .sbc sbc5_r sbc5_x0 sbc5_r_pos sbc5_digraph_constant
    sbc5_not_fixedFrom sbc5_not_pseudoStableAfter

theorem sbc5_fvct (t : ℕ) : fvct .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) = sbc5_lim := by
  refine fvct_of_eigen _ _ _ _ sbc5_v _ (sbc5Rate ^ t) ?_ (by
    funext i
    rw [adj_mulVec, sbc5_neighbors]
    fin_cases i <;> simp [Finset.sum_insert, sbc5_lim] <;> norm_num) (by
    have h2 := sbc_sqrt_two_sq
    funext i
    rw [adj_mulVec, sbc5_neighbors]
    fin_cases i <;> simp [Finset.sum_insert, sbc5_v, sbc5Rate] <;> nlinarith [h2])
    abs_sbc5Rate_lt_one
  rw [sbc5_closed_form]
  funext i
  simp

theorem sbc5_perStepFactor (t : ℕ) (i : Fin 5) (hi : i ∈ ({1, 2, 3} : Finset (Fin 5))) :
    perStepFactor .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0) i t = sbc5Rate := by
  apply perStepFactor_of_closed_form _ _ _ _ _ _ _ _ (sbc5_fvct t)
    sbc5_closed_form sbc5Rate_neg.ne
  fin_cases i <;> simp_all [sbc5_v]

end HK
