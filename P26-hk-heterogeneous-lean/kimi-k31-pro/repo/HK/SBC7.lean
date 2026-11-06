module

public import HK.Basic

@[expose] public section

namespace HK

theorem sbc7_table_even (u : ℝ) (h0 : 0 < u) (h1 : u ≤ 1) :
    neighbors .sbc sbc7_r (fun i => sbc7_lim i + u * sbc7_v i) =
      ![{0}, {0, 1, 2}, {1, 2, 3, 4}, {3}, {2, 3, 4, 5}, {4, 5, 6}, {6}] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbc7_r, sbc7_lim, sbc7_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem sbc7_table_odd (u : ℝ) (h0 : -1 / 6 ≤ u) (h1 : u < 0) :
    neighbors .sbc sbc7_r (fun i => sbc7_lim i + u * sbc7_v i) =
      ![{0}, {0, 1, 2}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {4, 5, 6}, {6}] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbc7_r, sbc7_lim, sbc7_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem sbc7_step_even (u : ℝ) (h0 : 0 < u) (h1 : u ≤ 1) :
    step .sbc sbc7_r (fun i => sbc7_lim i + u * sbc7_v i) =
      fun i => sbc7_lim i + (-1 / 6 * u) * sbc7_v i := by
  funext i
  rw [step_apply, sbc7_table_even u h0 h1]
  fin_cases i <;> simp [Finset.sum_insert, sbc7_lim, sbc7_v] <;> ring

theorem sbc7_step_odd (u : ℝ) (h0 : -1 / 6 ≤ u) (h1 : u < 0) :
    step .sbc sbc7_r (fun i => sbc7_lim i + u * sbc7_v i) =
      fun i => sbc7_lim i + (-1 / 6 * u) * sbc7_v i := by
  funext i
  rw [step_apply, sbc7_table_odd u h0 h1]
  fin_cases i <;> simp [Finset.sum_insert, sbc7_lim, sbc7_v] <;> ring

theorem sbc7_closed_form (t : ℕ) :
    traj .sbc sbc7_r sbc7_x0 t = fun i => sbc7_lim i + (-1 / 6 : ℝ) ^ t * sbc7_v i := by
  induction t with
  | zero =>
    funext i
    fin_cases i <;> simp [traj, sbc7_x0, sbc7_lim, sbc7_v] <;> norm_num
  | succ t ih =>
    rw [traj_succ, ih, pow_succ]
    rcases Nat.even_or_odd t with ht | ht
    · obtain ⟨h0, h1⟩ := pow_even ht
      rw [sbc7_step_even _ h0 h1]
      funext i
      ring
    · obtain ⟨h0, h1⟩ := pow_odd ht
      rw [sbc7_step_odd _ h0 h1]
      funext i
      ring

theorem sbc7_neighbors (t : ℕ) :
    neighbors .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) =
      ![{0}, {0, 1, 2}, {1, 2, 3, 4}, if Even t then {3} else {2, 3, 4}, {2, 3, 4, 5},
        {4, 5, 6}, {6}] := by
  rw [sbc7_closed_form]
  rcases Nat.even_or_odd t with ht | ht
  · obtain ⟨h0, h1⟩ := pow_even ht
    rw [ite_eq_left ht, sbc7_table_even _ h0 h1]
  · obtain ⟨h0, h1⟩ := pow_odd ht
    rw [ite_eq_right (Nat.not_even_iff_odd.mpr ht), sbc7_table_odd _ h0 h1]

theorem sbc7_digraph_not_eventually_constant (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) ≠
      proximityDigraph .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 τ) := by
  refine ⟨τ + 1, Nat.le_succ τ, fun h => ?_⟩
  have h2 := congrFun (congrFun (congrArg Digraph.Adj h) 3) 2
  simp only [proximityDigraph, sbc7_neighbors] at h2
  rcases Nat.even_or_odd τ with ht | ht
  · have h' : ¬ Even (τ + 1) := Nat.not_even_iff_odd.mpr ht.add_one
    simp [h', ht] at h2
  · have h' : Even (τ + 1) := ht.add_one
    have h'' : ¬ Even τ := Nat.not_even_iff_odd.mpr ht
    simp [h', h''] at h2

theorem sbc7_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbc sbc7_r sbc7_x0) τ :=
  not_fixedFrom_of_pow _ _ sbc7_v _ sbc7_closed_form (by norm_num)
    1 (by simp [sbc7_v]) τ

theorem sbc7_not_pseudoStableAfter (xinf : Fin 7 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc7_r sbc7_x0) xinf τ :=
  not_pseudoStable_of_pow _ _ sbc7_v _ abs_negSixth sbc7_closed_form (by norm_num) xinf τ

theorem sbc7_r_pos : ∀ i, 0 < sbc7_r i := by
  intro i
  fin_cases i <;> simp [sbc7_r]

end HK
