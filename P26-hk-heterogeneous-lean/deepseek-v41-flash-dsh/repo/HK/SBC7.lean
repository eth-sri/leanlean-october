module

public import HK.Basic

/-!
# The 7-agent SBC system (Hegarty–Ognissanti–Wedin §2)

`x(0) = (0, 38, 69, 84, 99, 130, 168)`, `r = (18, 42, 48, 12, 48, 42, 18)`;
`x(t) = (0, 36, 72, 84, 96, 132, 168) + (−1/6)ᵗ (0, 2, −3, 0, 3, −2, 0)`. The middle agent (index 3)
listens to itself alone at even `t` and to indices 2, 3, 4 at odd `t`; the proximity digraph is never
eventually constant; agents 1, 2, 4, 5 alternate sides of their limits.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- The neighbourhood table at `t`: agent 3 listens to itself alone at even `t`. -/
noncomputable def sbc7_T (t : ℕ) : Fin 7 → Finset (Fin 7) :=
  ![{0}, {0, 1, 2}, {1, 2, 3, 4}, if Even t then {3} else {2, 3, 4}, {2, 3, 4, 5}, {4, 5, 6}, {6}]

/-- The table at an even-time offset `0 < u ≤ 1`. -/
theorem sbc7_table_even (u : ℝ) (h0 : 0 < u) (h1 : u ≤ 1) :
    neighbors .sbc sbc7_r (fun i => sbc7_lim i + u * sbc7_v i) = sbc7_T 0 := by
  tab sbc7_r, sbc7_lim, sbc7_v, sbc7_T

/-- The table at an odd-time offset `-1/6 ≤ u < 0`. -/
theorem sbc7_table_odd (u : ℝ) (h0 : -1 / 6 ≤ u) (h1 : u < 0) :
    neighbors .sbc sbc7_r (fun i => sbc7_lim i + u * sbc7_v i) = sbc7_T 1 := by
  tab sbc7_r, sbc7_lim, sbc7_v, sbc7_T

theorem sbc7_step_even (u : ℝ) (h0 : 0 < u) (h1 : u ≤ 1) :
    step .sbc sbc7_r (fun i => sbc7_lim i + u * sbc7_v i) =
      fun i => sbc7_lim i + (-1 / 6 * u) * sbc7_v i := by
  stp sbc7_table_even u h0 h1 | sbc7_lim, sbc7_v, sbc7_T

theorem sbc7_step_odd (u : ℝ) (h0 : -1 / 6 ≤ u) (h1 : u < 0) :
    step .sbc sbc7_r (fun i => sbc7_lim i + u * sbc7_v i) =
      fun i => sbc7_lim i + (-1 / 6 * u) * sbc7_v i := by
  stp sbc7_table_odd u h0 h1 | sbc7_lim, sbc7_v, sbc7_T

theorem sbc7_rate : -1 < (-1 / 6 : ℝ) ∧ (-1 / 6 : ℝ) < 0 := ⟨by norm_num, by norm_num⟩

theorem sbc7_bounds (t : ℕ) : -1 / 6 ≤ (-1 / 6 : ℝ) ^ t ∧ (-1 / 6 : ℝ) ^ t ≤ 1 :=
  pow_bounds_of_neg sbc7_rate.1 sbc7_rate.2 t

chall sbc7_closed_form "simpa using traj_alt .sbc sbc7_r sbc7_x0 sbc7_lim sbc7_v (-1 / 6) 1 sbc7_rate.1 sbc7_rate.2 one_pos (fun u h0 h1 => sbc7_step_even u h0 h1) (fun u h0 h1 => sbc7_step_odd u (by linarith) h1) (by init sbc7_x0, sbc7_lim, sbc7_v) t"
  sbc7_neighbors "obtain ⟨h0, h1⟩ := sbc7_bounds t; rw [sbc7_closed_form_internal]
  rcases Nat.even_or_odd t with ht | ht
  · rw [ite_eq_left ht, sbc7_table_even _ (pow_pos_of_even sbc7_rate.2 ht) h1]; simp [sbc7_T]
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr ht), sbc7_table_odd _ h0 (pow_neg_of_odd sbc7_rate.2 ht)]; simp [sbc7_T]"

theorem sbc7_T_alt (t : ℕ) : sbc7_T (t + 1) ≠ sbc7_T t := by
  rcases Nat.even_or_odd t with ht | ht
  · have h1 : ¬ Even (t + 1) := Nat.not_even_iff_odd.mpr ht.add_one
    simp only [sbc7_T, h1, ht]
    decide
  · have h1 : Even (t + 1) := ht.add_one
    have h2 : ¬ Even t := Nat.not_even_iff_odd.mpr ht
    simp only [sbc7_T, h1, h2]
    decide

/-- §2: the proximity digraph is never eventually constant (`t = τ + 1` differs from `τ`). -/
theorem sbc7_digraph_not_eventually_constant_internal (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) ≠
      proximityDigraph .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 τ) :=
  digraph_not_const_of_alt _ _ _ _ sbc7_neighbors_internal sbc7_T_alt τ

theorem sbc7_adj_lim (t : ℕ) :
    (adjMatrix .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t)).mulVec sbc7_lim = sbc7_lim := by
  funext i
  rw [adj_mulVec, sbc7_neighbors_internal]
  fin_cases i
  · simp [sbc7_T, sbc7_lim]
  · simp [Finset.sum_insert, sbc7_T, sbc7_lim]; norm_num
  · simp [Finset.sum_insert, sbc7_T, sbc7_lim]; norm_num
  · simp only [sbc7_T]; split <;> simp [Finset.sum_insert, sbc7_lim] <;> norm_num
  · simp [Finset.sum_insert, sbc7_T, sbc7_lim]; norm_num
  · simp [Finset.sum_insert, sbc7_T, sbc7_lim]; norm_num
  · simp [sbc7_T, sbc7_lim]

theorem sbc7_adj_v (t : ℕ) :
    (adjMatrix .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t)).mulVec sbc7_v = (-1 / 6 : ℝ) • sbc7_v := by
  funext i
  rw [adj_mulVec, sbc7_neighbors_internal]
  fin_cases i
  · simp [sbc7_T, sbc7_v]
  · simp [Finset.sum_insert, sbc7_T, sbc7_v]; norm_num
  · simp [Finset.sum_insert, sbc7_T, sbc7_v]; norm_num
  · simp only [sbc7_T]; split <;> simp [Finset.sum_insert, sbc7_v]
  · simp [Finset.sum_insert, sbc7_T, sbc7_v]; norm_num
  · simp [Finset.sum_insert, sbc7_T, sbc7_v]; norm_num
  · simp [sbc7_T, sbc7_v]

theorem sbc7_fvct (t : ℕ) : fvct .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) = sbc7_lim := by
  refine fvct_of_adj _ _ _ _ _ (-1 / 6) ((-1 / 6 : ℝ) ^ t) ?_ (sbc7_adj_lim t) (sbc7_adj_v t)
    (by norm_num)
  rw [sbc7_closed_form_internal]
  rfl

theorem sbc7_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbc sbc7_r sbc7_x0) τ :=
  not_fixedFrom_of_geom1 _ sbc7_lim sbc7_v (-1 / 6) sbc7_rate.2 sbc7_closed_form_internal 1
    (by simp [sbc7_v]) τ

theorem sbc7_not_pseudoStableAfter (xinf : Fin 7 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc7_r sbc7_x0) xinf τ :=
  not_pseudoStable_of_geom1 _ sbc7_lim sbc7_v (-1 / 6) sbc7_rate.1 sbc7_rate.2 sbc7_closed_form_internal
    xinf τ

theorem sbc7_r_pos : ∀ i, 0 < sbc7_r i := by
  intro i
  fin_cases i <;> simp [sbc7_r]

end HK
