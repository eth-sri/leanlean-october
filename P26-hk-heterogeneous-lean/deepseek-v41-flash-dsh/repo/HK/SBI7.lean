module

public import HK.Basic

/-!
# The 7-agent SBI system (Hegarty–Ognissanti–Wedin §3)

`x(0) = (0, 15/2, 10 − φ/2, 11, 12 + φ/2, 29/2, 22)`, `r = (8, 4, 4, 8, 4, 4, 8)`, `φ = (1 + √5)/2`,
`λ = (1 − √5)/8`; `x(t) = (0, 7, 10, 11, 12, 15, 22) + (λᵗ/2) (0, 1, −φ, 0, φ, −1, 0)`. The middle
agent listens to agents 1–5 at even `t` and to 2, 3, 4 at odd `t`; the proximity digraph is never
eventually constant; agents 1, 2, 4, 5 alternate sides of their limits.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- The neighbourhood table at `t`: agent 3 listens to 1–5 at even `t`. -/
noncomputable def sbi7_T (t : ℕ) : Fin 7 → Finset (Fin 7) :=
  ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, if Even t then {1, 2, 3, 4, 5} else {2, 3, 4}, {2, 3, 4, 5},
    {3, 4, 5, 6}, {6}]

/-- The table at an even-time offset `0 < w ≤ 1/2`. -/
theorem sbi7_table_even (w : ℝ) (h0 : 0 < w) (h1 : w ≤ 1 / 2) :
    neighbors .sbi sbi7_r (fun i => sbi7_lim i + w * sbi_v i) = sbi7_T 0 := by
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have hsq := Real.goldenRatio_sq
  tabn sbi7_r, sbi7_lim, sbi_v, sbi7_T

/-- The table at an odd-time offset `(1 − φ)/8 ≤ w < 0`. -/
theorem sbi7_table_odd (w : ℝ) (h0 : (1 - Real.goldenRatio) / 8 ≤ w) (h1 : w < 0) :
    neighbors .sbi sbi7_r (fun i => sbi7_lim i + w * sbi_v i) = sbi7_T 1 := by
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have hsq := Real.goldenRatio_sq
  tabn sbi7_r, sbi7_lim, sbi_v, sbi7_T

theorem sbi7_step_even (w : ℝ) (h0 : 0 < w) (h1 : w ≤ 1 / 2) :
    step .sbi sbi7_r (fun i => sbi7_lim i + w * sbi_v i) =
      fun i => sbi7_lim i + ((1 - Real.goldenRatio) / 4 * w) * sbi_v i := by
  stps sbi7_table_even w h0 h1 | sbi7_lim, sbi_v, sbi7_T | 5

theorem sbi7_step_odd (w : ℝ) (h0 : (1 - Real.goldenRatio) / 8 ≤ w) (h1 : w < 0) :
    step .sbi sbi7_r (fun i => sbi7_lim i + w * sbi_v i) =
      fun i => sbi7_lim i + ((1 - Real.goldenRatio) / 4 * w) * sbi_v i := by
  stps sbi7_table_odd w h0 h1 | sbi7_lim, sbi_v, sbi7_T | 5

theorem sbi7_bounds (t : ℕ) : sbiRate ≤ sbiRate ^ t ∧ sbiRate ^ t ≤ 1 :=
  pow_bounds_of_neg sbiRate_mem.1 sbiRate_mem.2 t

chall sbi7_closed_form "have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  simpa [sbiRate_eq, div_eq_mul_inv] using traj_alt .sbi sbi7_r sbi7_x0 sbi7_lim sbi_v ((1 - Real.goldenRatio) / 4) (1 / 2) (by rw [← sbiRate_eq]; exact sbiRate_mem.1) (by rw [← sbiRate_eq]; exact sbiRate_mem.2) (by norm_num) (fun u h0 h1 => sbi7_step_even u h0 (by linarith)) (fun u h0 h1 => sbi7_step_odd u (by linarith) h1) (by init sbi7_x0, sbi7_lim, sbi_v) t"
  sbi7_neighbors "obtain ⟨h0, h1⟩ := sbi7_bounds t
  rw [sbi7_closed_form_internal]
  rcases Nat.even_or_odd t with ht | ht
  · rw [sbi7_table_even _ (by linarith [pow_pos_of_even sbiRate_mem.2 ht]) (by linarith)]
    simp [sbi7_T, ht]
  · rw [sbi7_table_odd _ (by rw [show (1 - Real.goldenRatio) / 8 = sbiRate / 2 by rw [sbiRate_eq]; ring]; linarith) (by linarith [pow_neg_of_odd sbiRate_mem.2 ht])]
    simp [sbi7_T, Nat.not_even_iff_odd.mpr ht]"

theorem sbi7_T_alt (t : ℕ) : sbi7_T (t + 1) ≠ sbi7_T t := by
  rcases Nat.even_or_odd t with ht | ht
  · have h1 : ¬ Even (t + 1) := Nat.not_even_iff_odd.mpr ht.add_one
    simp only [sbi7_T, h1, ht]
    decide
  · have h1 : Even (t + 1) := ht.add_one
    have h2 : ¬ Even t := Nat.not_even_iff_odd.mpr ht
    simp only [sbi7_T, h1, h2]
    decide

theorem sbi7_digraph_not_eventually_constant_internal (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) ≠
      proximityDigraph .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 τ) :=
  digraph_not_const_of_alt _ _ _ _ sbi7_neighbors_internal sbi7_T_alt τ

theorem sbi7_adj_lim (t : ℕ) :
    (adjMatrix .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t)).mulVec sbi7_lim = sbi7_lim := by
  funext i
  rw [adj_mulVec, sbi7_neighbors_internal]
  fin_cases i
  · simp [sbi7_T, sbi7_lim]
  · simp [Finset.sum_insert, sbi7_T, sbi7_lim]; norm_num
  · simp [Finset.sum_insert, sbi7_T, sbi7_lim]; norm_num
  · simp only [sbi7_T]; split <;> simp [Finset.sum_insert, sbi7_lim] <;> norm_num
  · simp [Finset.sum_insert, sbi7_T, sbi7_lim]; norm_num
  · simp [Finset.sum_insert, sbi7_T, sbi7_lim]; norm_num
  · simp [sbi7_T, sbi7_lim]

theorem sbi7_adj_v (t : ℕ) :
    (adjMatrix .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t)).mulVec sbi_v = sbiRate • sbi_v := by
  funext i
  rw [adj_mulVec, sbi7_neighbors_internal, sbiRate_eq]
  fin_cases i
  · simp [sbi7_T, sbi_v]
  · simp [Finset.sum_insert, sbi7_T, sbi_v]; ring
  · simp [Finset.sum_insert, sbi7_T, sbi_v]; sq 5
  · simp only [sbi7_T]; split <;> simp [Finset.sum_insert, sbi_v]
  · simp [Finset.sum_insert, sbi7_T, sbi_v]; sq 5
  · simp [Finset.sum_insert, sbi7_T, sbi_v]; ring
  · simp [sbi7_T, sbi_v]

theorem sbi7_fvct_internal (t : ℕ) : fvct .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) = sbi7_lim := by
  refine fvct_of_adj _ _ _ _ _ sbiRate (sbiRate ^ t / 2) ?_ (sbi7_adj_lim t) (sbi7_adj_v t)
    (abs_lt.mpr ⟨sbiRate_mem.1, by linarith [sbiRate_mem.2]⟩)
  rw [sbi7_closed_form_internal]
  rfl

theorem sbi7_rate_tendsto : Tendsto (fun t : ℕ => sbiRate ^ t / 2) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using tendsto_pow_mul_of_neg sbiRate_mem.1 sbiRate_mem.2 (1 / 2)

theorem sbi7_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbi sbi7_r sbi7_x0) τ :=
  not_fixedFrom_of_geom _ sbi7_lim sbi_v (fun t => sbiRate ^ t / 2) sbi7_closed_form_internal
    (by simpa [div_eq_mul_inv] using alternating sbiRate (1 / 2) sbiRate_mem.2 (by norm_num)) 1
    (by simp [sbi_v]) τ

theorem sbi7_not_pseudoStableAfter (xinf : Fin 7 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbi sbi7_r sbi7_x0) xinf τ :=
  not_pseudoStable_of_geom _ sbi7_lim sbi_v (fun t => sbiRate ^ t / 2) sbi7_rate_tendsto
    sbi7_closed_form_internal
    (by simpa [div_eq_mul_inv] using alternating sbiRate (1 / 2) sbiRate_mem.2 (by norm_num)) xinf τ

theorem sbi7_r_pos : ∀ i, 0 < sbi7_r i := by
  intro i
  fin_cases i <;> simp [sbi7_r]

end HK
