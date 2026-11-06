module

public import HK.Basic

@[expose] public section

namespace HK

open Filter Topology

theorem sbi7_table_even (w : ℝ) (hw0 : 0 < w) (hw1 : w ≤ 1 / 2) :
    neighbors .sbi sbi7_r (fun i => sbi7_lim i + w * sbi_v i) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {1, 2, 3, 4, 5}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := by
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have hp0 : 0 < w * Real.goldenRatio := mul_pos hw0 (by linarith)
  have hp1 : w * Real.goldenRatio ≤ 1 := by nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbi7_r, sbi7_lim, sbi_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem sbi7_table_odd (w : ℝ) (hw0 : (1 - Real.goldenRatio) / 8 ≤ w) (hw1 : w < 0) :
    neighbors .sbi sbi7_r (fun i => sbi7_lim i + w * sbi_v i) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := by
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have hsq := Real.goldenRatio_sq
  have hp1 : w * Real.goldenRatio < 0 := mul_neg_of_neg_of_pos hw1 (by linarith)
  have hm := mul_le_mul_of_nonneg_right hw0 (le_of_lt (lt_trans one_pos hφ1))
  have hp0 : -1 / 8 ≤ w * Real.goldenRatio := by nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbi7_r, sbi7_lim, sbi_v, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem sbi7_step_of_table (w : ℝ) (S3 : Finset (Fin 7))
    (hS : S3 = {1, 2, 3, 4, 5} ∨ S3 = {2, 3, 4})
    (htab : neighbors .sbi sbi7_r (fun i => sbi7_lim i + w * sbi_v i) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, S3, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}]) :
    step .sbi sbi7_r (fun i => sbi7_lim i + w * sbi_v i) =
      fun i => sbi7_lim i + ((1 - Real.goldenRatio) / 4 * w) * sbi_v i := by
  have hsq := Real.goldenRatio_sq
  have hsqw := congrArg (fun x : ℝ => w * x) hsq
  funext i
  rw [step_apply, htab]
  rcases hS with rfl | rfl <;> fin_cases i <;>
    simp [Finset.sum_insert, sbi7_lim, sbi_v] <;> nlinarith [hsqw]

theorem sbi7_closed_form (t : ℕ) :
    traj .sbi sbi7_r sbi7_x0 t = fun i => sbi7_lim i + sbiRate ^ t / 2 * sbi_v i := by
  induction t with
  | zero =>
    funext i
    fin_cases i <;> simp [traj, sbi7_x0, sbi7_lim, sbi_v] <;> ring
  | succ t ih =>
    rw [traj_succ, ih]
    rcases Nat.even_or_odd t with ht | ht
    · obtain ⟨h0, h1⟩ := sbiRate_pow_even ht
      rw [sbi7_step_of_table _ _ (Or.inl rfl) (sbi7_table_even _ h0 h1)]
      funext i
      rw [pow_succ, sbiRate_eq]
      ring
    · obtain ⟨h0, h1⟩ := sbiRate_pow_odd ht
      rw [sbi7_step_of_table _ _ (Or.inr rfl) (sbi7_table_odd _ h0 h1)]
      funext i
      rw [pow_succ, sbiRate_eq]
      ring

theorem sbi7_neighbors (t : ℕ) :
    neighbors .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, if Even t then {1, 2, 3, 4, 5} else {2, 3, 4},
        {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := by
  rw [sbi7_closed_form]
  rcases Nat.even_or_odd t with ht | ht
  · obtain ⟨h0, h1⟩ := sbiRate_pow_even ht
    rw [ite_eq_left ht, sbi7_table_even _ h0 h1]
  · obtain ⟨h0, h1⟩ := sbiRate_pow_odd ht
    rw [ite_eq_right (Nat.not_even_iff_odd.mpr ht), sbi7_table_odd _ h0 h1]

theorem sbi7_digraph_not_eventually_constant (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) ≠
      proximityDigraph .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 τ) := by
  refine ⟨τ + 1, Nat.le_succ τ, fun h => ?_⟩
  have h2 := congrFun (congrFun (congrArg Digraph.Adj h) 3) 1
  simp only [proximityDigraph, sbi7_neighbors] at h2
  rcases Nat.even_or_odd τ with ht | ht
  · have h' : ¬ Even (τ + 1) := Nat.not_even_iff_odd.mpr ht.add_one
    simp [h', ht] at h2
  · have h' : Even (τ + 1) := ht.add_one
    have h'' : ¬ Even τ := Nat.not_even_iff_odd.mpr ht
    simp [h', h''] at h2

theorem sbi7_closed_form' (t : ℕ) :
    traj .sbi sbi7_r sbi7_x0 t = fun i => sbi7_lim i + sbiRate ^ t * (1 / 2) * sbi_v i := by
  rw [sbi7_closed_form]
  funext i
  ring

theorem sbi7_rate_tendsto : Tendsto (fun t : ℕ => sbiRate ^ t * (1 / 2)) atTop (𝓝 0) := by
  simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one sbiRate_abs_lt_one).mul_const (1 / 2 : ℝ)

theorem sbi7_not_fixedFrom (τ : ℕ) : ¬ FixedFrom (traj .sbi sbi7_r sbi7_x0) τ :=
  not_fixedFrom_of_closed_form _ _ sbi_v _ sbi7_closed_form'
    (alternating _ _ sbiRate_neg (by norm_num)) 1 (by simp [sbi_v]) τ

theorem sbi7_not_pseudoStableAfter (xinf : Fin 7 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbi sbi7_r sbi7_x0) xinf τ :=
  not_pseudoStable_of_closed_form _ _ sbi_v _ sbi7_rate_tendsto sbi7_closed_form'
    (alternating _ _ sbiRate_neg (by norm_num)) xinf τ

theorem sbi7_r_pos : ∀ i, 0 < sbi7_r i := by
  intro i
  fin_cases i <;> simp [sbi7_r]

end HK
