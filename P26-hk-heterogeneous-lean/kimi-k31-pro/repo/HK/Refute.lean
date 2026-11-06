module

public import HK.SBC7
public import HK.SBI7
public import HK.SBC6
public import HK.SBI7b
public import HK.SBC5
public import HK.SBI6
public import HK.Generic

@[expose] public section

namespace HK

open Filter Topology

theorem not_conjecture22_sbc : ¬ Conjecture22For .sbc := fun h =>
  not_conjecture22_of .sbc sbc7_r sbc7_x0 sbc7_r_pos
    sbc7_digraph_not_eventually_constant (h 7)

theorem not_conjecture23_sbc : ¬ Conjecture23For .sbc := fun h =>
  not_conjecture23_of .sbc sbc7_r sbc7_x0 sbc7_r_pos sbc7_not_fixedFrom
    sbc7_not_pseudoStableAfter (h 7)

theorem not_conjecture22_sbi : ¬ Conjecture22For .sbi := fun h =>
  not_conjecture22_of .sbi sbi7_r sbi7_x0 sbi7_r_pos
    sbi7_digraph_not_eventually_constant (h 7)

theorem not_conjecture23_sbi : ¬ Conjecture23For .sbi := fun h =>
  not_conjecture23_of .sbi sbi7_r sbi7_x0 sbi7_r_pos sbi7_not_fixedFrom
    sbi7_not_pseudoStableAfter (h 7)

theorem not_theorem64iv_sbc : ¬ Theorem64ivFor .sbc := fun h =>
  not_theorem64iv_of .sbc sbc6_r sbc6_x0 (by intro i; fin_cases i <;> simp [sbc6_r])
    sbc6_digraph_constant sbc6_not_fixedFrom sbc6_not_pseudoStableAfter (h 6)

theorem not_theorem64iv_sbi : ¬ Theorem64ivFor .sbi := fun h =>
  not_theorem64iv_of .sbi sbi7b_r sbi7b_x0 (by intro i; fin_cases i <;> simp [sbi7b_r])
    sbi7b_digraph_constant sbi7b_not_fixedFrom sbi7b_not_pseudoStableAfter (h 7)

theorem not_conjecture22 : ¬ Conjecture22 := fun h => not_conjecture22_sbc (h .sbc)
theorem not_conjecture23 : ¬ Conjecture23 := fun h => not_conjecture23_sbc (h .sbc)
theorem not_theorem64iv : ¬ Theorem64iv := fun h => not_theorem64iv_sbc (h .sbc)

theorem not_theorem64iv_literal_sbc : ¬ Theorem64ivLiteralFor .sbc :=
  not_theorem64iv_literal_of .sbc not_theorem64iv_sbc

theorem not_theorem64iv_literal_sbi : ¬ Theorem64ivLiteralFor .sbi :=
  not_theorem64iv_literal_of .sbi not_theorem64iv_sbi

theorem not_theorem64iv_literal : ¬ Theorem64ivLiteral :=
  fun h => not_theorem64iv_literal_sbc (h .sbc)

theorem tendsto_limits :
    Tendsto (traj .sbc sbc7_r sbc7_x0) atTop (𝓝 sbc7_lim) ∧
    Tendsto (traj .sbi sbi7_r sbi7_x0) atTop (𝓝 sbi7_lim) ∧
    Tendsto (traj .sbc sbc6_r sbc6_x0) atTop (𝓝 sbc6_lim) ∧
    Tendsto (traj .sbi sbi7b_r sbi7b_x0) atTop (𝓝 sbi7b_lim) :=
  ⟨tendsto_of_pow_closed_form _ _ sbc7_v _ abs_negSixth sbc7_closed_form,
    tendsto_of_closed_form _ _ sbi_v _ sbi7_rate_tendsto sbi7_closed_form',
    tendsto_of_pow_closed_form _ _ sbc6_v _ abs_negSixth sbc6_closed_form,
    tendsto_of_pow_closed_form _ _ sbi_v _ sbiRate_abs_lt_one sbi7b_closed_form⟩

theorem not_fixedFrom (τ : ℕ) :
    ¬ FixedFrom (traj .sbc sbc7_r sbc7_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi7_r sbi7_x0) τ ∧
    ¬ FixedFrom (traj .sbc sbc6_r sbc6_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi7b_r sbi7b_x0) τ :=
  ⟨sbc7_not_fixedFrom τ, sbi7_not_fixedFrom τ, sbc6_not_fixedFrom τ, sbi7b_not_fixedFrom τ⟩

theorem not_pseudoStableAfter (xinf : Fin 7 → ℝ) (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc7_r sbc7_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi7_r sbi7_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbc sbc6_r sbc6_x0) yinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi7b_r sbi7b_x0) xinf τ :=
  ⟨sbc7_not_pseudoStableAfter xinf τ, sbi7_not_pseudoStableAfter xinf τ,
    sbc6_not_pseudoStableAfter yinf τ, sbi7b_not_pseudoStableAfter xinf τ⟩

theorem ref_equiTopologyDistance_pos_of {n : ℕ} (r z : Fin n → ℝ) (i j : Fin n) (hij : j ≠ i)
    (c : ℝ) (hc : 0 < c)
    (h : ∀ k, k ≠ i → c ≤ |(|z i - z k|) - r i| ∧ c ≤ |(|z i - z k|) - r k|) :
    0 < equiTopologyDistance r z i := by
  unfold equiTopologyDistance
  have hS : c ≤ sInf (equiTopologySet r z i) := by
    refine le_csInf ⟨_, j, hij, Or.inl rfl⟩ ?_
    rintro d ⟨k, hk, rfl | rfl⟩
    · exact (h k hk).1
    · exact (h k hk).2
  linarith

theorem alternating_fvct (t : ℕ) :
    fvct .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) = sbc7_lim ∧
    fvct .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) = sbi7_lim :=
  ⟨(by
    refine fvct_of_eigen _ _ _ _ sbc7_v _ ((-1 / 6 : ℝ) ^ t) ?_ (by
      funext i
      rw [adj_mulVec, sbc7_neighbors]
      split_ifs <;> fin_cases i <;> simp [Finset.sum_insert, sbc7_lim] <;> norm_num) (by
      funext i
      rw [adj_mulVec, sbc7_neighbors]
      split_ifs <;> fin_cases i <;> simp [Finset.sum_insert, sbc7_v] <;> norm_num) abs_negSixth
    rw [sbc7_closed_form]
    funext i
    simp), by
    refine fvct_of_eigen _ _ _ _ sbi_v _ (sbiRate ^ t / 2) ?_ (by
      funext i
      rw [adj_mulVec, sbi7_neighbors]
      split_ifs <;> fin_cases i <;> simp [Finset.sum_insert, sbi7_lim] <;> norm_num) (by
      have hsq := Real.goldenRatio_sq
      funext i
      rw [adj_mulVec, sbi7_neighbors, sbiRate_eq]
      split_ifs <;> fin_cases i <;> simp [Finset.sum_insert, sbi_v] <;> nlinarith [hsq])
      sbiRate_abs_lt_one
    rw [sbi7_closed_form]
    funext i
    simp⟩

theorem equiTopologyDistance_pos :
    (∀ i, 0 < equiTopologyDistance sbc6_r sbc6_lim i) ∧
    (∀ i, 0 < equiTopologyDistance sbi7b_r sbi7b_lim i) :=
  ⟨fun i => by
    refine ref_equiTopologyDistance_pos_of _ _ i (i + 1) (by fin_cases i <;> decide) 10
      (by norm_num) ?_
    intro k hk
    fin_cases i <;> fin_cases k <;> first | exact absurd rfl hk | norm_num [sbc6_r, sbc6_lim],
  fun i => by
    refine ref_equiTopologyDistance_pos_of _ _ i (i + 1) (by fin_cases i <;> decide) 5
      (by norm_num) ?_
    intro k hk
    fin_cases i <;> fin_cases k <;> first | exact absurd rfl hk | norm_num [sbi7b_r, sbi7b_lim]⟩

theorem equiTopologyDistance_eq_zero :
    (∀ i ∈ ({2, 3, 4} : Finset (Fin 7)), equiTopologyDistance sbc7_r sbc7_lim i = 0) ∧
    (∀ i ∈ ({1, 3, 5} : Finset (Fin 7)), equiTopologyDistance sbi7_r sbi7_lim i = 0) := by
  constructor <;> intro i hi <;> simp only [Finset.mem_insert, Finset.mem_singleton] at hi <;>
    rcases hi with rfl | rfl | rfl
  all_goals
    first
    | exact equiTopologyDistance_eq_zero_of sbc7_r sbc7_lim 2 3 (by decide)
        (Or.inr (by norm_num [sbc7_r, sbc7_lim]))
    | exact equiTopologyDistance_eq_zero_of sbc7_r sbc7_lim 3 2 (by decide)
        (Or.inl (by norm_num [sbc7_r, sbc7_lim]))
    | exact equiTopologyDistance_eq_zero_of sbc7_r sbc7_lim 4 3 (by decide)
        (Or.inr (by norm_num [sbc7_r, sbc7_lim]))
    | exact equiTopologyDistance_eq_zero_of sbi7_r sbi7_lim 1 3 (by decide)
        (Or.inl (by norm_num [sbi7_r, sbi7_lim]))
    | exact equiTopologyDistance_eq_zero_of sbi7_r sbi7_lim 3 1 (by decide)
        (Or.inr (by norm_num [sbi7_r, sbi7_lim]))
    | exact equiTopologyDistance_eq_zero_of sbi7_r sbi7_lim 5 3 (by decide)
        (Or.inl (by norm_num [sbi7_r, sbi7_lim]))

theorem not_conjecture22_sbc_seven : ¬ Conjecture22ForAgents .sbc 7 :=
  not_conjecture22_of .sbc sbc7_r sbc7_x0 sbc7_r_pos sbc7_digraph_not_eventually_constant

theorem not_conjecture22_sbi_seven : ¬ Conjecture22ForAgents .sbi 7 :=
  not_conjecture22_of .sbi sbi7_r sbi7_x0 sbi7_r_pos sbi7_digraph_not_eventually_constant

theorem small_tendsto :
    Tendsto (traj .sbc sbc5_r sbc5_x0) atTop (𝓝 sbc5_lim) ∧
    Tendsto (traj .sbi sbi6_r sbi6_x0) atTop (𝓝 sbi6_lim) :=
  ⟨tendsto_of_pow_closed_form _ _ sbc5_v _ abs_sbc5Rate_lt_one sbc5_closed_form,
    tendsto_of_pow_closed_form _ _ sbi6_v _ abs_sbi6Rate_lt_one sbi6_closed_form⟩

theorem small_digraph_constant (t : ℕ) :
    proximityDigraph .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) =
      proximityDigraph .sbc sbc5_r sbc5_x0 ∧
    proximityDigraph .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) =
      proximityDigraph .sbi sbi6_r sbi6_x0 :=
  ⟨sbc5_digraph_constant t, sbi6_digraph_constant t⟩

theorem small_not_fixedFrom (τ : ℕ) :
    ¬ FixedFrom (traj .sbc sbc5_r sbc5_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi6_r sbi6_x0) τ :=
  ⟨sbc5_not_fixedFrom τ, sbi6_not_fixedFrom τ⟩

theorem small_not_pseudoStableAfter (xinf : Fin 5 → ℝ) (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc5_r sbc5_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi6_r sbi6_x0) yinf τ :=
  ⟨sbc5_not_pseudoStableAfter xinf τ, sbi6_not_pseudoStableAfter yinf τ⟩

end HK
