module

public import HK.SBC7
public import HK.SBI7
public import HK.SBC6
public import HK.SBI7b
public import HK.SBC5
public import HK.SBI6
public import HK.SBI5Complex
public import HK.Generic

/-!
# The refutations, assembled; the conjunctions; the sharpness of Lemma 4.8's condition

Conjecture 2.2 and Conjecture 2.3 fail in each model by the two alternating systems; Theorem 6.4(iv)
fails in each model by the two constant-digraph systems of the source, and at five SBC and six SBI
agents by the smaller systems. The literal reading of Theorem 6.4(iv) implies the reading admitting
fixed states, so it fails too. The equi-topology distance of the limit vanishes at the alternating
agents of the two alternating systems and is positive at every agent of the two constant-digraph
systems of the source.
-/

@[expose] public section

namespace HK

open Filter Topology

chall not_conjecture22_sbc_seven "  intro h
  obtain ⟨τ, hτ⟩ := h sbc7_r sbc7_x0 sbc7_r_pos
  obtain ⟨t, ht, hne⟩ := sbc7_digraph_not_eventually_constant_internal τ
  exact hne (hτ t ht)"

chall not_conjecture22_sbi_seven "  intro h
  obtain ⟨τ, hτ⟩ := h sbi7_r sbi7_x0 sbi7_r_pos
  obtain ⟨t, ht, hne⟩ := sbi7_digraph_not_eventually_constant_internal τ
  exact hne (hτ t ht)"

theorem not_conjecture22_sbc_internal : ¬ Conjecture22For .sbc := fun h => not_conjecture22_sbc_seven_internal (h 7)

theorem not_conjecture22_sbi_internal : ¬ Conjecture22For .sbi := fun h => not_conjecture22_sbi_seven_internal (h 7)

theorem not_conjecture22_internal : ¬ Conjecture22 := fun h => not_conjecture22_sbc_internal (h .sbc)

theorem not_conjecture23_sbc_internal : ¬ Conjecture23For .sbc := fun h => not_conjecture23_sbc_five_internal (h 5)

theorem not_conjecture23_sbi_internal : ¬ Conjecture23For .sbi := fun h => not_conjecture23_sbi_six_internal (h 6)

theorem not_conjecture23_internal : ¬ Conjecture23 := fun h => not_conjecture23_sbc_internal (h .sbc)

chall not_theorem64iv_sbc "  intro h
  obtain ⟨t₂, -, hf | ⟨xinf, hps⟩⟩ := h 6 sbc6_r sbc6_x0 sbc6_r_pos 0
    (fun t _ => by simp only [proximityDigraph, sbc6_neighbors_internal])
  · exact sbc6_not_fixedFrom t₂ hf
  · exact sbc6_not_pseudoStableAfter xinf t₂ hps"

chall not_theorem64iv_sbi "  intro h
  obtain ⟨t₂, -, hf | ⟨xinf, hps⟩⟩ := h 7 sbi7b_r sbi7b_x0 sbi7b_r_pos 0
    (fun t _ => by simp only [proximityDigraph, sbi7b_neighbors_internal])
  · exact sbi7b_not_fixedFrom t₂ hf
  · exact sbi7b_not_pseudoStableAfter xinf t₂ hps"

theorem not_theorem64iv_internal : ¬ Theorem64iv := fun h => not_theorem64iv_sbc_internal (h .sbc)

chall not_theorem64iv_literal_sbc "  intro h
  apply not_theorem64iv_sbc_internal
  intro n r x₀ hr τ hτ
  obtain ⟨t₂, ht₂, hps⟩ := h n r x₀ hr τ hτ
  exact ⟨t₂, ht₂, Or.inr hps⟩"

chall not_theorem64iv_literal_sbi "  intro h
  apply not_theorem64iv_sbi_internal
  intro n r x₀ hr τ hτ
  obtain ⟨t₂, ht₂, hps⟩ := h n r x₀ hr τ hτ
  exact ⟨t₂, ht₂, Or.inr hps⟩"

theorem not_theorem64iv_literal_internal : ¬ Theorem64ivLiteral :=
  fun h => not_theorem64iv_literal_sbc_internal (h .sbc)

chall tendsto_limits "exact ⟨tendsto_of_geom1 _ sbc7_lim sbc7_v (-1 / 6) sbc7_rate.1 sbc7_rate.2 sbc7_closed_form_internal, tendsto_of_geom _ sbi7_lim sbi_v (fun t => sbiRate ^ t / 2) sbi7_rate_tendsto sbi7_closed_form_internal, tendsto_of_geom1 _ sbc6_lim sbc6_v (-1 / 6) sbc6_rate.1 sbc6_rate.2 sbc6_closed_form_internal, tendsto_of_geom1 _ sbi7b_lim sbi_v sbiRate sbiRate_mem.1 sbiRate_mem.2 sbi7b_closed_form_internal⟩"

chall not_fixedFrom "exact ⟨sbc7_not_fixedFrom τ, sbi7_not_fixedFrom τ, sbc6_not_fixedFrom τ, sbi7b_not_fixedFrom τ⟩"

chall not_pseudoStableAfter "exact ⟨sbc7_not_pseudoStableAfter xinf τ, sbi7_not_pseudoStableAfter xinf τ, sbc6_not_pseudoStableAfter yinf τ, sbi7b_not_pseudoStableAfter xinf τ⟩"

/-- A positive lower bound `c` on every term of the equi-topology set (with some `j ≠ i`) makes the
equi-topology distance positive. -/
theorem ref_equiTopologyDistance_pos_of {n : ℕ} (r z : Fin n → ℝ) (i j : Fin n) (hij : j ≠ i)
    (c : ℝ) (hc : 0 < c)
    (h : ∀ k, k ≠ i → c ≤ |(|z i - z k|) - r i| ∧ c ≤ |(|z i - z k|) - r k|) :
    0 < equiTopologyDistance r z i := by
  unfold equiTopologyDistance
  have hS : c ≤ sInf {d : ℝ | ∃ j, j ≠ i ∧ (d = |(|z i - z j|) - r i| ∨ d = |(|z i - z j|) - r j|)} := by
    have hne : Set.Nonempty
        {d : ℝ | ∃ j, j ≠ i ∧ (d = |(|z i - z j|) - r i| ∨ d = |(|z i - z j|) - r j|)} :=
      ⟨_, j, hij, Or.inl rfl⟩
    refine le_csInf hne ?_
    rintro d ⟨k, hk, rfl | rfl⟩
    · exact (h k hk).1
    · exact (h k hk).2
  linarith

/-- The twin of `equiTopologyDistance_eq_zero_of` with the other agent's bound. -/
theorem ref_equiTopologyDistance_eq_zero_of' {n : ℕ} (r z : Fin n → ℝ) (i j : Fin n) (hij : j ≠ i)
    (h : |z i - z j| = r j) : equiTopologyDistance r z i = 0 := by
  unfold equiTopologyDistance
  have hS : sInf {d : ℝ | ∃ j, j ≠ i ∧ (d = |(|z i - z j|) - r i| ∨ d = |(|z i - z j|) - r j|)} = 0 := by
    apply IsLeast.csInf_eq
    refine ⟨⟨j, hij, Or.inr (by rw [h, sub_self, abs_zero])⟩, ?_⟩
    rintro d ⟨k, -, rfl | rfl⟩ <;> exact abs_nonneg _
  rw [hS, mul_zero]

/-- At the limit of the 6-agent SBC system every term of the equi-topology set is at least `10`. -/
theorem ref_sbc6_etd_pos (i : Fin 6) : 0 < equiTopologyDistance sbc6_r sbc6_lim i := by
  refine ref_equiTopologyDistance_pos_of _ _ i (i + 1) (by fin_cases i <;> decide) 10
    (by norm_num) ?_
  intro k hk
  fin_cases i <;> fin_cases k <;> first | exact absurd rfl hk | norm_num [sbc6_r, sbc6_lim]

/-- At the limit of the §5 SBI system every term of the equi-topology set is at least `5`. -/
theorem ref_sbi7b_etd_pos (i : Fin 7) : 0 < equiTopologyDistance sbi7b_r sbi7b_lim i := by
  refine ref_equiTopologyDistance_pos_of _ _ i (i + 1) (by fin_cases i <;> decide) 5
    (by norm_num) ?_
  intro k hk
  fin_cases i <;> fin_cases k <;> first | exact absurd rfl hk | norm_num [sbi7b_r, sbi7b_lim]

theorem alternating_fvct_internal (t : ℕ) :
    fvct .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) = sbc7_lim ∧
    fvct .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) = sbi7_lim :=
  ⟨sbc7_fvct t, sbi7_fvct_internal t⟩

chall equiTopologyDistance_pos "exact ⟨ref_sbc6_etd_pos, ref_sbi7b_etd_pos⟩"

chall equiTopologyDistance_eq_zero "  constructor
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ref_equiTopologyDistance_eq_zero_of' _ _ 2 3 (by decide)
        (by norm_num [sbc7_r, sbc7_lim])
    · exact equiTopologyDistance_eq_zero_of _ _ 3 2 (by decide) (by norm_num [sbc7_r, sbc7_lim])
    · exact ref_equiTopologyDistance_eq_zero_of' _ _ 4 3 (by decide)
        (by norm_num [sbc7_r, sbc7_lim])
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact equiTopologyDistance_eq_zero_of _ _ 1 3 (by decide) (by norm_num [sbi7_r, sbi7_lim])
    · exact ref_equiTopologyDistance_eq_zero_of' _ _ 3 1 (by decide)
        (by norm_num [sbi7_r, sbi7_lim])
    · exact equiTopologyDistance_eq_zero_of _ _ 5 3 (by decide) (by norm_num [sbi7_r, sbi7_lim])"

chall small_tendsto "exact ⟨sbc5_tendsto, sbi6_tendsto⟩"

chall small_digraph_constant "exact ⟨sbc5_digraph_constant t, sbi6_digraph_constant t⟩"

chall small_not_fixedFrom "exact ⟨sbc5_not_fixedFrom τ, sbi6_not_fixedFrom τ⟩"

chall small_not_pseudoStableAfter "exact ⟨sbc5_not_pseudoStableAfter xinf τ, sbi6_not_pseudoStableAfter yinf τ⟩"

end HK
