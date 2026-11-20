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

theorem not_conjecture22_sbc_seven : ¬ Conjecture22ForAgents .sbc 7 :=
  refute22 (by norm_num [Fin.forall_fin_succ, sbc7_r]) sbc7_digraph_not_eventually_constant

theorem not_conjecture22_sbi_seven : ¬ Conjecture22ForAgents .sbi 7 :=
  refute22 (by norm_num [Fin.forall_fin_succ, sbi7_r]) sbi7_digraph_not_eventually_constant

theorem not_conjecture22_sbc : ¬ Conjecture22For .sbc := fun h => not_conjecture22_sbc_seven (h 7)
theorem not_conjecture22_sbi : ¬ Conjecture22For .sbi := fun h => not_conjecture22_sbi_seven (h 7)
theorem not_conjecture22 : ¬ Conjecture22 := fun h => not_conjecture22_sbc (h .sbc)

theorem not_conjecture23_sbc : ¬ Conjecture23For .sbc := fun h => not_conjecture23_sbc_five (h 5)
theorem not_conjecture23_sbi : ¬ Conjecture23For .sbi := fun h => not_conjecture23_sbi_six (h 6)
theorem not_conjecture23 : ¬ Conjecture23 := fun h => not_conjecture23_sbc (h .sbc)

theorem not_theorem64iv_sbc : ¬ Theorem64ivFor .sbc :=
  fun h => not_theorem64iv_sbc_five (h 5)

theorem not_theorem64iv_sbi : ¬ Theorem64ivFor .sbi :=
  fun h => not_theorem64iv_sbi_six (h 6)

theorem not_theorem64iv : ¬ Theorem64iv := fun h => not_theorem64iv_sbc (h .sbc)

private theorem literal_implies {m : Model} (h : Theorem64ivLiteralFor m) : Theorem64ivFor m := by
  intro n r x hr τ hτ
  obtain ⟨t, ht, hp⟩ := h n r x hr τ hτ
  exact ⟨t, ht, .inr hp⟩

theorem not_theorem64iv_literal_sbc : ¬ Theorem64ivLiteralFor .sbc := not_theorem64iv_sbc ∘ literal_implies
theorem not_theorem64iv_literal_sbi : ¬ Theorem64ivLiteralFor .sbi := not_theorem64iv_sbi ∘ literal_implies
theorem not_theorem64iv_literal : ¬ Theorem64ivLiteral := fun h => not_theorem64iv_literal_sbc (h .sbc)

local notation "X₇" => traj Model.sbc sbc7_r sbc7_x0
local notation "Y₇" => traj Model.sbi sbi7_r sbi7_x0
local notation "X₆" => traj Model.sbc sbc6_r sbc6_x0
local notation "Y₇b" => traj Model.sbi sbi7b_r sbi7b_x0

theorem tendsto_limits :
    Tendsto X₇ atTop (𝓝 sbc7_lim) ∧ Tendsto Y₇ atTop (𝓝 sbi7_lim) ∧
    Tendsto X₆ atTop (𝓝 sbc6_lim) ∧ Tendsto Y₇b atTop (𝓝 sbi7b_lim) :=
  ⟨sbc7_facts.1, sbi7_facts.1, sbc6_facts.1, sbi7b_facts.1⟩

theorem not_fixedFrom (τ : ℕ) :
    ¬ FixedFrom X₇ τ ∧ ¬ FixedFrom Y₇ τ ∧ ¬ FixedFrom X₆ τ ∧ ¬ FixedFrom Y₇b τ :=
  ⟨sbc7_facts.2.1 τ, sbi7_facts.2.1 τ, sbc6_facts.2.1 τ, sbi7b_facts.2.1 τ⟩

theorem not_pseudoStableAfter (xinf : Fin 7 → ℝ) (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter X₇ xinf τ ∧ ¬ PseudoStableAfter Y₇ xinf τ ∧
    ¬ PseudoStableAfter X₆ yinf τ ∧ ¬ PseudoStableAfter Y₇b xinf τ :=
  ⟨sbc7_facts.2.2 xinf τ, sbi7_facts.2.2 xinf τ, sbc6_facts.2.2 yinf τ, sbi7b_facts.2.2 xinf τ⟩

theorem alternating_fvct (t : ℕ) :
    fvct .sbc sbc7_r (X₇ t) = sbc7_lim ∧ fvct .sbi sbi7_r (Y₇ t) = sbi7_lim :=
  ⟨sbc7_fvct t, sbi7_fvct t⟩

local notation "X₅" => traj Model.sbc sbc5_r sbc5_x0
local notation "Y₆" => traj Model.sbi sbi6_r sbi6_x0

theorem small_tendsto : Tendsto X₅ atTop (𝓝 sbc5_lim) ∧ Tendsto Y₆ atTop (𝓝 sbi6_lim) :=
  ⟨sbc5_facts.1, sbi6_facts.1⟩

theorem small_digraph_constant (t : ℕ) :
    proximityDigraph .sbc sbc5_r (X₅ t) = proximityDigraph .sbc sbc5_r sbc5_x0 ∧
    proximityDigraph .sbi sbi6_r (Y₆ t) = proximityDigraph .sbi sbi6_r sbi6_x0 :=
  ⟨sbc5_digraph_constant t, sbi6_digraph_constant t⟩

theorem small_not_fixedFrom (τ : ℕ) : ¬ FixedFrom X₅ τ ∧ ¬ FixedFrom Y₆ τ :=
  ⟨sbc5_facts.2.1 τ, sbi6_facts.2.1 τ⟩

theorem small_not_pseudoStableAfter (xinf : Fin 5 → ℝ) (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter X₅ xinf τ ∧ ¬ PseudoStableAfter Y₆ yinf τ :=
  ⟨sbc5_facts.2.2 xinf τ, sbi6_facts.2.2 yinf τ⟩

/-- The two fixed-topology limits have strictly positive gaps. -/
theorem equiTopologyDistance_pos :
    (∀ i, 0 < equiTopologyDistance sbc6_r sbc6_lim i) ∧
    (∀ i, 0 < equiTopologyDistance sbi7b_r sbi7b_lim i) := by
  constructor <;> intro i <;> refine distance_pos (B := 1) (by norm_num) ?_ <;>
    intro j hj <;> fin_cases i <;> fin_cases j <;>
    norm_num [sbc6_r, sbc6_lim, sbi7b_r, sbi7b_lim] at *

/-- At the alternating edges the limit is exactly on a threshold. -/
theorem equiTopologyDistance_eq_zero :
    (∀ i ∈ ({2, 3, 4} : Finset (Fin 7)), equiTopologyDistance sbc7_r sbc7_lim i = 0) ∧
    (∀ i ∈ ({1, 3, 5} : Finset (Fin 7)), equiTopologyDistance sbi7_r sbi7_lim i = 0) := by
  constructor <;> intro i hi
  · refine distance_zero (j := if i = 3 then 2 else 3) (R := 12) ?_ ?_ ?_ <;>
      fin_cases i <;> norm_num [sbc7_r, sbc7_lim] at *
  · refine distance_zero (j := if i = 3 then 1 else 3) (R := 4) ?_ ?_ ?_ <;>
      fin_cases i <;> norm_num [sbi7_r, sbi7_lim] at *

end HK
