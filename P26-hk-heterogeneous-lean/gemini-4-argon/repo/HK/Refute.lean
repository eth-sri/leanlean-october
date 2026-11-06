module

public import HK.SBC7
public import HK.SBI7
public import HK.SBC6
public import HK.SBI7b
public import HK.SBC5
public import HK.SBI6
public import HK.Generic

/-!
# The refutations, assembled; the conjunctions; the sharpness of Lemma 4.8's condition

Conjecture 2.2 and Conjecture 2.3 fail in each model by the two alternating systems; Theorem 6.4(iv)
fails in each model by the two constant-digraph systems of the source (and Conjecture 2.3 and Theorem
6.4(iv) at five SBC and six SBI agents by the smaller systems, in `SBC5.lean` and `SBI6.lean`). The literal reading of Theorem 6.4(iv) implies the reading admitting fixed states, so it fails
too. The equi-topology distance of the limit vanishes at the alternating agents of the two alternating
systems and is positive at every agent of the two constant-digraph systems of the source.
-/

@[expose] public section

namespace HK

open Filter Topology

set_option hygiene false
set_option quotPrecheck false

local notation "g2" f => ⟨f sbc5_closed_form, f sbi6_closed_form⟩
local notation "g4" f =>
  ⟨f sbc7_closed_form, f sbi7_closed_form',
   f sbc6_closed_form, f sbi7b_closed_form⟩
local notation "rgeom(" hx "," hN ")" =>
  refute_both (digraph_const_of_neighbors hN) (fun _ => not_fixedFrom_geom hx)
    (fun _ _ => not_pseudoStable_geom hx)
local notation "rc22" d => fun h =>
  let ⟨τ, hτ⟩ := h _ _ fun i => by fin_cases i <;> norm_num
  let ⟨t, ht, hne⟩ := d τ; hne (hτ t ht)

theorem small_tendsto :
    Tendsto tr5 atTop (𝓝 sbc5_lim) ∧
    Tendsto tr6 atTop (𝓝 sbi6_lim) := g2 tendsto_geom

theorem small_digraph_constant t :
    pdc sbc5_r (tr5 t) = pdc sbc5_r sbc5_x0 ∧
    pdi sbi6_r (tr6 t) = pdi sbi6_r sbi6_x0 :=
  ⟨digraph_const_of_neighbors sbc5_neighbors t, digraph_const_of_neighbors sbi6_neighbors t⟩

theorem small_not_fixedFrom τ :
    ¬ FixedFrom tr5 τ ∧ ¬ FixedFrom tr6 τ :=
  g2 not_fixedFrom_geom

theorem small_not_pseudoStableAfter xinf yinf τ :
    ¬ PseudoStableAfter tr5 xinf τ ∧
    ¬ PseudoStableAfter tr6 yinf τ :=
  g2 not_pseudoStable_geom

local notation "na" f => fun h => f (h _)

def sbc5_refute := rgeom(sbc5_closed_form, sbc5_neighbors)

def sbi6_refute := rgeom(sbi6_closed_form, sbi6_neighbors)

theorem not_conjecture23_sbc_five : ¬ Conjecture23ForAgents .sbc 5 := sbc5_refute.1

theorem not_theorem64iv_sbc_five : ¬ Theorem64ivForAgents .sbc 5 := sbc5_refute.2

theorem not_conjecture23_sbi_six : ¬ Conjecture23ForAgents .sbi 6 := sbi6_refute.1

theorem not_theorem64iv_sbi_six : ¬ Theorem64ivForAgents .sbi 6 := sbi6_refute.2

theorem not_conjecture22_sbc_seven : ¬ Conjecture22ForAgents .sbc 7 :=
  rc22 sbc7_digraph_not_eventually_constant

theorem not_conjecture22_sbi_seven : ¬ Conjecture22ForAgents .sbi 7 :=
  rc22 sbi7_digraph_not_eventually_constant

/-- Conjecture 2.2 fails for SBC. -/
theorem not_conjecture22_sbc : ¬ Conjecture22For .sbc := na not_conjecture22_sbc_seven

/-- Conjecture 2.3 fails for SBC. -/
theorem not_conjecture23_sbc : ¬ Conjecture23For .sbc := na not_conjecture23_sbc_five

theorem not_conjecture22_sbi : ¬ Conjecture22For .sbi := na not_conjecture22_sbi_seven

theorem not_conjecture23_sbi : ¬ Conjecture23For .sbi := na not_conjecture23_sbi_six

theorem not_theorem64iv_sbc : ¬ Theorem64ivFor .sbc := na not_theorem64iv_sbc_five

theorem not_theorem64iv_sbi : ¬ Theorem64ivFor .sbi := na not_theorem64iv_sbi_six

theorem not_conjecture22 : ¬ Conjecture22 := na not_conjecture22_sbc

theorem not_conjecture23 : ¬ Conjecture23 := na not_conjecture23_sbc

theorem not_theorem64iv : ¬ Theorem64iv := na not_theorem64iv_sbc

theorem not_literal {m} (h : ¬ Theorem64ivFor m) : ¬ Theorem64ivLiteralFor m := fun hl =>
  h fun n r x₀ hr τ hτ => (hl n r x₀ hr τ hτ).imp fun _ => And.imp_right Or.inr

theorem not_theorem64iv_literal_sbc : ¬ Theorem64ivLiteralFor .sbc :=
  not_literal not_theorem64iv_sbc

theorem not_theorem64iv_literal_sbi : ¬ Theorem64ivLiteralFor .sbi :=
  not_literal not_theorem64iv_sbi

theorem not_theorem64iv_literal : ¬ Theorem64ivLiteral :=
  na not_theorem64iv_literal_sbc

theorem tendsto_limits :
    Tendsto tr7c atTop (𝓝 sbc7_lim) ∧
    Tendsto tr7i atTop (𝓝 sbi7_lim) ∧
    Tendsto tr6c atTop (𝓝 sbc6_lim) ∧
    Tendsto tr7b atTop (𝓝 sbi7b_lim) := g4 tendsto_geom

theorem not_fixedFrom τ :
    ¬ FixedFrom tr7c τ ∧ ¬ FixedFrom tr7i τ ∧
    ¬ FixedFrom tr6c τ ∧ ¬ FixedFrom tr7b τ :=
  g4 not_fixedFrom_geom

theorem not_pseudoStableAfter xinf yinf τ :
    ¬ PseudoStableAfter tr7c xinf τ ∧
    ¬ PseudoStableAfter tr7i xinf τ ∧
    ¬ PseudoStableAfter tr6c yinf τ ∧
    ¬ PseudoStableAfter tr7b xinf τ :=
  g4 not_pseudoStable_geom

theorem alternating_fvct t :
    fvct .sbc sbc7_r (tr7c t) = sbc7_lim ∧
    fvct .sbi sbi7_r (tr7i t) = sbi7_lim :=
  ⟨fvct_eigen sbc7_closed_form sbc7_neighbors,
   fvct_eigen sbi7_closed_form' sbi7_neighbors⟩
local notation "epos" => fun i =>
  mul_pos (by norm_num) <| lt_of_lt_of_le zero_lt_two <|
    le_csInf ⟨_, if i = 0 then 1 else 0, by aesop, .inl rfl⟩ <| by
      rintro _ ⟨k, hk, rfl | rfl⟩ <;>
        (fin_cases i <;> fin_cases k <;>
          first | contradiction | norm_num)

theorem equiTopologyDistance_pos :
    (∀ i, 0 < equiTopologyDistance sbc6_r sbc6_lim i) ∧
    (∀ i, 0 < equiTopologyDistance sbi7b_r sbi7b_lim i) :=
  ⟨epos, epos⟩

local notation "ezero" j => fun i hi =>
  mul_eq_zero_of_right _ <| IsLeast.csInf_eq
    ⟨⟨j, by fin_cases hi <;> norm_num⟩, lb0⟩

theorem equiTopologyDistance_eq_zero :
    (∀ i ∈ ~{2, 3, 4}, equiTopologyDistance sbc7_r sbc7_lim i = 0) ∧
    (∀ i ∈ ~{1, 3, 5}, equiTopologyDistance sbi7_r sbi7_lim i = 0) :=
  ⟨ezero (if i = 3 then 2 else 3), ezero (if i = 3 then 1 else 3)⟩

end HK
