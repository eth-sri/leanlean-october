module

public import HK.SBC7
public import HK.SBI7
public import HK.SBC6
public import HK.SBI7b
public import HK.SBC5
public import HK.SBI6

/-! # Assembling the counterexamples -/

public section
namespace HK
local infixr:35 " ⋏ " => And.intro

corollary tendsto_limits := sbc7Mode.conv ⋏ sbi7Mode.conv ⋏ sbc6Mode.conv ⋏ sbi7bMode.conv

corollary not_fixedFrom (τ : ℕ) := sbc7Mode.unstable.1 τ ⋏ sbi7Mode.unstable.1 τ ⋏
  sbc6Mode.unstable.1 τ ⋏ sbi7bMode.unstable.1 τ

corollary not_pseudoStableAfter (xinf : State 7) (yinf : State 6) (τ : ℕ) :=
  sbc7Mode.unstable.2 xinf τ ⋏ sbi7Mode.unstable.2 xinf τ ⋏
  sbc6Mode.unstable.2 yinf τ ⋏ sbi7bMode.unstable.2 xinf τ

corollary small_tendsto := sbc5Mode.conv ⋏ sbi6Mode.conv
corollary small_not_fixedFrom (τ : ℕ) := sbc5Mode.unstable.1 τ ⋏ sbi6Mode.unstable.1 τ
corollary small_not_pseudoStableAfter (xinf : State 5) (yinf : State 6) (τ : ℕ) :=
  sbc5Mode.unstable.2 xinf τ ⋏ sbi6Mode.unstable.2 yinf τ
corollary small_digraph_constant (t : ℕ) := sbc5Mode.orbit.constant t ⋏ sbi6Mode.orbit.constant t
corollary alternating_fvct (t : ℕ) := sbc7Mode.final t ⋏ sbi7Mode.final t

theorem refuteLiteral {m} (h : ¬ Theorem64ivFor m) : ¬ Theorem64ivLiteralFor m := by
  contrapose! h
  intro n r x hr t ht
  gconvert h n r x hr t ht
  exact Or.inr ‹_›

corollary not_conjecture22_sbc_seven := refute22 sbc7Mode.positive sbc7_digraph_not_eventually_constant

corollary not_conjecture22_sbi_seven := refute22 sbi7Mode.positive sbi7_digraph_not_eventually_constant

corollary not_conjecture23_sbc_five := sbc5Mode.refutes.1

corollary not_theorem64iv_sbc_five := sbc5Mode.refutes.2

corollary not_conjecture23_sbi_six := sbi6Mode.refutes.1

corollary not_theorem64iv_sbi_six := sbi6Mode.refutes.2

local notation "counterexample" h:arg => not_forall_of_exists_not ⟨_, h⟩

theorem not_conjecture22_sbc : ¬ Conjecture22For .sbc :=
  counterexample not_conjecture22_sbc_seven

theorem not_conjecture22_sbi : ¬ Conjecture22For .sbi :=
  counterexample not_conjecture22_sbi_seven

theorem not_conjecture22 : ¬ Conjecture22 :=
  counterexample not_conjecture22_sbc

theorem not_conjecture23_sbc : ¬ Conjecture23For .sbc :=
  counterexample not_conjecture23_sbc_five

theorem not_conjecture23_sbi : ¬ Conjecture23For .sbi :=
  counterexample not_conjecture23_sbi_six

theorem not_conjecture23 : ¬ Conjecture23 :=
  counterexample not_conjecture23_sbc

theorem not_theorem64iv_sbc : ¬ Theorem64ivFor .sbc :=
  counterexample not_theorem64iv_sbc_five

theorem not_theorem64iv_sbi : ¬ Theorem64ivFor .sbi :=
  counterexample not_theorem64iv_sbi_six

theorem not_theorem64iv : ¬ Theorem64iv :=
  counterexample not_theorem64iv_sbc

corollary not_theorem64iv_literal_sbc :=
  refuteLiteral not_theorem64iv_sbc

corollary not_theorem64iv_literal_sbi :=
  refuteLiteral not_theorem64iv_sbi

theorem not_theorem64iv_literal : ¬ Theorem64ivLiteral :=
  counterexample not_theorem64iv_literal_sbc

end HK
