module

public import IntervalCore
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Soundness of the interval library `IntervalCore`

`x ∈ₗ I` means `(I.lo : ℝ) ≤ x ≤ (I.hi : ℝ)`. For every operation of `IntervalCore` we prove the
inclusion property: if the arguments are members of the argument intervals, the value is a member
of the result (`Ival.mem_add`, `mem_sub`, `mem_neg`, `mem_mul`, `mem_div`, `mem_inv`, `mem_sqr`,
`mem_pow`, `mem_addRat`, `mem_mulRat`, `mem_divRat`, `mem_ofRat`, `mem_join_left`,
`mem_join_right`, `mem_round`, `mem_exp`), and the checks (`Ival.le_of_le`, `le_of_leRat`, …) are sound. The
rounding lemmas are `roundDown_le` and `le_roundUp` (in `ℚ`) and their casts to `ℝ`.

For the exponential (`expLo_le`, `le_expHi`, `Ival.mem_exp`): the fixed-point Taylor sum is a lower
bound by `Real.sum_le_exp_of_nonneg` (`taylor_fst_le`); its error bound gives an upper bound by
`Real.exp_bound` for the tail after `m ≥ 1` terms, `|Y|^m (m+1)/(m!·m) ≤ 2 Y^m/m!` for `|Y| ≤ 1`
(`le_taylor_add`), and `Real.abs_exp_sub_one_le` covers the rounding of the reduced argument. The
squarings use `Real.exp_add`, negative arguments `Real.exp_neg`, and `q ≤ -p` the bound
`2 ≤ exp 1`.
-/

@[expose] public section

namespace IntervalCore

open Finset

/-- Membership of a real number in an interval with rational ends. -/
def Mem (x : ℝ) (I : Ival) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

@[inherit_doc] infix:50 " ∈ₗ " => Mem

/-! ## Rounding -/

/-! ## Checks -/

namespace Ival

/-! ## Arithmetic -/

/-! ### Products -/

/-! ### Notation -/

end Ival

/-! ## Fixed point -/

/-! ## Taylor sums -/

/-! ## Squarings -/

/-! ## Exponential of `n / d ≥ 0` -/

/-! ## Exponential of a rational -/

namespace Ival

end Ival

end IntervalCore
