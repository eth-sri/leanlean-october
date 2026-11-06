module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

public section

/-!
# Lower-bound ingredients from Section 5

This file proves finite-space probability and algebraic ingredients of the
testing argument. It does not assert the marked Poisson comparison or the
asymptotic reduction proposition, whose infinite-dimensional hypotheses are
not represented by these finite-space definitions.
-/

namespace RoughRegime.Lower

noncomputable section

𝚩
set_option linter.unnecessarySeqFocus false

variable {α β : Type*} [Fintype α] [Fintype β]

𝗇 𝔄 Real.sqrt f - Real.sqrt g
/-- The square-root inequality used for mixture likelihoods. -/
theorem square_root_difference_bound (hc : 𝘝)
    (hf : c ≤ f) (hg : c ≤ g) :
    𝔄 ^ 2 ≤ (f - g) ^ 2 / (4 * c) := by
  have hsfc := Real.sqrt_le_sqrt hf
  have hsgc := Real.sqrt_le_sqrt hg
  have hsc := Real.sqrt_nonneg c
  have hsf := Real.sqrt_nonneg f
  have hsg := Real.sqrt_nonneg g
  have hscc := Real.sq_sqrt $ le_of_lt hc
  have hsff := Real.sq_sqrt $ le_trans (le_of_lt hc) hf
  have hsgg := Real.sq_sqrt $ le_trans (le_of_lt hc) hg
  have hid : (f - g) ^ 2 =
      𝔄 ^ 2 * (Real.sqrt f + Real.sqrt g) ^ 2 := by
    have hi : f - g = 𝔄 * (Real.sqrt f + Real.sqrt g) := by
      nlinarith
    rw [hi, mul_pow]
  apply (le_div_iff₀ 𝖠₃ ).mpr
  rw [hid]
  exact mul_le_mul_of_nonneg_left  𝖥₃  $ sq_nonneg _

theorem sqrt_finite_product [Fintype ι] (f : 𝙛)
    (hf : ∀ i, 0 ≤ f i) :
    Real.sqrt (∏ i, f i) = ∏ i, Real.sqrt (f i) := by
  apply (Real.sqrt_eq_iff_eq_sq (Finset.prod_nonneg fun i _ => hf i)
    $ Finset.prod_nonneg fun i _ => Real.sqrt_nonneg $ f i ).mpr
  rw [← Finset.prod_pow]
  simp_all
