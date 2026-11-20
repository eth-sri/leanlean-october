module

public import Mathlib

@[expose] public section

/-!
# Lower-bound ingredients from Section 5

This file proves finite-space probability and algebraic ingredients of the
testing argument. It does not assert the marked Poisson comparison or the
asymptotic reduction proposition, whose infinite-dimensional hypotheses are
not represented by these finite-space definitions.
-/

namespace RoughRegime.Lower

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The square-root inequality used for mixture likelihoods. -/
theorem square_root_difference_bound {f g c : ℝ} (hc : 0 < c)
    (hf : c ≤ f) (hg : c ≤ g) :
    (Real.sqrt f - Real.sqrt g) ^ 2 ≤ (f - g) ^ 2 / (4 * c) := by
  have hf0  := le_trans (le_of_lt hc) hf
  have hg0  := le_trans (le_of_lt hc) hg
  have hsfc := Real.sqrt_le_sqrt hf
  have hsgc := Real.sqrt_le_sqrt hg
  have hsc := Real.sqrt_nonneg c
  have hsff := Real.sq_sqrt hf0
  have hsgg := Real.sq_sqrt hg0
  have hprod : c ≤ Real.sqrt f * Real.sqrt g := by
    nlinarith [mul_le_mul hsfc hsgc hsc (Real.sqrt_nonneg f)]
  have hid : (f - g) ^ 2 =
      (Real.sqrt f - Real.sqrt g) ^ 2 * (Real.sqrt f + Real.sqrt g) ^ 2 := by
    grind
  apply (le_div_iff₀ (by positivity)).mpr
  rw [hid]
  bound

theorem sqrt_finite_product {ι : Type*} [Fintype ι] {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) :
    Real.sqrt (∏ i, f i) = ∏ i, Real.sqrt (f i) := by
  apply (Real.sqrt_eq_iff_eq_sq (Finset.prod_nonneg fun i _ => hf i)
    (by positivity)).mpr
  rw [← Finset.prod_pow]
  simp_all

end
end RoughRegime.Lower
