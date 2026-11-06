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

/-- The square-root inequality used for mixture likelihoods. -/
theorem square_root_difference_bound {f g c : ℝ} (hc : 0 < c)
    (hf : c ≤ f) (hg : c ≤ g) :
    (Real.sqrt f - Real.sqrt g) ^ 2 ≤ (f - g) ^ 2 / (4 * c) := by
  have hf0 : 0 ≤ f := le_trans (le_of_lt hc) hf
  have hg0 : 0 ≤ g := le_trans (le_of_lt hc) hg
  have hsfc := Real.sqrt_le_sqrt hf
  have hsgc := Real.sqrt_le_sqrt hg
  have hsc := Real.sqrt_nonneg c
  have hsf := Real.sqrt_nonneg f
  have hsg := Real.sqrt_nonneg g
  have hscc := Real.sq_sqrt (le_of_lt hc)
  have hsff := Real.sq_sqrt hf0
  have hsgg := Real.sq_sqrt hg0
  have hprod : c ≤ Real.sqrt f * Real.sqrt g := by
    nlinarith [mul_le_mul hsfc hsgc hsc hsf]
  have hden : 4 * c ≤ (Real.sqrt f + Real.sqrt g) ^ 2 := by nlinarith
  have hid : (f - g) ^ 2 =
      (Real.sqrt f - Real.sqrt g) ^ 2 * (Real.sqrt f + Real.sqrt g) ^ 2 := by
    have hi : f - g = (Real.sqrt f - Real.sqrt g) * (Real.sqrt f + Real.sqrt g) := by
      nlinarith
    rw [hi, mul_pow]
  apply (le_div_iff₀ (by positivity : 0 < 4 * c)).mpr
  rw [hid]
  exact mul_le_mul_of_nonneg_left hden (sq_nonneg _)

theorem sqrt_finite_product {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    Real.sqrt (∏ i, f i) = ∏ i, Real.sqrt (f i) := by
  apply (Real.sqrt_eq_iff_eq_sq (Finset.prod_nonneg fun i _ => hf i)
    (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg (f i))).mpr
  rw [← Finset.prod_pow]
  simp_rw [Real.sq_sqrt (hf _)]

end
end RoughRegime.Lower
