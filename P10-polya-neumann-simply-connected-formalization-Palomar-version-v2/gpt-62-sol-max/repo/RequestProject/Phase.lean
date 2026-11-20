module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

/-!
# Eigenphases and counting (Definition 5.18 and Section 9)

This file formalizes the scalar and combinatorial parts of Section 9 of the paper.

* `argNeg z` is the negative argument `Arg₋ z ∈ (-2π, 0)` of a unimodular `z ≠ 1`
  (Definition 5.18).
* Lemma 9.2 (scalar part): `|z - 1| ≤ -Arg₋ z`, and on the lower semicircle
  `|Arg₋ z| ≤ (π/2) |z - 1|` (the bound used in Lemma 9.1).
* Lemma 9.2 (summed form): for any summable family of eigenvalues, `-Φ₋ ≥ |z_j - 1|` for each
  member, hence `M(E) ≥ E|Ω|/(4π) + ‖U_E - I‖/(2π)` whenever `‖U_E - I‖` is attained by an
  eigenvalue.
* Lemma 9.3 (last step): a continuous integer-valued function on an interval is constant.
* Lemma 9.6: the induction across the Neumann eigenvalues, stated for an abstract
  integer-valued function `M` that equals `1` at small energies, is locally constant away from
  a discrete set `S` and jumps by at most `m(μ)` at `μ ∈ S`; then
  `M(E) ≤ 1 + ∑_{μ ∈ S, μ < E} m(μ)`.
* Theorem 9.7 (last step): an inequality `f ≤ N` valid off a discrete set passes to every
  energy when `f` is left-continuous and `N` is locally constant from the left.

The spectral inputs (trace-class eigenvalue sums, the Fredholm determinant, the Cayley upper
bound of Proposition 7.11 and Lemma 8.8) are not formalized; they appear here as hypotheses.
-/

@[expose] public section

open Set Real

noncomputable section

namespace PolyaNeumann

/-- The negative argument `Arg₋ z`: for `|z| = 1`, `z ≠ 1`, the unique `t ∈ (-2π, 0)` with
`e^{it} = z`. -/
def argNeg (z : ℂ) : ℝ := if Complex.arg z < 0 then Complex.arg z else Complex.arg z - 2 * π

section

variable {z : ℂ} (hz : ‖z‖ = 1)
include z hz

/-- `Arg₋ z ∈ (-2π, 0)` for `z ≠ 1` on the unit circle. -/
theorem argNeg_mem_Ioo  (h1 : z ≠ 1) : argNeg z ∈ Ioo (-2 * π) 0 := by
  have hlo := Complex.neg_pi_lt_arg z
  have hhi := Complex.arg_le_pi z
  have h0 : Complex.arg z ≠ 0 := by
    intro h
    apply h1
    have := Complex.norm_mul_exp_arg_mul_I z
    simp_all
  unfold argNeg
  grind

/-- `e^{i Arg₋ z} = z` on the unit circle. -/
theorem exp_argNeg  : Complex.exp (argNeg z * Complex.I) = z := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  rw [hz, Complex.ofReal_one, one_mul] at h
  unfold argNeg
  split_ifs
  assumption
  simp_all [sub_mul, Complex.exp_sub, h]

/-- **Lemma 9.2 (scalar inequality).**  `|z - 1| ≤ -Arg₋ z` on the unit circle. -/
theorem norm_sub_one_le_neg_argNeg  : ‖z - 1‖ ≤ -argNeg z := by
  have hneg : argNeg z ≤ 0 := by
    unfold argNeg
    split_ifs with h
    gcongr
    · linarith [Complex.arg_le_pi z, Real.pi_pos]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := argNeg z)
  rw [mul_comm, exp_argNeg hz, Real.norm_eq_abs, abs_of_nonpos hneg] at this
  assumption

end


end PolyaNeumann

end
