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

/-- `Arg₋ z ∈ (-2π, 0)` for `z ≠ 1` on the unit circle. -/
theorem argNeg_mem_Ioo {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) : argNeg z ∈ Ioo (-2 * π) 0 := by
  have hlo := Complex.neg_pi_lt_arg z
  have hhi := Complex.arg_le_pi z
  have h0 : Complex.arg z ≠ 0 := by
    intro h
    apply h1
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz, h] at this
    simpa using this.symm
  unfold argNeg
  split_ifs with h
  · exact ⟨by linarith [Real.pi_pos], h⟩
  · have : 0 < Complex.arg z := lt_of_le_of_ne (not_lt.mp h) (Ne.symm h0)
    exact ⟨by linarith, by linarith⟩

/-- `e^{i Arg₋ z} = z` on the unit circle. -/
theorem exp_argNeg {z : ℂ} (hz : ‖z‖ = 1) : Complex.exp (argNeg z * Complex.I) = z := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  rw [hz, Complex.ofReal_one, one_mul] at h
  unfold argNeg
  split_ifs
  · exact h
  · rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, h]
    push_cast
    rw [Complex.exp_two_pi_mul_I, div_one]

/-- **Lemma 9.2 (scalar inequality).**  `|z - 1| ≤ -Arg₋ z` on the unit circle. -/
theorem norm_sub_one_le_neg_argNeg {z : ℂ} (hz : ‖z‖ = 1) : ‖z - 1‖ ≤ -argNeg z := by
  have hneg : argNeg z ≤ 0 := by
    unfold argNeg
    split_ifs with h
    · exact h.le
    · linarith [Complex.arg_le_pi z, Real.pi_pos]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := argNeg z)
  rw [mul_comm, exp_argNeg hz, Real.norm_eq_abs, abs_of_nonpos hneg] at this
  exact this

/-- **Lemma 9.1 (lower semicircle bound).**  If `|z| = 1`, `z ≠ 1` and `Im z ≤ 0` then
`|Arg₋ z| ≤ (π/2) |z - 1|`. -/
theorem abs_argNeg_le_of_im_nonpos {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) (him : z.im ≤ 0) :
    |argNeg z| ≤ π / 2 * ‖z - 1‖ := by
  -- first, `Arg₋ z ∈ [-π, 0]`
  have hmem : argNeg z ∈ Icc (-π) 0 := by
    have hlo := Complex.neg_pi_lt_arg z
    have hhi := Complex.arg_le_pi z
    have hI := argNeg_mem_Ioo hz h1
    rcases him.lt_or_eq with h | h
    · have ha : Complex.arg z < 0 := Complex.arg_neg_iff.mpr h
      unfold argNeg
      rw [if_pos ha]
      exact ⟨hlo.le, ha.le⟩
    · have hre : z.re < 0 := by
        by_contra hre
        push_neg at hre
        apply h1
        have h0 : Complex.arg z = 0 := Complex.arg_eq_zero_iff.mpr ⟨hre, h⟩
        have := Complex.norm_mul_exp_arg_mul_I z
        rw [hz, h0] at this
        simpa using this.symm
      have hpi : Complex.arg z = π := Complex.arg_eq_pi_iff.mpr ⟨hre, h⟩
      unfold argNeg
      rw [if_neg (by rw [hpi]; exact not_lt.mpr Real.pi_pos.le), hpi]
      exact ⟨by linarith, by linarith [Real.pi_pos]⟩
  set t := argNeg z with ht
  have hexp : ‖z - 1‖ = ‖Complex.exp (Complex.I * t) - 1‖ := by
    rw [mul_comm, ht, exp_argNeg hz]
  rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_of_nonpos hmem.2]
  have hs : 2 / π * (-t / 2) ≤ Real.sin (-t / 2) :=
    Real.mul_le_sin (by linarith [hmem.2]) (by linarith [hmem.1])
  have hsin : Real.sin (t / 2) = -Real.sin (-t / 2) := by rw [neg_div, Real.sin_neg, neg_neg]
  have hnn : (0 : ℝ) ≤ 2 / π * (-t / 2) :=
    mul_nonneg (by positivity) (by linarith [hmem.2])
  rw [hsin, abs_mul, abs_neg, abs_two, abs_of_nonneg (hnn.trans hs)]
  have hpi := Real.pi_pos
  have : -t ≤ π / 2 * (2 * Real.sin (-t / 2)) := by
    have h2 : 2 / π * (-t / 2) * π = -t := by field_simp
    nlinarith
  linarith

/-- **Lemma 9.2 (phase remainder, abstract form).**  For a family `z` of unimodular numbers
`≠ 1` (the nonunit eigenvalues of `U_E`, with multiplicity) whose negative arguments are
summable, `-Φ₋ = -∑ Arg₋ z_i ≥ |z_j - 1|` for every `j`. -/
theorem norm_sub_one_le_neg_tsum_argNeg {ι : Type*} {z : ι → ℂ} (hz : ∀ i, ‖z i‖ = 1)
    (h1 : ∀ i, z i ≠ 1) (hs : Summable fun i => argNeg (z i)) (j : ι) :
    ‖z j - 1‖ ≤ -∑' i, argNeg (z i) := by
  have hnn : ∀ i, 0 ≤ -argNeg (z i) := fun i => by
    linarith [(argNeg_mem_Ioo (hz i) (h1 i)).2]
  rw [← tsum_neg]
  exact (norm_sub_one_le_neg_argNeg (hz j)).trans
    (hs.neg.le_tsum j fun i _ => hnn i)

/-- **Lemma 9.2 (second inequality).**  With `Φ₋ = ∑ Arg₋ z_i` and
`M = (E|Ω|/2 - Φ₋)/(2π)`, if the norm `‖U_E - I‖ = r` is attained as `|z_j - 1|`, then
`M ≥ E|Ω|/(4π) + r/(2π)`.  (If the family is empty, take `r = 0`.) -/
theorem phase_integer_ge {ι : Type*} {z : ι → ℂ} (hz : ∀ i, ‖z i‖ = 1) (h1 : ∀ i, z i ≠ 1)
    (hs : Summable fun i => argNeg (z i)) (E area r : ℝ)
    (hr : r = 0 ∨ ∃ j, ‖z j - 1‖ = r) :
    E * area / (4 * π) + r / (2 * π) ≤ (E * area / 2 - ∑' i, argNeg (z i)) / (2 * π) := by
  have key : r ≤ -∑' i, argNeg (z i) := by
    rcases hr with rfl | ⟨j, rfl⟩
    · rw [← tsum_neg]
      exact tsum_nonneg fun i => by linarith [(argNeg_mem_Ioo (hz i) (h1 i)).2]
    · exact norm_sub_one_le_neg_tsum_argNeg hz h1 hs j
  have hpi := Real.pi_pos
  rw [show E * area / (4 * π) + r / (2 * π) = (E * area / 2 + r) / (2 * π) by
    field_simp; ring]
  gcongr
  linarith

end PolyaNeumann

end
