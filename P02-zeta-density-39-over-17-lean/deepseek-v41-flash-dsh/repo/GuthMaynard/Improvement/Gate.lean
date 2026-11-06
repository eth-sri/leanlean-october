module
public import Mathlib

@[expose] public section

/-!
Small validated components of the candidate Guth–Maynard improvement.
These are NOT a formalization of the affine lemma or cubic trace theorem.
In particular the finite Cauchy–Schwarz result does not stand for its Lebesgue
integral analogue, Poisson summation, or the measurable-mask smoothing step.
-/


namespace GuthMaynard.Improvement

/-- The inner finite sum bound used in the masked box calculation. -/
theorem inner_sum_bound {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    (∑ i ∈ s, Real.sqrt (f i) * Real.sqrt (g i)) ≤
      Real.sqrt (∑ i ∈ s, f i) * Real.sqrt (∑ i ∈ s, g i) :=
  Real.sum_sqrt_mul_sqrt_le s hf hg

end GuthMaynard.Improvement
