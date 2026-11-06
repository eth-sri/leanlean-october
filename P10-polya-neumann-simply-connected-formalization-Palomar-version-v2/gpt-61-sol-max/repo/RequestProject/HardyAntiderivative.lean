module

public import RequestProject.PlanarTypes

public import RequestProject.BoundaryTransmutation

/-!
# Conditional Hardy support for the Fourier antiderivative

If the multiplier coefficients have strictly negative support and the
input coefficients have nonpositive support, their convolution has zero
coefficients at every nonnegative frequency. Consequently the existing
normalized `antiPrim` preserves nonpositive support and its Fourier
derivative is the full convolution, including at frequency zero.

These are conditional coefficient statements. This file does not identify
the multiplier with a physical conformal boundary derivative, construct an
interior antiholomorphic extension, or establish Vekua endpoint identities.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

/-- A coefficient sequence supported on the nonpositive Fourier modes. -/
def IsNonpositiveFourierSupport (h : FourierSeq)  :=
  ∀ n, 0 < n → h n = 0

/-- A coefficient sequence supported on the strictly negative Fourier modes. -/
def IsStrictNegativeFourierSupport (a : FourierSeq)  :=
  ∀ n, 0 ≤ n → a n = 0

section
variable {a h } (ha : IsStrictNegativeFourierSupport a) (hh : IsNonpositiveFourierSupport h)
include a h ha hh

/-- A strictly negative multiplier and a nonpositive input have no
nonnegative convolution coefficients. Every summand is zero, so no
summability hypothesis is needed for this support statement. -/
theorem seqConv_eq_zero_of_strictNegative_nonpositive  (hn : 0 ≤ n) :
    seqConv a h n = 0 := by
  calc
    (∑' k, a k * h (n - k)) = ∑' _ : ℤ, 0 := by
      apply tsum_congr
      intro k
      by_cases hk : 0 ≤ k
      · rw [ha k hk, zero_mul]
      · rw [hh (n - k) (by omega), mul_zero]
    _ = 0 := tsum_zero

/-- In particular, the product has zero mean, as required by a periodic
antiderivative. -/
theorem seqConv_zero_of_strictNegative_nonpositive : seqConv a h 0 = 0 :=
  seqConv_eq_zero_of_strictNegative_nonpositive ha hh le_rfl

/-- The normalization changes only the constant coefficient and hence
preserves the nonpositive Fourier sector. -/
theorem antiPrim_nonpositive :
    IsNonpositiveFourierSupport (antiPrim a h) := by
  grind [antiPrim, primSeq, seqConv_eq_zero_of_strictNegative_nonpositive, PolyaNeumann.IsNonpositiveFourierSupport]

/-- Every iterated normalized primitive remains in the same Fourier sector. -/
theorem antiPrimIter_nonpositive j :
    IsNonpositiveFourierSupport (antiPrimIter a j h) := by
  induction j with
  | zero => exact hh
  | succ j ih =>
      change IsNonpositiveFourierSupport ((antiPrim a)^[j + 1] h)
      rw [Function.iterate_succ_apply']
      exact antiPrim_nonpositive ha ih

end


end PolyaNeumann

end
