/- Shared rank conditions and roots in the determinant-method estimates. -/
module

public import CCDN.AuxiliaryPolynomial.DegreeBound
public import Mathlib.Data.Nat.Choose.Basic

public section
namespace CCDN

/-- The positive-real `r`th root, for the intrinsic dimension parameter `r`. -/
noncomputable abbrev dimensionRoot (r d : ℕ) : ℝ := (d : ℝ) ^ (1 / (r : ℝ))

/-- The exact homogeneous Hilbert rank of a hypersurface, without truncated subtraction. -/
noncomputable abbrev HasHypersurfaceRank (r d M s : ℕ) : Prop :=
  s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M

end CCDN
