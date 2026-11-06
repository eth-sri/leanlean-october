module

public import PottsDiscontinuity.SixVertex.InfinityCover
public import PottsDiscontinuity.SixVertex.InfinityEigenvector
public import PottsDiscontinuity.SixVertex.InfinityPerron

/-! # The exact largest eigenvalue at negative infinity (Lemma 3.2) -/

public section

open Finset Matrix
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

variable {N n r : ℕ}

section
variable (hn : 0 < n) (hN : N = 2 * (n + r))
include hn hN
/-- The centered free-fermion product is the Perron root of the independent-state
restriction, identified by its strictly positive sine-product eigenvector. -/
theorem pfRoot_infinityRestriction_centered  :
    pfRoot (infinityRestriction N n) = centeredCosineProduct r ((N : ℝ) + 2 * r) := by
  let : Nonempty (IndependentState N n) := ⟨independentPacked (by omega)⟩
  exact pfRoot_eq_of_strictly_positive_eigenvector infinityRestriction_isHermitian
    infinityRestriction_nonneg (fun x => defectGroundWeight_pos (by omega) x.1.1)
    (infinityRestriction_defectGroundWeight_eigen hn hN)

/-- The exact value of the largest eigenvalue of the full limiting block. This
strengthens (3.2) to the equality used in Corollary 3.4, including half filling. -/
theorem pfRoot_infinityBlock_value  :
    pfRoot (infinityBlock N n) =
      2 ^ r * ∏ j ∈ range r,
        (1 + Real.cos (Real.pi * (2 * (j : ℝ) + 1) / ((n : ℝ) + 2 * r))) := by
  rw [pfRoot_infinityBlock_eq_restriction hn (by omega),
    pfRoot_infinityRestriction_centered hn hN]
  have hL : (N : ℝ) + 2 * r = 2 * ((n : ℝ) + 2 * r) := by
    rw [hN]
    grind
  rw [hL, centeredCosineProduct_source]
end

end PottsDiscontinuity.SixVertex
