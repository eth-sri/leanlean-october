module

public import PottsDiscontinuity.SixVertex.Sec33Ratios
public import PottsDiscontinuity.SixVertex.Sec33Symmetry

/-!
# Abstract assembly of the six-vertex dominance gap

The repaired large-width argument for the six-vertex dominance gap (Section 3.3) has external
Potts-model inputs.  This
module proves its finite spectral assembly conditionally on the stated exponential gap for all
`r ≥ 2` and the strict `r = 1` comparison; it does not prove those analytic hypotheses.
-/

@[expose] public section

open Finset Matrix Filter Topology PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ} {c η : ℝ}

/-- Every particle-number block is the sector at its distance from half filling, after using the
global arrow-flip symmetry on the upper half. -/
theorem exists_Lambda_offset_eq_pfRoot (hEven : Even N) {n : ℕ} (hn : n ≤ N) :
    ∃ r ≤ N / 2, pfRoot (transferBlock N c n) = Lambda c N r := by
  by_cases hmid : n ≤ N / 2
  · refine ⟨N / 2 - n, Nat.sub_le _ _, ?_⟩
    unfold Lambda
    have hsub : N / 2 - (N / 2 - n) = n := by omega
    rw [hsub]
  · let r := n - N / 2
    rcases hEven with ⟨k, hk⟩
    have hN : N = 2 * (N / 2) := by omega
    have hr : r ≤ N / 2 := by
      omega
    refine ⟨r, hr, ?_⟩
    have hcomp : N - n = N / 2 - r := by
      omega
    rw [pfRoot_transferBlock_compl (N := N) c hn]
    unfold Lambda
    rw [hcomp]

variable (hc : 0 < c) (hEven : Even N) (hN : 0 < N)
include hc hN

end PottsDiscontinuity.SixVertex
