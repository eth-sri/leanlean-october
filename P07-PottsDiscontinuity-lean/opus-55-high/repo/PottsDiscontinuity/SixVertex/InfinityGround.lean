module

public import PottsDiscontinuity.SixVertex.InfinitySupport

/-!
# The positive sine-product candidate on the original defect carrier

The shifted coordinates are `X_j + j` and their circumference is
`N + card(defects x)`. Positivity holds directly for this actual finite candidate.
Its eigenvector equation is not asserted in this file.
-/

@[expose] public noncomputable section

open Finset

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ}

section
variable (x : Finset (Fin N))
/-- Canonically ordered defect positions, shifted by their zero-based labels. -/
def defectCoordinate (j : Fin (defects x).card) : ℕ :=
  ((defects x).orderEmbOfFin rfl j).val + j.val

/-- The Vandermonde sine product evaluated on the shifted defect coordinates. -/
def defectGroundWeight  : ℝ :=
  ∏ a : Fin (defects x).card, ∏ b ∈ Ioi a,
    Real.sin (Real.pi * ((defectCoordinate x b : ℝ) - defectCoordinate x a) /
      ((N : ℝ) + (defects x).card))

theorem defectCoordinate_strictMono  : StrictMono (defectCoordinate x) := by
  intro a b hab
  have hp := (defects x).orderEmbOfFin rfl |>.strictMono hab
  unfold defectCoordinate
  omega

theorem defectCoordinate_lt (j : Fin (defects x).card) :
    defectCoordinate x j < N + (defects x).card := by
  grind [defectCoordinate]
end

/-- The candidate is strictly positive, with the empty product included. -/
theorem defectGroundWeight_pos (hN : 0 < N) (x : Finset (Fin N)) :
    0 < defectGroundWeight x := by
  apply prod_pos
  intro a _
  apply prod_pos
  intro b hb
  have hp := defectCoordinate_strictMono x (mem_Ioi.mp hb)
  have hdiff : (0 : ℝ) < (defectCoordinate x b : ℝ) - defectCoordinate x a := by
    simp_all
  have hbound : (defectCoordinate x b : ℝ) - defectCoordinate x a <
      (N : ℝ) + (defects x).card := by
    have hcast : (defectCoordinate x b : ℝ) < (N : ℝ) + (defects x).card := by
      exact_mod_cast (defectCoordinate_lt x b)
    linarith
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [div_lt_iff₀ (by positivity)]
    exact mul_lt_mul_of_pos_left hbound Real.pi_pos

end PottsDiscontinuity.SixVertex
