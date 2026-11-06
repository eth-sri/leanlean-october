module
public import Mathlib

public import PottsDiscontinuity.SixVertex.InfinitySupport

/-!
# The positive sine-product candidate on the original defect carrier

The shifted coordinates are `X_j + j` and their circumference is
`N + card(defects x)`. Positivity holds directly for this actual finite candidate.
Its eigenvector equation is not asserted in this file.
-/

@[expose] public section

open Finset

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ}

/-- Canonically ordered defect positions, shifted by their zero-based labels. -/
noncomputable def defectCoordinate (x : Finset (Fin N))
    (j : Fin (defects x).card)  :=
  ((defects x).orderEmbOfFin rfl j).val + j.val

/-- The Vandermonde sine product evaluated on the shifted defect coordinates. -/
noncomputable def defectGroundWeight (x : Finset (Fin N))  :=
  ∏ a : Fin (defects x).card, ∏ b ∈ Ioi a,
    Real.sin (Real.pi * ((defectCoordinate x b : ℝ) - defectCoordinate x a) /
      ((N : ℝ) + (defects x).card))

theorem defectCoordinate_strictMono (x : Finset (Fin N)) : StrictMono (defectCoordinate x) := by
  intro a b hab
  have hp := (defects x).orderEmbOfFin rfl |>.strictMono hab
  
  
  unfold defectCoordinate
  omega

theorem defectCoordinate_lt (x : Finset (Fin N)) (j : Fin (defects x).card) :
    defectCoordinate x j < N + (defects x).card := by
  grind +locals

/-- The candidate is strictly positive, with the empty product included. -/
theorem defectGroundWeight_pos (hN : 0 < N) (x : Finset (Fin N)) :
    0 < defectGroundWeight x := by
  apply prod_pos
  intro a _
  apply prod_pos
  intro b hb
  
  
  
  
  
  
  
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos (mul_pos Real.pi_pos (sub_pos.mpr (Nat.cast_lt.mpr (defectCoordinate_strictMono x (mem_Ioi.mp hb))))) (by positivity)
  · rw [div_lt_iff₀ (by positivity)]
    exact mul_lt_mul_of_pos_left (by
                                    have hcast :  defectCoordinate x b  < (N : ℝ) + (defects x).card := by
                                      exact_mod_cast (defectCoordinate_lt x b)
                                    grind) Real.pi_pos

end PottsDiscontinuity.SixVertex
