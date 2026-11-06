/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.GammaRatios
public import DOZZ.FourPoint.Dual.ConnectionAlgebra
import Mathlib.Tactic

/-! # The coefficient ratio in ordinary crossing

The connection determinant is (c-1)/(c-a-b). Gamma recurrence is shared with
the dual seed computation; no new independent Gamma identities are assumed.
-/

public section
namespace DOZZ.Proofs

/-- The inverse connection coefficient is exactly l(a)l(b)/(l(c)l(a+b-c)). -/
theorem crossing_connection_first_ratio a b c
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (hc : 0 < c) (hc1 : c < 1)
    (hδ : 0 < c - a - b) (hδ1 : c - a - b < 1) :
    -(Real.Gamma (2 - c) * Real.Gamma (c - a - b) *
        (Real.Gamma (1 - a))⁻¹ * (Real.Gamma (1 - b))⁻¹) /
      ((Real.Gamma c * Real.Gamma (a + b - c) *
        (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹) * ((c - 1) / (c - a - b))) =
      lR a * lR b / (lR c * lR (a + b - c)) := by
  let δ := c - a - b
  rw [(show a + b - c = -δ by dsimp [δ]; ring)]
  calc
    _ = (-δ / (c - 1)) * (Real.Gamma (2 - c) / Real.Gamma c) *
        (Real.Gamma δ / Real.Gamma (-δ)) * lR a * lR b := by
      unfold lR
      change -(Real.Gamma (2 - c) * Real.Gamma δ *
          (Real.Gamma (1 - a))⁻¹ * (Real.Gamma (1 - b))⁻¹) /
        ((Real.Gamma c * Real.Gamma (-δ) * (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹) *
          ((c - 1) / δ)) = _
      field_simp [((Real.Gamma_pos_of_pos ha).ne'), ((Real.Gamma_pos_of_pos hb).ne' : Real.Gamma b ≠ 0), ((Real.Gamma_pos_of_pos (sub_pos.mpr ha1)).ne' : Real.Gamma (1 - a) ≠ 0), ((Real.Gamma_pos_of_pos (sub_pos.mpr hb1)).ne' : Real.Gamma (1 - b) ≠ 0), ((Real.Gamma_pos_of_pos hc).ne' : Real.Gamma c ≠ 0), (Real.Gamma_ne_zero (real_ne_neg_nat_of_frac (k := -1) (by push_cast; dsimp [δ]; linarith only [hδ1]) (by push_cast; dsimp [δ]; linarith only [hδ])) : Real.Gamma (-δ) ≠ 0), (show c - 1 ≠ 0 by linarith only [hc1]), (hδ.ne' : δ ≠ 0)]
    _ = _ := dual_connection_first_multiplier a b c δ hc hc1 hδ hδ1

end DOZZ.Proofs
