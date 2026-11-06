/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceFullComparison
import Mathlib.Tactic
/-! The actual two-sided moment comparison gives a signed scalar error bound. -/
public section
open scoped ENNReal
namespace DOZZ.Proofs

/-- Finite moments with two-sided multiplicative comparison differ by the comparison error.
Only the original moment needs a finiteness bound; the copied one inherits it. -/
theorem reflected_moment_comparison_error (a b : ℝ≥0∞) (m : ℝ) (hm : 1 ≤ m)
    (ha : a ≠ ⊤) (hab : a ≤ ENNReal.ofReal m*b) (hba : b ≤ ENNReal.ofReal m*a) :
    b ≠ ⊤ ∧ |a.toReal-b.toReal| ≤ (m-1)*m*a.toReal := by
  have hm0  := zero_le_one.trans hm
  have hb  := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha) hba
  have hab' : a.toReal ≤ m*b.toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb) hab
    simp_all
  have hba' : b.toReal ≤ m*a.toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha) hba
    simp_all
  have hm1  := sub_nonneg.mpr hm
  have hbound := mul_le_mul_of_nonneg_left hba' hm1
  have ha0 := ENNReal.toReal_nonneg (a := a)

  refine ⟨hb, abs_sub_le_iff.mpr ⟨?_, ?_⟩⟩
  · grind
  · calc b.toReal-a.toReal ≤ (m-1)*a.toReal := by linarith only [hba']
         _ ≤ (m-1)*m*a.toReal := by
           bound

end DOZZ.Proofs
