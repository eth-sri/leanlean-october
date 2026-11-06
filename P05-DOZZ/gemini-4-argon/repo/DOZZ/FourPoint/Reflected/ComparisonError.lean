/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceFullComparison
import Mathlib.Tactic
/-! The actual two-sided moment comparison gives a signed scalar error bound. -/
@[expose] public section
open scoped ENNReal
namespace DOZZ.Proofs

/-- Finite moments with two-sided multiplicative comparison differ by the comparison error.
Only the original moment needs a finiteness bound; the copied one inherits it. -/
theorem reflected_moment_comparison_error (a b : ℝ≥0∞) m (hm : 1 ≤ m)
    (ha : a ≠ ⊤) (hab : a ≤ ENNReal.ofReal m*b) (hba : b ≤ ENNReal.ofReal m*a) :
    b ≠ ⊤ ∧ |a.toReal-b.toReal| ≤ (m-1)*m*a.toReal := by
  have hm0 := zero_le_one.trans hm
  have hb := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha) hba
  have hba' : b.toReal ≤ m*a.toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hm0] using (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha) hba)
  have hm1 := sub_nonneg.mpr hm
  refine ⟨hb, abs_sub_le_iff.mpr ⟨?_, ?_⟩⟩
  · calc a.toReal-b.toReal ≤ (m-1)*b.toReal := by linarith only [(by simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hm0] using (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb) hab))]
         _ ≤ (m-1)*m*a.toReal := by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hba' hm1)
  · calc b.toReal-a.toReal ≤ (m-1)*a.toReal := by linarith only [hba']
         _ ≤ (m-1)*m*a.toReal := by
           simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (ENNReal.toReal_nonneg (a := a)) hm) hm1

end DOZZ.Proofs
