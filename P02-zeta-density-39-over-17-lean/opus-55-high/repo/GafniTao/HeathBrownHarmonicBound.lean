module
public import GafniTao.HeathBrownHarmonicSum
public import Mathlib.NumberTheory.Harmonic.Bounds
import WeylPort.Analytic.RealLaplace

public section

/-!
# The logarithmic loss in Heath-Brown's shift sum

The source replaces the harmonic sum over positive shifts by `O(log N)`.
This file records that replacement with its exact finite endpoint behavior.
-/

namespace GafniTao


theorem harmonic_cast_le_one_add_log_of_le
    {D N : ℕ} (hDN : D ≤ N) (hN : 1 ≤ N) :
    (harmonic D : ℝ) ≤ 1 + Real.log N := by
  by_cases hD0 : D = 0
  · have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    pm_888
    simp [hD0]
    linarith
  · have hDpos : (0 : ℝ) < D := by
      positivity
    calc
      (harmonic D : ℝ) ≤ 1 + Real.log D := harmonic_le_one_add_log D
      _ ≤ 1 + Real.log N := by
        exact add_le_add_right
          (Real.log_le_log hDpos
            (by exact_mod_cast hDN : (D : ℝ) ≤ (N : ℝ))) 1

theorem heathBrownShiftBound_harmonic_le
    {N k H : ℕ} {lambda : ℝ} (hN : 1 ≤ N) :
    (harmonic (heathBrownShiftBound N k H lambda) : ℝ) ≤
      1 + Real.log N :=
  harmonic_cast_le_one_add_log_of_le
    (heathBrownShiftBound_le_N N k H lambda) hN



end GafniTao
