module
public import GuthMaynard.NativeSource.GuthMaynard.DFIEquation26
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.Harmonic.Bounds
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# The epsilon bound for the divisor function

DFI use the standard estimate `d(n) \ll_\varepsilon n^\varepsilon`
after equation (26).  This file proves that estimate from factorization,
with the dependence on `\varepsilon` represented by an existential constant.
-/

open scoped BigOperators

namespace GuthMaynard.NativeMoment

/-- The harmonic loss is bounded by any prescribed positive power, with an
explicit epsilon-dependent constant. -/
theorem harmonic_le_epsilon_rpow
    {ε : ℝ} (hε : 0 < ε) (L : ℕ) :
    ((harmonic L : ℚ) : ℝ) ≤
      (1 + ε⁻¹) * max 1 ((L : ℝ) ^ ε) := by
  by_cases hL : L = 0
  · simp [hL, add_nonneg zero_le_one (inv_nonneg.mpr hε.le)]
  pm_117 hLPos L
  have hLone : (1 : ℝ) ≤ L := by aesop
  have hpowOne : (1 : ℝ) ≤ (L : ℝ) ^ ε := by
    pm_4844 hLone
  have hlogPower := Real.log_le_sub_one_of_pos
    (Real.rpow_pos_of_pos hLPos ε)
  rw [Real.log_rpow hLPos] at hlogPower
  have hlog : Real.log L ≤ ε⁻¹ * ((L : ℝ) ^ ε - 1) := by
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hε).2 (by grind)
  calc
    ((harmonic L : ℚ) : ℝ) ≤ 1 + Real.log L := harmonic_le_one_add_log L
    _ ≤ 1 + ε⁻¹ * ((L : ℝ) ^ ε - 1) := by linarith
    _ ≤ (1 + ε⁻¹) * ((L : ℝ) ^ ε) := by
      pm_4935 hinv ε hε.le
      nlinarith
    _ ≤ (1 + ε⁻¹) * max 1 ((L : ℝ) ^ ε) := by simp_all

end GuthMaynard.NativeMoment
