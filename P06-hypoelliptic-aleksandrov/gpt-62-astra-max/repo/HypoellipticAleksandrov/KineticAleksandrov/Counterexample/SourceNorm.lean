module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic.Linarith

/-! # The radius-uniform subcritical source norm -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/-- The shell norm powers combine to the precise source exponent. -/
theorem source_norm_rpow_identity (d : ℕ) (alpha p V K r : ℝ)
    (hp : 0 < p) (hV : 0 < V) (hK : 0 ≤ K) (hr : 0 < r) :
    ENNReal.ofReal (K * Real.rpow r (alpha - 2)) *
      ENNReal.ofReal (V * r ^ (4 * d)) ^ (1 / p) =
        ENNReal.ofReal (K * Real.rpow V (1 / p) *
          Real.rpow r (alpha - 2 + 4 * d / p)) := by
  simp only [Real.rpow_eq_pow]
  rw [ENNReal.ofReal_rpow_of_nonneg
    (mul_nonneg hV.le (pow_nonneg hr.le _))
    (div_nonneg zero_le_one hp.le),
    ← ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_pos_of_pos hr _).le),
    Real.mul_rpow hV.le (pow_nonneg hr.le _), ← Real.rpow_natCast_mul hr.le]
  have he : (4 * d : ℕ) * (1 / p : ℝ) = 4 * (d : ℝ) / p := by
    push_cast
    ring
  rw [he]
  congr 1
  calc
    _ = (K * V ^ (1 / p)) * (r ^ (alpha - 2) * r ^ (4 * d / p)) := by ring
    _ = _ := by rw [← Real.rpow_add hr]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
