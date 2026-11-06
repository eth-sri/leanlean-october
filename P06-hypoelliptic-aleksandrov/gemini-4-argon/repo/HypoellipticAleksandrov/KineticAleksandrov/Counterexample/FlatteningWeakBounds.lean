module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningWeakConvergence
import Mathlib.Tactic.GCongr

/-! # Uniform bounds for flattened smooth approximations on punctured compact sets -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter Set Metric

/- Multiplication by the negative flattening slope preserves an absolute bound. -/
theorem abs_flatSlope_mul_le (s g M : ℝ) (hg : |g| ≤ M) :
    |(-deriv flatteningPsi s) * g| ≤ M := by
  rw [abs_mul, abs_neg]
  have hs : |deriv flatteningPsi s| ≤ 1 := by
    rw [abs_of_nonneg (flatteningPsi_deriv_bounds s).1]
    exact (flatteningPsi_deriv_bounds s).2
  calc
    _ ≤ 1 * M := mul_le_mul hs hg (abs_nonneg _) (by norm_num)
    _ = M := one_mul _

/- The nonlinear Hessian correction is uniformly bounded on bounded first and second jets. -/
theorem abs_flatSecond_le (s gi gk hij alpha r M P : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (hi : |gi| ≤ M) (hk : |gk| ≤ M) (hh : |hij| ≤ M)
    (hP : 0 ≤ P) (hp : deriv (deriv flatteningPsi) s ≤ P) :
    |-deriv flatteningPsi s * hij - Real.rpow r (-alpha) *
        deriv (deriv flatteningPsi) s * gi * gk| ≤ M + Real.rpow r (-alpha) * P * M ^ 2 := by
  simp only [Real.rpow_eq_pow]
  have hpow := (Real.rpow_pos_of_pos hr (-alpha)).le
  have hpabs : |deriv (deriv flatteningPsi) s| ≤ P := by
    rw [abs_of_nonneg (flatteningPsi_deriv2_nonneg s)]
    exact hp
  calc
    _ ≤ |(-deriv flatteningPsi s) * hij| +
        |r ^ (-alpha) * deriv (deriv flatteningPsi) s * gi * gk| := abs_sub _ _
    _ ≤ M + r ^ (-alpha) * P * M ^ 2 := by
      apply add_le_add (abs_flatSlope_mul_le s hij M hh)
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hpow, pow_two]
      calc
        _ ≤ r ^ (-alpha) * P * M * M := by gcongr
        _ = _ := by ring

/- The unflattened approximations and all their classical jets have one eventual compact bound. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
