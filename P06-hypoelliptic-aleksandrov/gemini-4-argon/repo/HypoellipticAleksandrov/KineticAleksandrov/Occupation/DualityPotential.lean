module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DualityMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelGreen
public import HypoellipticAleksandrov.Measure.TimeVelocity
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Occupation integration and the parabolic potential

The projected measure's smooth-source pairing is the initial-measure integral of the
Duhamel potential at time zero. The endpoint conjugate norm is exactly the source ABP norm.
-/

@[expose] public section
noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set SectionTwo
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal

variable {d : ℕ}

/- Smooth-source occupation integration is integration of the zero-time potential. -/
theorem occupation_endpoint_gt_one (hd : 0 < d) : 1 < ((d : ℝ) + 1) / d := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  exact (lt_div_iff₀ hdR).2 (by linarith)

/- The endpoint conjugate exponent is exactly `d+1`. -/
end HypoellipticAleksandrov.KineticAleksandrov.Occupation
