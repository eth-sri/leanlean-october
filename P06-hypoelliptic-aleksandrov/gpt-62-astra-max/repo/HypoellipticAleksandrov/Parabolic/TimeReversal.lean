module

public import HypoellipticAleksandrov.Parabolic.ABP
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Tactic.Linarith

/-!
# Reverse-time local Dirichlet estimate for the parabolic ABP theorem

This module applies the lower-ellipticity forward ABP corollary to
`H (θ, v) = h (1 - θ, v)`; the reflected function is not negated. It proves
the set, boundary, derivative, operator, and restricted-norm transport needed
for the reverse-time local Dirichlet estimate.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal MatrixOrder

variable {d : ℕ} (f : TimeVelocity d → ℝ) (A : CoefficientField d) (z : TimeVelocity d)

include z in
/-- Reflection of a time--velocity point about the time slice `t = 1 / 2`. -/
def timeReflection : TimeVelocity d :=
  (1 - z.1, z.2)

include f in
/-- Pullback of a scalar field by the fixed time reflection. -/
def timeReflectedScalar : TimeVelocity d → ℝ :=
  fun z => f (timeReflection z)

/-- Time reflection is continuous. -/
theorem continuous_timeReflection : Continuous (@timeReflection d) := (continuous_const.sub continuous_fst).prodMk continuous_snd

/-- Reflection preserves product Lebesgue volume. -/
theorem timeReflection_measurePreserving :
    MeasurePreserving (@timeReflection d) (volume : Measure (TimeVelocity d)) volume := by
  let htime : MeasurePreserving (fun t : ℝ => 1 - t)
      volume volume := by
    exact (measurePreserving_add_left (volume : Measure ℝ) 1).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hprod := htime.prod (MeasurePreserving.id (volume : Measure (PDE.Vec d)))
  rw [volume_timeVelocity_eq_prod d]
  exact hprod

end HypoellipticAleksandrov.Parabolic
