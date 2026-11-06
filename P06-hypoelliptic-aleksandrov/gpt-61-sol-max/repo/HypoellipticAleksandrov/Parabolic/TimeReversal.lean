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

open MeasureTheory
open scoped MatrixOrder

variable {d : ℕ}

/-- Reflection of a time--velocity point about the time slice `t = 1 / 2`. -/
def timeReflection  (z : TimeVelocity d) : TimeVelocity d :=
  (1 - z.1, z.2)

/-- Pullback of a scalar field by the fixed time reflection. -/
def timeReflectedScalar  (f : HypoellipticAleksandrov.Parabolic.ScalarField d) : HypoellipticAleksandrov.Parabolic.ScalarField d :=
  fun z => f (timeReflection z)

/-- Pullback of a curried coefficient field by the fixed time reflection. -/
def timeReflectedCoefficient  (A : CoefficientField d) : CoefficientField d :=
  fun t v => A (1 - t) v

/-- Evaluation of a reflected scalar field. -/
@[simp] theorem timeReflectedScalar_apply  (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (z : TimeVelocity d) :
    timeReflectedScalar f z = f (timeReflection z) :=
  rfl



/-- Time reflection is an involution. -/
@[simp] theorem timeReflection_involutive  :
    Function.Involutive (@timeReflection d) := by
  intro z
  ext <;> simp [timeReflection]

/-- Time reflection is continuous. -/
theorem continuous_timeReflection  : Continuous (@timeReflection d) := (continuous_const.sub continuous_fst).prodMk continuous_snd

/-- Coefficient pullback preserves continuity. -/
theorem isContinuousCoefficient_timeReflected  {A : CoefficientField d}
    (hA : IsContinuousCoefficient A) :
    IsContinuousCoefficient (timeReflectedCoefficient A) := (id (Continuous.comp hA continuous_timeReflection))

/-- Reflection preserves product Lebesgue volume. -/
theorem timeReflection_measurePreserving  :
    MeasurePreserving (@timeReflection d) (volume )  := by
  let htime : MeasurePreserving (fun t : ℝ => 1 - t)
      (volume ) volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      (measurePreserving_add_left (volume : Measure ℝ) 1).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hprod := htime.prod (MeasurePreserving.id (volume : Measure (PDE.Vec d)))
  assumption

end HypoellipticAleksandrov.Parabolic
