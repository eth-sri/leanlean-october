module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

/-!
# Factorial estimates for iterated boundary primitives

The iterates in this file are actual complex interval integrals, starting from an
arbitrary continuous function.  Bounds on the coefficient and the initial function
are required only on the interval in the estimate.

This supplies the factorial estimate for a Volterra primitive.  Identifying the
Fourier-defined boundary `antiPrim` with this interval primitive (including the
choice of integration constant and any zero-mode correction) is a separate bridge;
no such identification is assumed or proved here.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace PolyaNeumann

/-- Iteration of the genuine primitive `f ↦ (t ↦ ∫ s in 0..t, a s * f s)`. -/
def volterraPrimitiveIterate (a h : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => h
  | n + 1 => fun t => ∫ s in (0 : ℝ)..t, a s * volterraPrimitiveIterate a h n s

variable {a h : ℝ → ℂ}

/-- Continuity of every genuine primitive iterate. -/
theorem continuous_volterraPrimitiveIterate (ha : Continuous a) (hh : Continuous h) :
    ∀ n, Continuous (volterraPrimitiveIterate a h n)
  | 0 => hh
  | n + 1 => intervalIntegral.continuous_primitive
      (fun x y =>
        (ha.mul (continuous_volterraPrimitiveIterate ha hh n)).intervalIntegrable x y) 0

section

variable (ha : Continuous a) (hh : Continuous h)
include ha hh

/-- The continuous integrand defining the next iterate is interval integrable. -/
theorem intervalIntegrable_volterraPrimitiveIntegrand
     (n : ℕ) (x y : ℝ) :
    IntervalIntegrable (fun s => a s * volterraPrimitiveIterate a h n s) volume x y :=
  (ha.mul (continuous_volterraPrimitiveIterate ha hh n)).intervalIntegrable x y



end


/-- The next iterate has the genuine derivative prescribed by its continuous integrand. -/
theorem hasDerivAt_volterraPrimitiveIterate_succ
    (ha : Continuous a) (hh : Continuous h) (n : ℕ) (t : ℝ) :
    HasDerivAt (volterraPrimitiveIterate a h (n + 1))
      (a t * volterraPrimitiveIterate a h n t) t := by
  have hc := ha.mul (continuous_volterraPrimitiveIterate ha hh n)
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_volterraPrimitiveIntegrand ha hh n 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

end PolyaNeumann

end
