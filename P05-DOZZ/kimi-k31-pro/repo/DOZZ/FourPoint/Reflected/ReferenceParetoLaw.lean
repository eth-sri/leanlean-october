/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DOZZ.FourPoint.Dual.ReferencePareto
import DOZZ.FourPoint.Reflected.MaximumParetoLaw
/-! The exponentiated Williams reference maximum has the literal Pareto law. -/
open MeasureTheory ProbabilityTheory
namespace DOZZ.Proofs

/-- The independent reference maximum used in the transported Williams model is exactly the
Pareto variable used in the signed source estimates. -/
theorem reflected_maximum_reference_pareto_law
    (B₀ : Measure BrownianPath) (hB₀ : IsBrownianReal (fun t p => p t) B₀)
    (γ ν : ℝ) (hγ : 0 < γ) (hν : 0 < ν) :
    (brownianMaximumReferenceLaw ν).map (fun m => Real.exp (γ*m)) =
      paretoMeasure 1 (2*ν/γ) := DOZZ.Proofs.dual_reference_maximum_exp_pareto_law B₀ hB₀ γ ν hγ hν

end DOZZ.Proofs
