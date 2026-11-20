module

public import HypoellipticAleksandrov.Parabolic.WeakDerivativesLocal
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Distributional uniqueness for weak time--velocity derivatives

This module proves uniqueness of locally integrable weak derivative
representatives on open time--velocity domains, and the resulting coherence
of the selected representatives in a parabolic weak jet.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace ParabolicMemLpOn

/-- Restricted `L^p` membership with exponent at least one is locally
integrable on the underlying raw set. -/
theorem locallyIntegrableOn {d : ℕ} {U : Set (TimeVelocity d)}
    {p : ℝ≥0∞} {f : TimeVelocity d → ℝ}
    (hf : ParabolicMemLpOn U p f) (hp : 1 ≤ p) :
    LocallyIntegrableOn f U volume := by
  exact locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable hp)

end ParabolicMemLpOn

end HypoellipticAleksandrov.Parabolic
