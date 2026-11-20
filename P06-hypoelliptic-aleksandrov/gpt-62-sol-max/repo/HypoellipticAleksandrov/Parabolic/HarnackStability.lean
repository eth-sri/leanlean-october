module

public import HypoellipticAleksandrov.Parabolic.HarnackPerturbation
public import HypoellipticAleksandrov.Parabolic.HarnackStabilityLimit
public import HypoellipticAleksandrov.Parabolic.WeakSolutionMollifierResidualConvergence

/-!
# Aligned approximation stability for parabolic Harnack

This module passes the finite source-bearing Harnack chain estimate through a
common compact-uniform smooth approximation and then applies it to the aligned
mollifications of a nonnegative local weak solution.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open scoped Matrix.Norms.Elementwise

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- Extended restricted parabolic norm convergence to zero gives convergence of the
corresponding real restricted norm. -/
theorem tendsto_parabolicLpNormOn_of_tendsto_parabolicELpNormOn_zero
    {d : Nat} {K : Set (TimeVelocity d)}
    {R : Nat -> TimeVelocity d -> Real}
    (hR : Tendsto (fun n => parabolicELpNormOn d (R n) K)
      atTop (nhds 0)) :
    Tendsto (fun n => parabolicLpNormOn d (R n) K)
      atTop (nhds 0) := by
  simpa only [parabolicLpNormOn, Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hR

end HypoellipticAleksandrov.Parabolic
