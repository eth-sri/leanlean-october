module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.BasisEndpoint
import Mathlib.Tactic

/-!
# Matching a classical solution to the M basis

The positive second solution permits reduction of order without division at a zero.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Set Filter
open scoped Topology

/- The regular M solution has zero scaled derivative at the singular endpoint. -/
theorem tendsto_M_scaled_deriv_zero (a : ℝ) (b : Pos) :
    Tendsto (fun z : ℝ => z * deriv (M a b) z) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun z : ℝ => z * deriv (M a b) z) 0 := by
    simp_rw [deriv_M]
    exact continuousAt_id.mul
      (continuousAt_const.mul (hasDerivAt_M _ _ 0).continuousAt)
  simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

/- Every classical solution with the two endpoint limits is a linear combination of the M basis. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
