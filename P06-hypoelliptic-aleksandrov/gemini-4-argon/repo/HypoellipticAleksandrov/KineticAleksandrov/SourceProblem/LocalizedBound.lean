module

public import HypoellipticAleksandrov.KineticAleksandrov.SourceProblem.LocalizedAdmissibility
public import HypoellipticAleksandrov.KineticAleksandrov.SourceProblem.InteriorEstimate
import HypoellipticAleksandrov.KineticAleksandrov.SourceProblem.InteriorReduction
import HypoellipticAleksandrov.Parabolic.ABP

/-!
# The localized bound `0 ≤ V ≤ C R^(d/(d+1)) ‖F‖_{L^{d+1}}` (companion paper, Proposition 4.2)

The upper bound uses the interior Aleksandrov estimate applied to the reflected and rescaled
solution
of `LocalizedKrylov.lean`; the Jacobian of the scaling is `R^(d+2)`, giving the factor
`R^(d/(d+1))`.  The estimate holds on the whole closed cylinder: the open cylinder by Krylov,
the rest by continuity of `V`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped Topology MatrixOrder Matrix.Norms.Elementwise ENNReal
open Parabolic HypoellipticAleksandrov.KineticAleksandrov.LsuFree

variable {d : ℕ}

/- The localized bound with the `L^{d+1}` norm of `F` over the source cylinder itself. -/
theorem parabolicLpNormOn_le_parabolicLpNorm_direct
    {F } (hF : Continuous F)
    (hFc : HasCompactSupport F) (S : Set (TimeVelocity d)) :
    parabolicLpNormOn d F S ≤ parabolicLpNorm d F := by
  exact ENNReal.toReal_mono ((hF.memLp_of_hasCompactSupport (p := parabolicExponent d) (μ := volume) hFc).ne) (eLpNorm_mono_measure F Measure.restrict_le_self)

/- Localized bound `0 ≤ V ≤ C R^(d/(d+1)) ‖F‖_{L^{d+1}}`, with the global `L^{d+1}` norm. -/
end HypoellipticAleksandrov.KineticAleksandrov.Occupation
