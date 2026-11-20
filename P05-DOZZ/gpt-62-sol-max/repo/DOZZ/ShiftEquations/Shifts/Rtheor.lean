/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import DOZZ.ShiftEquations.Shifts.Seeds.SeedTwo

public import DOZZ.Brownian.Reflection.RtheorIdentification
public import DOZZ.Statements.FourPoint.DualCrossingL
import DOZZ.Brownian.ReflectionPoleIsolation
import DOZZ.ShiftEquations.Shift.FirstShift
import DOZZ.ShiftEquations.DualR.Assembly
import DOZZ.ShiftEquations.Reflection.EndpointContinuity
public import DOZZ.ShiftEquations.Representatives

/-!
# `R = R^DOZZ` from the two reflection shifts
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- **`R = R^DOZZ` off the poles, from the second dual seed.** `hseedTwo` is the complete statement
of `dual_crossing_seed_two` at universe `0`. -/
theorem reflection_Rtheor_off_poles_of_seedTwo
    (hseedTwo : DualCrossingSeedTwo.{0})
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ α : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : γ / 2 < α ∧ α < Q γ) (hPole : ReflectionPoleFree γ α)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) :
    (reflectionR P γ μ α B Z : ℂ) = reflectionDOZZ γ μ (α : ℂ) :=
  reflection_Rtheor_off_poles_of_shift_equations
    reflectionR_first_shift_meromorphic
    (fun P X M γ μ hγ hγ2 hγirr hμ hX hM =>
      reflectionR_dual_shift_unknown_constant P X M γ μ hγ hγ2 hγirr hμ hX hM
        fun α ε α' h1 h2 h3 h4 => hseedTwo P M X γ μ α ε α' hγ hγ2 hμ h1 h2 h3 h4 hX hM)
    reflection_endpoint_and_gamma_continuity
    P γ μ α hγ hγ2 hμ hα hPole B Z hData

/-- The probabilistic reflection coefficient equals the DOZZ coefficient off its poles. -/
theorem reflection_Rtheor_off_poles
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ α : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : γ / 2 < α ∧ α < Q γ) (hPole : ReflectionPoleFree γ α)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) :
    (reflectionR P γ μ α B Z : ℂ) = reflectionDOZZ γ μ (α : ℂ) :=
  reflection_Rtheor_off_poles_of_seedTwo dual_crossing_seed_two P γ μ α hγ hγ2 hμ hα hPole B Z hData

end DOZZ.Proofs

end
