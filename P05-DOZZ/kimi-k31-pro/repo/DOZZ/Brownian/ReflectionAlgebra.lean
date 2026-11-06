/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.Brownian.ReflectionR

/-!
# Brownian reflection coefficient algebraic bridge

This module isolates the scalar reduction from the full reflection coefficient to its unit-volume
moment. It uses only definition modules; witness independence is proved separately.
-/


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Equality of the unit-volume reflection moments implies equality of the full coefficients. -/
theorem reflectionR_eq_of_reflectionBarR_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (γ μ α : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (B' : Ω' → BrownianPath × BrownianPath) (Z' : Ω' → Measure ℝ)
    (hRbar : reflectionBarR P γ α B Z =
      reflectionBarR P' γ α B' Z') :
    reflectionR P γ μ α B Z = reflectionR P' γ μ α B' Z' := by
  simp [reflectionR, hRbar]

end DOZZ.Proofs

