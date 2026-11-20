/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.PoleSubtracted.Masses
public import DOZZ.FourPoint.Reflected.CircleTilt

/-!
# The Cameron–Martin tilt by the circle average at the origin

Tilting by `a X_m(0) - m a²/2` (the circle average at radius `e^{-m}` has variance `m`) multiplies
the chaos by `exp (γ a Cov(X(x), X_m(0)))`, and
`Cov(X(x), X_m(0)) = log |x|_+ - log max(e^{-m}, |x|)` ([KRV, Theorem 12.1]). The density is
`circleTiltDensity γ a m`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- **Cameron–Martin tilt by the circle average at the origin.** For real `a`, `m ∈ ℕ` and every
measurable functional `H` of the chaos,
`E[e^{a X_m(0) - m a²/2} H(M)] = E[H(e^{γ a Cov(X(·), X_m(0))} M)]`. -/
theorem lintegral_circleTilt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (a : ℝ) (m : ℕ) (H : Measure ℂ → ℝ≥0∞)
    (hH : Measurable H) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * Xc ω 0 m - m * a ^ 2 / 2)) * H (M ω) ∂P =
      ∫⁻ ω, H ((M ω).withDensity (circleTiltDensity γ a m)) ∂P := by
  delta circleTiltDensity
  simpa only [mul_assoc] using
    reflected_lintegral_circleTilt P X hX γ hγ hγ2 M hM Xc hXc a m (Nat.cast_nonneg m) H hH

end DOZZ.Proofs

end
