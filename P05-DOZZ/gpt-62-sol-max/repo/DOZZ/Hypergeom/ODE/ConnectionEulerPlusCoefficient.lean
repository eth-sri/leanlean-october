/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerFamilyLimits
public import DOZZ.Hypergeom.ODE.ConnectionEndpointLimits
public import DOZZ.Hypergeom.ODE.ConnectionGammaCoefficients

/-! Euler endpoint evaluations for the two `F₊` connection coefficients. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter Set
open scoped Topology

private theorem gaussPlus_power_tendsto_one (c : ℝ) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ ((1 - c : ℝ) : ℂ))
      (𝓝[Iio 1] 1) (𝓝 1) := by
  simpa using (Complex.continuousAt_ofReal_cpow_const 1 ((1 - c : ℝ) : ℂ)
    (Or.inr one_ne_zero)).tendsto.mono_left nhdsWithin_le_nhds

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) (a b c : ℝ) (hA : 0 < a - c + 1)
  (hB : 0 < b - c + 1)
include hH hA hB

/-- In the positive-excess Euler region, the first midpoint coefficient of `F₊` is its Gamma
value. The ordinary Euler integral applies to the shifted parameters in the definition of `F₊`. -/
theorem connectionPlusFirstCramer_eq_gamma_of_real
    (hδ : 0 < c - a - b)
    (hcInt : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ)
    (hδInt : ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ) :
    connectionPlusFirstCramerCoefficient H (a, b, c) =
      gaussConnectionPlusGammaCoefficient₁ (a, b, c) := by
  have h := (gaussPlus_power_tendsto_one c).mul
    (gaussEuler_tendsto_firstGamma hH (a - c + 1) (b - c + 1) (2 - c) hA hB (by linarith))
  exact connectionPlusFirstCramer_eq_of_endpoint_limit hH
    (gaussConnection_real_parameters hcInt hδInt) (by simpa using hδ) (by
    convert h using 2
    · simp [gaussFPlus]
    · simp only [one_mul, gaussConnectionMinusGammaCoefficient₁, gaussConnectionPlusGammaCoefficient₁,
        Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_ofNat]
      ring_nf)

/-- In the negative-excess Euler region, the second midpoint coefficient of `F₊` is its Gamma
value. Euler's transformation moves the shifted integral to positive excess before taking the
endpoint limit. -/
theorem connectionPlusSecondCramer_eq_gamma_of_real
    (h1a : 0 < 1 - a) (h1b : 0 < 1 - b) (hδ : c - a - b < 0)
    (hcInt : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ)
    (hδInt : ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ) :
    connectionPlusSecondCramerCoefficient H (a, b, c) =
      gaussConnectionPlusGammaCoefficient₂ (a, b, c) := by
  have h := (gaussPlus_power_tendsto_one c).mul
    (gaussEuler_tendsto_secondGamma hH (a - c + 1) (b - c + 1) (2 - c) hA hB
      (by linarith) (by linarith) (by linarith))
  exact connectionPlusSecondCramer_eq_of_scaled_endpoint_limit hH
    (gaussConnection_real_parameters hcInt hδInt) (by simp; linarith) (by
    convert h using 2
    · simp only [gaussFPlus, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_ofNat]
      rw [show (2 - (c : ℂ)) - (a - c + 1) - (b - c + 1) = c - a - b by ring]
      ac_rfl
    · simp only [one_mul, gaussConnectionMinusGammaCoefficient₂, gaussConnectionPlusGammaCoefficient₂,
        Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_ofNat]
      ring_nf)

end

end DOZZ.Proofs
