/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerSeries
public import DOZZ.Hypergeom.ODE.ConnectionEndpointLimits
public import DOZZ.Hypergeom.ODE.ConnectionGammaCoefficients

/-! Evaluation of the first zero-basis connection coefficient from the real Euler integral. -/

public section

namespace DOZZ.Proofs

open Filter Set
open scoped Topology

/-- On the real Euler region, the first midpoint Cramer coefficient is the first Gamma
coefficient. Nonintegrality is retained only for the ODE connection-basis hypotheses. -/
theorem connectionMinusFirstCramer_eq_gamma_of_real
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < c - a - b)
    (hcInt : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ)
    (hδInt : ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ) :
    connectionMinusFirstCramerCoefficient H (a, b, c) =
      gaussConnectionMinusGammaCoefficient₁ (a, b, c) := by
  let p : ℂ × ℂ × ℂ := (a, b, c)
  have hc : 0 < c := by linarith
  have hcb : 0 < c - b := by linarith
  have hca : 0 < c - a := by linarith
  have hp : p ∈ gaussConnectionParameterDomain := by
    change (∀ n : ℤ, (c : ℂ) ≠ (n : ℂ)) ∧
      ∀ n : ℤ, (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ (n : ℂ)
    constructor
    · intro n heq
      apply hcInt
      exact ⟨n, heq.symm⟩
    · intro n heq
      apply hδInt
      refine ⟨n, ?_⟩
      simp_all
  have hEulerValue :
      Tendsto (fun x : ℝ =>
        ((Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) : ℝ) : ℂ) *
          (realGaussEulerKernelIntegral a b c x : ℂ))
        (𝓝[Iio 1] 1)
        (𝓝 ((Real.Gamma c * Real.Gamma (c - a - b) /
          (Real.Gamma (c - a) * Real.Gamma (c - b)) : ℝ) : ℂ)) := by
    convert Complex.continuous_ofReal.continuousAt.tendsto.comp
      (realGaussEulerKernelIntegral_tendsto_gauss_value a b c ha hb hδ) using 1
    aesop
  have hxpos : ∀ᶠ x : ℝ in 𝓝[Iio 1] 1, 0 < x := Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hxlt : ∀ᶠ x : ℝ in 𝓝[Iio 1] 1, x < 1 := by
    change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1
    simpa only [mem_Iio] using
      (eventually_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1)
  have hEulerEq : ∀ᶠ x : ℝ in 𝓝[Iio 1] 1,
      H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) =
        ((Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) : ℝ) : ℂ) *
          (realGaussEulerKernelIntegral a b c x : ℂ) := by
    filter_upwards [hxpos, hxlt] with x hx hx1
    have heq := realGaussEulerIntegral_eq_family hH a b c x ha hb hcb hx hx1
    simpa [realGaussEulerKernelIntegral] using heq.symm
  have hEulerEq'  :=
    hEulerEq.mono fun x hx => hx.symm
  have hF : Tendsto
      (fun x : ℝ => gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ))
      (𝓝[Iio 1] 1)
      (𝓝 ((Real.Gamma c * Real.Gamma (c - a - b) /
          (Real.Gamma (c - a) * Real.Gamma (c - b)) : ℝ) : ℂ)) := by
    simpa [gaussFMinus] using Filter.Tendsto.congr' hEulerEq' hEulerValue
  have hδre : 0 < (((c : ℂ) - (a : ℂ) - (b : ℂ)).re) := by
    simp_all
  have hcoeff := connectionMinusFirstCramer_eq_of_endpoint_limit hH hp hδre hF
  have hGamma :
      ((Real.Gamma c * Real.Gamma (c - a - b) /
          (Real.Gamma (c - a) * Real.Gamma (c - b)) : ℝ) : ℂ) =
        gaussConnectionMinusGammaCoefficient₁ p := by
    have hΓc  := (Real.Gamma_pos_of_pos hc).ne'
    have hΓδ  :=
      (Real.Gamma_pos_of_pos hδ).ne'
    have hΓca  := (Real.Gamma_pos_of_pos hca).ne'
    have hΓcb  := (Real.Gamma_pos_of_pos hcb).ne'
    dsimp [gaussConnectionMinusGammaCoefficient₁, p]
    rw [show (c : ℂ) - (a : ℂ) - (b : ℂ) = ((c - a - b : ℝ) : ℂ) by push_cast; ring,
      show (c : ℂ) - (a : ℂ) = ((c - a : ℝ) : ℂ) by push_cast; ring,
      show (c : ℂ) - (b : ℂ) = ((c - b : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal c, Complex.Gamma_ofReal (c - a - b),
      Complex.Gamma_ofReal (c - a), Complex.Gamma_ofReal (c - b)]
    push_cast
    field_simp [hΓc, hΓδ, hΓca, hΓcb]
  simpa [p] using hcoeff.trans hGamma

end DOZZ.Proofs
