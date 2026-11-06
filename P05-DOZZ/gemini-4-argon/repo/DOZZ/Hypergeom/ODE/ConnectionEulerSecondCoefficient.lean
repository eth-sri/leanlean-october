/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerTransform
public import DOZZ.Hypergeom.ODE.ConnectionEndpointLimits
public import DOZZ.Hypergeom.ODE.ConnectionGammaCoefficients

/-! Evaluation of the second zero-basis connection coefficient from Euler's transformation. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter Set
open scoped Topology

/-- On the negative-excess real Euler region, the second midpoint Cramer coefficient is the
second Gamma coefficient. Euler's transformation converts the endpoint into a positive-excess
Euler integral, where dominated convergence applies. -/
theorem connectionMinusSecondCramer_eq_gamma_of_real
    {H} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hca : 0 < c - a) (hcb : 0 < c - b) (hδ : c - a - b < 0)
    (hcInt : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ)
    (hδInt : ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ) :
    connectionMinusSecondCramerCoefficient H (a, b, c) =
      gaussConnectionMinusGammaCoefficient₂ (a, b, c) := by
  let p : ℂ × ℂ × ℂ := (a, b, c)
  have heta : 0 < a + b - c := by linarith
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
      calc
        (n : ℂ) = (c : ℂ) - (a : ℂ) - (b : ℂ) := heq.symm
        _ = ((c - a - b : ℝ) : ℂ) := by push_cast; ring
  let F : Filter ℝ := 𝓝[Iio 1] 1
  let η : ℝ := a + b - c
  have hcb' : c - (c - b) = b := by ring
  have hEulerEq :
      (fun x : ℝ => (1 - (x : ℂ)) ^ (-((c : ℂ) - (a : ℂ) - (b : ℂ))) *
        gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)) =ᶠ[F]
      (fun x : ℝ =>
        (Real.Gamma c : ℂ) /
          ((Real.Gamma (c - b) : ℂ) * (Real.Gamma b : ℂ)) *
          (realGaussEulerKernelIntegral (c - a) (c - b) c x : ℂ)) := by
    filter_upwards [(by dsimp [F]; exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))), (by dsimp [F]; change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1; simpa only [mem_Iio] using (eventually_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1))] with x hx hx1
    calc
      _ = (1 - (x : ℂ)) ^ (-((c : ℂ) - (a : ℂ) - (b : ℂ))) *
          ((1 - (x : ℂ)) ^ ((c : ℂ) - (a : ℂ) - (b : ℂ)) *
            H (c - a : ℝ) (c - b : ℝ) (c : ℝ) (x : ℝ)) := by
        rw [show gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) =
          H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) by rfl, (realGaussEulerTransform_family hH a b c x ha hb hca hcb hx hx1)]
      _ = H (c - a : ℝ) (c - b : ℝ) (c : ℝ) (x : ℝ) := (by rw [← mul_assoc, ← Complex.cpow_add _ _ (show (1 : ℂ) - (x : ℂ) ≠ 0 by apply sub_ne_zero.mpr; exact_mod_cast (ne_of_lt hx1).symm), neg_add_cancel, Complex.cpow_zero, one_mul])
      _ = (Real.Gamma c : ℂ) /
          ((Real.Gamma (c - b) : ℂ) * (Real.Gamma b : ℂ)) *
          (realGaussEulerKernelIntegral (c - a) (c - b) c x : ℂ) := by
        simpa [realGaussEulerKernelIntegral, Complex.ofReal_div,
          Complex.ofReal_mul] using (realGaussEulerIntegral_eq_family hH (c - a) (c - b) c x hca hcb (by rw [hcb']; exact hb) hx hx1).symm
  have hcastEta : p.1 + p.2.1 - p.2.2 = ((a + b - c : ℝ) : ℂ) := by
    change (a : ℂ) + (b : ℂ) - (c : ℂ) = ((a + b - c : ℝ) : ℂ)
    push_cast
    ring
  have hGamma :
      ((Real.Gamma c * Real.Gamma η /
          (Real.Gamma a * Real.Gamma b) : ℝ) : ℂ) =
        gaussConnectionMinusGammaCoefficient₂ p := by
    dsimp [gaussConnectionMinusGammaCoefficient₂, p, η]
    rw [show (a : ℂ) + (b : ℂ) - (c : ℂ) = ((a + b - c : ℝ) : ℂ) by
      push_cast; ring,
      Complex.Gamma_ofReal c, Complex.Gamma_ofReal (a + b - c),
      Complex.Gamma_ofReal a, Complex.Gamma_ofReal b]
    push_cast
    field_simp [((Real.Gamma_pos_of_pos (by linarith)).ne'), ((Real.Gamma_pos_of_pos heta).ne'), ((Real.Gamma_pos_of_pos ha).ne'), ((Real.Gamma_pos_of_pos hb).ne')]
  simpa [p] using (connectionMinusSecondCramer_eq_of_scaled_endpoint_limit hH hp (by rw [hcastEta]; simp only [Complex.ofReal_re]; exact heta) (by simpa [F, p, η] using ((show Tendsto (fun x : ℝ => ((Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b) : ℂ) * (realGaussEulerKernelIntegral (c - a) (c - b) c x : ℂ))) F (𝓝 ((Real.Gamma c * Real.Gamma η / (Real.Gamma a * Real.Gamma b) : ℝ) : ℂ)) by exact (show Tendsto (fun x : ℝ => (((Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b) : ℝ) * realGaussEulerKernelIntegral (c - a) (c - b) c x : ℝ) : ℂ)) F (𝓝 ((Real.Gamma c * Real.Gamma η / (Real.Gamma a * Real.Gamma b) : ℝ) : ℂ)) by simpa only [Function.comp_def] using (Complex.continuous_ofReal.continuousAt.tendsto.comp (by simpa only [(show c - (c - a) = a by ring), hcb', (show a - (c - b) = η by dsimp [η]; ring)] using (realGaussEulerKernelIntegral_tendsto_gauss_value (c - a) (c - b) c hca hcb (by rw [show c - (c - a) - (c - b) = a + b - c by ring]; exact heta))))).congr' (by filter_upwards with x; rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_mul])).congr' hEulerEq.symm))).trans (by simpa only [Complex.ofReal_mul, Complex.ofReal_div] using hGamma)

end DOZZ.Proofs
