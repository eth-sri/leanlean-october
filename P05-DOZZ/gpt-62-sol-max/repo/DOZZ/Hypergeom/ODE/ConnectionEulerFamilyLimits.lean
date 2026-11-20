/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerTransform
public import DOZZ.Hypergeom.ODE.ConnectionGammaCoefficients
public import DOZZ.Hypergeom.ODE.ConnectionAnalyticContinuation

/-! The ordinary and scaled Euler endpoint limits for positive and negative excess. -/

@[expose] public section

open Filter Set Topology

namespace DOZZ.Proofs

private theorem eventually_between_zero_one : ∀ᶠ x : ℝ in 𝓝[Iio 1] 1, x ∈ Ioo 0 1 :=
  (eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds zero_lt_one)).and
    eventually_mem_nhdsWithin

theorem gaussConnection_real_parameters {a b c : ℝ}
    (hc : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ)
    (hδ : ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ) :
    ((a : ℂ), (b : ℂ), (c : ℂ)) ∈ gaussConnectionParameterDomain := by
  refine ⟨fun n h => hc ⟨n, h.symm⟩, fun n h => hδ ⟨n, ?_⟩⟩
  simpa only [Complex.ofReal_sub] using h.symm

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) (a b c : ℝ) (ha : 0 < a)
  (hb : 0 < b)
include hH ha hb

theorem gaussEuler_tendsto_firstGamma (hδ : 0 < c - a - b) :
    Tendsto (fun x : ℝ => H a b c x) (𝓝[Iio 1] 1)
      (𝓝 (gaussConnectionMinusGammaCoefficient₁ (a, b, c))) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (realGaussEulerKernelIntegral_tendsto_gauss_value a b c ha hb hδ)
  change Tendsto (fun x : ℝ => ↑(Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) *
      realGaussEulerKernelIntegral a b c x) : ℝ → ℂ) (𝓝[Iio 1] 1) _ at h
  have hlim : (↑(Real.Gamma c * Real.Gamma (c - a - b) /
        (Real.Gamma (c - a) * Real.Gamma (c - b))) : ℂ) =
      gaussConnectionMinusGammaCoefficient₁ (a, b, c) := by
    simp only [gaussConnectionMinusGammaCoefficient₁, Complex.ofReal_mul, Complex.ofReal_div,
      ← Complex.Gamma_ofReal, Complex.ofReal_sub, Complex.ofReal_inv, div_eq_mul_inv, mul_inv]
    ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_between_zero_one] with x hx
  simpa only [realGaussEulerKernelIntegral, realGaussEulerKernel, Complex.ofReal_mul] using
    realGaussEulerIntegral_eq_family hH a b c x ha hb (by linarith) hx.1 hx.2

theorem gaussEuler_tendsto_secondGamma (hca : 0 < c - a) (hcb : 0 < c - b)
    (hδ : c - a - b < 0) :
    Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (-((c : ℂ) - a - b)) * H a b c x)
      (𝓝[Iio 1] 1) (𝓝 (gaussConnectionMinusGammaCoefficient₂ (a, b, c))) := by
  have h := gaussEuler_tendsto_firstGamma hH (c - a) (c - b) c hca hcb (by linarith)
  have heq : gaussConnectionMinusGammaCoefficient₁ (↑(c - a), ↑(c - b), ↑c) =
      gaussConnectionMinusGammaCoefficient₂ (↑a, ↑b, ↑c) := by
    simp only [gaussConnectionMinusGammaCoefficient₁, gaussConnectionMinusGammaCoefficient₂,
      Complex.ofReal_sub, sub_sub_cancel]
    congr 4
    ring
  rw [heq] at h
  refine h.congr' ?_
  filter_upwards [eventually_between_zero_one] with x hx
  have hne : (1 : ℂ) - x ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hx.2.ne')
  rw [realGaussEulerTransform_family hH a b c x ha hb hca hcb hx.1 hx.2,
    ← mul_assoc, ← Complex.cpow_add _ _ hne, neg_add_cancel, Complex.cpow_zero, one_mul]

end

end DOZZ.Proofs
