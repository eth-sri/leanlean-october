/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarGaussConstant
public import DOZZ.Statements.Hypergeom.PlanarDifferenceKernel
public import DOZZ.Hypergeom.Planar.DifferenceDiscreteLaplacian
public import DOZZ.Hypergeom.Planar.TaylorNormalization
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import DOZZ.Hypergeom.Planar.TaylorIntegral

/-! The KRV difference integral follows from scaling and its Riesz discrete Laplacian. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace DOZZ.Proofs

section
variable (k β : ℝ) (hk : 0 < k)
include hk

/-- The coefficient of the first-subtracted parent, recovered from its dominated discrete
Laplacian. -/
theorem planarDifference_constant_from_discrete_laplacian (hβ : k < β) (hβ₂ : β < 2) (hβtail : k + 1 < β) :
    ((∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u : ℝ) : ℂ) =
      DOZZ.planarGaussConstant k β := by
  apply planarGaussConstant_of_discreteLaplacian k β hk hβ hβ₂
    (fun z => ∫ u, DOZZ.planarDifferenceKernel k β z u)
    (planarDifferenceKernel_integral_scale_norm k β hk hβ hβ₂)
  have h (t : ℝ) := integral_planarDiscreteLaplacian (DOZZ.planarDifferenceKernel k β)
    (integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail) t 1
  simp_rw [← h]
  change Tendsto (fun t => ∫ u, planarDifferenceDiscreteQuotient k β t u) _ _
  simpa only [planarDifferenceDiscreteQuotient_eq_kernel, planarTaylorDiscreteQuotient_eq_kernel] using
    planarTaylorDiscreteQuotient_integral_tendsto k β hk hβ hβ₂

/-- Proof of the difference-integral statement `DOZZ.planar_difference_integral`. -/
theorem planar_difference_integral
    (hβ : k + 1 < β) (hβ₂ : β < 2) :
    ∀ z : ℂ, Integrable (DOZZ.planarDifferenceKernel k β z) volume ∧
      ((∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) : ℂ) =
        (‖z‖ ^ (2 + k - β) : ℝ) * DOZZ.planarGaussConstant k β := by
  have hInt := integrable_planarDifferenceKernel k β hk (by linarith) hβ₂ hβ
  have hA := planarDifference_constant_from_discrete_laplacian k β hk (by linarith) hβ₂ hβ
  have hscale := planarDifferenceKernel_integral_scale_norm k β hk (by linarith) hβ₂
  intro z
  refine ⟨hInt z, ?_⟩
  rw [integral_complex_ofReal, hscale z, Complex.ofReal_mul, hA]

end

end DOZZ.Proofs
