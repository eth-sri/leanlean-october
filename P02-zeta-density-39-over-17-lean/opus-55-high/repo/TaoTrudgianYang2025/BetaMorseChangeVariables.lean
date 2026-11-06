module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaMorseDerivativeBounds
public import Mathlib.MeasureTheory.Function.JacobianOneDim
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Exact change of variables by the actual quadratic inverse

Both the Bochner integral and integrability are transported. The
positive Jacobian is proved, so its absolute value is not silently dropped.
-/

noncomputable section

open Set Expdb Filter MeasureTheory
open scoped ContDiff Topology

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

theorem modelPhaseMorseInverse_injOn (F : ℝ → ℝ) (v : ℝ) :
    InjOn (modelPhaseMorseInverse F v) (modelPhaseMorseRange F v) := by
  intro z hz w hw he
  have h := congrArg (modelPhaseMorseCoordinate F v) he
  simpa only [modelPhaseMorseCoordinate_inverse hz,modelPhaseMorseCoordinate_inverse hw] using h

section
variable {F : ℝ → ℝ}
include F
theorem modelPhaseMorseInverse_image {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseMorseInverse F v '' modelPhaseMorseRange F v = Ioo (1 : ℝ) 2 := by
  pm_7964 modelPhaseMorseInverse_mem
  · intro u hu
    exact ⟨modelPhaseMorseCoordinate F v u,⟨u,hu,rfl⟩,
      modelPhaseMorseInverse_coordinate hσ hδ hF hv hu⟩

theorem modelPhaseMorseInverse_deriv_pos {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) :
    0 < deriv (modelPhaseMorseInverse F v) z := by
  pm_7733
  exact inv_pos.mpr (modelPhaseMorseCoordinate_deriv_pos hσ hδ hF hv
    (modelPhaseMorseInverse_mem hz))

theorem integral_Ioo_eq_morseIntegral {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (g : ℝ → ℂ) :
    (∫ u in Ioo (1 : ℝ) 2, g u) =
      ∫ z in modelPhaseMorseRange F v,
        ((deriv (modelPhaseMorseInverse F v) z : ℝ) : ℂ)*g (modelPhaseMorseInverse F v z) := by
  have hd : ∀ z ∈ modelPhaseMorseRange F v,
      HasDerivWithinAt (modelPhaseMorseInverse F v)
        (deriv (modelPhaseMorseInverse F v) z) (modelPhaseMorseRange F v) z :=
    fun _ hz => (modelPhaseMorseInverse_hasStrictDerivAt hσ hδ hF hv hz).hasDerivAt
      |>.differentiableAt.hasDerivAt.hasDerivWithinAt
  have hs := (modelPhaseMorseRange_isOpen hσ hδ hF hv).measurableSet
  have h := integral_image_eq_integral_abs_deriv_smul hs hd
    (modelPhaseMorseInverse_injOn F v) g
  rw [modelPhaseMorseInverse_image hσ hδ hF hv] at h
  refine h.trans (setIntegral_congr_fun hs (fun z hz => ?_))
  rw [abs_of_pos (modelPhaseMorseInverse_deriv_pos hσ hδ hF hv hz),Complex.real_smul]
end

end TaoTrudgianYang2025
