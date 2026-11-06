module
import Mathlib
public import WrittenDensity.RightZero
public import TraceAlternatives.CurrentDensityCurve

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Montgomery.WrittenDensity
open MathCollab.Density

/- A uniform actual-count consequence, with the constant preceding every height. -/
def DensityBound (σ p ε : ℝ) : Prop :=
  MathCollab.Density.ZetaBound σ ((p+ε))

theorem density_weaken {σ p q ε : ℝ} (h : DensityBound σ p ε)
    (hpq : p ≤ q) : DensityBound σ q ε := by
  obtain ⟨C,hC,h⟩ := h
  refine ⟨C,hC,?_⟩
  intro T hT
  exact (h T hT).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T) (by linarith)) hC.le)



/- Rational enclosures used only to compare the exact algebraic source endpoint. -/
theorem source_transition_endpoint_bounds :
    (3132/4000 : ℝ) ≤ (201+Real.sqrt 145)/272 ∧
    (201+Real.sqrt 145)/272 ≤ (3133/4000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 145)
  have hn := Real.sqrt_nonneg (145:ℝ)
  constructor <;> nlinarith


