module
public import WrittenDensity.RightZero
public import LaterPairs.NativeSharpRows78

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Montgomery.WrittenDensity
open MathCollab.Density

def DensityBound (σ p ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
    (zetaDensityCount σ T : ℝ) ≤ C*T^(p+ε)

theorem density_weaken {σ p q ε : ℝ} (h : DensityBound σ p ε)
    (hpq : p ≤ q) : DensityBound σ q ε := by
  obtain ⟨C,hC,h⟩ := h
  refine ⟨C,hC,fun T hT => (h T hT).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) hC.le)⟩

