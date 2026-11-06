module

public import RequestProject.LpBoundedMultiplier
public import Mathlib.MeasureTheory.Function.L2Space

/-! The actual L² pairing for a real essentially bounded multiplier. -/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Filter
open scoped ComplexConjugate InnerProductSpace

theorem inner_lpBoundedMultiplier_real
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a : α → ℂ) ha {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (hreal : ∀ᵐ x ∂μ, conj (a x) = a x)
    (v w : Lp ℂ 2 μ) :
    ⟪lpBoundedMultiplier a ha hbound v, w⟫_ℂ =
      ⟪v, lpBoundedMultiplier a ha hbound w⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lpBoundedMultiplier_ae a ha hbound v,
    lpBoundedMultiplier_ae a ha hbound w, hreal] with x hv hw hr
  simp [hv, hw, hr]
  ring

end PolyaNeumann

end
