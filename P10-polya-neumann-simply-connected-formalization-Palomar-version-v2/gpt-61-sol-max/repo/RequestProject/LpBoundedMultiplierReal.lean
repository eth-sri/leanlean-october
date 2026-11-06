module

public import RequestProject.LpBoundedMultiplier
public import Mathlib.MeasureTheory.Function.L2Space

/-! The actual L² pairing for a real essentially bounded multiplier. -/

public section



namespace PolyaNeumann

open MeasureTheory Filter
open scoped ComplexConjugate InnerProductSpace

theorem inner_lpBoundedMultiplier_real
    {α : Type*} [MeasurableSpace α] {μ }
    (a : α → ℂ) ha {C }
    (hbound : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (hreal : ∀ᵐ x ∂μ, conj (a x) = a x)
    v w :
    ⟪lpBoundedMultiplier a ha hbound v, w⟫_ℂ =
      ⟪v, lpBoundedMultiplier a ha hbound w⟫_ℂ := by
  apply integral_congr_ae
  filter_upwards [lpBoundedMultiplier_ae a ha hbound v,
    lpBoundedMultiplier_ae a ha hbound w, hreal] with x hv hw hr
  simp  [hv, hw, hr]
  ring

end PolyaNeumann
