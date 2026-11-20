module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.Tactic

/-! Multiplication by an actual essentially bounded coefficient in L². -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Filter

section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a : α → ℂ) (ha : AEStronglyMeasurable a μ) {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖a x‖ ≤ C)

def lpBoundedMultiplier : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL μ ⊤ 2 2 ((memLp_top_of_bound ha C hbound).toLp a)

section

variable (v : Lp ℂ 2 μ)

theorem lpBoundedMultiplier_ae :
    (lpBoundedMultiplier a ha hbound v : α → ℂ) =ᵐ[μ] fun x => a x * v x :=
  ((ContinuousLinearMap.mul ℂ ℂ).coeFn_holder ((memLp_top_of_bound ha C hbound).toLp a) v).trans
    ((memLp_top_of_bound ha C hbound).coeFn_toLp.mul EventuallyEq.rfl)

theorem norm_lpBoundedMultiplier_le :
    ‖lpBoundedMultiplier a ha hbound v‖ ≤ C * ‖v‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [lpBoundedMultiplier_ae a ha hbound v, hbound] with x hx hb
  rw [hx, norm_mul]
  gcongr

end

end

end PolyaNeumann

end
