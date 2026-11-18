module
public import Mathlib

@[expose] public section
open Finset
noncomputable section
namespace GafniTao
theorem ford_norm_sum_sq_le_card_mul_sum_norm_sq
    {α : Type*} (B : Finset α) (V : α → ℂ) :
    ‖∑ b ∈ B, V b‖ ^ 2 ≤
      (B.card : ℝ) * ∑ b ∈ B, ‖V b‖ ^ 2 := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le B V) 2).trans (by
      simpa using
        (sq_sum_le_card_mul_sum_sq (s := B) (f := fun b => ‖V b‖)))

end GafniTao
