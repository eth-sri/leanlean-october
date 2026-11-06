module

public import OAI.NumberTheory.DirichletL.Reflection.OriginalWeights
public import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase


noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma bounded_row_multiplier_energy {κ : Type*} (rows : Finset κ) (r f : κ→ℂ)
    (hr : ∀ k∈rows,‖r k‖≤1) :
    (∑ k∈rows,‖r k*f k‖^2)≤∑ k∈rows,‖f k‖^2 := by
  apply Finset.sum_le_sum
  intro k hk
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hr k hk)

end
end SevenEighths.InverseReflectedPhase

end OAI
