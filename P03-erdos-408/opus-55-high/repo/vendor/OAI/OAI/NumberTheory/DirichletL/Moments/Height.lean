module

public import OAI.NumberTheory.DirichletL.Moments.Twist

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.CenteredMomentHeight

lemma normalized_height_le (t : ℝ) : ‖t / (2 * Real.pi)‖ ≤ ‖t‖ := by
  rw [norm_div, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])

end SevenEighths.CenteredMomentHeight
end

end OAI
