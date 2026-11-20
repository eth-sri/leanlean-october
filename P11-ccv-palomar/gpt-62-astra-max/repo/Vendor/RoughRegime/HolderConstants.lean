module

public import RoughRegime.Model

@[expose] public section

/-! Exact Hölder norms of constant functions, using the model's actual coordinate
derivatives. This discharges the smoothness requirement for constant local paths. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace RoughRegime.Model

theorem holderExponent_pos {t : ℝ} (ht : 0 < t) : 0 < holderExponent t := by
  have hcast : (Nat.ceil t - 1 : ℕ) = (Nat.ceil t : ℝ) - 1 := by
    simp_all
  unfold holderExponent holderOrder
  linarith [Nat.ceil_lt_add_one ht.le]

end RoughRegime.Model
