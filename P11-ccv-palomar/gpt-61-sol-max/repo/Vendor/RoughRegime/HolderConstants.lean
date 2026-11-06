module

public import RoughRegime.Model

@[expose] public section

/-! Exact Hölder norms of constant functions, using the model's actual coordinate
derivatives. This discharges the smoothness requirement for constant local paths. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace RoughRegime.Model

theorem holderExponent_pos {t } (ht : 0 < t) : 0 < holderExponent t := by
  have hc : 0 < Nat.ceil t := Nat.ceil_pos.mpr ht
  have hcast : ((Nat.ceil t - 1 : ℕ) : ℝ) = (Nat.ceil t : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  unfold holderExponent holderOrder
  rw [hcast]
  linarith [Nat.ceil_lt_add_one ht.le]



end RoughRegime.Model
