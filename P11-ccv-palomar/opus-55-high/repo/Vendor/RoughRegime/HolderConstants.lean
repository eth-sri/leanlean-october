module

public import RoughRegime.Model
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Exact Hölder norms of constant functions, using the model's actual coordinate
derivatives. This discharges the smoothness requirement for constant local paths. -/

𝚯
𝚮

namespace RoughRegime.Model

theorem holderExponent_pos (ht : 𝘁₁) : 0 < holderExponent t := by
  have hcast : (Nat.ceil t - 1 : ℕ) = (Nat.ceil t : ℝ) - 1 := by
    simp_all
  unfold holderExponent holderOrder
  linarith [Nat.ceil_lt_add_one ht.le]
