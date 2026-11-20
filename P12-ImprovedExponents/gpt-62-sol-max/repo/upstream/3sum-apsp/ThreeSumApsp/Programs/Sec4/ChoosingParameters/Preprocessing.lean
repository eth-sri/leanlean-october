/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Parameters

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp

variable {N D₀ : ℕ} {Y : Matrix (Fin D₀) (Fin N) ℤ} {aY : ℕ} {μ μ' : ℕ → ℤ}

/-- **Y with zero rows**: a copy of Y followed by zeros is the padded matrix. -/
theorem matAt_padInnerRows {F a : ℕ} (mY : MatAt μ aY Y)
    (hcopy : ∀ i < D₀ * N, μ' (a + i) = μ (aY + i))
    (hzero : ∀ i < (F - D₀) * N, μ' (a + D₀ * N + i) = 0) : MatAt μ' a (padInnerRows F Y) := by
  intro i j
  unfold padInnerRows
  by_cases hi : (i : ℕ) < D₀
  · rw [dif_pos hi, Nat.add_assoc, hcopy _ (Nat.mul_add_lt_mul hi j.isLt), ← Nat.add_assoc]
    exact mY ⟨i, hi⟩ j
  · have hrow : (i : ℕ) * N = D₀ * N + ((i : ℕ) - D₀) * N := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' (not_lt.mp hi)]
    have hidx := Nat.mul_add_lt_mul (by omega : (i : ℕ) - D₀ < F - D₀) j.isLt
    grind

end Light.Sec4
