/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Parameters

/-!
# Corollaries 26 and 31 in the light language: the preprocessing, with rational parameters

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D with
zero columns of X and zero rows of Y." Proof of Corollary 31: "We repeat the proof of Corollary 26
with L := ⌈cm⌉ and t := ⌈θm⌉". Then the preprocessing of Theorem 30 on the padded matrices; "for
smaller m the corollary again holds trivially".

The routine meets its specification (`pre31_meets`). It computes m and branches. Below the threshold
it writes the flag 0 (`PreInput31.ready_small`). From the threshold on it computes L, t and the
addresses, pads X, and pads Y by a copy and a fill with zeros (`prePad31_ends`,
`matAt_padInnerRows`); then it calls the preprocessing of Theorem 30 and writes the base address and
the flag 1 (`preBuild31_ends`, `PreInput31.ready_large`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : ThreeSumApsp.IntMatrix N D₀}
  {Y : ThreeSumApsp.IntMatrix D₀ N} {aX aY fr : ℕ} {U : ℤ} {μ μ' : Light.Memory}

/-! ## What the routine is given, and what it leaves -/

/-- What the preprocessing is given: besides what both routines are given, the matrices X and Y
stand at aX and aY. -/
structure PreInput31 (lim : Limits) (G : RatParams) {N D₀ : ℕ} (X : ThreeSumApsp.IntMatrix N D₀)
    (Y : ThreeSumApsp.IntMatrix D₀ N) (aX aY fr : ℕ) (U : ℤ) (μ : Light.Memory) : Prop
    extends Input31 lim G X Y aX aY fr U where
  matX : MatAt μ aX X
  matY : MatAt μ aY Y

/-- **Y with zero rows**: a copy of Y followed by zeros is the padded matrix. -/
theorem matAt_padInnerRows {F a} (mY : MatAt μ aY Y)
    (hcopy : ∀ i < D₀ * N, μ' (a + i) = μ (aY + i))
    (hzero : ∀ i < (F - D₀) * N, μ' (a + D₀ * N + i) = 0) : MatAt μ' a (padInnerRows F Y) := by
  intro i j
  unfold padInnerRows
  by_cases hi : (i : ℕ) < D₀
  · rw [dif_pos hi, Nat.add_assoc, hcopy _ (Nat.mul_add_lt_mul hi j.isLt), ← Nat.add_assoc]
    exact mY ⟨i, hi⟩ j
  · have hrow : (i : ℕ) * N = D₀ * N + ((i : ℕ) - D₀) * N := by
      ram_safe

    rw [dif_neg hi, hrow, ← Nat.add_assoc, Nat.add_assoc (a + D₀ * N), hzero _ (Nat.mul_add_lt_mul (by omega : (i : ℕ) - D₀ < F - D₀) j.isLt)]

/-! ## From the threshold on -/

/-- The areas from the free pointer on: fr, fr + 1, fr + 2 | X' | Y' | the block of Theorem 30 from
b0 on. F = 4^m is the padded inner dimension, and R the number of cells in the zero rows of Y'. -/
structure Areas31 (lim : Limits) (N D₀ fr F R : ℕ) : Prop where
  R_eq : R = (F - D₀) * N
  base : blockAt N D₀ fr = fr + 3 + N * F + N * F
  base_lt : blockAt N D₀ fr < lim.space
  D_le : D₀ ≤ F
  rows : D₀ * N + R = N * F
  F_le : F ≤ N * F

theorem PreInput31.areas (h : PreInput31 lim G X Y aX aY fr U μ) (hm : G.m₀ ≤ logFour D₀) :
    Areas31 lim N D₀ fr (D (logFour D₀)) ((D (logFour D₀) - D₀) * N) where
  R_eq := rfl
  base := rfl
  base_lt := (G.blockAt_lt_blockEnd N D₀ fr).trans_le (structEnd_large hm N fr ▸ h.lim.space)
  D_le := le_D_logFour D₀
  rows := by grind [Nat.add_sub_cancel', le_D_logFour]
  F_le := Nat.le_mul_of_pos_left _ h.one_le_N

/-- The time of prePad31. -/
def tPrePad31 (G : RatParams) N D₀ :=
  tCeilMul G.a (logFour D₀) + tCeilMul G.p (logFour D₀) + tPadX N (D (logFour D₀)) + tCopy (D₀ * N)
    + tFill ((D (logFour D₀) - D₀) * N) + 60

/-- The state after prePad31: the locals hold the parameters and the addresses, the padded matrices
stand at their places, and only cells between fr and b0 have changed. -/
def Padded31 (G : RatParams) {N D₀} (X : ThreeSumApsp.IntMatrix N D₀)
    (Y : ThreeSumApsp.IntMatrix D₀ N)
    (aX aY fr : ℕ) (μ : Light.Memory) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : Light.Memory),
    σ = ⟨frame [N, D₀, aX, aY, fr, logFour D₀, D (logFour D₀), G.L (logFour D₀),
      G.t (logFour D₀), paddedXAt fr, paddedYAt N D₀ fr, blockAt N D₀ fr, r,
      N * D (logFour D₀)], μ'⟩ ∧
    MatAt μ' (paddedXAt fr) (padInnerCols (D (logFour D₀)) X) ∧
    MatAt μ' (paddedYAt N D₀ fr) (padInnerRows (D (logFour D₀)) Y) ∧
    SameOutside μ μ' fr (blockAt N D₀ fr - fr)

/-! ## The routine -/

end Light.Sec4
