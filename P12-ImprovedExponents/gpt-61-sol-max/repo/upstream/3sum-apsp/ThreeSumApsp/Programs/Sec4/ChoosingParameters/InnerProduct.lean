/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Contracts

/-!
# An entry of the product as an inner product

Proof of Corollary 26: "(For m < 60, D is bounded by a constant, and the corollary holds
trivially.)"; proof of Corollary 31: "for smaller m the corollary again holds trivially". In the
programs a query then computes an inner product, of a bounded number D of summands. The routine adds
the D products X[I, s] Y[s, J]. `ipPart` is the sum of the first s of them, with its recursion
(`ipPart_succ`), its bound (`abs_ipPart_le`) and its last value (`ipPart_full`); `ipAt_meets` is the
specification.
-/

@[expose] public section

namespace Light.Sec4

open Finset


/-- ipAt(I, J, N, D, aX, aY): the inner product of row I of X and column J of Y. -/
def ipAtBody  :=
  .set 6 (k 0) ;; .set 7 (k 0) ;;
  .set 8 (v 4 +' v 0 *' v 3) ;; .set 9 (v 5 +' v 1) ;;
  .while (v 6 <' v 3)
    (.set 7 (v 7 +' M (v 8 +' v 6) *' M (v 9 +' v 6 *' v 2)) ;;
      .set 6 (v 6 +' k 1)) ;;
  .set 0 (v 7)

section
variable {N D₀ : ℕ} (X : ThreeSumApsp.IntMatrix N D₀) (Y : ThreeSumApsp.IntMatrix D₀ N) (I J : Fin N)

/-- The first s summands of the inner product. -/
def ipPart s := ∑ i ∈ range s, if h : i < D₀ then X I ⟨i, h⟩ * Y ⟨i, h⟩ J else 0

theorem ipPart_full : ipPart X Y I J D₀ = (X * Y) I J := by
  grind [Matrix.mul_apply, ipPart, Finset.sum_range]

theorem ipPart_succ {s} hs :
    ipPart X Y I J (s + 1) = ipPart X Y I J s + X I ⟨s, hs⟩ * Y ⟨s, hs⟩ J := by
  ram_arith [ipPart, Finset.sum_range_succ]

variable {X Y}

theorem abs_mul_entry_le {U} (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) s :
    |X I s * Y s J| ≤ U * U := by
  rw [abs_mul]
  exact mul_le_mul (hX _ _) (hY _ _) (abs_nonneg _) (le_trans (abs_nonneg _) (hX I s))

theorem abs_ipPart_le {U} (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) :
    ∀ s ≤ D₀, |ipPart X Y I J s| ≤ s * (U * U)
  | 0, _ => by simp [ipPart]
  | s + 1, hs => by
    rw [ipPart_succ X Y I J hs]
    refine (abs_add_le _ _).trans ?_
    have := abs_ipPart_le hX hY s (by omega)
    have := abs_mul_entry_le I J hX hY ⟨s, hs⟩
    push_cast
    linarith

end

theorem ipAt_meets {lim} {P} (hP : P[63]? = some ipAtBody)
    (hstd : Std lim) : IpAtSpec lim P := by
  intro N D₀ aX aY X Y U μ I J hD hmX hmY hX hY sX sY hU
  refine fun d _ => ⟨ipAtBody, hP, ?_⟩


  have  : (I : ℕ) * D₀ + D₀ ≤ N * D₀ := Nat.mul_add_le_mul I.isLt le_rfl

  have  : N ≤ D₀ * N := Nat.le_mul_of_pos_left _ hD
  -- every partial sum and every product fits in a word


  unfold ipAtBody tIpAt
  -- s := 0 ; sum := 0 ; row := aX + I * D ; col := aY + J
  light_set 0
  light_set 0
  light_set (aX + (I : ℕ) * D₀ : ℕ)
  light_set (aY + (J : ℕ) : ℕ)
  -- while s < D: sum := sum + mem[row + s] * mem[col + s * N] ; s := s + 1
  refine Ends.next _ (Ends.whileBlock (fun s σ => σ = ⟨frame [I, J, N, D₀, aX, aY, s,
      ipPart X Y I J s, (aX + (I : ℕ) * D₀ : ℕ), (aY + (J : ℕ) : ℕ)], μ⟩) D₀
    rfl ?round ?done (hT := le_rfl))
  case round =>
    rintro s _ hs rfl
    have  : s * N + N ≤ D₀ * N := Nat.mul_add_le_mul hs le_rfl
    have hx := hmX I ⟨s, hs⟩
    have hy : μ (aY + J + s * N) = Y ⟨s, hs⟩ J := by
      rw [← hmY ⟨s, hs⟩ J]
      congr 1
      change aY + (J : ℕ) + s * N = aY + s * N + (J : ℕ)
      omega
    have haddrX : ((aX : ℤ) + (I : ℕ) * D₀ + s).toNat = aX + (I : ℕ) * D₀ + s := by
      omega
    have haddrY : ((aY : ℤ) + (J : ℕ) + s * N).toNat = aY + (J : ℕ) + s * N := by
      omega
    have hsum := abs_le.1 ((fun s hs =>
      (abs_ipPart_le I J hX hY s hs).trans (le_trans
        (mul_le_mul_of_nonneg_right (mod_cast hs)
          (le_trans (abs_nonneg _) (abs_mul_entry_le I J hX hY ⟨0, hD⟩))) hU)
    ) (s + 1) hs)
    have hxy := abs_le.1 ((fun s =>
      (abs_mul_entry_le I J hX hY s).trans (le_trans (le_mul_of_one_le_left
        (le_trans (abs_nonneg _) (abs_mul_entry_le I J hX hY s)) (mod_cast hD)) hU)
    ) ⟨s, hs⟩)
    rw [ipPart_succ X Y I J hs] at hsum ⊢
    generalize ipPart X Y I J s = S at hsum ⊢
    generalize X I ⟨s, hs⟩ = x at hx hsum hxy ⊢
    generalize Y ⟨s, hs⟩ J = y at hy hsum hxy ⊢
    exact ⟨by light_side, by simp; omega, by light_side [haddrX, haddrY, hx, hy],
      by simp [update_frame_setLocal, haddrX, haddrY, hx, hy]⟩
  case done =>
    rintro _ rfl
    -- return sum
    exact ⟨by light_side, by simp, Ends.setTo (ipPart X Y I J D₀) ⟨ipPart_full X Y I J, rfl⟩⟩

end Light.Sec4
