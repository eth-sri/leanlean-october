/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Contracts

/-!
# An entry of the product as an inner product

Proof of Corollary 26: "(For m < 60, D is bounded by a constant, and the corollary holds
trivially.)"; proof of Corollary 31: "for smaller m the corollary again holds trivially". In the
programs a query then computes an inner product, of a bounded number D of summands. The routine adds
the D products X[I, s] Y[s, J]. `ipPart` is the sum of the first s of them, with its recursion
(`ipPart_succ`), its bound (`abs_ipPart_le`) and its last value (`ipPart_full`); `ipAt_meets` is the
specification.
-/


namespace Light.Sec4

open Finset

namespace IpAt

/- The locals of ipAt. The first six are its arguments I, J, N, D, aX, aY; the answer replaces I.
Then come the index s of the summand, the sum, the address of row I of X, and the address of Y[0,
J]. -/
slots Row Col Size Dim MatX MatY Pos Sum RowAt ColAt

end IpAt

open IpAt in
/-- ipAt(I, J, N, D, aX, aY): the inner product of row I of X and column J of Y. -/
def ipAtBody : Stmt :=
  .set Pos (k 0) ;; .set Sum (k 0) ;;
  .set RowAt (v MatX +' v Row *' v Dim) ;; .set ColAt (v MatY +' v Col) ;;
  .while (v Pos <' v Dim)
    (.set Sum (v Sum +' M (v RowAt +' v Pos) *' M (v ColAt +' v Pos *' v Size)) ;;
      .set Pos (v Pos +' k 1)) ;;
  .set Row (v Sum)

section
variable {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (I J : Fin N)

/-- The first s summands of the inner product. -/
def ipPart (s : ℕ) : ℤ := ∑ i ∈ range s, if h : i < D₀ then X I ⟨i, h⟩ * Y ⟨i, h⟩ J else 0

theorem ipPart_full : ipPart X Y I J D₀ = (X * Y) I J := by
  grind [Matrix.mul_apply, ipPart, Finset.sum_range]

theorem ipPart_succ {s : ℕ} (hs : s < D₀) :
    ipPart X Y I J (s + 1) = ipPart X Y I J s + X I ⟨s, hs⟩ * Y ⟨s, hs⟩ J := by
  simp_all [ipPart, Finset.sum_range_succ]

variable {X Y}

variable {U : ℤ}

theorem abs_mul_entry_le (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) (s : Fin D₀) :
    |X I s * Y s J| ≤ U * U := by
  rw [abs_mul]
  exact mul_le_mul (by simp_all) (by simp_all) (abs_nonneg _) (le_trans (abs_nonneg _) (by aesop))

theorem abs_ipPart_le (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) :
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

theorem ipAt_meets {lim : Limits} {P : Program} (hP : P[Proc.ipAt]? = some ipAtBody)
    (hstd : Std lim) : IpAtSpec lim P := by
  intro N D₀ aX aY X Y U μ I J hD hmX hmY hX hY sX sY hU
  refine fun d _ => ⟨ipAtBody, hP, ?_⟩
  have hrow : I * D₀ + D₀ ≤ N * D₀ := Nat.mul_add_le_mul I.isLt le_rfl
  have hN : N ≤ D₀ * N := Nat.le_mul_of_pos_left _ hD
  -- every partial sum and every product fits in a word
  unfold ipAtBody tIpAt
  -- s := 0 ; sum := 0 ; row := aX + I * D ; col := aY + J
  light_set 0
  light_set 0
  light_set (aX + I * D₀)
  light_set (aY + J)
  -- while s < D: sum := sum + mem[row + s] * mem[col + s * N] ; s := s + 1
  refine Ends.next _ (Ends.whileBlock (fun s σ => σ = ⟨frame [I, J, N, D₀, aX, aY, s,
      ipPart X Y I J s, (aX + (I : ℕ) * D₀), (aY + (J : ℕ))], μ⟩) D₀
    (by rfl) ?_ ?_ (hT := le_rfl))
  ·
    rintro s _ hs rfl
    have hcell : s * N + N ≤ D₀ * N := Nat.mul_add_le_mul hs le_rfl
    have hx := hmX I ⟨s, hs⟩
    have hy : μ (aY + J + s * N) = Y ⟨s, hs⟩ J := by
      rw [← hmY _ J]
      grind
    have haddrX : ((aX : ℤ) + I * D₀ + s).toNat = aX + I * D₀ + s := by
      rfl
    have haddrY : ((aY : ℤ) + J + s * N).toNat = aY + J + s * N := by
      rfl
    have hsum := abs_le.1 ((fun s hs =>
    (abs_ipPart_le I J hX hY s hs).trans (le_trans
      (mul_le_mul_of_nonneg_right (by omega)
        (le_trans (abs_nonneg _) (abs_mul_entry_le I J hX hY ⟨0, hD⟩))) hU)) (s + 1) hs)
    have hxy := abs_le.1 ((fun s =>
    (abs_mul_entry_le I J hX hY s).trans (le_trans (le_mul_of_one_le_left
      (le_trans (abs_nonneg _) (abs_mul_entry_le I J hX hY s)) (by omega)) hU)) ⟨s, hs⟩)
    rw [ipPart_succ X Y I J hs] at hsum ⊢
    exact ⟨by light_side, by simp_all, by light_side [haddrX, haddrY, hx, hy],
      by simp_all [update_frame_setLocal]⟩
  ·
    rintro _ rfl
    -- return sum
    exact ⟨by light_side, by simp, Ends.setTo (ipPart X Y I J D₀) ⟨ipPart_full X Y I J, rfl⟩⟩
