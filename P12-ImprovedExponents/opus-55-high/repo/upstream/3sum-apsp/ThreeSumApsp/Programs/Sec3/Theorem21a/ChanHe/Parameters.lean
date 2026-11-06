/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Lib.Sqrt
import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.HostContracts

/-!
# The parameters of the reduction from 3SUM to Convolution-3SUM

Theorem 21(a), after [CH20, Theorem 5.1].  params(n, V, out) computes the
three parameters of the reduction for n numbers of absolute value at most V: the number Λ =
⌊log₂(2V)⌋ + 1 of binary digits (`ChanHe.Lam`), the bound m on the primes (`ChanHe.mPar`), and the
number of levels of the recursion tree (`ChanHe.fuel`).  The program follows the definitions of the
three numbers line by line, so the proof (`params_spec`) only has to check that each intermediate
value fits in a word: each is at most a small multiple of V, of m or of n + 2 (first section).
-/


namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe

variable {lim : Limits} {P : Program}

variable (n V : ℕ)

/-! ## The sizes of the intermediate values -/

theorem five_mul_Lam_le_wPar : 5 * Lam V ≤ wPar n V :=
  Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

theorem wPar_succ_le_mPar : wPar n V + 1 ≤ mPar n V :=
  Nat.le_mul_of_pos_right _ (by omega)

theorem log_wPar_le_mPar : 2 * Nat.log 2 (wPar n V + 1) + 4 ≤ mPar n V :=
  Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

theorem height_le : height n ≤ Nat.log 2 n + 2 :=
  Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

/-! ## The program -/

namespace Params

/- The locals of params.  The arguments: the number n of integers, the bound V on their absolute
values, and the address of the three cells for the results.  Then, in the order in which they are
computed: ⌊log₂(2V)⌋; Λ; ⌊√n⌋; w + 1 with w = 5Λ(⌊√n⌋ + 1); ⌊log₂(w + 1)⌋; m; ⌊log₂ n⌋;
⌈log₂(⌊log₂ n⌋ + 2)⌉; the number of levels. -/
slots Len Bound Out LogBound Digits Root Want LogWant PrimeBound LogLen Height Levels

end Params

open Params in
/-- params(n, V, out), over the procedures pLog2, pClog2 (logarithms, rounded down and up) and pSqrt
(the integer square root): writes Λ, m and the number of levels to the three cells from out. -/
def paramsBody (pLog2 pClog2 pSqrt : ℕ) : Stmt :=
  .call pLog2 [v Bound +' v Bound] LogBound ;;
  .set Digits (v LogBound +' k 1) ;;
  .call pSqrt [v Len] Root ;;
  .set Want (k 5 *' v Digits *' (v Root +' k 1) +' k 1) ;;
  .call pLog2 [v Want] LogWant ;;
  .set PrimeBound (v Want *' (k 2 *' v LogWant +' k 4)) ;;
  .call pLog2 [v Len] LogLen ;;
  .call pClog2 [v LogLen +' k 2] Height ;;
  .set Levels (k 3 *' v Height -' k 2) ;;
  .store (v Out) (v Digits) ;;
  .store (v Out +' k 1) (v PrimeBound) ;;
  .store (v Out +' k 2) (v Levels)

/-- **params** meets its specification. -/
theorem params_spec {p pLog2 pClog2 pSqrt : ℕ} (hP : P[p]? = some (paramsBody pLog2 pClog2 pSqrt))
    (hL : Log2Spec lim P pLog2) (hC : Clog2Spec lim P pClog2) (hS : P[pSqrt]? = some sqrtBody) :
    ParamsSpec lim P p := by
  intro d n V out μ hout hw hword hdep
  apply Meets.of_body hP
  -- the definitions of the three parameters, in the integers
  have eΛ : Lam V = Nat.log 2 (2 * V) + 1 := by rfl
  have ew : 5 * Lam V * ((Nat.sqrt n : ℤ) + 1) = wPar n V := by rfl
  have em : ((wPar n V) + 1) * (2 * (Nat.log 2 (wPar n V + 1) : ℤ) + 4) = mPar n V := by
    rfl
  have eh : height n = Nat.clog 2 _ := rfl
  have ef : 3 * (height n : ℤ) - 2 = fuel n := by grind [height_pos, fuel]
  -- each intermediate value is at most a small multiple of `V`, of `m` or of `n + 2`
  have := five_mul_Lam_le_wPar n V
  have := wPar_succ_le_mPar n V
  have := log_wPar_le_mPar n V
  have := height_le n
  have := n.sqrt_le_self
  have := Nat.log_le_self 2 n
  have : mPar n V + 1 ≤ (mPar n V + 1) ^ 2 := by grind [Nat.le_self_pow]
  unfold tParams paramsBody
  -- LogBound := log2(Bound + Bound)
  light_call (hL _ (2 * V) μ (by omega)) with _ μ ⟨rfl, rfl⟩
  -- Digits := LogBound + 1
  light_set (Lam V)
  -- Root := sqrt(Len)
  light_call (sqrt_meets (K := n) hS μ (by omega)) with _ μ ⟨rfl, rfl⟩
  -- Want := 5 * Digits * (Root + 1) + 1
  light_set (wPar n V + 1) using ew
  -- LogWant := log2(Want)
  light_call (hL _ (wPar n V + 1) μ (by omega)) with _ μ ⟨rfl, rfl⟩
  -- PrimeBound := Want * (2 * LogWant + 4)
  light_set (mPar n V) using em
  -- LogLen := log2(Len)
  light_call (hL _ n μ (by omega)) with _ μ ⟨rfl, rfl⟩
  -- Height := clog2(LogLen + 2)
  light_call (hC _ (Nat.log 2 n + 2) μ (by omega)) with _ μ ⟨rfl, rfl⟩
  -- Levels := 3 * Height - 2
  light_set (fuel n)
  -- mem[Out] := Digits ; mem[Out + 1] := PrimeBound ; mem[Out + 2] := Levels
  light_store out (Lam V)
  light_store (out + 1) (mPar n V)
  light_store (out + 2) (fuel n)
  refine ⟨?_, ?_⟩
  · simp [seg_cons]
  · intro c hc
    grind
