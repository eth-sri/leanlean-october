/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Lang.Lib.Sqrt
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.HostContracts

/-!
# The parameters of the reduction from 3SUM to Convolution-3SUM

Theorem 21(a), after [CH20, Theorem 5.1].  params(n, V, out) computes the
three parameters of the reduction for n numbers of absolute value at most V: the number Λ =
⌊log₂(2V)⌋ + 1 of binary digits (`ChanHe.Lam`), the bound m on the primes (`ChanHe.mPar`), and the
number of levels of the recursion tree (`ChanHe.fuel`).  The program follows the definitions of the
three numbers line by line, so the proof (`params_spec`) only has to check that each intermediate
value fits in a word: each is at most a small multiple of V, of m or of n + 2 (first section).
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe

variable {lim : Limits} {P : Program}

/-! ## The sizes of the intermediate values -/

/-! ## The program -/


/-- params(n, V, out), over the procedures pLog2, pClog2 (logarithms, rounded down and up) and pSqrt
(the integer square root): writes Λ, m and the number of levels to the three cells from out. -/
def paramsBody (pLog2 pClog2 pSqrt : ℕ)  :=
  .call pLog2 [v 1 +' v 1] 3 ;;
  .set 4 (v 3 +' k 1) ;;
  .call pSqrt [v 0] 5 ;;
  .set 6 (k 5 *' v 4 *' (v 5 +' k 1) +' k 1) ;;
  .call pLog2 [v 6] 7 ;;
  .set 8 (v 6 *' (k 2 *' v 7 +' k 4)) ;;
  .call pLog2 [v 0] 9 ;;
  .call pClog2 [v 9 +' k 2] 10 ;;
  .set 11 (k 3 *' v 10 -' k 2) ;;
  .store (v 2) (v 4) ;;
  .store (v 2 +' k 1) (v 8) ;;
  .store (v 2 +' k 2) (v 11)

/-- **params** meets its specification. -/
theorem params_spec {p pLog2 pClog2 pSqrt} (hP : P[p]? = some (paramsBody pLog2 pClog2 pSqrt))
    (hL : Log2Spec lim P pLog2) (hC : Clog2Spec lim P pClog2) (hS : P[pSqrt]? = some sqrtBody) :
    ParamsSpec lim P p := by
  intro d n V out μ hout hw hword hdep
  refine Meets.of_body hP ?_
  -- the definitions of the three parameters, in the integers
  have  : (Lam V : ℤ) = Nat.log 2 (2 * V) + 1 := by simp [Lam]
  have ew : 5 * (Lam V : ℤ) * ((Nat.sqrt n : ℤ) + 1) = wPar n V := by simp [wPar]
  have em : ((wPar n V : ℤ) + 1) * (2 * (Nat.log 2 (wPar n V + 1) : ℤ) + 4) = mPar n V := by
    simp [mPar]
  have  : height n = Nat.clog 2 (Nat.log 2 n + 2) := rfl
  have  : 3 * (height n : ℤ) - 2 = fuel n := by have := height_pos n; simp only [fuel]; omega
  -- each intermediate value is at most a small multiple of `V`, of `m` or of `n + 2`
  have := (by grind : 5 * Lam V ≤ wPar n V)
  have := (by grind : wPar n V + 1 ≤ mPar n V)
  have := (by grind : 2 * Nat.log 2 (wPar n V + 1) + 4 ≤ mPar n V)
  have := (Nat.clog_le_of_le_pow (LT.lt.le Nat.lt_two_pow_self) : height n ≤ Nat.log 2 n + 2)
  have := Nat.sqrt_le_self n
  have := Nat.log_le_self 2 n
  have : mPar n V + 1 ≤ (mPar n V + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hword' : ((8 * mPar n V + 1 + 8 * V + 4 * n + 64 : ℕ) : ℤ) ≤ lim.word :=
    le_trans (mod_cast by omega) hword
  push_cast at hword'
  unfold tParams paramsBody
  -- LogBound := log2(Bound + Bound)
  light_call (hL (d + 1) (2 * V) μ (by push_cast; omega)) with _ μ ⟨rfl, rfl⟩
  -- Digits := LogBound + 1
  light_set (Lam V)
  -- Root := sqrt(Len)
  light_call (sqrt_meets (K := n) hS μ (by push_cast; omega)) with _ μ ⟨rfl, rfl⟩
  -- Want := 5 * Digits * (Root + 1) + 1
  light_set (wPar n V + 1 : ℕ) using ew
  -- LogWant := log2(Want)
  light_call (hL (d + 1) (wPar n V + 1) μ (by push_cast; omega)) with _ μ ⟨rfl, rfl⟩
  -- PrimeBound := Want * (2 * LogWant + 4)
  light_set (mPar n V) using em
  -- LogLen := log2(Len)
  light_call (hL (d + 1) n μ (by omega)) with _ μ ⟨rfl, rfl⟩
  -- Height := clog2(LogLen + 2)
  light_call (hC (d + 1) (Nat.log 2 n + 2) μ (by push_cast; omega)) with _ μ ⟨rfl, rfl⟩
  -- Levels := 3 * Height - 2
  light_set (fuel n)
  -- mem[Out] := Digits ; mem[Out + 1] := PrimeBound ; mem[Out + 2] := Levels
  light_store out (Lam V)
  light_store (out + 1) (mPar n V)
  light_store (out + 2) (fuel n)
  refine ⟨?_, ?_⟩
  · simp [seg_cons]
  · intro c hc
    simp [show c ≠ out by omega, show c ≠ out + 1 by omega, show c ≠ out + 2 by omega]

end Light.Sec3.ChanHe
