module

public import ThreeSumApsp.Lang.Lib.Emod
public import ThreeSumApsp.Lang.Lib.MergeSort
public import ThreeSumApsp.Lang.Lib.Sieve
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Contracts
public import ThreeSumApsp.Lang.Lib.Sqrt
public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Sizes
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Reduction
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Bits
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Distinct
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Modulus
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.NodeArray
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Prepare

@[expose] public section

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# 3SUM from Convolution-3SUM: the routines of the general library

The programs of the reduction call five routines of the general library: the remainder, the two
logarithms, the sieve and sorting.  Each theorem here says that the routine meets the specification
under which the reduction calls it (`EmodSpec`, `Log2Spec`, `Clog2Spec`, `PrimesSpec`, `SortSpec`).
The library's theorem about the body gives the result.  What is left is to read the limits off the
need, and to compare the library's count of steps with the rounder time function of the
specification.
-/


namespace Light.Sec3.ChanHe

variable {lim : Limits} {P : Program} {p : ℕ}

/-- `⌈log₂ x⌉ ≤ ⌊log₂ x⌋ + 1`. -/
theorem clog_le_log_succ (x : ℕ) : Nat.clog 2 x ≤ Nat.log 2 x + 1 :=
  Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by norm_num) x).le

/-- The remainder. -/
theorem emodSpec_of (hP : P[p]? = some emodBody) : EmodSpec lim P p := by
  intro d fr V M x μ hM hx hok
  have hword := hok.word
  have hcells := hok.cells
  simp only [emodNeed] at hword hcells
  push_cast at hword
  have := emodRounds_le (M := M) (show x.natAbs ≤ V by have := abs_le.mp hx; omega)
  refine (emod_meets hP ⟨hM, hok.space, hword, hcells⟩ hx).mono_time ?_
  unfold tEmod emodTime
  omega

/-- The logarithm, rounded down. -/
theorem log2Spec_of (hP : P[p]? = some log2Body) : Log2Spec lim P p := by
  intro d x μ hword
  refine (log2_meets hP μ (by push_cast; omega)).mono_time ?_
  unfold tLog2 log2Time
  omega

/-- The logarithm, rounded up. -/
theorem clog2Spec_of (hP : P[p]? = some clog2Body) : Clog2Spec lim P p := by
  intro d x μ hword
  have := clog_le_log_succ x
  refine (clog2_meets hP μ (by push_cast; omega)).mono_time ?_
  unfold tLog2 clog2Time
  omega

/-- The sieve. -/
theorem primesSpec_of (hP : P[p]? = some sieveBody) : PrimesSpec lim P p := by
  intro d fr m out μ hout hok
  have hword := hok.word
  have hcells := hok.cells
  simp only [primesNeed] at hword hcells
  push_cast at hword
  refine (sieve_meets hP ⟨hok.space, by push_cast; omega, hout, hcells⟩).mono ?_
    fun _ _ ⟨hcount, hseg, hkept⟩ => ⟨hcount, hseg, hkept.mono fun _ ha => ⟨ha.2, Or.inl ha.1⟩⟩
  -- `15 m (⌊log₂ m⌋ + 5) + …` against `60 m (⌊log₂ m⌋ + 2) + 60`
  unfold tPrimes sieveTime
  rw [mul_assoc 15, mul_assoc 60, mul_add m, mul_add m]
  omega

/-- Sorting.  The program holds sort at the number p, and half, merge and copy, which sort
calls. -/
theorem sortSpec_of {pHalf pMerge pCopy : ℕ} (C : MergeSort.Procs P p pHalf pMerge pCopy) :
    SortSpec lim P p := by
  intro d fr a V L μ hseg _ hbelow hok
  have hword := hok.word
  have hcells := hok.cells
  have hdepth := hok.depth
  simp only [sortNeed] at hword hcells hdepth
  push_cast at hword
  have hclog := clog_le_log_succ L.length
  refine (sort_meets C hok.space (by omega) hseg hbelow hcells d (by omega)).mono ?_ fun _ _ h => h
  -- `n ⌈log₂ n⌉ ≤ n (⌊log₂ n⌋ + 1)`
  have := Nat.mul_le_mul_left L.length hclog
  unfold tSort sortTime
  rw [mul_assoc 80, mul_add L.length] at *
  omega


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The parameters of the reduction from 3SUM to Convolution-3SUM

Theorem 21(a), after [CH20, Theorem 5.1].  params(n, V, out) computes the
three parameters of the reduction for n numbers of absolute value at most V: the number Λ =
⌊log₂(2V)⌋ + 1 of binary digits (`ChanHe.Lam`), the bound m on the primes (`ChanHe.mPar`), and the
number of levels of the recursion tree (`ChanHe.fuel`).  The program follows the definitions of the
three numbers line by line, so the proof (`params_spec`) only has to check that each intermediate
value fits in a word: each is at most a small multiple of V, of m or of n + 2 (first section).
-/



open ThreeSumApsp ThreeSumApsp.ChanHe Finset

variable {lim : Limits} {P : Program}

/-! ## The sizes of the intermediate values -/

theorem five_mul_Lam_le_wPar (n V : ℕ) : 5 * Lam V ≤ wPar n V :=
  Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

theorem wPar_succ_le_mPar (n V : ℕ) : wPar n V + 1 ≤ mPar n V :=
  Nat.le_mul_of_pos_right _ (by omega)

theorem log_wPar_le_mPar (n V : ℕ) : 2 * Nat.log 2 (wPar n V + 1) + 4 ≤ mPar n V :=
  Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

theorem height_le (n : ℕ) : height n ≤ Nat.log 2 n + 2 :=
  Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

/-! ## The program -/

namespace Params

/-- The locals of params.  The arguments: the number n of integers, the bound V on their absolute
values, and the address of the three cells for the results.  Then, in the order in which they are
computed: ⌊log₂(2V)⌋; Λ; ⌊√n⌋; w + 1 with w = 5Λ(⌊√n⌋ + 1); ⌊log₂(w + 1)⌋; m; ⌊log₂ n⌋;
⌈log₂(⌊log₂ n⌋ + 2)⌉; the number of levels. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Bound : ℕ := 1
@[inherit_doc Len] abbrev Out : ℕ := 2
@[inherit_doc Len] abbrev LogBound : ℕ := 3
@[inherit_doc Len] abbrev Digits : ℕ := 4
@[inherit_doc Len] abbrev Root : ℕ := 5
@[inherit_doc Len] abbrev Want : ℕ := 6
@[inherit_doc Len] abbrev LogWant : ℕ := 7
@[inherit_doc Len] abbrev PrimeBound : ℕ := 8
@[inherit_doc Len] abbrev LogLen : ℕ := 9
@[inherit_doc Len] abbrev Height : ℕ := 10
@[inherit_doc Len] abbrev Levels : ℕ := 11

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
  refine Meets.of_body hP ?_
  -- the definitions of the three parameters, in the integers
  have eΛ : (Lam V : ℤ) = Nat.log 2 (2 * V) + 1 := by simp [Lam]
  have ew : 5 * (Lam V : ℤ) * ((Nat.sqrt n : ℤ) + 1) = wPar n V := by simp [wPar]
  have em : ((wPar n V : ℤ) + 1) * (2 * (Nat.log 2 (wPar n V + 1) : ℤ) + 4) = mPar n V := by
    simp [mPar]
  have : height n = Nat.clog 2 (Nat.log 2 n + 2) := rfl
  have : 3 * (height n : ℤ) - 2 = fuel n := by have := height_pos n; simp only [fuel]; omega
  -- each intermediate value is at most a small multiple of `V`, of `m` or of `n + 2`
  have := five_mul_Lam_le_wPar n V
  have := wPar_succ_le_mPar n V
  have := log_wPar_le_mPar n V
  have := height_le n
  have := Nat.sqrt_le_self n
  have := Nat.log_le_self 2 n
  have : mPar n V + 1 ≤ (mPar n V + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hword' : ((8 * (mPar n V + 1) + 8 * V + 4 * n + 64 : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast (by omega)) hword
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


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The arithmetic of the reduction from 3SUM to Convolution-3SUM

Theorem 21(a), after [CH20, Theorem 5.1]. Two statements about the time and
the need of the host (`chTime`, `chNeed`), which are explicit expressions in the number n of
integers and the bound on their absolute values.

* The need is polynomially bounded if the need of the solver of Convolution-3SUM is
  (`polyNeed_chNeed`).
* For inputs of absolute value at most n^κ, the host's own work is n^{3/2} times a polylogarithm, it
  calls the solver polylogarithmically often, and all calls are at the same length, which is n times
  a polylogarithm, and with the same bound on the numbers, which is polynomial in n. This gives the
  transfer of running times (`claim_CH20_Theorem_5_1_of_host`).

Both are proved by following the expressions, in the calculus `Scale.SoftO` of orders of growth:
`SoftOSqrtPow F i` says that F(n) is at most a polylogarithm times (⌊√n⌋ + 1)^i, and `PolyBounded F`
that F(n, U) is at most a polynomial in (n + 1)(U + 1).
-/




/-! ## The host on inputs of absolute value at most `n^k` -/

/-- The bound `V = 2 n^k` with which the host works. -/
abbrev boundAt (k n : ℕ) : ℕ := 2 * n ^ k

/-- The host's own work. -/
def ownAt (k n : ℕ) : ℕ := 20 * k + 40 + coreOwn n (boundAt k n)

/-- The number of calls of the solver. -/
def callsAt (k n : ℕ) : ℕ := coreCalls n (boundAt k n)

/-- The bound on the numbers of the instances that the solver is asked. -/
def magAt (k n : ℕ) : ℕ := 60 * boundAt k n + 40

/-- The time of the host is its own work plus the calls of the solver, which are all at one length
and with one bound. -/
theorem chTime_eq {k n U : ℕ} (hU : U ≤ n ^ k) (Tn : ℕ → ℕ → ℕ) :
    chTime k Tn n U = ownAt k n + callsAt k n * Tn (lenOf k n) (magAt k n) := by
  simp only [chTime, coreTime, lenOf, ownAt, callsAt, magAt, boundAt, max_eq_right hU]
  omega

namespace ClaimF

/-! ## The time functions at the bound `V = 2 n^k`

In `SoftOSqrtPow F i` the index 0 stands for a polylogarithm, 1 for `Õ(√n)`, 2 for `Õ(n)` and 3 for
`Õ(n^{3/2})`.  The bound `m` on the primes has the index 1 (`softO_mPar`). -/

section own

variable (k : ℕ)

/-- The number of candidate primes, which is at most the bound `m` on the primes. -/
abbrev numPrimes (n : ℕ) : ℕ := #(Nat.primesLE (mPar n (boundAt k n)))

/-- The number of candidate primes is `Õ(√n)`. -/
theorem softO_numPrimes : SoftOSqrtPow (numPrimes k) 1 :=
  (softO_mPar k).of_le fun _ _ => Nat.card_primesLE_le _

/-- One remainder takes a step for each binary digit. -/
theorem softO_tEmod : SoftOSqrtPow (fun n => tEmod (boundAt k n)) 0 := by
  unfold tEmod
  growth_sqrt []

/-- The remainders of `n` numbers. -/
theorem softO_tResid : SoftOSqrtPow (fun n => tResid n (boundAt k n)) 2 := by
  unfold tResid
  growth_sqrt [softO_tEmod k]

/-- One pass over `n` remainders. -/
theorem softO_tTally : SoftOSqrtPow (fun n => tTally n) 2 := by
  unfold tTally
  growth_sqrt []

/-- The colliding pairs of a set of `n` numbers modulo one prime. -/
theorem softO_tColl : SoftOSqrtPow (fun n => tColl n (boundAt k n)) 2 := by
  unfold tColl
  growth_sqrt [softO_tResid k, softO_tTally]

/-- The heavy elements of a set of `n` numbers. -/
theorem softO_tHeavy : SoftOSqrtPow (fun n => tHeavy n (boundAt k n)) 2 := by
  unfold tHeavy
  growth_sqrt [softO_tResid k, softO_tTally]

/-- One search goes through the `Õ(√n)` candidate primes, at `Õ(n)` steps each. -/
theorem softO_tSearch : SoftOSqrtPow (fun n => tSearch (numPrimes k n) n n n (boundAt k n)) 3 := by
  unfold tSearch
  growth_sqrt [softO_numPrimes k, softO_tColl k]

/-- The modulus of a node: two searches. -/
theorem softO_tModulus :
    SoftOSqrtPow (fun n => tModulus (numPrimes k n) n n n (boundAt k n)) 3 := by
  unfold tModulus
  growth_sqrt [softO_tSearch k, softO_tColl k]

/-- The array of a node has `O(m²) = Õ(n)` cells. -/
theorem softO_tNodeArray :
    SoftOSqrtPow (fun n => tNodeArray (mPar n (boundAt k n)) n n n (boundAt k n)) 2 := by
  unfold tNodeArray
  growth_sqrt [softO_mPar k, softO_tResid k, softO_tTally]

/-- One call of the recursive procedure, without the call of the solver. -/
theorem softO_nodeOwn :
    SoftOSqrtPow (fun n => nodeOwn n (boundAt k n) (mPar n (boundAt k n)) (numPrimes k n)) 3 := by
  unfold nodeOwn
  growth_sqrt [softO_tModulus k, softO_tNodeArray k, softO_tHeavy k]

/-- The recursive procedure is called polylogarithmically often for one three-set input. -/
theorem softO_callsB : SoftOSqrtPow (fun n => callsB n) 0 := by
  unfold callsB
  growth_sqrt [Scale.SoftO.of_forall_le three_pow_fuel_le]

/-- The routines params and prep cost `Õ(n)`. -/
theorem softO_tSetup : SoftOSqrtPow (fun n => tSetup n (boundAt k n)) 2 := by
  unfold tSetup tParams tPrep tLog2 tPrimes tSort tDistinct tBits
  growth_sqrt [softO_wPar k, softO_mPar k, softO_Lam k]

/-- The host's own work is `Õ(n^{3/2})`. -/
theorem softO_ownAt : SoftOSqrtPow (ownAt k) 3 := by
  unfold ownAt coreOwn inputsB tPick tTwice tZeroThree
  growth_sqrt [softO_tSetup k, softO_nodeOwn k, softO_callsB, softO_Lam k]

/-- The host calls the solver polylogarithmically often. -/
theorem softO_callsAt : SoftOSqrtPow (callsAt k) 0 := by
  unfold callsAt coreCalls inputsB
  growth_sqrt [softO_callsB, softO_Lam k]

end own

end ClaimF

/-- **The need of the host is polynomially bounded** if the need of the solver is.  The number of
binary digits and the number of levels of the recursion are at most linear. -/
theorem polyNeed_chNeed (κ : ℕ) (r : ℕ → ℕ → Need) (hr : PolyNeed r) : PolyNeed (chNeed κ r) := by
  have hfuel : ∀ n, fuel n ≤ 3 * (n + 2) := fun n => by
    have : height n ≤ Nat.log 2 n + 2 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    have : Nat.log 2 n ≤ n := Nat.log_le_self _ _
    unfold fuel
    omega
  have hm : PolyBounded fun n U => mPar n (2 * max U (n ^ κ)) := by
    unfold mPar wPar Lam
    growth_poly []
  unfold chNeed coreNeed coreCells nodesNeed modulusNeed wordNeed Lam
  poly_need [hr.word, hr.cells, hr.depth, hm, Scale.SoftO.of_forall_le hfuel]

/-- [CH20, Theorem 5.1] for programs of the light language, from the host: 3SUM from
Convolution-3SUM.  For inputs of absolute value at most `n^κ` the host is taken with the parameter
`k = ⌈κ⌉`. -/
theorem claim_CH20_Theorem_5_1_of_host (h : ∀ κ : ℕ, IsHost c3Task s3Task (chTime κ) (chNeed κ)) :
    Claim.CH20_Theorem_5_1 lightModel := by
  intro κ _
  have hκ : κ ≤ ⌈κ⌉₊ := Nat.le_ceil κ
  generalize ⌈κ⌉₊ = k at hκ
  refine ⟨fun n => ownAt k n, fun n => callsAt k n, fun n => magAt k n, lenOf k, 160, k,
    (ClaimF.softO_ownAt k).isPowPolylog (by norm_num),
    (ClaimF.softO_callsAt k).isPowPolylog (by norm_num), isPowPolylog_lenOf k,
    fun n hn => ⟨one_le_lenOf k n, ?_, ?_⟩, ?_⟩
  · exact Nat.one_le_cast.2 (by unfold magAt boundAt; omega)
  · have hpow : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn
    have hmag : magAt k n ≤ 160 * n ^ k := by unfold magAt boundAt; omega
    rw [Real.rpow_natCast]
    change (magAt k n : ℝ) ≤ _
    exact_mod_cast hmag
  rintro T ⟨P, p, Tn, r, hr, hsol, hT⟩
  obtain ⟨R, p', hsol'⟩ := (h k).1 P p Tn r hsol
  refine ⟨timeUpTo (chTime k Tn), hsol'.solvedIn ((h k).2 r hr), fun n hn =>
    timeUpTo_le fun U hU => ?_⟩
  have hUk : U ≤ n ^ k := by
    have hle : (U : ℝ) ≤ (n : ℝ) ^ (k : ℝ) := (hU.trans_eq (max_eq_left (by positivity))).trans
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hκ)
    rw [Real.rpow_natCast] at hle
    exact_mod_cast hle
  rw [chTime_eq hUk]
  push_cast
  gcongr
  exact hT _ _ _ (one_le_lenOf k n) (by unfold magAt boundAt; omega) le_rfl

end Light.Sec3.ChanHe

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The host of the reduction from 3SUM to Convolution-3SUM

Theorem 21(a), after [CH20, Theorem 5.1]: 3SUM on n numbers reduces to
instances of Convolution-3SUM.  This file holds the outermost procedure of the reduction.

s3(n, U, x, fr), with a parameter κ that is fixed with the program: the host replaces the bound U by
U' = max U (n^κ) and calls core(n, 2U', x, fr) (`CoreSpec`).  So on all inputs with U ≤ n^κ the
solver of Convolution-3SUM is asked for instances of one and the same length and bound (`chTime`).
The power n^κ is computed by κ multiplications; the text of the program has one assignment for each
of them (`hostPow_ends`).  `hostCall_ends` is the call of core, and `host_spec` the whole.
-/


open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Host

/-- The number n of numbers, and at the end the answer. -/
abbrev Num : ℕ := 0
/-- The bound U. -/
abbrev Bound : ℕ := 1
/-- The address of the numbers. -/
abbrev Addr : ℕ := 2
/-- The free pointer. -/
abbrev Free : ℕ := 3
/-- n^κ, and then max U (n^κ). -/
abbrev Power : ℕ := 4

end Host

open Host

/-- κ multiplications of Power by n. -/
def hostPow : ℕ → Stmt
  | 0 => .skip
  | κ + 1 => .set Power (v Power *' v Num) ;; hostPow κ

/-- s3(n, U, x, fr): Power := max U (n^κ), and then the answer of the procedure number pCore (core)
on (n, 2 Power, x, fr). -/
def hostBody (κ pCore : ℕ) : Stmt :=
  .set Power (k 1) ;;
  hostPow κ ;;
  .ite (v Power <' v Bound) (.set Power (v Bound)) .skip ;;
  .call pCore [v Num, v Power +' v Power, v Addr, v Free] Num

/-- **The κ multiplications** take n^j to n^(j + κ), if all these powers fit in a word. -/
theorem hostPow_ends {n B : ℕ} {U a fr : ℤ} {μ : ℕ → ℤ} (hB : (B : ℤ) ≤ lim.word) (κ : ℕ) :
    ∀ j : ℕ, (∀ i ≤ j + κ, n ^ i ≤ B) →
      Ends lim P d (hostPow κ) ⟨frame [n, U, a, fr, (n ^ j : ℕ)], μ⟩ (4 * κ) fun σ' =>
        σ' = ⟨frame [n, U, a, fr, (n ^ (j + κ) : ℕ)], μ⟩ := by
  induction κ with
  | zero => exact fun j _ => Ends.skip rfl
  | succ κ ih =>
    intro j hb
    have : (n : ℤ) ^ j * n ≤ lim.word :=
      le_trans (by exact_mod_cast hb (j + 1) (by omega)) hB
    have : 0 ≤ (n : ℤ) ^ j * n := by positivity
    unfold hostPow
    -- Power := Power * Num
    light_set (n ^ (j + 1) : ℕ) using pow_succ
    rw [show j + (κ + 1) = j + 1 + κ by omega]
    exact (ih (j + 1) fun i hi => hb i (by omega)).mono (by simp; omega) fun _ h => h

/-- **The call of core**, with max U (n^κ) in Power. -/
theorem hostCall_ends {κ pCore : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    (hC : CoreSpec lim P pCore T r) {x : VecInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hok : (chNeed κ r x.N x.U).Ok lim fr d) :
    Ends lim P d (.call pCore [v Num, v Power +' v Power, v Addr, v Free] Num)
      ⟨frame [(x.N : ℤ), x.U, x.a, fr, (max x.U (x.N ^ κ) : ℕ)], μ⟩
      (8 + coreTime T x.N (2 * max x.U (x.N ^ κ))) fun σ' =>
        σ'.loc 0 = flag (ThreeSum (vecOf x.N x.X)) ∧ Kept μ σ'.mem fr := by
  have hword := hok.word
  have hdepth := hok.depth
  simp only [chNeed] at hword hdepth
  have hU := hpre.U_pos
  have hUle : x.U ≤ max x.U (x.N ^ κ) := le_max_left _ _
  have : max x.U (x.N ^ κ) ≤ x.N ^ κ + x.U := max_le (by omega) (by omega)
  have hcells : fr + (coreNeed r x.N (2 * max x.U (x.N ^ κ))).cells ≤ lim.space := hok.cells
  generalize max x.U (x.N ^ κ) = U' at *
  have hentries : AbsLe x.X U' := fun y hy => (hpre.le y hy).trans (by exact_mod_cast hUle)
  have hneed : (coreNeed r x.N (2 * U')).Ok lim fr (d + 1) :=
    { word := le_trans (by exact_mod_cast (by omega)) hword
      cells := hcells
      space := hok.space
      depth := by omega }
  -- Num := pCore(Num, Power + Power, Addr, Free)
  exact Ends.callTo (hC (d + 1) x.N U' x.a fr x.X μ hpre.len hentries hpre.seg hpre.below
    hpre.N_pos (hU.trans hUle) hneed) (fun res μ' h => h)

/-- **The host**: from the specification of core to what the task 3SUM asks. -/
theorem host_spec {κ pCore : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    (hC : CoreSpec lim P pCore T r) {x : VecInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hok : (chNeed κ r x.N x.U).Ok lim fr d) :
    Ends lim P d (hostBody κ pCore) ⟨frame [(x.N : ℤ), x.U, x.a, fr], μ⟩ (chTime κ T x.N x.U)
      fun σ' => σ'.loc 0 = flag (ThreeSum (vecOf x.N x.X)) ∧ Kept μ σ'.mem fr := by
  have hword := hok.word
  simp only [chNeed] at hword
  have : 1 ≤ x.N ^ κ := Nat.one_le_pow _ _ hpre.N_pos
  have hB : ((x.N ^ κ : ℕ) : ℤ) ≤ lim.word := le_trans (by exact_mod_cast (by omega)) hword
  have hcall := hostCall_ends hC hpre hok
  unfold hostBody chTime
  -- Power := 1
  light_set (x.N ^ 0 : ℕ)
  -- the κ multiplications
  light_piece (hostPow_ends hB κ 0 fun i hi =>
    Nat.pow_le_pow_right hpre.N_pos (by omega)) with _ rfl
  rw [Nat.zero_add]
  -- if Power < Bound then Power := Bound
  refine Ends.iteThen (fun hc => ?_) (fun hc => ?_)
  · have hc' : x.N ^ κ < x.U := by exact_mod_cast (show ((x.N ^ κ : ℕ) : ℤ) < x.U from hc)
    rw [max_eq_left hc'.le] at hcall ⊢
    -- Power := Bound, and the call
    light_set x.U
    exact hcall.mono (by light_time) fun _ h => h
  · have hc' : ¬ x.N ^ κ < x.U := fun h => hc (show ((x.N ^ κ : ℕ) : ℤ) < x.U by exact_mod_cast h)
    rw [max_eq_right (not_lt.1 hc')] at hcall ⊢
    -- skip, and the call
    exact Ends.next _ (Ends.skip (T := 0) (hcall.mono (by light_time) fun _ h => h))

end Light.Sec3.ChanHe

end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The reduction from 3SUM to Convolution-3SUM: the loop over the splittings.  row and grid

A step added to the reduction of [CH20, Theorem 5.1], one of the reductions behind Theorem 21(a):
the reduction from 3SUM on one set to the version with three sets, by the first binary digit in
which two labels differ (the label of a value x is x + V).  Below, "round" is the routine of that
name, which handles one splitting; a round of a loop is called so only in the names rowRound and
gridRound and in their lemmas.

* row runs through the splittings `(β, β', v)` for a fixed `β` and adds up the answers of round
  (`row_spec`; a round of its loop is `rowRound_ends`, and what it does to the sum is
  `RowSum.succ`).
* grid runs through `β` and returns 1 if some row has a positive sum (`grid_spec`,
  `gridRound_ends`).
-/


open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

variable {lim : Limits} {P : Program}

/-! ## The procedures -/

namespace Row

/-- The local variables of row: the arguments β, nd, val, bt, Λ, A, n, f, cx, fr; the sum; β'; and
the last answer.  Local 0 also takes the result. -/
abbrev Beta : ℕ := 0
@[inherit_doc Beta] abbrev Result : ℕ := 0
@[inherit_doc Beta] abbrev NumValues : ℕ := 1
@[inherit_doc Beta] abbrev Val : ℕ := 2
@[inherit_doc Beta] abbrev Table : ℕ := 3
@[inherit_doc Beta] abbrev Digits : ℕ := 4
@[inherit_doc Beta] abbrev Out0 : ℕ := 5
@[inherit_doc Beta] abbrev MaxLen : ℕ := 6
@[inherit_doc Beta] abbrev Levels : ℕ := 7
@[inherit_doc Beta] abbrev Params : ℕ := 8
@[inherit_doc Beta] abbrev Free : ℕ := 9
@[inherit_doc Beta] abbrev Total : ℕ := 10
@[inherit_doc Beta] abbrev Beta' : ℕ := 11
@[inherit_doc Beta] abbrev Ans : ℕ := 12

end Row

open Row in
/-- A round of row: the answers for (β, β', false) and (β, β', true) are added to the sum. -/
def rowRound (pRound : ℕ) : Stmt :=
  .call pRound
    [v Beta, v Beta', k 0,
      v NumValues, v Val, v Table, v Digits, v Out0, v MaxLen, v Levels, v Params, v Free] Ans ;;
  .set Total (v Total +' v Ans) ;;
  .call pRound
    [v Beta, v Beta', k 1,
      v NumValues, v Val, v Table, v Digits, v Out0, v MaxLen, v Levels, v Params, v Free] Ans ;;
  .set Total (v Total +' v Ans)

open Row in
/-- row(β, nd, val, bt, Λ, A, n, f, cx, fr): sum := 0; a round for each β' < Λ; return the sum. -/
def rowBody (pRound : ℕ) : Stmt :=
  .set Total (k 0) ;;
  .for Beta' (v Digits) (rowRound pRound) ;;
  .set Result (v Total)

namespace Grid

/-- The local variables of grid: the arguments nd, val, bt, Λ, A, n, f, cx, fr; the answer so far;
β; and the sum of the last row.  Local 0 also takes the result. -/
abbrev NumValues : ℕ := 0
@[inherit_doc NumValues] abbrev Result : ℕ := 0
@[inherit_doc NumValues] abbrev Val : ℕ := 1
@[inherit_doc NumValues] abbrev Table : ℕ := 2
@[inherit_doc NumValues] abbrev Digits : ℕ := 3
@[inherit_doc NumValues] abbrev Out0 : ℕ := 4
@[inherit_doc NumValues] abbrev MaxLen : ℕ := 5
@[inherit_doc NumValues] abbrev Levels : ℕ := 6
@[inherit_doc NumValues] abbrev Params : ℕ := 7
@[inherit_doc NumValues] abbrev Free : ℕ := 8
@[inherit_doc NumValues] abbrev Ans : ℕ := 9
@[inherit_doc NumValues] abbrev Beta : ℕ := 10
@[inherit_doc NumValues] abbrev Total : ℕ := 11

end Grid

open Grid in
/-- A round of grid: if the sum of row β is positive, the answer is 1. -/
def gridRound (pRow : ℕ) : Stmt :=
  .call pRow
    [v Beta, v NumValues, v Val, v Table, v Digits, v Out0, v MaxLen, v Levels, v Params, v Free]
    Total ;;
  .ite (k 0 <' v Total) (.set Ans (k 1)) .skip

open Grid in
/-- grid(nd, val, bt, Λ, A, n, f, cx, fr): answer := 0; a round for each β < Λ; return the
answer. -/
def gridBody (pRow : ℕ) : Stmt :=
  .set Ans (k 0) ;;
  .for Beta (v Digits) (gridRound pRow) ;;
  .set Result (v Ans)

/-! ## What the two routines share -/

/-- What row and grid assume provides a word for 2Λ + 16, one more level of calls, and what the
routine one level below assumes. -/
theorem GridPre.down {r : ℕ → ℕ → Need} {a : FrontArgs} {d f e : ℕ}
    (H : GridPre lim r a f (e + 1) d) :
    2 * (a.Λ : ℤ) + 16 ≤ lim.word ∧ d < lim.depth ∧ GridPre lim r a f e (d + 1) := by
  have := H.V_pos
  have hword := H.ok.word
  have hdepth := H.ok.depth
  have := Nat.log_lt_self 2 (x := 2 * a.V) (by omega)
  simp only [gridNeed] at hword hdepth
  push_cast at hword
  have : a.Λ ≤ 2 * a.V := by rw [H.lam, Lam]; omega
  exact ⟨by omega, by omega, H.V_pos, H.m_pos, H.lam, H.primes,
    H.ok.mono (by simp [gridNeed]) (by simp [gridNeed]) (by simp only [gridNeed]; omega)⟩

/-! ## row -/

/-- What is known about the sum after the splittings (β, β', v) with β' < i: it lies between 0 and
2i, and it is positive exactly if one of the answers was yes. -/
structure RowSum (S : ℕ → Bool → Prop) (i : ℕ) (acc : ℤ) : Prop where
  nonneg : 0 ≤ acc
  le : acc ≤ 2 * (i : ℤ)
  pos_iff : 0 < acc ↔ ∃ β' < i, ∃ v, S β' v

/-- Adding the answers for (i, false) and (i, true) takes `RowSum S i` to `RowSum S (i + 1)`. -/
theorem RowSum.succ {S : ℕ → Bool → Prop} {i : ℕ} {acc : ℤ} (h : RowSum S i acc) :
    RowSum S (i + 1) (acc + flag (S i false) + flag (S i true)) := by
  have := h.nonneg
  have := h.le
  have := flag_mem (S i false)
  have := flag_mem (S i true)
  have hsplit : (∃ β' < i + 1, ∃ v, S β' v) ↔ (∃ β' < i, ∃ v, S β' v) ∨ S i false ∨ S i true := by
    rw [Nat.exists_lt_succ_right, Bool.exists_bool]
  refine ⟨by omega, by push_cast; omega, ?_⟩
  rw [hsplit, ← h.pos_iff]
  by_cases hf : S i false <;> by_cases ht : S i true <;>
    simp [flag_of, flag_of_not, hf, ht] <;> omega

section row

variable {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {a : FrontArgs} {d f β pRound : ℕ} {μ : ℕ → ℤ}

/-- The state before round i of the loop of row: the locals are the arguments, the sum, i, and the
last answer; the sum is as `RowSum` says; and below the free pointer only the 3n cells from A have
changed. -/
def RowInv (μ : ℕ → ℤ) (a : FrontArgs) (f β i : ℕ) (σ : State) : Prop :=
  ∃ (acc x : ℤ) (μ' : ℕ → ℤ), RowSum (a.Yes f β) i acc ∧ KeptBut μ μ' a.fr a.A (3 * a.n) ∧
    σ = ⟨frame ((β : ℤ) :: a.vals f ++ [acc, (i : ℤ), x]), μ'⟩

/-- **A round of row** adds the answers for (β, β', false) and (β, β', true) to the sum. -/
theorem rowRound_ends (hRound : RoundSpec lim P pRound T r) (hmem : FrontMem μ a) (hβ : β < a.Λ)
    (H : GridPre lim r a f 1 d) {i : ℕ} (hi : i < a.Λ) {σ : State} (hσ : RowInv μ a f β i σ) :
    Ends lim P d (rowRound pRound) σ (2 * tRound T a.n a.V a.m a.np f + 36) fun σ' =>
      σ'.loc Row.Beta' = i ∧ RowInv μ a f β (i + 1)
        { σ' with loc := Function.update σ'.loc Row.Beta' ((i : ℤ) + 1) } := by
  obtain ⟨acc, x, μ', hsum, kept, rfl⟩ := hσ
  obtain ⟨hword, hd, H'⟩ := H.down
  have := flag_mem (a.Yes f β i false)
  have := flag_mem (a.Yes f β i true)
  have := hsum.nonneg
  have := hsum.le
  -- x := round(β, β', 0, nd, val, bt, Λ, A, n, f, cx, fr)
  light_call (hRound a f β i false μ' (hmem.keptBut kept) hβ hi (d + 1) H')
    with _ μ₁ ⟨rfl, kept₁⟩
  -- sum := sum + x
  light_set (acc + flag (a.Yes f β i false))
  -- x := round(β, β', 1, nd, val, bt, Λ, A, n, f, cx, fr)
  light_call (hRound a f β i true μ₁ (hmem.keptBut (kept.trans kept₁)) hβ hi (d + 1) H')
    with _ μ₂ ⟨rfl, kept₂⟩
  -- sum := sum + x
  light_set (acc + flag (a.Yes f β i false) + flag (a.Yes f β i true))
  exact ⟨by simp, _, _, μ₂, hsum.succ, kept.trans (kept₁.trans kept₂),
      by rw [update_frame_setLocal]; rfl⟩

/-- **row** meets its specification. -/
theorem row_spec {p : ℕ} (hP : P[p]? = some (rowBody pRound))
    (hRound : RoundSpec lim P pRound T r) : RowSpec lim P p T r := by
  intro a f β μ hmem hβ d H
  refine .of_body hP ?_
  have := H.down.1
  -- sum := 0
  refine Ends.setToThen 0 ?_ (hT := by simp [tRow])
  -- for β' < Λ
  refine Ends.next _ (Ends.for (RowInv μ a f β) a.Λ (2 * tRound T a.n a.V a.m a.np f + 36)
    ?start ?round ?done ?bound (hT := le_rfl)) (by simp [tRow]; ring_nf; omega)
  case start =>
    -- The last local has not been written yet and is 0.
    exact ⟨0, 0, μ, ⟨le_rfl, by simp, by simp⟩, .refl,
      by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl⟩
  case round => exact fun i σ hi _ hσ => rowRound_ends hRound hmem hβ H hi hσ
  case done =>
    rintro _ - ⟨acc, x, μ', hsum, kept, rfl⟩
    -- return the sum
    exact Ends.setTo acc
      ⟨by simpa using hsum.nonneg, by simpa using hsum.le, by simpa using hsum.pos_iff, kept⟩
      (hT := by simp [tRow]; ring_nf; omega)
  case bound =>
    rintro i _ - - ⟨acc, x, μ', -, -, rfl⟩
    simp

end row

/-! ## grid -/

section grid

variable {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {a : FrontArgs} {d f pRow : ℕ} {μ : ℕ → ℤ}

/-- Some splitting (β, β', v) of row β gives a yes-instance. -/
abbrev FrontArgs.RowYes (a : FrontArgs) (f β : ℕ) : Prop := ∃ β' < a.Λ, ∃ v, a.Yes f β β' v

/-- The state before round i of the loop of grid: the locals are the arguments, the answer so far,
i, and the sum of the last row; the answer tells whether one of the rows below i had a positive sum;
and below the free pointer only the 3n cells from A have changed. -/
def GridInv (μ : ℕ → ℤ) (a : FrontArgs) (f i : ℕ) (σ : State) : Prop :=
  ∃ (x : ℤ) (μ' : ℕ → ℤ), KeptBut μ μ' a.fr a.A (3 * a.n) ∧
    σ = ⟨frame (a.vals f ++ [flag (∃ β < i, a.RowYes f β), (i : ℤ), x]), μ'⟩

/-- **A round of grid** asks for the sum of row i and sets the answer to 1 if it is positive. -/
theorem gridRound_ends (hRow : RowSpec lim P pRow T r) (hmem : FrontMem μ a)
    (H : GridPre lim r a f 2 d) {i : ℕ} (hi : i < a.Λ) {σ : State} (hσ : GridInv μ a f i σ) :
    Ends lim P d (gridRound pRow) σ (tRow T a.n a.V a.m a.np f a.Λ + 18) fun σ' =>
      σ'.loc Grid.Beta = i ∧ GridInv μ a f (i + 1)
        { σ' with loc := Function.update σ'.loc Grid.Beta ((i : ℤ) + 1) } := by
  obtain ⟨x, μ', kept, rfl⟩ := hσ
  obtain ⟨hword, hd, H'⟩ := H.down
  -- sum := row(β, nd, val, bt, Λ, A, n, f, cx, fr)
  light_call (hRow a f i μ' (hmem.keptBut kept) hi (d + 1) H') with sum μ₁ ⟨-, -, hpos, kept₁⟩
  -- if 0 < sum then answer := 1
  refine Ends.iteLast (fun hyes => ?_) (fun hno => ?_)
  · have hrow := hpos.1 (by simpa using hyes)
    exact Ends.setTo 1 ⟨by simp, sum, μ₁, kept.trans kept₁, by
      rw [update_frame_setLocal, flag_of (Nat.exists_lt_succ_right.2 (Or.inr hrow))]; rfl⟩
  · have hrow : ¬ a.RowYes f i := fun h => hno (by simpa using hpos.2 h)
    refine Ends.skip ⟨by simp, sum, μ₁, kept.trans kept₁, ?_⟩
    rw [update_frame_setLocal, flag_congr (Nat.exists_lt_succ_right.trans (or_iff_left hrow))]
    rfl

/-- **grid** meets its specification. -/
theorem grid_spec {p : ℕ} (hP : P[p]? = some (gridBody pRow)) (hRow : RowSpec lim P pRow T r) :
    GridSpec lim P p T r := by
  intro a f μ hmem d H
  refine .of_body hP ?_
  have := H.down.1
  -- answer := 0
  refine Ends.setToThen 0 ?_ (hT := by simp [tGrid])
  -- for β < Λ
  refine Ends.next _ (Ends.for (GridInv μ a f) a.Λ (tRow T a.n a.V a.m a.np f a.Λ + 18)
    ?start ?round ?done ?bound (hT := le_rfl)) (by simp [tGrid]; ring_nf; omega)
  case start =>
    exact ⟨0, μ, .refl, by
      rw [update_frame_setLocal, ← frame_append_zeros _ 1, flag_of_not (by simp)]; rfl⟩
  case round => exact fun i σ hi _ hσ => gridRound_ends hRow hmem H hi hσ
  case done =>
    rintro _ - ⟨x, μ', kept, rfl⟩
    -- return the answer
    exact Ends.setTo (flag (∃ β < a.Λ, a.RowYes f β)) ⟨rfl, kept⟩
      (hT := by simp [tGrid]; ring_nf; omega)
  case bound =>
    rintro i _ - - ⟨x, μ', -, rfl⟩
    simp

end grid


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The program of the reduction from 3SUM to Convolution-3SUM, assembled

The procedures of the reduction are appended to the program of an arbitrary solver of
Convolution-3SUM. Each of them meets its specification because the procedures that it calls meet
theirs; the last one, the host, solves 3SUM (`isHost_s3`).  That the answer is right comes from
`core_spec`, through `threeSum_iff_trees`.  With the arithmetic of `claim_CH20_Theorem_5_1_of_host`
this gives [CH20, Theorem 5.1] (Theorem 21(a)) for programs of the light language
(`claim_CH20_Theorem_5_1`).
-/




namespace Proc

/-- The places of the procedures in the list `chBodies`. -/
abbrev emod : ℕ := 0
@[inherit_doc emod] abbrev log2 : ℕ := 1
@[inherit_doc emod] abbrev clog2 : ℕ := 2
@[inherit_doc emod] abbrev sqrt : ℕ := 3
@[inherit_doc emod] abbrev sieve : ℕ := 4
@[inherit_doc emod] abbrev half : ℕ := 5
@[inherit_doc emod] abbrev merge : ℕ := 6
@[inherit_doc emod] abbrev copy : ℕ := 7
@[inherit_doc emod] abbrev fill : ℕ := 8
@[inherit_doc emod] abbrev sort : ℕ := 9
@[inherit_doc emod] abbrev resid : ℕ := 10
@[inherit_doc emod] abbrev tally : ℕ := 11
@[inherit_doc emod] abbrev coll : ℕ := 12
@[inherit_doc emod] abbrev heavy : ℕ := 13
@[inherit_doc emod] abbrev search : ℕ := 14
@[inherit_doc emod] abbrev modulus : ℕ := 15
@[inherit_doc emod] abbrev nodeArray : ℕ := 16
@[inherit_doc emod] abbrev nodes : ℕ := 17
@[inherit_doc emod] abbrev distinct : ℕ := 18
@[inherit_doc emod] abbrev twice : ℕ := 19
@[inherit_doc emod] abbrev zeroThree : ℕ := 20
@[inherit_doc emod] abbrev bits : ℕ := 21
@[inherit_doc emod] abbrev pick : ℕ := 22
@[inherit_doc emod] abbrev round : ℕ := 23
@[inherit_doc emod] abbrev row : ℕ := 24
@[inherit_doc emod] abbrev grid : ℕ := 25
@[inherit_doc emod] abbrev params : ℕ := 26
@[inherit_doc emod] abbrev prep : ℕ := 27
@[inherit_doc emod] abbrev core : ℕ := 28
@[inherit_doc emod] abbrev host : ℕ := 29

end Proc

/-- The procedures of the reduction, for a solver of Convolution-3SUM that is procedure number pC3
of a program with o procedures: the procedure at the place i of this list gets the number o + i.
The places have the names `Proc.emod`, …, `Proc.host`, in the order of the list. -/
def chBodies (κ pC3 o : ℕ) : Program :=
  [emodBody,
    log2Body,
    clog2Body,
    sqrtBody,
    sieveBody,
    halfBody,
    mergeBody,
    copyBody,
    fillBody,
    sortBody (o + Proc.sort) (o + Proc.half) (o + Proc.merge) (o + Proc.copy),
    residBody (o + Proc.emod),
    tallyBody,
    collBody (o + Proc.resid) (o + Proc.tally),
    heavyBody (o + Proc.resid) (o + Proc.tally),
    searchBody (o + Proc.coll),
    modulusBody (o + Proc.search) (o + Proc.coll),
    nodeArrayBody (o + Proc.resid) (o + Proc.tally),
    nodesBody (o + Proc.nodes) (o + Proc.modulus) (o + Proc.nodeArray) pC3 (o + Proc.heavy),
    distinctBody,
    twiceBody,
    zeroThreeBody,
    bitsBody,
    pickBody,
    roundBody (o + Proc.pick) (o + Proc.nodes),
    rowBody (o + Proc.round),
    gridBody (o + Proc.row),
    paramsBody (o + Proc.log2) (o + Proc.clog2) (o + Proc.sqrt),
    prepBody (o + Proc.sieve) (o + Proc.fill) (o + Proc.copy) (o + Proc.sort) (o + Proc.distinct)
      (o + Proc.bits),
    coreBody (o + Proc.params) (o + Proc.prep) (o + Proc.grid) (o + Proc.twice) (o + Proc.zeroThree)
      (o + Proc.nodes),
    hostBody κ (o + Proc.core)]

/-- **The host**: from every solver of Convolution-3SUM, the procedures of the reduction make a
solver of 3SUM. -/
theorem isHost_s3 (κ : ℕ) : IsHost c3Task s3Task (chTime κ) (chNeed κ) := by
  refine ⟨fun P₀ pC3 T r hsol => ⟨chBodies κ pC3 P₀.length, P₀.length + Proc.host,
    hostBody κ (P₀.length + Proc.core), ?_,
    fun R lim d x μ fr hpre hok => ?_⟩, fun r hr => polyNeed_chNeed κ r hr⟩
  · have := getElem?_append_append (P₀ := P₀) (B := chBodies κ pC3 P₀.length) [] (i := Proc.host)
      rfl
    rwa [List.append_nil] at this
  rw [List.append_assoc]
  have L : ∀ {i : ℕ} {body : Stmt}, (chBodies κ pC3 P₀.length)[i]? = some body →
      (P₀ ++ (chBodies κ pC3 P₀.length ++ R))[P₀.length + i]? = some body :=
    fun h => getElem?_append_append R h
  have hEmod : EmodSpec lim (P₀ ++ (chBodies κ pC3 P₀.length ++ R)) P₀.length :=
    emodSpec_of (L (i := Proc.emod) rfl)
  have hLog2 := log2Spec_of (lim := lim) (L (i := Proc.log2) rfl)
  have hClog2 := clog2Spec_of (lim := lim) (L (i := Proc.clog2) rfl)
  have hPrimes := primesSpec_of (lim := lim) (L (i := Proc.sieve) rfl)
  have hSort :=
    sortSpec_of (lim := lim) ⟨L (i := Proc.sort) rfl, L (i := Proc.half) rfl,
      L (i := Proc.merge) rfl, L (i := Proc.copy) rfl⟩
  have hResid := resid_spec (L (i := Proc.resid) rfl) hEmod
  have hTally := tally_spec (lim := lim) (L (i := Proc.tally) rfl)
  have hColl := coll_spec (L (i := Proc.coll) rfl) hResid hTally
  have hHeavy := heavy_spec (L (i := Proc.heavy) rfl) hResid hTally
  have hModulus := modulusSpec_of (L (i := Proc.modulus) rfl) (L (i := Proc.search) rfl) hColl
  have hArray := nodeArray_spec (L (i := Proc.nodeArray) rfl) hResid hTally
  have hNodes := nodes_spec ⟨hsol, L (i := Proc.nodes) rfl, hModulus, hArray, hHeavy⟩
  have hDistinct := distinct_spec (lim := lim) (L (i := Proc.distinct) rfl)
  have hTwice := twice_spec (lim := lim) (L (i := Proc.twice) rfl)
  have hZero := zeroThree_spec (lim := lim) (L (i := Proc.zeroThree) rfl)
  have hBits := bits_spec (lim := lim) (L (i := Proc.bits) rfl)
  have hPick := pick_spec (lim := lim) (L (i := Proc.pick) rfl)
  have hRound := round_spec (L (i := Proc.round) rfl) hPick hNodes
  have hRow := row_spec (L (i := Proc.row) rfl) hRound
  have hGrid := grid_spec (L (i := Proc.grid) rfl) hRow
  have hParams := params_spec (L (i := Proc.params) rfl) hLog2 hClog2 (L (i := Proc.sqrt) rfl)
  have hPrep :=
    prep_spec (L (i := Proc.prep) rfl) hPrimes (L (i := Proc.fill) rfl) (L (i := Proc.copy) rfl)
      hSort hDistinct hBits
  have hCore := core_spec (L (i := Proc.core) rfl) hParams hPrep hGrid hTwice hZero hNodes
  exact host_spec hCore hpre hok

/-- [CH20, Theorem 5.1] for programs of the light language: 3SUM from Convolution-3SUM. -/
theorem claim_CH20_Theorem_5_1 : Claim.CH20_Theorem_5_1 lightModel :=
  claim_CH20_Theorem_5_1_of_host isHost_s3

end Light.Sec3.ChanHe
