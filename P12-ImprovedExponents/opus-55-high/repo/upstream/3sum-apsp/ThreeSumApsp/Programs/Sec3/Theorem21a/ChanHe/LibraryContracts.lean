/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Lang.Lib.Emod
import ThreeSumApsp.Lang.Lib.MergeSort
import ThreeSumApsp.Lang.Lib.Sieve
import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Contracts

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
  have hrounds := emodRounds_le (M := M) (show x.natAbs ≤ V by linarith)
  refine (emod_meets hP ⟨hM, hok.space, hok.word, hok.cells⟩ hx).mono_time ?_
  unfold tEmod emodTime
  omega

/-- The logarithm, rounded down. -/
theorem log2Spec_of (hP : P[p]? = some log2Body) : Log2Spec lim P p := by
  intro d x μ hword
  refine (log2_meets hP μ).mono_time ?_
  unfold tLog2 log2Time
  omega

/-- The logarithm, rounded up. -/
theorem clog2Spec_of (hP : P[p]? = some clog2Body) : Clog2Spec lim P p := by
  intro d x μ hword
  have := clog_le_log_succ x
  refine (clog2_meets hP μ).mono_time ?_
  unfold tLog2 clog2Time
  omega

/-- The sieve. -/
theorem primesSpec_of (hP : P[p]? = some sieveBody) : PrimesSpec lim P p := by
  intro d fr m out μ hout hok
  have hword := hok.word
  have hcells := hok.cells
  simp [primesNeed] at hword hcells
  refine (sieve_meets hP ⟨hok.space, by omega, hout, hcells⟩).mono ?_
    fun _ _ ⟨hcount, hseg, hkept⟩ => ⟨hcount, hseg, hkept.mono fun _ ha => by omega⟩
  -- `15 m (⌊log₂ m⌋ + 5) + …` against `60 m (⌊log₂ m⌋ + 2) + 60`
  unfold tPrimes sieveTime
  grind

/-- Sorting.  The program holds sort at the number p, and half, merge and copy, which sort
calls. -/
theorem sortSpec_of {pHalf pMerge pCopy : ℕ} (C : MergeSort.Procs P p pHalf pMerge pCopy) :
    SortSpec lim P p := by
  intro d fr a V L μ hseg _ hbelow hok
  have hword := hok.word
  have hcells := hok.cells
  have hdepth := hok.depth
  simp [sortNeed] at hword hcells hdepth
  have hclog := clog_le_log_succ L.length
  refine (sort_meets C hok.space (by omega) hseg hbelow hcells d (by omega)).mono ?_ fun _ _ h => h
  -- `n ⌈log₂ n⌉ ≤ n (⌊log₂ n⌋ + 1)`
  have hmul := Nat.mul_le_mul_left L.length hclog
  unfold tSort sortTime
  grind
