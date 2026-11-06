/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Lang.Auto
public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.Passes
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem21b.BitSearch

/-!
# The (min,+)-product from "all pairs", bit by bit

Theorem 21(b), after [VW18, Theorem 4.2].  The host below computes the
(min,+)-product over an arbitrary solver of the task "all pairs": for three matrices X, Y, V, which
pairs (i, j) have X[i,k] + Y[k,j] < V[i,j] for some k.

mp(n, U, a, b, c, fr).  All entries of the product lie between −2U and 2U.  The output array starts
as −2U everywhere.  Let R be least with 2^R > 4U; the powers 1, 2, …, 2^(R−1) are written to the R
cells from fr while R is found by doubling.  For t = R − 1, …, 0: V := lo + 2^t (the n² cells from
fr + R), the solver writes its flags to the next n² cells, and lo grows by 2^t where the flag is 0.
Before the round for t, lo ≤ C[i,j] < lo + 2^(t+1): lo is C[i,j] with the lowest t + 1 bits of
C[i,j] + 2U cleared (lows x (t + 1)).  The entries of V have absolute value at most 6U.

The result is isHost_mp : IsHost pairsTask mpTask mpTime mpNeed.  First the lists: the lower bounds
lows x t, which start as −2U (lows_top), end as the product (lows_zero), and change in a round as
bump changes them (lows_round, from bitLo_step).  Then the program: the powers of two (powers_spec),
a round (round_spec, with the invariant Inv), all rounds (rounds_spec), the host (mp_spec).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

/-! ## The program -/

/-- The number of rounds: the least R with 2^R > 4U. -/
def mpRounds U := Nat.log 2 (4 * U) + 1


/-- The numbers n², 2U, 4U, −2U, 6U. -/
def mpConsts  :=
  .set 6 (v 0 *' v 0) ;;
  .set 7 (v 1 +' v 1) ;;
  .set 8 (v 7 +' v 7) ;;
  .set 9 (k 0 -' v 7) ;;
  .set 10 (v 7 +' v 8)

/-- The powers 1, 2, …, 2^(R−1) are written to the cells from fr, while R is found by doubling. -/
def mpPowers  :=
  .set 11 (k 0) ;;
  .set 12 (k 1) ;;
  .while (v 12 ≤' v 8) (
    .store (v 5 +' v 11) (v 12) ;;
    .set 11 (v 11 +' k 1) ;;
    .set 12 (v 12 +' v 12))

/-- The round for t = Count − 1: V := lo + 2^t, the solver's flags, and lo grows by 2^t where the
flag is 0. -/
def mpRound (pPairs pAddc pBump : ℕ)  :=
  .set 11 (v 11 -' k 1) ;;
  .set 12 (M (v 5 +' v 11)) ;;
  .call pAddc [v 6, v 12, v 4, v 13] 16 ;;
  .call pPairs [v 0, v 10, v 2, v 3, v 13, v 14, v 15] 16 ;;
  .call pBump [v 6, v 12, v 14, v 4] 16

/-- mp(n, U, a, b, c, fr), over the procedures number pPairs (a solver of "all pairs"), pFill, pAddc
and pBump. -/
def mpBody (pPairs pFill pAddc pBump : ℕ)  :=
  mpConsts ;;
  mpPowers ;;
  .set 13 (v 5 +' v 11) ;;
  .set 14 (v 13 +' v 6) ;;
  .set 15 (v 14 +' v 6) ;;
  .call pFill [v 4, v 6, v 9] 16 ;;
  .while (k 0 <' v 11) (mpRound pPairs pAddc pBump)

/-- The number of steps of one round, given the time of the solver. -/
def Mp.roundTime (T : Light.SolverTime) n U := T n (6 * U) + 49 * (n * n) + 42

/-- The time of the host, given the time of the solver: R calls at the bound 6U, and O(n²) steps for
each call. -/
def mpTime (T : Light.SolverTime) n U :=
  mpRounds U * (T n (6 * U) + 49 * (n * n) + 70) + 13 * (n * n) + 60

/-- The need of the host, given the need of the solver: the numbers up to 8U + 1, room for the R
powers of two, for V and for the flags, and one more level of calls. -/
def mpNeed (r : Light.NeedFn) (n U : ℕ) : Need where
  word := max (r n (6 * U)).word (8 * U + 1)
  cells := mpRounds U + 2 * (n * n) + (r n (6 * U)).cells
  depth := (r n (6 * U)).depth + 1

namespace Mp

/-! ## The number of rounds -/

/-- The powers of two below 2^R are at most 4U. -/
theorem pow_range {U i} (hU : 1 ≤ U) (hi : i < mpRounds U) :
    0 < (2 : ℤ) ^ i ∧ (2 : ℤ) ^ i ≤ 4 * U := by

  exact ⟨by positivity, mod_cast Nat.pow_le_of_le_log (by omega) (by simp_all [mpRounds])⟩

/-- 2^R is above 4U. -/
theorem lt_pow_rounds (U : ℕ) : 4 * (U : ℤ) < 2 ^ mpRounds U := mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (4 * U)

/-! ## The lists of a round -/

variable {x : MatInst} {μ : Light.Memory} {fr : ℕ}

/-- The lower bounds when t rounds remain: bitLo U t c for every entry c of the product, that is c
with the lowest t bits of c + 2U cleared.  So lo ≤ c < lo + 2^t. -/
def lows (x : MatInst) t := (minPlusList x.n x.A x.B).map (bitLo x.U t)

/-- The matrix V of the round for t: the lower bounds plus 2^t. -/
def asked x t := (lows x (t + 1)).map (· + 2 ^ t)

/-- The flags that the solver returns in the round for t. -/
noncomputable def flags x t := pairFlags x.n x.A x.B (asked x t)

@[simp] theorem length_lows x t : (lows x t).length = x.n * x.n := by
  simp [lows, length_minPlusList]

@[simp] theorem length_asked x t : (asked x t).length = x.n * x.n := by
  simp [asked]

@[simp] theorem length_flags x t : (flags x t).length = x.n * x.n := by
  simp [flags, pairFlags]

/-- An entry of the lower bounds. -/
theorem getElem_lows x t q hq :
    (lows x t)[q] = bitLo x.U t (minPlusEntry x.n x.A x.B (q / x.n) (q % x.n)) := by
  simp [lows, minPlusList]

/-- The entries of the product lie between −2U and 2U. -/
def entry_range (hpre : x.Pre μ fr) i j :=
  abs_le.1 (abs_minPlusEntry_le hpre.n_pos (by positivity) hpre.leA hpre.leB i j)

variable (hpre : x.Pre μ fr)

include hpre in
/-- The lower bounds lie between −2U and 2U. -/
theorem lows_range t q (hq : q < (lows x t).length) :
    -2 * x.U ≤ (lows x t)[q] ∧ (lows x t)[q] ≤ 2 * x.U := by
  rw [getElem_lows]
  have hentry := entry_range hpre (q / x.n) (q % x.n)
  exact ⟨le_bitLo _ _ _, (bitLo_le hentry.1 _).trans hentry.2⟩

include hpre in
/-- At the beginning all lower bounds are −2U. -/
theorem lows_top :
    lows x (mpRounds x.U) = List.replicate (x.n * x.n) (-2 * (x.U : ℤ)) := by
  refine List.ext_getElem (by simp) fun q hq _ => ?_
  rw [getElem_lows, List.getElem_replicate]
  exact bitLo_top (by linarith [(entry_range hpre (q / x.n) (q % x.n)).2, lt_pow_rounds x.U])

include hpre in
/-- At the end the lower bounds are the product. -/
theorem lows_zero : lows x 0 = minPlusList x.n x.A x.B := by
  refine List.ext_getElem (by simp [length_minPlusList]) fun q hq _ => ?_
  rw [getElem_lows, bitLo_zero (entry_range hpre _ _).1]
  simp [minPlusList]

include hpre in
/-- A flag of the round for t: is the entry of the product below the lower bound plus 2^t? -/
theorem getElem_flags t q hq :
    (flags x t)[q] = flag (minPlusEntry x.n x.A x.B (q / x.n) (q % x.n) <
      bitLo x.U (t + 1) (minPlusEntry x.n x.A x.B (q / x.n) (q % x.n)) + 2 ^ t) := by

  have hV : (asked x t).getD q 0 =
      bitLo x.U (t + 1) (minPlusEntry x.n x.A x.B (q / x.n) (q % x.n)) + 2 ^ t := by
    simp_all [asked, getElem_lows]
  simp only [flags, pairFlags, List.getElem_map, List.getElem_range, hV]
  exact flag_congr (exists_sum_lt_iff hpre.n_pos x.A x.B (q / x.n) (q % x.n) _)

include hpre in
/-- **One round**: each lower bound grows by 2^t where the flag is 0. -/
theorem lows_round t :
    List.zipWith (fun l f => l + 2 ^ t * (1 - f)) (lows x (t + 1)) (flags x t) =
      lows x t := by
  refine List.ext_getElem (by simp) fun q _ _ => ?_
  rw [List.getElem_zipWith, getElem_flags hpre, getElem_lows, getElem_lows,
    bitLo_step (entry_range hpre _ _).1 t]

/-- A flag is 0 or 1. -/
theorem flags_eq_zero_or_one x t : ∀ f ∈ flags x t, f = 0 ∨ f = 1 := by
  intro f hf
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hf
  have := flag_mem (∃ k < x.n, x.A.getD (q / x.n * x.n + k) 0 + x.B.getD (k * x.n + q % x.n) 0 <
    (asked x t).getD q 0)
  omega

include hpre in
/-- The lower bounds have absolute value at most 2U. -/
theorem absLe_lows t : AbsLe (lows x t) (2 * x.U) := by
  intro y hy
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hy
  exact abs_le.2 (lows_range hpre t q hq)

include hpre in
/-- The entries of V have absolute value at most 6U. -/
theorem abs_asked_le {t} (ht : t < mpRounds x.U) :
    ∀ y ∈ lows x (t + 1), |y + 2 ^ t| ≤ 6 * (x.U : ℤ) := by
  intro y hy
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hy
  have  := pow_range hpre.U_pos ht
  have  := lows_range hpre (t + 1) q hq
  exact abs_le.2 ⟨by omega, by omega⟩

/-! ## The surroundings -/

variable {P₀ R₀ : Program} {pPairs pFill pAddc pBump : ℕ} {T : Light.SolverTime} {r : Light.NeedFn}
  {lim : Limits} {d : ℕ}

/-- The surroundings of mp: a solver of "all pairs", and the three passes in the program. -/
structure Ctx (P₀ R₀ : Program) (pPairs pFill pAddc pBump : ℕ) (T : Light.SolverTime) (r : Light.NeedFn) :
    Prop where
  sol : Solves pairsTask P₀ pPairs T r
  fill : (P₀ ++ R₀)[pFill]? = some fillBody
  addc : (P₀ ++ R₀)[pAddc]? = some addcBody
  bump : (P₀ ++ R₀)[pBump]? = some bumpBody

/-- What the limits have to allow for: the numbers of the solver and those up to 8U + 1; room for
the powers of two, V, the flags and the solver; one level of calls more than the solver needs. -/
structure Lim (lim : Limits) (d : ℕ) (r : Light.NeedFn) (x : MatInst) (fr : ℕ) : Prop where
  solver : ((r x.n (6 * x.U)).word : ℤ) ≤ lim.word
  word : 8 * (x.U : ℤ) + 1 ≤ lim.word
  cells : fr + (mpRounds x.U + 2 * (x.n * x.n) + (r x.n (6 * x.U)).cells) ≤ lim.space
  space : (lim.space : ℤ) ≤ lim.word
  depth : d + (r x.n (6 * x.U)).depth + 1 ≤ lim.depth

private theorem lim_of_ok (hok : (mpNeed r x.n x.U).Ok lim fr d) : Lim lim d r x fr where
  solver := le_trans (mod_cast le_max_left _ _) hok.word
  word := le_trans (mod_cast le_max_right (r x.n (6 * x.U)).word (8 * x.U + 1)) hok.word
  cells := hok.cells
  space := hok.space
  depth := hok.depth

/-- The first eleven local variables, which do not change after mpConsts. -/
abbrev consts (x : MatInst) (fr : ℕ) : List ℤ :=
  [x.n, x.U, x.a, x.b, x.c, fr, x.n * x.n, 2 * x.U, 4 * x.U, -2 * x.U,
    6 * x.U]

/-- The local variables during the rounds. -/
abbrev locals x (fr count : ℕ) power unused :=
  consts x fr ++ [(count : ℤ), power, fr + mpRounds x.U,
    fr + mpRounds x.U + x.n * x.n, fr + mpRounds x.U + x.n * x.n + x.n * x.n, unused]

/-! ## Before the rounds -/

/-- mpConsts computes the five numbers. -/
theorem consts_spec {P} (hpre : x.Pre μ fr) (hlim : Lim lim d r x fr) :
    Ends lim P d mpConsts ⟨frame [x.n, x.U, x.a, x.b, x.c, fr], μ⟩ 20 fun σ' =>
      σ' = ⟨frame (consts x fr), μ⟩ := by
  light_block [Light.Sec3.Mp.consts, mpConsts]

/-- mpPowers finds R and writes the powers of two to the R cells from fr. -/
theorem powers_spec {P} (hpre : x.Pre μ fr) (hlim : Lim lim d r x fr) :
    Ends lim P d mpPowers ⟨frame (consts x fr), μ⟩ (19 * mpRounds x.U + 10) fun σ' =>
      σ' = ⟨frame (consts x fr ++ [(mpRounds x.U : ℤ), 2 ^ mpRounds x.U]),
        wrote μ fr (fun i => 2 ^ i) (mpRounds x.U)⟩ := by
  light_facts hlim
  unfold mpPowers
  -- count := 0; power := 1
  light_set (0 : ℕ)
  light_set (2 ^ 0)
  -- while power ≤ 4U: mem[fr + count] := power; count := count + 1; power := power + power
  refine Ends.whileBlock (fun i σ => σ = ⟨frame (consts x fr ++ [(i : ℤ), 2 ^ i]),
    wrote μ fr (fun i => 2 ^ i) i⟩) (mpRounds x.U) (by rw [wrote_zero]; rfl) ?round ?done
  case round =>
    rintro i _ hi rfl
    have  := pow_range hpre.U_pos hi
    refine ⟨by light_side, by simp; omega, by light_side, ?_⟩
    rw [← wrote_succ]
    simp [update_frame_setLocal, pow_succ, mul_two]
  case done =>
    rintro _ rfl
    have  := lt_pow_rounds x.U
    exact ⟨by light_side, by simp; omega, rfl⟩

/-! ## A round -/

/-- The memory when t rounds remain: the lower bounds stand at c, the powers of two at fr, and below
the free pointer no cell outside c has changed. -/
structure Mem (x : MatInst) (μ : Light.Memory) (fr t : ℕ) (μ' : Light.Memory) : Prop where
  lo : Seg μ' x.c (lows x t)
  pows : ∀ i < mpRounds x.U, μ' (fr + i) = 2 ^ i
  kept : KeptBut μ μ' fr x.c (x.n * x.n)

/-- The state when t rounds remain. -/
def Inv x μ fr t (σ : State) :=
  ∃ (power unused : ℤ) (μ' : Light.Memory), σ = ⟨frame (locals x fr t power unused), μ'⟩ ∧ Mem x μ fr t μ'

private theorem Inv.loc_count {t} {σ} (hI : Inv x μ fr t σ) : σ.loc 11 = t := by
  obtain ⟨_, _, _, rfl, -⟩ := hI
  rfl

/-- The instance that the solver gets in the round for t: the two matrices, V at fr + R, and the
place for the flags behind it. -/
def pairsInst (x : MatInst) (fr t : ℕ) : PairsInst :=
  ⟨x.n, 6 * x.U, x.a, x.b, fr + mpRounds x.U, fr + mpRounds x.U + x.n * x.n, x.A, x.B, asked x t⟩

include hpre in
/-- It is an instance, once V stands at its place and the two matrices are still at theirs. -/
theorem pairsInst_pre {t} (ht : t < mpRounds x.U) {μ'}
    (sA : Seg μ' x.a x.A) (sB : Seg μ' x.b x.B) (sV : Seg μ' (fr + mpRounds x.U) (asked x t)) :
    (pairsInst x fr t).Pre μ' (fr + mpRounds x.U + x.n * x.n + x.n * x.n) :=
  have  := hpre.belowA
  have  := hpre.belowB
  have  := hpre.U_pos
  have hle : ∀ L , AbsLe L x.U → AbsLe L (6 * x.U) := fun L hL y hy =>
    (hL y hy).trans (by omega)
  { n_pos := hpre.n_pos
    U_pos := by change 1 ≤ 6 * x.U; omega
    lenX := hpre.lenA
    lenY := hpre.lenB
    lenV := length_asked x t
    segX := sA
    segY := sB
    segV := sV
    leX := hle _ hpre.leA
    leY := hle _ hpre.leB
    leV := fun y hy => by
      obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
      exact (abs_asked_le hpre ht y' hy').trans (le_of_eq rfl)
    belowX := by simp only [pairsInst]; omega
    belowY := by simp only [pairsInst]; omega
    belowV := by simp only [pairsInst]; omega
    belowOut := by simp only [pairsInst]; omega
    apartX := by simp only [pairsInst]; omega
    }

variable (C : Ctx P₀ R₀ pPairs pFill pAddc pBump T r)

include C in
/-- **One round** goes from the state with t + 1 remaining rounds to the state with t. -/
theorem round_spec  (hpre : x.Pre μ fr)
    (hlim : Lim lim d r x fr) {t} (ht : t < mpRounds x.U) {σ}
    (hI : Inv x μ fr (t + 1) σ) :
    Ends lim (P₀ ++ R₀) d (mpRound pPairs pAddc pBump) σ (roundTime T x.n x.U) (Inv x μ fr t) := by
  obtain ⟨power, unused, μ₀, rfl, hM⟩ := hI


  light_facts hlim hpre hM
  unfold mpRound roundTime
  -- count := count - 1; power := mem[fr + count]
  light_set t
  light_set (2 ^ t) using hM.pows t ht
  -- addc(n², power, c, asked): V := lo + 2^t
  light_call (addc_meets C.addc (2 ^ t) (fr + mpRounds x.U) hM.lo (length_lows x _)
    (by omega) (by omega) fun y hy => (abs_asked_le hpre ht y hy).trans (by omega))
    with _ μ₁ ⟨sV, sameAddc⟩
  -- The solver writes its flags.
  refine Ends.callToThen (T' := T x.n (6 * x.U)) (C.sol.meets R₀ (pairsInst x fr t)
    (fr + mpRounds x.U + x.n * x.n + x.n * x.n) (pairsInst_pre hpre ht
      hpre.segA.keep hpre.segB.keep sV)
    ⟨hlim.solver, by ram_arith [pairsTask, pairsInst], hlim.space,
      by ram_arith [pairsTask, pairsInst]⟩) ?_ (by simp [pairsTask, pairsInst])
  rintro _ μ₂ ⟨sF, keptSolver⟩
  -- What the task promises, in terms of x: the flags, and no other change below the solver's free
  -- pointer.
  replace sF : Seg μ₂ (fr + mpRounds x.U + x.n * x.n) (flags x t) := sF
  replace keptSolver : KeptBut μ₁ μ₂ (fr + mpRounds x.U + x.n * x.n + x.n * x.n)
    (fr + mpRounds x.U + x.n * x.n) (x.n * x.n) := keptSolver
  -- bump(n², power, flags, c): lo grows by 2^t where the flag is 0
  have hpow := pow_range hpre.U_pos ht
  light_call (bump_meets C.bump (2 ^ t) sF hM.lo.keep ⟨length_flags x t, length_lows x _⟩
    (by omega) (by omega) (flags_eq_zero_or_one x t) (absLe_lows hpre _)
    ⟨by rw [abs_of_pos hpow.1]; omega, by omega⟩)
    with _ μ₃ ⟨hnew, sameBump⟩
  exact ⟨_, _, μ₃, rfl,
    { lo := lows_round hpre t ▸ hnew
      pows := fun i hi => (by light_keep : μ₃ (fr + i) = μ₀ (fr + i)).trans (hM.pows i hi)
      kept := by light_keep }⟩

include C in
/-- **The rounds** go from the state with R remaining rounds to the state with none. -/
theorem rounds_spec  (hpre : x.Pre μ fr)
    (hlim : Lim lim d r x fr) {σ} (hI : Inv x μ fr (mpRounds x.U) σ) :
    Ends lim (P₀ ++ R₀) d (.while (k 0 <' v 11) (mpRound pPairs pAddc pBump)) σ
      (mpRounds x.U * (roundTime T x.n x.U + 4) + 4) (Inv x μ fr 0) := by
  have hzero : ((0 : ℕ) : ℤ) ≤ lim.word := by have := hlim.word; omega
  refine Ends.whileConst (fun j σ => Inv x μ fr (mpRounds x.U - j) σ) (mpRounds x.U)
    (roundTime T x.n x.U) (by simpa using hI) ?round ?done
    (by ram_safe)
  case round =>
    intro j σ₂ hj hI₂
    obtain ⟨t, ht⟩ : ∃ t, mpRounds x.U - j = t + 1 := ⟨mpRounds x.U - j - 1, by omega⟩
    rw [show mpRounds x.U - (j + 1) = t by omega]
    rw [ht] at hI₂
    exact ⟨⟨hzero, trivial⟩, by simp_all [hI₂.loc_count],
      round_spec C hpre hlim (by omega) hI₂⟩
  case done =>
    intro σ₂ hI₂
    rw [Nat.sub_self] at hI₂
    exact ⟨⟨hzero, trivial⟩, by simp_all [hI₂.loc_count], hI₂⟩

end Mp

/-! ## The host -/

open Mp in
/-- **The host is correct**, in every program that begins with the solver's program and has the
three passes. -/
theorem mp_spec {P₀ R₀ } {pPairs pFill pAddc pBump } {T }
    {r } (C : Ctx P₀ R₀ pPairs pFill pAddc pBump T r) {lim } {d }
    {x } {μ } {fr } (hpre : x.Pre μ fr) (hok : (mpNeed r x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R₀) d (mpBody pPairs pFill pAddc pBump)
      ⟨frame (mpTask.args x ++ [(fr : ℤ)]), μ⟩ (mpTime T x.n x.U)
      fun σ' => mpTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hlim := lim_of_ok hok

  light_facts hlim hpre

  -- For the comparisons of times below: of the steps counted for each round, 24 pay for its power
  -- of two.
  have  : mpRounds x.U * (T x.n (6 * x.U) + 49 * (x.n * x.n) + 70) =
      mpRounds x.U * (roundTime T x.n x.U + 4) + 24 * mpRounds x.U := by unfold roundTime; ring
  unfold mpBody mpTime
  -- The numbers n², 2U, 4U, −2U, 6U, and the powers of two.
  light_piece (consts_spec hpre hlim) with _ rfl
  light_piece (powers_spec hpre hlim) with _ rfl
  -- asked := fr + R; flags := asked + n²; solverFree := flags + n²
  light_set (fr + mpRounds x.U : ℕ)
  light_set (fr + mpRounds x.U + x.n * x.n : ℕ)
  light_set (fr + mpRounds x.U + x.n * x.n + x.n * x.n : ℕ)
  -- fill(c, n², −2U): the first lower bounds
  light_call (fill_meets C.fill (dst := x.c) (n := x.n * x.n) (x := -2 * (x.U : ℤ)) hlim.space
    (by omega)) with _ μ₁ ⟨sLo, sameFill⟩
  -- The rounds.
  refine (rounds_spec C hpre hlim ⟨_, _, μ₁, rfl,
    { lo := lows_top hpre ▸ sLo
      pows := fun i hi => (sameFill _ (by omega)).trans (wrote_done hi)
      kept := by light_keep }⟩).mono ?_ ?_
  · light_time
  · rintro _ ⟨_, _, μ', rfl, hM⟩
    exact ⟨lows_zero hpre ▸ hM.lo, hM.kept⟩

/-- The need of the host is polynomially bounded if the need of the solver is. -/
theorem polyNeed_mpNeed {r} (hr : PolyNeed r) : PolyNeed (mpNeed r) := by
  unfold mpNeed mpRounds
  poly_need [hr.word, hr.cells, hr.depth]

/-- **The (min,+)-product from "all pairs"**, as a host. -/
theorem isHost_mp : IsHost pairsTask mpTask mpTime mpNeed := by
  refine ⟨fun P p T r hs => ?_, fun r hr => polyNeed_mpNeed hr⟩
  refine ⟨[fillBody, addcBody, bumpBody, mpBody p P.length (P.length + 1) (P.length + 2)],
    P.length + 3, mpBody p P.length (P.length + 1) (P.length + 2), by simp,
    fun R lim d x μ fr hpre hok => ?_⟩
  rw [List.append_assoc]
  exact mp_spec ⟨hs, by simp, by simp, by simp⟩ hpre hok

end Light.Sec3
