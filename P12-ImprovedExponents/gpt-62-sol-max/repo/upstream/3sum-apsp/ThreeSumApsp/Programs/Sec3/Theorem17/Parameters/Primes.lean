/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

public import ThreeSumApsp.Lang.Lib.Filter
public import ThreeSumApsp.Lang.Lib.Sieve
public import ThreeSumApsp.Lang.Lib.Sqrt
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Hashing

/-!
# The primes of the window (proof of Theorem 17)

The hashing of the proof of Theorem 17 uses "a prime p ∈ [√D/2, √D)".  primes(dst, D) lists these
primes in increasing order and returns their number (`primes_meets`).

* It computes s = ⌊√D⌋ and calls the sieve of Eratosthenes, which writes all primes up to s to dst.
  The sieve gets the s + 1 cells behind these s cells for its table.
* One pass keeps the primes p with D ≤ 4p² and p² < D and moves them to the front (`pass_spec`, with
  the shared filter pass).  What it keeps is the list of the window (`filter_primesBelow`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The pure side -/

/-- The number p lies in the window: √D/2 ≤ p < √D, by integer comparisons. -/
abbrev InWindow (D p : ℕ) : Prop := D ≤ 4 * (p * p) ∧ p * p < D

/-- The numbers of the list L that lie in the window. -/
abbrev inWindow (D : ℕ) (L : List ℕ) : List ℕ := L.filter fun p => InWindow D p

/-- The primes of the window are those of the primes up to ⌊√D⌋ that lie in the window. -/
theorem filter_primesBelow (D : ℕ) :
    inWindow D (Sieve.primesBelow (Nat.sqrt D + 1)) = primesList D := by
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) ?_ ?_ ?_
  · exact ((List.pairwise_le_range).filter _).filter _
  · exact (List.pairwise_le_range).filter _
  · refine (List.perm_ext_iff_of_nodup ((List.nodup_range.filter _).filter _)
      (List.nodup_range.filter _)).2 fun q => ?_
    refine Iff.trans ?_ (Spec.mem_primesList (D := D) (q := q)).symm
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, sq]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨Nat.lt_succ_of_le (Nat.le_sqrt.2 h.2.2.le), h.1⟩, h.2⟩⟩

theorem mul_self_le_of_mem_primesBelow {D p : ℕ} (hp : p ∈ Sieve.primesBelow (Nat.sqrt D + 1)) :
    p * p ≤ D :=
  Nat.le_sqrt.1 (Nat.lt_succ_iff.1 (List.mem_range.1 (List.mem_filter.1 hp).1))

/-- There are at most s - 1 primes up to s. -/
theorem length_primesBelow_succ_le (s : ℕ) : (Sieve.primesBelow (s + 1)).length ≤ s - 1 := by
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · rfl
  · have := Sieve.length_primesBelow_add_two_le (i := s + 1) (by omega)
    omega

/-! ## The program -/

namespace Primes

registers [Dest, Size, Root, Total, Index, Count]

abbrev readPrime : Expr := M (v Dest +' v Index)

def test : Guard :=
  let sq := readPrime *' readPrime
  .both (.atom (v Size ≤' k 4 *' sq)) (.atom (sq <' v Size))

end Primes

open Primes

def primesPass : Stmt := filterPass Index Total Dest Count test readPrime ;; .set 0 (v Count)

/-- primes(dst, D), with the numbers of the procedure sqrt and of the sieve. -/
def primesBody (pSqrt pSieve : ℕ) : Stmt :=
  .call pSqrt [v Size] Root ;;
  .call pSieve [v Root, v Dest, v Dest +' v Root] Total ;;
  primesPass

/-- The number of steps of primes(dst, D). -/
def tPrimes (D : ℕ) : ℕ := 80 * (Nat.sqrt D ^ 3 + 1)

namespace Primes

variable {μ : ℕ → ℤ} {dst D s : ℕ} {L : List ℕ}

theorem pass_spec (hw : (lim.space : ℤ) ≤ lim.word) (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word)
    (hdst : dst + L.length ≤ lim.space) (hL : ∀ p ∈ L, p * p ≤ D) (seg : SegN μ dst L) :
    Ends lim P d primesPass ⟨frame [dst, D, s, L.length], μ⟩ (50 * L.length + 10) fun σ =>
      σ.loc 0 = ((inWindow D L).length : ℕ) ∧ SegN σ.mem dst (inWindow D L) ∧
        SameOutside μ σ.mem dst L.length := by
  unfold primesPass
  refine Ends.next _ (Ends.filterPass _ _ (fun j F => F = (inWindow D (L.take j)).map Nat.cast)
    rfl ?_ ?_ hw hdst rfl rfl (hT := le_rfl)) (by light_time [filterStep, test])
  · intro j F ν hj hF H
    have hle := H.size
    have hp := hL _ (List.getElem_mem hj)
    have hread := (H.same (dst + j) (Or.inr (by omega))).trans (seg.getElem hj)
    have htest : InWindow D L[j] ↔ (D : ℤ) ≤ 4 * ((L[j] : ℤ) * L[j]) ∧ (L[j] : ℤ) * L[j] < D := by exact_mod_cast Iff.rfl
    refine ⟨by light_side [test, hread], by light_side, ?_, ?_⟩ <;> intro h
    · have hkeep := htest.mpr (by simpa [test, hread, Cond.holds_le] using h)
      have he : readPrime.val (filterState (frame [dst, D, s, L.length]) Index Count j F ν) = L[j] := by
        simpa using hread
      rw [he, hF, List.take_succ_eq_append_getElem hj]
      unfold inWindow
      rw [List.filter_append, List.filter_singleton, decide_eq_true hkeep, List.map_append]
      rfl
    · have hskip : ¬ InWindow D L[j] := fun hh => h (by simpa [test, hread, Cond.holds_le] using htest.mp hh)
      rw [hF, List.take_succ_eq_append_getElem hj]
      unfold inWindow
      rw [List.filter_append, List.filter_singleton, decide_eq_false hskip]
      simp only [Bool.cond_false, List.append_nil]
  · intro F ν hF H
    rw [List.take_length] at hF
    subst F
    refine Ends.setLast ⟨by simp, H.seg, H.same.mono le_rfl (Nat.add_le_add_left H.size _)⟩
      (hT := by light_time [filterStep, test])

/-- What primes needs of the program: the procedures sqrt and the sieve of Eratosthenes. -/
structure Ctx (P : Program) (pSqrt pSieve : ℕ) : Prop where
  hSqrt : P[pSqrt]? = some sqrtBody
  hSieve : P[pSieve]? = some sieveBody

/-- The square root, the sieve up to s, and a pass over n ≤ s - 1 primes. -/
theorem time_le {s n : ℕ} (hn : n ≤ s - 1) :
    18 * s + sieveTime s + 50 * n + 32 ≤ 80 * (s ^ 3 + 1) := by
  unfold sieveTime
  rcases Nat.lt_or_ge s 2 with hs | hs
  · interval_cases s <;> simp at hn ⊢ <;> omega
  · have hlog : 15 * s * (Nat.log 2 s + 5) ≤ 15 * s * (s + 4) :=
      Nat.mul_le_mul_left _ (by have := Nat.log_lt_self 2 (x := s) (by omega); omega)
    have hsq : 2 * (s * s) ≤ s ^ 3 := by
      nlinarith
    lia

end Primes

/-- **primes** writes the primes of the window, in increasing order, to dst, and returns their
number.  Only the 2 ⌊√D⌋ + 1 cells from dst may change. -/
theorem primes_meets {μ : ℕ → ℤ} {D : ℕ} {q dst pSqrt pSieve : ℕ} (hP : P[q]? = some (primesBody pSqrt pSieve))
    (C : Primes.Ctx P pSqrt pSieve) (hw : (lim.space : ℤ) ≤ lim.word)
    (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word) (hdst : dst + (2 * Nat.sqrt D + 1) ≤ lim.space)
    (hd : d < lim.depth) :
    Meets lim P q d [dst, D] μ (tPrimes D) fun r μ' =>
      r = ((primesList D).length : ℕ) ∧ SegN μ' dst (primesList D) ∧
        SameOutside μ μ' dst (2 * Nat.sqrt D + 1) := by
  refine .of_body hP ?_;
  have hsD : Nat.sqrt D ≤ D := Nat.sqrt_le_self D
  have hL := fun p => mul_self_le_of_mem_primesBelow (D := D) (p := p)
  have hlen := length_primesBelow_succ_le (Nat.sqrt D)
  have htime := time_le hlen
  have hsqrt : Meets lim P pSqrt (d + 1) [D] μ (18 * Nat.sqrt D + 12) fun r μ' =>
      r = Nat.sqrt D ∧ μ' = μ :=
    sqrt_meets C.hSqrt μ (by omega)
  have hsieve := sieve_meets (μ := μ) (d := d + 1) (out := dst) (fr := dst + Nat.sqrt D) C.hSieve
    ⟨hw, by omega, le_rfl, by omega⟩
  rw [Sieve.sort_primesLE, ← Sieve.length_primesBelow] at hsieve
  rw [← filter_primesBelow D, tPrimes]
  generalize Sieve.primesBelow (Nat.sqrt D + 1) = L at *
  generalize Nat.sqrt D = s at *
  -- s := sqrt(D)
  refine Ends.callToThen hsqrt ?_
  rintro _ μ₀ ⟨rfl, hμ₀⟩
  obtain rfl : μ = μ₀ := hμ₀.symm
  -- total := sieve(s, dst, dst + s)
  refine Ends.callToThen hsieve ?_
  rintro _ μ₁ ⟨rfl, seg, kept⟩
  -- the pass
  refine (pass_spec hw hD (by omega) hL seg).mono (by light_time) ?_
  rintro σ' ⟨hcount, front, same⟩
  exact ⟨hcount, front, kept.then same fun b hb => ⟨⟨by omega, by omega⟩, by omega⟩⟩

end Light.Sec3
