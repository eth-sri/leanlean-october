/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Lib.Sieve
import ThreeSumApsp.Lang.Lib.Sqrt
import ThreeSumApsp.Programs.Tasks
import ThreeSumApsp.Spec.Sec3.Theorem17.Hashing

/-!
# The primes of the window (proof of Theorem 17)

The hashing of the proof of Theorem 17 uses "a prime p ∈ [√D/2, √D)".  primes(dst, D) lists these
primes in increasing order and returns their number (`primes_spec`).

* It computes s = ⌊√D⌋ and calls the sieve of Eratosthenes, which writes all primes up to s to dst.
  The sieve gets the s + 1 cells behind these s cells for its table.
* One pass keeps the primes p with D ≤ 4p² and p² < D and moves them to the front (`pass_spec`, with
  the round `keep_spec`).  What it keeps is the list of the window (`filter_primesBelow`).
-/


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
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact ((List.pairwise_le_range).filter _).filter _
  · exact List.pairwise_le_range.filter _
  · refine (List.perm_ext_iff_of_nodup ((List.nodup_range.filter _).filter _)
      (List.nodup_range.filter _)).2 fun q => ?_
    refine Iff.trans ?_ (Spec.mem_primesList (D := D) (q := q)).symm
    grind [Nat.lt_succ_of_le, Nat.le_sqrt]

theorem mul_self_le_of_mem_primesBelow {D p : ℕ} (hp : p ∈ Sieve.primesBelow (Nat.sqrt D + 1)) :
    p * p ≤ D :=
  Nat.le_sqrt.1 (Nat.lt_succ_iff.1 (List.mem_range.1 (List.mem_filter.1 hp).1))

/-- There are at most s - 1 primes up to s. -/
theorem length_primesBelow_succ_le (s : ℕ) : (Sieve.primesBelow (s + 1)).length ≤ s - 1 := by
  rcases s.eq_zero_or_pos with rfl | hpos
  · rfl
  · have := Sieve.length_primesBelow_add_two_le (i := s + 1) (by omega)
    omega

theorem inWindow_take_succ_of_mem {D j : ℕ} {L : List ℕ} (hj : j < L.length) (h : InWindow D L[j]) :
    inWindow D (L.take (j + 1)) = inWindow D (L.take j) ++ [L[j]] := by
  grind [List.take_succ_eq_append_getElem, List.filter_cons_of_pos]

theorem inWindow_take_succ_of_not_mem {D j : ℕ} {L : List ℕ} (hj : j < L.length)
    (h : ¬ InWindow D L[j]) : inWindow D (L.take (j + 1)) = inWindow D (L.take j) := by
  grind [List.take_succ_eq_append_getElem, List.filter_cons_of_neg]

/-! ## The program -/

namespace Primes

/- The local variables of primes: the arguments dst and D; s = ⌊√D⌋; the number of primes up to s;
the number j of those that have been looked at; the prime p that is looked at and its square; the
number cnt of primes that have been kept. -/
slots Dest Size Root Total Index Prime Square Count

end Primes

open Primes

/-- The prime number j of the list is kept if it lies in the window. -/
def primesKeep : Stmt :=
  .set Prime (M (v Dest +' v Index)) ;;
  .set Square (v Prime *' v Prime) ;;
  .set Index (v Index +' k 1) ;;
  .ite (v Size ≤' k 4 *' v Square)
    (.ite (v Square <' v Size)
      (.store (v Dest +' v Count) (v Prime) ;; .set Count (v Count +' k 1))
      .skip)
    .skip

/-- The pass over the primes up to s; the result is the number of primes that are kept. -/
def primesPass : Stmt :=
  .set Count (k 0) ;;
  .set Index (k 0) ;;
  .while (v Index <' v Total) primesKeep ;;
  .set 0 (v Count)

/-- primes(dst, D), with the numbers of the procedure sqrt and of the sieve. -/
def primesBody (pSqrt pSieve : ℕ) : Stmt :=
  .call pSqrt [v Size] Root ;;
  .call pSieve [v Root, v Dest, v Dest +' v Root] Total ;;
  primesPass

/-- The number of steps of primes(dst, D). -/
def tPrimes (D : ℕ) : ℕ := 80 * (Nat.sqrt D ^ 3 + 1)

namespace Primes

variable {μ : ℕ → ℤ} {dst D s : ℕ} {L : List ℕ}

/-- The first j primes of the list L have been looked at: those in the window stand at the front of
dst, the primes from number j on are still in their places, and no cell outside the list has
changed. -/
def Sifted (μ : ℕ → ℤ) (dst D s : ℕ) (L : List ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (p q : ℤ),
    σ = ⟨frame [dst, D, s, L.length, j, p, q, (inWindow D (L.take j)).length], μ'⟩ ∧
    SegN μ' dst (inWindow D (L.take j)) ∧ SegN μ' (dst + j) (L.drop j) ∧
    SameOutside μ μ' dst L.length

/-- One round of the pass. -/
theorem keep_spec {j : ℕ} {σ : State} (hw : (lim.space : ℤ) ≤ lim.word)
    (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word) (hdst : dst + L.length ≤ lim.space)
    (hL : ∀ p ∈ L, p * p ≤ D) (hj : j < L.length) (h : Sifted μ dst D s L j σ) :
    Ends lim P d primesKeep σ primesKeep.blockCost (Sifted μ dst D s L (j + 1)) := by
  obtain ⟨μ', p₀, q₀, rfl, front, rest, same⟩ := h
  rw [List.drop_eq_getElem_cons hj] at rest
  obtain ⟨hread, hrest⟩ : μ' _ = (L[j] : ℕ) ∧ SegN μ' _ _ :=
    seg_cons.1 rest
  have hcnt : (inWindow D (L.take j)).length ≤ j :=
    by grind
  have hsq : L[j] * L[j] ≤ D := by exact_mod_cast by simp_all
  have htake := inWindow_take_succ_of_mem (D := D) hj
  have hpass := inWindow_take_succ_of_not_mem (D := D) hj
  unfold Sifted
  generalize L[j] = p at *
  generalize inWindow D _ = F at *
  unfold primesKeep
  -- p := dst[j]; q := p * p; j := j + 1
  refine Ends.setToThen p ?_ (by simp [Limits.Addr, abs_le]; omega)
  refine Ends.setToThen (p * p) ?_ (by simp; omega)
  apply Ends.setToThen (j + 1)
  -- if D ≤ 4 q and q < D
  refine Ends.iteLast (fun hlow => Ends.iteLast (fun hhigh => ?_) fun hnhigh => ?_) fun hnlow => ?_
  · have hin : InWindow D p :=
      ⟨by exact_mod_cast (by simp_all : D ≤ 4 * ((p : ℤ) * p)),
        by exact_mod_cast (by assumption : (p : ℤ) * p < D)⟩
    rw [htake hin]
    -- dst[cnt] := p; cnt := cnt + 1
    apply Ends.storeToThen (dst + F.length) p
    exact Ends.setTo (F.length + 1) ⟨Function.update μ' _ p, p, p * p,
      by simp, front.snoc p, hrest.update_out (by omega) _,
      same.update ⟨by omega, by omega⟩ _⟩
  · rw [hpass fun hin => hnhigh (by simpa using (by omega : (p : ℤ) * p < D))]
    exact Ends.skip ⟨μ', p, p * p, rfl, front, hrest, same⟩
  · rw [hpass fun hin => hnlow (by
      simpa [Cond.holds_le] using (by omega : D ≤ 4 * ((p : ℤ) * p)))]
    exact Ends.skip ⟨μ', p, p * p, rfl, front, hrest, same⟩

/-- The pass keeps the numbers of the list that lie in the window, and returns how many they are. -/
theorem pass_spec (hw : (lim.space : ℤ) ≤ lim.word) (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word)
    (hdst : dst + L.length ≤ lim.space) (hL : ∀ p ∈ L, p * p ≤ D) (seg : SegN μ dst L) :
    Ends lim P d primesPass ⟨frame [dst, D, s, L.length], μ⟩ (38 * L.length + 10) fun σ' =>
      σ'.loc 0 = ((inWindow D L).length : ℕ) ∧ SegN σ'.mem dst (inWindow D L) ∧
        SameOutside μ σ'.mem dst L.length := by
  -- cnt := 0; j := 0
  refine Ends.setToThen 0 (Ends.setToThen 0 ?_)
  -- while j < total
  refine Ends.next _ (Ends.whileConst (Sifted μ dst D s L) L.length primesKeep.blockCost ?_
    ?_ ?_ le_rfl) (by simp [primesKeep]; omega)
  ·
    exact ⟨μ, 0, 0, by simp, by tauto, by assumption, .refl⟩
  ·
    rintro j σ hj h
    have hrun := keep_spec (P := P) (d := d) hw hD hdst hL hj h
    obtain ⟨μ', p, q, rfl, -⟩ := h
    simp_all
  ·
    rintro _ h
    rw [Sifted, List.take_length] at h
    obtain ⟨μ', p, q, rfl, front, -, same⟩ := h
    refine ⟨by light_side, by light_side, ?_⟩
    -- the result is cnt
    exact Ends.setTo (inWindow D L).length ⟨by simp, front, same⟩ (by simp)
      (by simp [primesKeep]; omega)

/-- What primes needs of the program: the procedures sqrt and the sieve of Eratosthenes. -/
structure Ctx (P : Program) (pSqrt pSieve : ℕ) : Prop where
  hSqrt : P[pSqrt]? = some sqrtBody
  hSieve : P[pSieve]? = some sieveBody

/-- The square root, the sieve up to s, and a pass over n ≤ s - 1 primes. -/
theorem time_le {s n : ℕ} (hn : n ≤ s - 1) :
    18 * s + sieveTime s + 38 * n + 32 ≤ 80 * (s ^ 3 + 1) := by
  unfold sieveTime
  rcases s.lt_or_ge 2 with hs | hs
  · interval_cases s <;> simp at hn ⊢ <;> omega
  · have hlog : 15 * s * (Nat.log 2 s + 5) ≤ 15 * s * (s + 4) :=
      Nat.mul_le_mul_left _ (by have := Nat.log_lt_self 2 (x := s) (by omega); omega)
    have hsq : 2 * (s * s) ≤ s ^ 3 := by
      rw [pow_succ, sq, Nat.mul_comm]
      exact Nat.mul_le_mul_left _ hs
    grind

end Primes

/-- **primes** writes the primes of the window, in increasing order, to dst, and returns their
number.  Only the 2 ⌊√D⌋ + 1 cells from dst may change. -/
theorem primes_spec {μ : ℕ → ℤ} {dst D pSqrt pSieve : ℕ} (C : Primes.Ctx P pSqrt pSieve)
    (hw : (lim.space : ℤ) ≤ lim.word) (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word)
    (hdst : dst + (2 * Nat.sqrt D + 1) ≤ lim.space) (hd : d < lim.depth) :
    Ends lim P d (primesBody pSqrt pSieve) ⟨frame [dst, D], μ⟩ (tPrimes D) fun σ' =>
      σ'.loc 0 = ((primesList D).length : ℕ) ∧ SegN σ'.mem dst (primesList D) ∧
        SameOutside μ σ'.mem dst (2 * Nat.sqrt D + 1) := by
  have hsD := D.sqrt_le_self
  have hlen := length_primesBelow_succ_le (Nat.sqrt D)
  have htime := time_le hlen
  have hsqrt : Meets lim P pSqrt (d + 1) _ μ _ fun r μ' =>
      r = Nat.sqrt D ∧ μ' = μ :=
    sqrt_meets C.hSqrt μ (by omega)
  have hsieve := sieve_meets (μ := μ) (d := d + 1) (fr := dst + Nat.sqrt D) C.hSieve
    ⟨hw, by omega, le_rfl, by omega⟩
  rw [Sieve.sort_primesLE] at hsieve
  rw [← filter_primesBelow, tPrimes]
  apply Ends.callToThen hsqrt
  rintro _ μ₀ ⟨rfl, hμ₀⟩
  obtain rfl := hμ₀.symm
  -- total := sieve(s, dst, dst + s)
  apply Ends.callToThen hsieve
  rintro _ μ₁ ⟨rfl, seg, kept⟩
  -- the pass
  apply (pass_spec hw hD (by omega) (fun p => mul_self_le_of_mem_primesBelow (D := D) (p := p)) seg).mono (by light_time)
  rintro σ' ⟨hcount, front, same⟩
  exact ⟨hcount, front, kept.then same fun b hb => by omega⟩
