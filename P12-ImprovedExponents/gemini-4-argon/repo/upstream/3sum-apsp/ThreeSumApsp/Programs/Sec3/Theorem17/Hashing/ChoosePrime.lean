module

public import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters
public import ThreeSumApsp.Spec.Sec3.Theorem17.Strassen
public import Mathlib.Data.List.MinMax
public import ThreeSumApsp.Lang.Lib.Sieve
public import ThreeSumApsp.Lang.Lib.Sqrt
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Hashing
public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.CountPrime

@[expose] public section

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The prime that is chosen (proof of Theorem 17)

`chosenPrime n D AB BC AC` is the first prime of the window `√D/2 ≤ p < √D` at which the count,
computed with Strassen's algorithm from the three lists of weights, is smallest.  Here
`triOf n AB BC AC` is the instance of Exact Triangle whose weights are read from the three lists:
`w(a,b)` at `a n + b` of `AB`, `w(b,c)` at `b n + c` of `BC`, `w(a,c)` at `a n + c` of `AC`.

* The computed count is the count of the proof of Theorem 17 at every prime of the window
  (`countOf_eq`), so the chosen prime is a selected prime in the sense of the proof of Theorem 17,
  "We select the prime with the smallest count" (`chosenPrime_isSelected`).  It lies between 2 and
  `⌊√D⌋` (`two_le_chosenPrime`, `chosenPrime_le_sqrt`).
* A program finds it in one pass over the primes: `bestOf f L i` is the best of the first `i`
  elements of a list (`bestOf_one`, `bestOf_succ`, `bestOf_length`).
* The paper bounds the weights by `n^ν`; a program has a bound `U`.  `kappaOf n U` is the least
  exponent `κ ≥ 1` with `U ≤ n^κ`, and with it the bound of the proof of Theorem 17 on the number
  `F(p)` of false positives, that is, of triples with `S(a,b,c) ≠ 0` and `p ∣ S(a,b,c)`, holds for
  the chosen prime (`F_chosenPrime_le`).
-/


namespace ThreeSumApsp.Spec

/-! ## The chosen prime -/

/-- "We select the prime with the smallest count" (the first such prime; 0 if the window has no
prime). -/
def chosenPrime (n D : ℕ) (AB BC AC : List ℤ) : ℕ :=
  ((primesList D).argmin fun p => (countOf n p AB BC AC).toNat).getD 0

section Chosen

variable {n D : ℕ} (AB BC AC : List ℤ)

/-- **The chosen prime is a selected prime** (proof of Theorem 17: "We select the prime with the
smallest count"). -/
theorem chosenPrime_isSelected (hD : 16 ≤ D) :
    (triOf n AB BC AC).IsSelectedPrime D (chosenPrime n D AB BC AC) := by
  -- The window has a prime `p₀`, so `List.argmin` returns `some m`, and the default 0 of
  -- `chosenPrime` is never used.
  obtain ⟨p₀, hp₀, -⟩ := TriangleInstance.exists_isSelectedPrime (triOf n AB BC AC) D hD
  rw [primesInRange_eq, List.mem_toFinset] at hp₀
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1
    (mt (List.argmin_eq_none (f := fun p => (countOf n p AB BC AC).toNat)).1
      (List.ne_nil_of_mem hp₀))
  -- The computed count is the count of the proof of Theorem 17 at every prime of the window.
  have hcount : ∀ q ∈ primesList D,
      (triOf n AB BC AC).countZeroMod q = (countOf n q AB BC AC).toNat := fun q hq => by
    rw [countOf_eq n AB BC AC (mem_primesList.1 hq).1.ne_zero, Int.toNat_natCast]
  rw [chosenPrime, hm, Option.getD_some, TriangleInstance.IsSelectedPrime, primesInRange_eq]
  refine ⟨List.mem_toFinset.2 (List.argmin_mem hm), fun q hq => ?_⟩
  rw [hcount m (List.argmin_mem hm), hcount q (List.mem_toFinset.1 hq)]
  exact List.le_of_mem_argmin (f := fun p => (countOf n p AB BC AC).toNat)
    (List.mem_toFinset.1 hq) hm

/-- The chosen prime is a prime of the window. -/
theorem chosenPrime_mem (hD : 16 ≤ D) : chosenPrime n D AB BC AC ∈ primesInRange D :=
  (chosenPrime_isSelected AB BC AC hD).1

/-- The chosen number is in the list of the primes of the window. -/
theorem chosenPrime_mem_primesList (hD : 16 ≤ D) :
    chosenPrime n D AB BC AC ∈ primesList D := by
  have hmem := chosenPrime_mem (n := n) AB BC AC hD
  rwa [primesInRange_eq, List.mem_toFinset] at hmem

/-- The chosen prime is at least 2. -/
theorem two_le_chosenPrime (hD : 16 ≤ D) : 2 ≤ chosenPrime n D AB BC AC :=
  (mem_primesList.1 (chosenPrime_mem_primesList AB BC AC hD)).1.two_le

/-- The chosen prime is at most `⌊√D⌋`. -/
theorem chosenPrime_le_sqrt (hD : 16 ≤ D) : chosenPrime n D AB BC AC ≤ Nat.sqrt D :=
  le_sqrt_of_mem_primesList (chosenPrime_mem_primesList AB BC AC hD)

end Chosen

/-! ## The smallest count, by one pass -/

/-- The first of the first `i` elements of a list at which `f` is smallest; 0 for `i = 0`. -/
def bestOf (f : ℕ → ℕ) (L : List ℕ) (i : ℕ) : ℕ := ((L.take i).argmin f).getD 0

/-- The first element is the best of one. -/
theorem bestOf_one (f : ℕ → ℕ) (L : List ℕ) : bestOf f L 1 = L.getD 0 0 := by
  cases L <;> simp [bestOf]

/-- One more element: it is the best so far exactly if `f` is smaller there. -/
theorem bestOf_succ (f : ℕ → ℕ) (L : List ℕ) {i : ℕ} (hi : 1 ≤ i) (hiL : i < L.length) :
    bestOf f L (i + 1) = if f L[i] < f (bestOf f L i) then L[i] else bestOf f L i := by
  rw [bestOf, bestOf, List.take_succ_eq_append_getElem hiL, List.argmin_concat]
  cases h : (L.take i).argmin f with
  | none => exact absurd (List.argmin_eq_none.1 h) (List.ne_nil_of_length_pos (by simp; omega))
  | some c => simp only [Option.getD_some]; split_ifs <;> rfl

/-- The best of all the elements is what `List.argmin` returns. -/
theorem bestOf_length (f : ℕ → ℕ) (L : List ℕ) : (L.argmin f).getD 0 = bestOf f L L.length := by
  rw [bestOf, List.take_length]

/-! ## False positives, in terms of a bound on the weights -/

/-- The least exponent `κ ≥ 1` with `U ≤ n^κ`. -/
noncomputable def kappaOf (n U : ℕ) : ℝ := max 1 (Real.log U / Real.log n)

/-- The exponent is at least 1. -/
theorem one_le_kappaOf (n U : ℕ) : 1 ≤ kappaOf n U := le_max_left _ _

/-- `U ≤ n^κ` for this exponent. -/
theorem le_rpow_kappaOf {n U : ℕ} (hn : 2 ≤ n) (hU : 1 ≤ U) :
    (U : ℝ) ≤ (n : ℝ) ^ kappaOf n U := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hU0 : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  calc (U : ℝ) = (n : ℝ) ^ Real.logb n U := (Real.rpow_logb (by linarith) hn1.ne' hU0).symm
    _ ≤ (n : ℝ) ^ kappaOf n U := Real.rpow_le_rpow_of_exponent_le hn1.le (le_max_right _ _)

/-- It is the least such exponent. -/
theorem kappaOf_le {n U : ℕ} (hn : 2 ≤ n) (hU : 1 ≤ U) {κ' : ℝ} (h1 : 1 ≤ κ')
    (h : (U : ℝ) ≤ (n : ℝ) ^ κ') : kappaOf n U ≤ κ' := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hU0 : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  refine max_le h1 ?_
  rw [div_le_iff₀ (Real.log_pos hn1), ← Real.log_rpow (by linarith)]
  exact Real.log_le_log hU0 h

/-- Weights of absolute value at most `U` are at most `n^κ`. -/
theorem weightsPolyBounded_kappaOf {n U : ℕ} (hn : 2 ≤ n) (hU : 1 ≤ U) {AB BC AC : List ℤ}
    (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U) :
    (triOf n AB BC AC).WeightsPolyBounded (kappaOf n U) := by
  have key : ∀ l : List ℤ, AbsLe l U → ∀ i,
      ((|l.getD i 0| : ℤ) : ℝ) ≤ (n : ℝ) ^ kappaOf n U := fun l hl i =>
    le_trans (by exact_mod_cast AbsLe.abs_getD_le (Int.natCast_nonneg U) hl i)
      (le_rpow_kappaOf hn hU)
  exact ⟨fun a b => key AB hAB _, fun b c => key BC hBC _, fun a c => key AC hAC _⟩

/-- **The number of false positives of the chosen prime** (proof of Theorem 17:
"F(p) = O(n³ log(3n^ν)/√D) = O(ν n³ log n/√D)"), with the constant `Hashing.falsePositiveConst`. -/
theorem F_chosenPrime_le {n D U : ℕ} (hD : 16 ≤ D) (hDn : D ≤ n) (hU : 1 ≤ U) {AB BC AC : List ℤ}
    (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U) :
    ((triOf n AB BC AC).F (chosenPrime n D AB BC AC) : ℝ) ≤
      Hashing.falsePositiveConst * (kappaOf n U * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D) :=
  Hashing.F_le_falsePositiveConst_mul hD hDn (one_le_kappaOf n U) _
    (weightsPolyBounded_kappaOf (by omega) hU hAB hBC hAC) (chosenPrime_isSelected AB BC AC hD)

end ThreeSumApsp.Spec

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


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
  · simp [Sieve.primesBelow_one]
  · have := Sieve.length_primesBelow_add_two_le (i := s + 1) (by omega)
    omega

theorem inWindow_take_succ_of_mem {D j : ℕ} {L : List ℕ} (hj : j < L.length) (h : InWindow D L[j]) :
    inWindow D (L.take (j + 1)) = inWindow D (L.take j) ++ [L[j]] := by
  unfold inWindow
  rw [List.take_succ_eq_append_getElem hj, List.filter_append,
    List.filter_cons_of_pos (by simpa using h), List.filter_nil]

theorem inWindow_take_succ_of_not_mem {D j : ℕ} {L : List ℕ} (hj : j < L.length)
    (h : ¬ InWindow D L[j]) : inWindow D (L.take (j + 1)) = inWindow D (L.take j) := by
  unfold inWindow
  rw [List.take_succ_eq_append_getElem hj, List.filter_append,
    List.filter_cons_of_neg (by simpa using h), List.filter_nil, List.append_nil]

/-! ## The program -/

namespace Primes

/-- The local variables of primes: the arguments dst and D; s = ⌊√D⌋; the number of primes up to s;
the number j of those that have been looked at; the prime p that is looked at and its square; the
number cnt of primes that have been kept. -/
abbrev Dest : ℕ := 0
@[inherit_doc Dest] abbrev Size : ℕ := 1
@[inherit_doc Dest] abbrev Root : ℕ := 2
@[inherit_doc Dest] abbrev Total : ℕ := 3
@[inherit_doc Dest] abbrev Index : ℕ := 4
@[inherit_doc Dest] abbrev Prime : ℕ := 5
@[inherit_doc Dest] abbrev Square : ℕ := 6
@[inherit_doc Dest] abbrev Count : ℕ := 7

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
  obtain ⟨hread, hrest⟩ : μ' (dst + j) = (L[j] : ℕ) ∧ SegN μ' (dst + (j + 1)) (L.drop (j + 1)) :=
    seg_cons.1 rest
  have hcnt : (inWindow D (L.take j)).length ≤ j :=
    (List.length_filter_le _ _).trans (List.length_take_le _ _)
  have hsq : ((L[j] : ℕ) : ℤ) * (L[j] : ℕ) ≤ D := by exact_mod_cast hL _ (List.getElem_mem hj)
  have hsq0 : (0 : ℤ) ≤ ((L[j] : ℕ) : ℤ) * (L[j] : ℕ) := by positivity
  have hle : L[j] ≤ D := (Nat.le_mul_self _).trans (hL _ (List.getElem_mem hj))
  have htake := inWindow_take_succ_of_mem (D := D) hj
  have hpass := inWindow_take_succ_of_not_mem (D := D) hj
  unfold Sifted
  generalize L[j] = p at *
  generalize inWindow D (L.take j) = F at *
  push_cast at hD
  unfold primesKeep
  -- p := dst[j]; q := p * p; j := j + 1
  refine Ends.setToThen (p : ℕ) ?_ (by simp [Limits.Addr, abs_le, hread]; omega)
  refine Ends.setToThen (p * p : ℕ) ?_ (by simp [abs_le, -abs_mul]; omega)
  refine Ends.setToThen (j + 1 : ℕ) ?_
  -- if D ≤ 4 q and q < D
  refine Ends.iteLast (fun hlow => Ends.iteLast (fun hhigh => ?_) fun hnhigh => ?_) fun hnlow => ?_
  · have hin : InWindow D p :=
      ⟨by exact_mod_cast (by simpa [Int.lt_add_one_iff] using hlow : (D : ℤ) ≤ 4 * ((p : ℤ) * p)),
        by exact_mod_cast (by simpa using hhigh : (p : ℤ) * p < D)⟩
    rw [htake hin]
    -- dst[cnt] := p; cnt := cnt + 1
    refine Ends.storeToThen (dst + F.length) p ?_
    exact Ends.setTo (F.length + 1 : ℕ) ⟨Function.update μ' (dst + F.length) p, p, (p * p : ℕ),
      by simp, front.snoc p, hrest.update_out (Or.inl (by omega)) _,
      same.update ⟨by omega, by omega⟩ _⟩
  · rw [hpass fun hin => hnhigh (by simpa using (by exact_mod_cast hin.2 : (p : ℤ) * p < D))]
    exact Ends.skip ⟨μ', p, (p * p : ℕ), rfl, front, hrest, same⟩
  · rw [hpass fun hin => hnlow (by
      simpa [Int.lt_add_one_iff] using (by exact_mod_cast hin.1 : (D : ℤ) ≤ 4 * ((p : ℤ) * p)))]
    exact Ends.skip ⟨μ', p, (p * p : ℕ), rfl, front, hrest, same⟩

/-- The pass keeps the numbers of the list that lie in the window, and returns how many they are. -/
theorem pass_spec (hw : (lim.space : ℤ) ≤ lim.word) (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word)
    (hdst : dst + L.length ≤ lim.space) (hL : ∀ p ∈ L, p * p ≤ D) (seg : SegN μ dst L) :
    Ends lim P d primesPass ⟨frame [dst, D, s, L.length], μ⟩ (38 * L.length + 10) fun σ' =>
      σ'.loc 0 = ((inWindow D L).length : ℕ) ∧ SegN σ'.mem dst (inWindow D L) ∧
        SameOutside μ σ'.mem dst L.length := by
  -- cnt := 0; j := 0
  refine Ends.setToThen (0 : ℕ) (Ends.setToThen (0 : ℕ) ?_)
  -- while j < total
  refine Ends.next _ (Ends.whileConst (Sifted μ dst D s L) L.length primesKeep.blockCost ?start
    ?round ?done le_rfl) (by simp [primesKeep]; omega)
  case start =>
    exact ⟨μ, 0, 0, by simp, by rw [List.take_zero]; exact Seg.nil, by simpa using seg, .refl⟩
  case round =>
    rintro j σ hj h
    have hrun := keep_spec (P := P) (d := d) hw hD hdst hL hj h
    obtain ⟨μ', p, q, rfl, -⟩ := h
    exact ⟨by light_side, by light_side, hrun⟩
  case done =>
    rintro _ h
    rw [Sifted, List.take_length] at h
    obtain ⟨μ', p, q, rfl, front, -, same⟩ := h
    refine ⟨by light_side, by light_side, ?_⟩
    -- the result is cnt
    exact Ends.setTo ((inWindow D L).length : ℕ) ⟨by simp, front, same⟩ (by simp)
      (by simp [primesKeep]; omega)

/-- What primes needs of the program: the procedures sqrt and the sieve of Eratosthenes. -/
structure Ctx (P : Program) (pSqrt pSieve : ℕ) : Prop where
  hSqrt : P[pSqrt]? = some sqrtBody
  hSieve : P[pSieve]? = some sieveBody

/-- The square root, the sieve up to s, and a pass over n ≤ s - 1 primes. -/
theorem time_le {s n : ℕ} (hn : n ≤ s - 1) :
    18 * s + sieveTime s + 38 * n + 32 ≤ 80 * (s ^ 3 + 1) := by
  unfold sieveTime
  rcases Nat.lt_or_ge s 2 with hs | hs
  · interval_cases s <;> simp at hn ⊢ <;> omega
  · have hlog : 15 * s * (Nat.log 2 s + 5) ≤ 15 * s * (s + 4) :=
      Nat.mul_le_mul_left _ (by have := Nat.log_lt_self 2 (x := s) (by omega); omega)
    have : 2 * (s * s) ≤ s ^ 3 := by
      rw [pow_succ, sq, Nat.mul_comm]
      exact Nat.mul_le_mul_left _ hs
    have : 2 * s ≤ s * s := Nat.mul_le_mul_right _ hs
    have : 15 * s * (s + 4) = 15 * (s * s) + 60 * s := by ring
    omega

end Primes

/-- **primes** writes the primes of the window, in increasing order, to dst, and returns their
number.  Only the 2 ⌊√D⌋ + 1 cells from dst may change. -/
theorem primes_spec {μ : ℕ → ℤ} {dst D pSqrt pSieve : ℕ} (C : Primes.Ctx P pSqrt pSieve)
    (hw : (lim.space : ℤ) ≤ lim.word) (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word)
    (hdst : dst + (2 * Nat.sqrt D + 1) ≤ lim.space) (hd : d < lim.depth) :
    Ends lim P d (primesBody pSqrt pSieve) ⟨frame [dst, D], μ⟩ (tPrimes D) fun σ' =>
      σ'.loc 0 = ((primesList D).length : ℕ) ∧ SegN σ'.mem dst (primesList D) ∧
        SameOutside μ σ'.mem dst (2 * Nat.sqrt D + 1) := by
  have : Nat.sqrt D ≤ D := Nat.sqrt_le_self D
  have hL := fun p => mul_self_le_of_mem_primesBelow (D := D) (p := p)
  have hlen := length_primesBelow_succ_le (Nat.sqrt D)
  have := time_le hlen
  have hsqrt : Meets lim P pSqrt (d + 1) [D] μ (18 * Nat.sqrt D + 12) fun r μ' =>
      r = Nat.sqrt D ∧ μ' = μ :=
    sqrt_meets C.hSqrt μ (by push_cast at hD ⊢; omega)
  have hsieve := sieve_meets (μ := μ) (d := d + 1) (out := dst) (fr := dst + Nat.sqrt D) C.hSieve
    ⟨hw, by push_cast at hD ⊢; omega, le_rfl, by omega⟩
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

end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The choice of the prime (proof of Theorem 17, "Hashing modulo a prime")

"We reduce the weights modulo a prime p ∈ [√D/2, √D), chosen deterministically. […] For every prime
p in the range we count the triples with S(a,b,c) ≡ 0 (mod p). […] We select the prime with the
smallest count".  Here S(a,b,c) is the weight of the triangle, the sum of its entries in the three
lists of weights ab, bc and ac, and D is the parameter of Theorem 17.

choosePrime(n, U, ab, bc, ac, D, w), where w is the address of the work area, lists the primes of
the range (`primesList D`) at w, computes the number len of binary digits of U and the numbers
K = ⌈log₂ n⌉ and 2^K (`chLevel_spec`), and goes through the primes once.  A round counts for one
prime, by a call of countPrime with the work area behind the list of the primes, and keeps the prime
if it is the first one or its count is smaller than the best so far (`chKeep_spec`,
`chRound_spec`).

On the pure side, `bestOf f L i` is the first of the first i primes with the smallest count, one
more prime changes it as the program does (`BestSoFar.step`), and at the end it is the chosen prime
(`bestOf_length`).  `choosePrime_spec` is the whole routine.
-/


namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

/-- The numbers of the procedures that choosePrime calls. -/
structure ChNums : Type where
  pPrimes : ℕ
  pBitLen : ℕ
  pCountPrime : ℕ
  cp : CpNums
  pSqrt : ℕ
  pSieve : ℕ

/-- The program holds the procedures that choosePrime calls. -/
structure ChCtx (P : Program) (ν : ChNums) : Prop where
  hPrimes : P[ν.pPrimes]? = some (primesBody ν.pSqrt ν.pSieve)
  hBitLen : P[ν.pBitLen]? = some bitLenBody
  hCountPrime : P[ν.pCountPrime]? = some (countPrimeBody ν.cp)
  cp : CpCtx P ν.cp
  primes : Primes.Ctx P ν.pSqrt ν.pSieve

namespace ChoosePrime

/-- The local variables of choosePrime: the arguments n, U, ab, bc, ac, D, w; the number of primes;
len; K; 2^K; the address of the work area of countPrime; the number of the prime; the prime; its
count; the best prime so far; its count. -/
abbrev Num : ℕ := 0
@[inherit_doc Num] abbrev Bound : ℕ := 1
@[inherit_doc Num] abbrev ListAB : ℕ := 2
@[inherit_doc Num] abbrev ListBC : ℕ := 3
@[inherit_doc Num] abbrev ListAC : ℕ := 4
@[inherit_doc Num] abbrev Range : ℕ := 5
@[inherit_doc Num] abbrev Work : ℕ := 6
@[inherit_doc Num] abbrev Primes : ℕ := 7
@[inherit_doc Num] abbrev Len : ℕ := 8
@[inherit_doc Num] abbrev Level : ℕ := 9
@[inherit_doc Num] abbrev Rows : ℕ := 10
@[inherit_doc Num] abbrev Area : ℕ := 11
@[inherit_doc Num] abbrev Idx : ℕ := 12
@[inherit_doc Num] abbrev Prime : ℕ := 13
@[inherit_doc Num] abbrev Count : ℕ := 14
@[inherit_doc Num] abbrev Best : ℕ := 15
@[inherit_doc Num] abbrev BestCount : ℕ := 16

end ChoosePrime

open ChoosePrime in
/-- K = ⌈log₂ n⌉ and 2^K, by doubling. -/
def chLevel : Stmt :=
  .set Level (k 0) ;;
  .set Rows (k 1) ;;
  .while (v Rows <' v Num) (
    .set Rows (v Rows +' v Rows) ;;
    .set Level (v Level +' k 1))

open ChoosePrime in
/-- The prime is kept if it is the first one or its count is smaller than the best so far. -/
def chKeep : Stmt :=
  .ite (v Idx =' k 0) (.set Best (v Prime) ;; .set BestCount (v Count))
    (.ite (v Count <' v BestCount) (.set Best (v Prime) ;; .set BestCount (v Count)) .skip)

open ChoosePrime in
/-- One round: the count for the prime number i. -/
def chRound (ν : ChNums) : Stmt :=
  .set Prime (M (v Work +' v Idx)) ;;
  .call ν.pCountPrime
    [v Num, v ListAB, v ListBC, v ListAC, v Prime, v Len, v Level, v Rows, v Area] Count ;;
  chKeep

open ChoosePrime in
/-- choosePrime(n, U, ab, bc, ac, D, w). -/
def choosePrimeBody (ν : ChNums) : Stmt :=
  .call ν.pPrimes [v Work, v Range] Primes ;;
  .call ν.pBitLen [v Bound] Len ;;
  chLevel ;;
  .set Area (v Work +' v Primes) ;;
  .set Best (k 0) ;;
  .set BestCount (k 0) ;;
  .for Idx (v Primes) (chRound ν) ;;
  .set Num (v Best)

/-- The number of cells that choosePrime may change, from w on: the list of the primes and the work
area of countPrime for the largest possible prime. -/
def chooseCells (n U D : ℕ) : ℕ :=
  Nat.sqrt D + countCells n (Nat.sqrt D) (bitLen U) (Nat.clog 2 n)

/-- An upper bound on the number of steps of choosePrime. -/
def chooseTime (n U D : ℕ) : ℕ :=
  tPrimes D + tBitLen U + 12 * Nat.clog 2 n +
    Nat.sqrt D * (countTime n (Nat.sqrt D) (bitLen U) (Nat.clog 2 n) + 50) + 60

/-- What choosePrime needs: the three lists of n² weights of absolute value at most U lie below w,
the cells from w on lie in the memory, and the numbers that are formed fit in a word. -/
structure ChoosePrimePre (lim : Limits) (d : ℕ) (μ : ℕ → ℤ) (x : TriInst) (D w : ℕ) : Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  inst : x.Pre μ w
  cells : w + chooseCells x.n x.U D ≤ lim.space
  wordD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word
  wordU : ((2 * x.U + 2 : ℕ) : ℤ) ≤ lim.word
  wordN : ((2 * x.n + 1 : ℕ) : ℤ) ≤ lim.word
  wordDbl : ((Nat.sqrt D * 2 ^ (bitLen x.U + 1) : ℕ) : ℤ) ≤ lim.word
  wordStr : ((4 * (16 ^ Nat.clog 2 x.n * Nat.sqrt D) : ℕ) : ℤ) ≤ lim.word
  wordSum : ((x.n * x.n * (16 ^ Nat.clog 2 x.n * Nat.sqrt D) : ℕ) : ℤ) ≤ lim.word
  depth : d + 2 * Nat.clog 2 x.n + 3 ≤ lim.depth

/-! ## The pure side: the best prime so far -/

/-- The count is not negative: it is a number of triples. -/
theorem countOf_nonneg (n : ℕ) {p : ℕ} (hp : 1 ≤ p) (AB BC AC : List ℤ) :
    0 ≤ countOf n p AB BC AC := by
  rw [countOf_eq n AB BC AC (by omega)]
  exact Int.natCast_nonneg _

/-- What the locals best and cnt hold after i primes: nothing yet, or the best prime so far and its
count c, where c q is the count for the prime q. -/
def BestSoFar (c : ℕ → ℤ) (L : List ℕ) (i : ℕ) (best cnt : ℤ) : Prop :=
  (i = 0 ∧ best = 0) ∨
    (1 ≤ i ∧ best = (bestOf (fun q => (c q).toNat) L i : ℕ) ∧
      cnt = c (bestOf (fun q => (c q).toNat) L i) ∧ 0 ≤ cnt)

/-- One more prime: it is kept if it is the first one or its count is smaller. -/
theorem BestSoFar.step {c : ℕ → ℤ} {L : List ℕ} {i : ℕ} {best cnt : ℤ}
    (h : BestSoFar c L i best cnt) (hi : i < L.length) (hc : 0 ≤ c L[i]) :
    BestSoFar c L (i + 1) (if i = 0 ∨ c L[i] < cnt then (L[i] : ℕ) else best)
      (if i = 0 ∨ c L[i] < cnt then c L[i] else cnt) := by
  refine Or.inr ⟨Nat.succ_pos i, ?_⟩
  obtain ⟨rfl, -⟩ | ⟨hi1, rfl, rfl, hcnt⟩ := h
  · rw [show bestOf (fun q => (c q).toNat) L (0 + 1) = L[0] from
      (bestOf_one _ L).trans (List.getD_eq_getElem _ _ hi)]
    simp [hc]
  · have hcmp : (c L[i]).toNat < (c (bestOf (fun q => (c q).toNat) L i)).toNat ↔
        c L[i] < c (bestOf (fun q => (c q).toNat) L i) := by omega
    rw [bestOf_succ _ L hi1 hi]
    simp only [hcmp, show i ≠ 0 by omega, false_or]
    split_ifs <;> simp [hc, hcnt]

/-! ## The parts of the program -/

/-- The local variables of choosePrime during the loop over the primes. -/
@[simp] def chFrame (n U ab bc ac D w nP len K : ℕ) (i q c best cnt : ℤ) : List ℤ :=
  [n, U, ab, bc, ac, D, w, nP, len, K, (2 ^ K : ℕ), (w + nP : ℕ), i, q, c, best, cnt]

section parts

variable {ν : ChNums} {μ μ' : ℕ → ℤ} {n U ab bc ac D w nP len K : ℕ} {AB BC AC : List ℤ}

/-- **K = ⌈log₂ n⌉ and 2^K.** -/
theorem chLevel_spec (hword : ((2 * n + 1 : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d chLevel ⟨frame [n, U, ab, bc, ac, D, w, nP, len], μ⟩ (12 * Nat.clog 2 n + 8)
      fun σ' => σ' = ⟨frame [n, U, ab, bc, ac, D, w, nP, len, (Nat.clog 2 n : ℕ),
        (2 ^ Nat.clog 2 n : ℕ)], μ⟩ := by
  have test : ∀ j, 2 ^ j < n ↔ j < Nat.clog 2 n := fun j =>
    (Nat.lt_clog_iff_pow_lt (by norm_num)).symm
  generalize Nat.clog 2 n = L at test
  push_cast at hword
  -- level := 0; rows := 1
  light_set (0 : ℕ)
  light_set (1 : ℕ)
  -- while rows < n: rows := rows + rows; level := level + 1.  Before round j, rows = 2^j.
  refine Ends.whileBlock
    (fun j σ => σ = ⟨frame [n, U, ab, bc, ac, D, w, nP, len, j, (2 ^ j : ℕ)], μ⟩) L (by simp) ?round
    ?done
  case round =>
    rintro j _ hj rfl
    have hlt := (test j).2 hj
    have hjlt : j < 2 ^ j := Nat.lt_two_pow_self
    rw [pow_succ, Nat.mul_two]
    generalize 2 ^ j = q at hlt hjlt
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hnot := mt (test L).1 (lt_irrefl L)
    generalize 2 ^ L = q at hnot
    exact ⟨by light_side, by light_side, rfl⟩

/-- **Keeping the better prime.** -/
theorem chKeep_spec (h0 : 0 ≤ lim.word) (i : ℕ) (q c best cnt : ℤ) :
    Ends lim P d chKeep ⟨frame (chFrame n U ab bc ac D w nP len K i q c best cnt), μ⟩ 12 fun σ' =>
      σ' = ⟨frame (chFrame n U ab bc ac D w nP len K i q c
        (if i = 0 ∨ c < cnt then q else best) (if i = 0 ∨ c < cnt then c else cnt)), μ⟩ := by
  refine Ends.block ⟨by simp [chKeep, h0], ?_⟩ (by simp [chKeep])
  by_cases hi : i = 0 <;> by_cases hc : c < cnt <;>
    simp [chKeep, update_frame_setLocal, hi, hc]

variable {x : TriInst}

/-- The cells that choosePrime may change lie in the memory: the list of the primes, and the work
area of countPrime. -/
theorem ChoosePrimePre.cells_le (pre : ChoosePrimePre lim d μ x D w) :
    w + (Nat.sqrt D + countCells x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n)) ≤ lim.space :=
  pre.cells

/-- What countPrime assumes holds for each prime q of the range, with the work area behind the list
of the primes, as long as only cells from w on have changed. -/
theorem ChoosePrimePre.countPre (pre : ChoosePrimePre lim d μ x D w)
    (rest : SameOutside μ μ' w (chooseCells x.n x.U D)) {q : ℕ} (hq : q ∈ primesList D) :
    CountPrimePre lim (d + 1) μ' x q (bitLen x.U) (Nat.clog 2 x.n) (w + (primesList D).length) := by
  have cells := pre.cells_le
  have depth := pre.depth
  have := length_primesList_le D
  have hqS : q ≤ Nat.sqrt D := le_sqrt_of_mem_primesList hq
  have := countCells_mono hqS x.n (bitLen x.U) (Nat.clog 2 x.n)
  exact
    { space_le := pre.space_le, inst := pre.inst.keep.mono (Nat.le_add_right _ _)
      p_pos := (mem_primesList.1 hq).1.one_le, hK := rfl, hU := Nat.lt_size_self x.U
      cells := by omega
      wordDbl := le_trans (by exact_mod_cast Nat.mul_le_mul_right _ hqS) pre.wordDbl
      wordStr := le_trans
        (by exact_mod_cast Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left _ hqS)) pre.wordStr
      wordSum := le_trans
        (by exact_mod_cast Nat.mul_le_mul_left (x.n * x.n) (Nat.mul_le_mul_left _ hqS)) pre.wordSum
      depth := by omega }

/-- The state of choosePrime before round i: the best prime so far and its count are in their
locals, the list of the primes stands at w, and only cells from w on have changed. -/
def ChInv (μ : ℕ → ℤ) (x : TriInst) (D w i : ℕ) (σ : State) : Prop :=
  ∃ (q c best cnt : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (chFrame x.n x.U x.ab x.bc x.ac D w (primesList D).length (bitLen x.U)
      (Nat.clog 2 x.n) i q c best cnt), μ'⟩ ∧
    BestSoFar (fun p => countOf x.n p x.AB x.BC x.AC) (primesList D) i best cnt ∧
    SegN μ' w (primesList D) ∧ SameOutside μ μ' w (chooseCells x.n x.U D)

open ChoosePrime in
/-- **One round of choosePrime.** -/
theorem chRound_spec (ctx : ChCtx P ν) (pre : ChoosePrimePre lim d μ x D w) {i : ℕ}
    (hi : i < (primesList D).length) {σ : State} (h : ChInv μ x D w i σ) :
    Ends lim P d (chRound ν) σ (countTime x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) + 28)
      fun σ' => σ'.loc Idx = i ∧ ChInv μ x D w (i + 1)
        { σ' with loc := Function.update σ'.loc Idx ((i : ℤ) + 1) } := by
  obtain ⟨q₀, c₀, best, cnt, μ', rfl, hbest, seg, rest⟩ := h
  have := pre.space_le
  have := pre.cells_le
  have depth := pre.depth
  have := length_primesList_le D
  have hmem : (primesList D)[i] ∈ primesList D := List.getElem_mem hi
  have := countTime_mono (le_sqrt_of_mem_primesList hmem) x.n (bitLen x.U) (Nat.clog 2 x.n)
  have :=
    countCells_mono (le_sqrt_of_mem_primesList hmem) x.n (bitLen x.U) (Nat.clog 2 x.n)
  have hread : μ' (w + i) = ((primesList D)[i] : ℕ) := by
    rw [seg i (by simpa using hi), List.getElem_map]
  -- prime := w[i]
  light_set ((primesList D)[i] : ℕ) using hread
  -- count := countPrime(n, ab, bc, ac, prime, len, K, 2^K, area)
  refine Ends.callToThen (countPrime_meets ctx.hCountPrime ctx.cp (pre.countPre rest hmem)) ?_
    (hT := by simp; omega)
  rintro _ μ'' ⟨rfl, rest'⟩
  -- The prime is kept if it is the first one or its count is smaller.
  refine (chKeep_spec (by omega) i _ _ best cnt).mono (by simp; omega) ?_
  rintro _ rfl
  refine ⟨by simp, ((primesList D)[i] : ℕ), countOf x.n (primesList D)[i] x.AB x.BC x.AC, _, _,
    μ'', by simp [update_frame_setLocal],
    hbest.step hi (countOf_nonneg x.n (mem_primesList.1 hmem).1.one_le x.AB x.BC x.AC),
    seg.keep, rest.trans (rest'.mono (by omega) ?_)⟩
  unfold chooseCells
  omega

/-- **primes** as a procedure. -/
theorem primes_meets {q dst pSqrt pSieve : ℕ} (hP : P[q]? = some (primesBody pSqrt pSieve))
    (C : Primes.Ctx P pSqrt pSieve) (hw : (lim.space : ℤ) ≤ lim.word)
    (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word) (hdst : dst + (2 * Nat.sqrt D + 1) ≤ lim.space)
    (hd : d < lim.depth) :
    Meets lim P q d [dst, D] μ (tPrimes D) fun r μ' =>
      r = ((primesList D).length : ℕ) ∧ SegN μ' dst (primesList D) ∧
        SameOutside μ μ' dst (2 * Nat.sqrt D + 1) :=
  Meets.of_body hP (primes_spec C hw hD hdst hd)

/-- **bitLen** as a procedure. -/
theorem bitLen_meets {q : ℕ} (hP : P[q]? = some bitLenBody)
    (hU : ((2 * U + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [U] μ (tBitLen U) fun r μ' => r = (bitLen U : ℕ) ∧ μ' = μ :=
  Meets.of_body hP (bitLen_spec hU)

open ChoosePrime in
/-- **choosePrime** returns the first prime of the range with the smallest count (0 if the range has
no prime), and changes only cells of its work area. -/
theorem choosePrime_spec (ctx : ChCtx P ν) (pre : ChoosePrimePre lim d μ x D w) :
    Ends lim P d (choosePrimeBody ν) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, D, w], μ⟩
      (chooseTime x.n x.U D) fun σ' =>
        σ'.loc 0 = (chosenPrime x.n D x.AB x.BC x.AC : ℕ) ∧
          SameOutside μ σ'.mem w (chooseCells x.n x.U D) := by
  have := pre.space_le
  have := pre.cells_le
  have depth := pre.depth
  have := length_primesList_le D
  have : Nat.sqrt D + 1 ≤ countCells x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) := by
    have hle : Nat.sqrt D ≤ 4 ^ Nat.clog 2 x.n * Nat.sqrt D :=
      Nat.le_mul_of_pos_left _ (by positivity)
    unfold countCells
    generalize 4 ^ Nat.clog 2 x.n * Nat.sqrt D = A at hle ⊢
    generalize 2 ^ Nat.clog 2 x.n = B
    omega
  have hloop : (primesList D).length *
      (countTime x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) + 36) ≤
      Nat.sqrt D * (countTime x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) + 50) :=
    Nat.mul_le_mul (length_primesList_le D) (by omega)
  unfold chooseTime
  -- primes := the primes of the range, at w
  light_call (primes_meets (dst := w) ctx.hPrimes ctx.primes pre.space_le pre.wordD
    (by omega) (by omega)) with _ μ₁ ⟨rfl, seg, rest⟩
  -- len := bitLen(U)
  light_call (bitLen_meets ctx.hBitLen pre.wordU) with _ μ₂ ⟨rfl, hμ⟩
  rw [hμ]
  -- K and 2^K
  light_piece (chLevel_spec pre.wordN) with _ rfl
  -- area := w + primes; best := 0; bestCount := 0
  light_set (w + (primesList D).length : ℕ)
  light_set 0
  light_set 0
  -- for i < primes: one round
  refine Ends.next _ (Ends.for (ChInv μ x D w) (primesList D).length
    (countTime x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) + 28) ?start
    (fun i σ hi _ h => chRound_spec ctx pre hi h) ?done ?bound (hT := le_rfl))
    (by simp; ring_nf at hloop ⊢; omega)
  case start =>
    exact ⟨0, 0, 0, 0, μ₁, by simp [update_frame_setLocal], Or.inl ⟨rfl, rfl⟩, seg,
      rest.mono le_rfl (by unfold chooseCells; omega)⟩
  case bound =>
    rintro i _ - - ⟨q, c, best, cnt, μ', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨q, c, best, cnt, μ', rfl, hbest, -, rest'⟩
    -- return best
    refine Ends.setTo best ⟨?_, rest'⟩ (hT := by simp; ring_nf at hloop ⊢; omega)
    change best = (((primesList D).argmin fun q => (countOf x.n q x.AB x.BC x.AC).toNat).getD 0 : ℕ)
    obtain ⟨hnil, rfl⟩ | ⟨hpos, rfl, -, -⟩ := hbest
    · rw [List.eq_nil_of_length_eq_zero hnil]
      rfl
    · rw [bestOf_length]

/-- **choosePrime** as a procedure. -/
theorem choosePrime_meets {q : ℕ} (hP : P[q]? = some (choosePrimeBody ν)) (ctx : ChCtx P ν)
    (pre : ChoosePrimePre lim d μ x D w) :
    Meets lim P q d [x.n, x.U, x.ab, x.bc, x.ac, D, w] μ (chooseTime x.n x.U D) fun r μ' =>
      r = (chosenPrime x.n D x.AB x.BC x.AC : ℕ) ∧ SameOutside μ μ' w (chooseCells x.n x.U D) :=
  Meets.of_body hP (choosePrime_spec ctx pre)

end parts

end Light.Sec3
