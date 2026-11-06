/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters
public import ThreeSumApsp.Spec.Sec3.Theorem17.Strassen
public import Mathlib.Data.List.MinMax

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

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The chosen prime -/

/-- "We select the prime with the smallest count" (the first such prime; 0 if the window has no
prime). -/
def chosenPrime n D AB BC AC :=
  ((primesList D).argmin fun p => (countOf n p AB BC AC).toNat).getD 0

section

variable {n D : ℕ} (AB BC AC : List ℤ)

variable (hD : 16 ≤ D)

include hD in
/-- **The chosen prime is a selected prime** (proof of Theorem 17: "We select the prime with the
smallest count"). -/
theorem chosenPrime_isSelected :
    (triOf n AB BC AC).IsSelectedPrime D (chosenPrime n D AB BC AC) := by
  -- The window has a prime `p₀`, so `List.argmin` returns `some m`, and the default 0 of
  -- `chosenPrime` is never used.
  obtain ⟨p₀, hp₀, -⟩ := TriangleInstance.exists_isSelectedPrime (triOf n AB BC AC) D hD
  rw [primesInRange_eq, List.mem_toFinset] at hp₀
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1
    (mt (List.argmin_eq_none (f := fun p => (countOf n p AB BC AC).toNat)).1
      (List.ne_nil_of_mem hp₀))
  -- The computed count is the count of the proof of Theorem 17 at every prime of the window.
  have  : ∀ q ∈ primesList D,
      (triOf n AB BC AC).countZeroMod q = (countOf n q AB BC AC).toNat := fun q hq => by
    grind [countOf_eq, mem_primesList]
  rw [chosenPrime, hm, Option.getD_some, TriangleInstance.IsSelectedPrime, primesInRange_eq]
  refine ⟨List.mem_toFinset.2 (List.argmin_mem hm), fun q hq => ?_⟩
  grind [List.argmin_mem, List.mem_toFinset, List.le_of_mem_argmin]

include hD in
/-- The chosen prime is a prime of the window. -/
theorem chosenPrime_mem : chosenPrime n D AB BC AC ∈ primesInRange D :=
  (chosenPrime_isSelected AB BC AC hD).1

/-- The chosen number is in the list of the primes of the window. -/
private def chosenPrime_mem_primesList (hD : 16 ≤ D) := by
  have hmem := chosenPrime_mem (n := n) AB BC AC hD
  rwa [primesInRange_eq, List.mem_toFinset] at hmem

include hD in
/-- The chosen prime is at least 2. -/
theorem two_le_chosenPrime : 2 ≤ chosenPrime n D AB BC AC :=
  (mem_primesList.1 (chosenPrime_mem_primesList AB BC AC hD)).1.two_le

include hD in
/-- The chosen prime is at most `⌊√D⌋`. -/
theorem chosenPrime_le_sqrt : chosenPrime n D AB BC AC ≤ Nat.sqrt D :=
  le_sqrt_of_mem_primesList (chosenPrime_mem_primesList AB BC AC hD)

end

/-! ## The smallest count, by one pass -/

/-- The first of the first `i` elements of a list at which `f` is smallest; 0 for `i = 0`. -/
def bestOf (f : ℕ → ℕ) (L : List ℕ) i := ((L.take i).argmin f).getD 0

/-- The first element is the best of one. -/
theorem bestOf_one f L : bestOf f L 1 = L.getD 0 0 := by
  cases L <;> simp [bestOf]

/-- One more element: it is the best so far exactly if `f` is smaller there. -/
theorem bestOf_succ f L {i} (hi : 1 ≤ i) hiL :
    bestOf f L (i + 1) = if f L[i] < f (bestOf f L i) then L[i] else bestOf f L i := by
  rw [bestOf, bestOf, List.take_succ_eq_append_getElem hiL, List.argmin_concat]
  cases h : (L.take i).argmin f with
  | none => ram_safe
  | some c => aesop

/-- The best of all the elements is what `List.argmin` returns. -/
theorem bestOf_length f L : (L.argmin f).getD 0 = bestOf f L L.length := by
  rw [bestOf, List.take_length]

/-! ## False positives, in terms of a bound on the weights -/

/-- The least exponent `κ ≥ 1` with `U ≤ n^κ`. -/
noncomputable def kappaOf (n U : ℕ) := max 1 (Real.log U / Real.log n)

/-- The exponent is at least 1. -/
theorem one_le_kappaOf n U : 1 ≤ kappaOf n U := le_max_left _ _

/-- `U ≤ n^κ` for this exponent. -/
theorem le_rpow_kappaOf {n U : ℕ} (hn : 2 ≤ n) (hU : 1 ≤ U) :
    (U : ℝ) ≤ (n : ℝ) ^ kappaOf n U := by
  have hn1 : (1 : ℝ) < (n : ℝ) := mod_cast hn

  calc (U : ℝ) = (n : ℝ) ^ Real.logb n U := (Real.rpow_logb (by linarith) hn1.ne' (mod_cast hU)).symm
    _ ≤ (n : ℝ) ^ kappaOf n U := Real.rpow_le_rpow_of_exponent_le hn1.le (le_max_right _ _)

/-- It is the least such exponent. -/
theorem kappaOf_le {n U : ℕ} (hn : 2 ≤ n) (hU : 1 ≤ U) {κ'} (h1 : 1 ≤ κ')
    (h : (U : ℝ) ≤ (n : ℝ) ^ κ') : kappaOf n U ≤ κ' := by
  have hn1 : (1 : ℝ) < (n : ℝ) := mod_cast hn

  refine max_le h1 ?_
  rw [div_le_iff₀ (Real.log_pos hn1), ← Real.log_rpow (by linarith)]
  exact Real.log_le_log (mod_cast hU) h

/-- Weights of absolute value at most `U` are at most `n^κ`. -/
theorem weightsPolyBounded_kappaOf {n U : ℕ} (hn : 2 ≤ n) (hU : 1 ≤ U) {AB BC AC}
    (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U) :
    (triOf n AB BC AC).WeightsPolyBounded (kappaOf n U) := by
  have key : ∀ l , AbsLe l U → ∀ i,
      ((|l.getD i 0| : ℤ) : ℝ) ≤ (n : ℝ) ^ kappaOf n U := fun l hl i =>
    le_trans (mod_cast AbsLe.abs_getD_le (Int.natCast_nonneg U) hl i)
      (le_rpow_kappaOf hn hU)
  exact ⟨fun a b => key AB hAB _, fun b c => key BC hBC _, fun a c => key AC hAC _⟩

/-- **The number of false positives of the chosen prime** (proof of Theorem 17:
"F(p) = O(n³ log(3n^ν)/√D) = O(ν n³ log n/√D)"), with the constant `Hashing.falsePositiveConst`. -/
def F_chosenPrime_le {n D U : ℕ} hD (hDn : D ≤ n) hU {AB BC AC}
    (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U) :=
  Hashing.F_le_falsePositiveConst_mul hD hDn (one_le_kappaOf n U) _
    (weightsPolyBounded_kappaOf (by omega) hU hAB hBC hAC) (chosenPrime_isSelected AB BC AC hD)

end ThreeSumApsp.Spec
