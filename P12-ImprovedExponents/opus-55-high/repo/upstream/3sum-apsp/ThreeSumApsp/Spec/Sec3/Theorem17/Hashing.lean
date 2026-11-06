/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Spec.Sec3.Theorem17.Cyclic

/-!
# Hashing modulo a prime (proof of Theorem 17), on numbers and lists

The reduction of Theorem 17 hashes the weights modulo a prime `p` of the window `√D/2 ≤ p < √D` and
selects the prime with the fewest triples `(a,b,c)` with `S(a,b,c) ≡ 0 (mod p)`, where
`S(a,b,c) = w(a,b) + w(b,c) + w(a,c)`.  This file has the parts of this step that a program
computes:

* the residue of a weight as a natural number below `p` (`resid`, `residList`);
* the entries of the matrices `P` and `Q` of the proof of Theorem 17 as unit vectors (`cycVec_matP`,
  `cycVec_matQ`), and the count of the triples, read off the vectors of `PQ` (`countZeroMod_eq`);
* the primes of the window by comparisons of integers (`primesList`, `primesInRange_eq`).
-/


namespace ThreeSumApsp.Spec

/-! ## Residues -/

/-- The residue of `w` modulo `p` in `{0, …, p − 1}`. -/
def resid (p : ℕ) (w : ℤ) : ℕ := (w % (p : ℤ)).toNat

variable {p : ℕ}

/-- The residue, as an integer. -/
theorem resid_cast (hp : p ≠ 0) (w : ℤ) : (resid p w : ℤ) = w % (p : ℤ) :=
  Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp) w

/-- The residue is less than `p`. -/
theorem resid_lt (hp : p ≠ 0) (w : ℤ) : resid p w < p :=
  Int.toNat_emod_lt (Nat.pos_of_ne_zero hp) w

/-- The residue is the number below `p` that is congruent to `w`. -/
theorem resid_eq_iff (hp : p ≠ 0) (w : ℤ) {r : ℕ} (hr : r < p) :
    resid p w = r ↔ w ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
  rw [Int.ModEq, Int.emod_eq_of_lt (Int.natCast_nonneg r) (Int.ofNat_lt.2 hr), ← resid_cast hp,
    Nat.cast_inj]

/-- The residue of `-w` from the residue of `w`. -/
theorem resid_neg (hp : p ≠ 0) (w : ℤ) : resid p (-w) = (p - resid p w) % p := by
  apply (resid_eq_iff hp _ (Nat.mod_lt _ (Nat.pos_of_ne_zero hp))).2
  have hself : p ≡ 0 [ZMOD p] := by simp
  have hsub := (Int.mod_modEq _ p).trans (hself.sub (Int.mod_modEq w p))
  rw [Int.natCast_mod, Nat.cast_sub (resid_lt hp w).le, resid_cast hp]
  rw [zero_sub] at hsub
  tauto

/-- The residues of a list. -/
def residList (p : ℕ) (l : List ℤ) : List ℕ := l.map (resid p)

/-- The residues of a list, read with a default: beyond the end of the list both sides are 0. -/
theorem getD_residList (p : ℕ) (l : List ℤ) (i : ℕ) :
    (residList p l).getD i 0 = resid p (l.getD i 0) := by
  rw [residList, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [resid]

/-- The table `p, 2p, 4p, …, 2^len p`. -/
def dblList (p len : ℕ) : List ℤ := (List.range (len + 1)).map fun j : ℕ => ((p * 2 ^ j : ℕ) : ℤ)

/-- The number of binary digits of `U`: the least `len` with `U < 2^len`. -/
def bitLen (U : ℕ) : ℕ := Nat.size U

variable {n : ℕ}

/-! ## The count of the proof of Theorem 17 -/

/-- Proof of Theorem 17: the entry `P[a,c] = x^{w(a,c) mod p}` is a unit vector. -/
theorem cycVec_matP (T : TriangleInstance ℤ n) (hp : p ≠ 0) (a c : Fin n) :
    cycVec hp (T.matP p a c) = vunit p (resid p (T.wAC a c)) := by
  rw [TriangleInstance.matP, Matrix.of_apply, cycVec_x_pow]
  exact congrArg _ (Nat.mod_eq_of_lt (resid_lt hp _))

/-- Proof of Theorem 17: the entry `Q[c,b] = x^{w(b,c) mod p}` is a unit vector. -/
theorem cycVec_matQ (T : TriangleInstance ℤ n) (hp : p ≠ 0) (c b : Fin n) :
    cycVec hp (T.matQ p c b) = vunit p (resid p (T.wBC b c)) := by
  rw [TriangleInstance.matQ, Matrix.of_apply, cycVec_x_pow]
  exact congrArg _ (Nat.mod_eq_of_lt (resid_lt hp _))

/-- Proof of Theorem 17: the count of the triples with `S(a,b,c) ≡ 0 (mod p)` is "the sum over the
pairs (a,b) ∈ A × B of the coefficient of x^{-w(a,b) mod p} in (PQ)[a,b]". -/
theorem countZeroMod_eq (T : TriangleInstance ℤ n) (hp : p ≠ 0) :
    (T.countZeroMod p : ℤ) =
      ∑ a, ∑ b, (cycVec hp ((T.matP p * T.matQ p) a b)).getD (resid p (-T.wAB a b)) 0 := by
  rw [TriangleInstance.countZeroMod_eq, T.F_add_Z₀_eq_sum_coeff hp]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    (getD_cycVec hp _ (resid_lt hp _)).symm

/-! ## The primes of the window -/

/-- The primes `p` with `√D/2 ≤ p < √D`, by integer comparisons: `D ≤ 4p²` and `p² < D`. -/
def primesList (D : ℕ) : List ℕ :=
  (List.range D).filter fun p => p.Prime ∧ D ≤ 4 * p ^ 2 ∧ p ^ 2 < D

/-- The comparisons with `√D` are comparisons of integers. -/
theorem primesInRange_eq (D : ℕ) : primesInRange D = (primesList D).toFinset := by
  ext q
  have hlow : Real.sqrt D / 2 ≤ q ↔ D ≤ 4 * q ^ 2 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), Real.sqrt_le_left (by positivity),
      show (q * 2) ^ 2 = ((4 * q ^ 2 : ℕ) : ℝ) by grind, Nat.cast_le]
  have hhigh : q < Real.sqrt D ↔ q ^ 2 < D := by
    rw [Real.lt_sqrt (by positivity)]
    exact_mod_cast Iff.rfl
  simp_all [primesInRange, primesList]

variable {D q : ℕ}

/-- The primes of the window, without the bound `q < D` of the search. -/
theorem mem_primesList : q ∈ primesList D ↔ q.Prime ∧ D ≤ 4 * q ^ 2 ∧ q ^ 2 < D := by
  simp only [primesList, List.mem_filter, List.mem_range, decide_eq_true_eq, and_iff_right_iff_imp]
  grind [Nat.le_self_pow]

/-- A prime of the window is at most `⌊√D⌋`. -/
theorem le_sqrt_of_mem_primesList (h : q ∈ primesList D) : q ≤ Nat.sqrt D :=
  Nat.le_sqrt'.2 (mem_primesList.1 h).2.2.le

/-- The window has at most `⌊√D⌋` primes. -/
theorem length_primesList_le (D : ℕ) : (primesList D).length ≤ Nat.sqrt D := by
  have hnodup : (primesList D).Nodup := List.nodup_range.filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  calc (primesList D).toFinset.card ≤ (Finset.Icc 1 (Nat.sqrt D)).card := by
        refine Finset.card_le_card fun q hq => ?_
        grind [List.mem_toFinset, mem_primesList, le_sqrt_of_mem_primesList]
    _ = D.sqrt := by simp
