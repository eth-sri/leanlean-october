/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Modified in 2026 for ImprovedExponents (Jihoon Hyun): ported to Lean and Mathlib v4.35.0-rc2.
-/

import PaperStatements
import ThreeSumApsp.Util.Index
import ThreeSumApsp.Util.PrimesInWindow
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.RingTheory.AdjoinRoot
noncomputable section

/-!
# Theorem 17, first step: hashing modulo a prime

The first step of the proof of Theorem 17 reduces the weights modulo a prime `p` in the range
`[√D/2, √D)` with few false positives.

* **Counting.**  The number of triples with `S(a,b,c) ≡ 0 (mod p)` is `F(p) + Z₀`
  (`TriangleInstance.countZeroMod_eq`), and it can be read off the product of two matrices over
  `ℤ[x]/(x^p − 1)` (`TriangleInstance.coeff_matP_mul_matQ`,
  `TriangleInstance.F_add_Z₀_eq_sum_coeff`).  There are fewer than `√D` primes in the range
  (`card_primesInRange_lt`).
* **Selecting.**  The prime with the smallest count exists
  (`TriangleInstance.exists_isSelectedPrime`) and has the fewest false positives
  (`TriangleInstance.IsSelectedPrime.F_le`).
* **The bound on `F(p)`**, `TriangleInstance.F_le_of_le_card_primesInRange` and
  `TriangleInstance.exists_F_le`.  A triple is a false positive of at most `log_{√D/2}(3n^ν)` primes
  in the range (`TriangleInstance.card_falsePositive_primes_le`), so the numbers `F(q)` add up to at
  most `n³` times that (`TriangleInstance.sum_F_le`); there are `Ω(√D/log D)` primes in the range
  (`exists_le_card_primesInRange`); `F(p)` is at most the average
  (`TriangleInstance.IsSelectedPrime.F_mul_card_le_sum`); and `log D ≤ 4 log(√D/2)`
  (`log_le_four_mul_log_sqrt_div_two`).  The constant of the bound has a name,
  `Hashing.falsePositiveConst`.
-/


namespace ThreeSumApsp

/-! ### The primes in the range -/

/-- Proof of Theorem 17, "a prime p ∈ [√D/2, √D)": the primes in the range are the primes `p` with
`√D/2 ≤ p < √D`.  (The bound `p < D` in the definition excludes none of them.) -/
theorem mem_primesInRange {D p : ℕ} :
    p ∈ primesInRange D ↔ p.Prime ∧ Real.sqrt D / 2 ≤ (p : ℝ) ∧ (p : ℝ) < Real.sqrt D := by
  unfold primesInRange
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨by simp, fun h => ⟨?_, h⟩⟩
  -- From `p < √D` we get `p ≤ p² < D`.
  have hsq : p ^ 2 < D := by exact_mod_cast (Real.lt_sqrt (Nat.cast_nonneg p)).1 h.2.2
  grind [Nat.le_self_pow, two_ne_zero]

/-! ### The ring `ℤ[x]/(x^p − 1)` -/

open Polynomial in
/-- Proof of Theorem 17: "the ring ℤ[x]/(x^p − 1)".  (`Polynomial.C 1` is the constant polynomial
1.) -/
abbrev CyclicRing (p : ℕ) : Type := AdjoinRoot ((X : ℤ[X]) ^ p - C 1)

namespace CyclicRing

open Polynomial

variable {p : ℕ}

/-- The element `x` of `ℤ[x]/(x^p − 1)`. -/
def x (p : ℕ) : CyclicRing p := AdjoinRoot.root _

/-- Proof of Theorem 17: "the coefficient of x^r" in an element `z` of `ℤ[x]/(x^p − 1)`, for `0 ≤ r
< p`, as a linear map: the coefficient of `x^r` in the unique polynomial of degree less than `p`
that represents `z` (Mathlib's `AdjoinRoot.modByMonicHom` gives that polynomial; it asks for the
fact that `x^p − 1` is monic, which holds as `p ≠ 0`). -/
def coeff (hp : p ≠ 0) (r : ℕ) : CyclicRing p →ₗ[ℤ] ℤ :=
  lcoeff ℤ r ∘ₗ AdjoinRoot.modByMonicHom (by grind [monic_X_pow_sub_C])

variable (hp : p ≠ 0)

/-- The coefficient, in terms of the representing polynomial. -/
theorem coeff_apply (r : ℕ) (z : CyclicRing p) :
    coeff hp r z = (AdjoinRoot.modByMonicHom (monic_X_pow_sub_C (1 : ℤ) hp) z).coeff r :=
  rfl

/-- In `ℤ[x]/(x^p − 1)` we have `x^p = 1`. -/
theorem x_pow_self (p : ℕ) : x p ^ p = 1 := by
  have h : AdjoinRoot.mk _ ((X : ℤ[X]) ^ p - C 1) = 0 := AdjoinRoot.mk_self
  exact sub_eq_zero.1 h

/-- The coefficient of `x^r` in the power `x^k` of `ℤ[x]/(x^p − 1)` is 1 if `r = k mod p` and 0
otherwise. -/
theorem coeff_x_pow (k r : ℕ) :
    coeff hp r (x p ^ k) = if r = k % p then 1 else 0 := by
  have hred : x p ^ k = x p ^ (k % p) := by
    grind [Nat.div_add_mod, pow_add, pow_mul, x_pow_self, one_pow, one_mul]
  have hdeg : ((X : ℤ[X]) ^ (k % p)).degree < ((X : ℤ[X]) ^ p - C 1).degree := by
    rw [degree_X_pow, degree_X_pow_sub_C (Nat.pos_of_ne_zero hp)]
    simp_all [Nat.mod_lt, Nat.pos_of_ne_zero]
  rw [coeff_apply, hred, x, ← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff (by grind [monic_X_pow_sub_C])).2 hdeg, coeff_X_pow]

end CyclicRing

/-- A number `r < p` is the sum of the residues of `u` and `v` in `{0, …, p − 1}`, reduced modulo
`p`, exactly if `u + v ≡ r`. -/
theorem eq_add_toNat_emod_iff {p r : ℕ} (hp : p ≠ 0) (hr : r < p) (u v : ℤ) :
    r = ((u % (p : ℤ)).toNat + (v % (p : ℤ)).toNat) % p ↔ u + v ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
  rw [← Int.natCast_inj, Int.ModEq, Int.emod_eq_of_lt (Int.natCast_nonneg r) (by omega),
    eq_comm]
  grind [Int.natCast_toNat_emod, Nat.pos_of_ne_zero, Int.add_emod]

/-! ### Counting the triples with `S(a,b,c) ≡ 0 (mod p)` -/

namespace TriangleInstance

variable {n : ℕ} (T : TriangleInstance ℤ n)

/-- Proof of Theorem 17: "A false positive of p is a triple (a,b,c) with S(a,b,c) ≠ 0 and p ∣
S(a,b,c)". -/
def IsFalsePositive (p : ℕ) (t : Fin n × Fin n × Fin n) : Prop :=
  T.S t.1 t.2.1 t.2.2 ≠ 0 ∧ (p : ℤ) ∣ T.S t.1 t.2.1 t.2.2

open Classical in
/-- Proof of Theorem 17: "let F(p) denote the number of false positives of p". -/
def F (p : ℕ) : ℕ :=
  (Finset.univ.filter fun t : Fin n × Fin n × Fin n => T.IsFalsePositive p t).card

open Classical in
/-- Proof of Theorem 17: "Z₀, the number of zero triangles". -/
def Z₀ : ℕ :=
  (Finset.univ.filter fun t : Fin n × Fin n × Fin n => T.IsZeroTriangle t.1 t.2.1 t.2.2).card

/-- Proof of Theorem 17: "This number is the number of false positives F(p) plus Z₀, the number of
zero triangles, which does not depend on p." -/
theorem countZeroMod_eq (p : ℕ) : T.countZeroMod p = T.F p + T.Z₀ := by
  classical
  simp only [countZeroMod, F, Z₀, Finset.card_filter, ← Finset.sum_add_distrib]
  -- A triple with `p ∣ S(a,b,c)` is a zero triangle or a false positive, and not both.
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h0 : T.S t.1 t.2.1 t.2.2 = 0 <;>
    simp [IsFalsePositive, IsZeroTriangle, Int.modEq_zero_iff_dvd, h0]

/-- Proof of Theorem 17: "let P[a,c] := x^{w(a,c) mod p}", a matrix over `ℤ[x]/(x^p − 1)`.  `w mod
p` is the residue in `{0, …, p − 1}`. -/
def matP (p : ℕ) : Matrix (Fin n) (Fin n) (CyclicRing p) :=
  Matrix.of fun a c => CyclicRing.x p ^ (T.wAC a c % (p : ℤ)).toNat

/-- Proof of Theorem 17: "and Q[c,b] := x^{w(b,c) mod p}". -/
def matQ (p : ℕ) : Matrix (Fin n) (Fin n) (CyclicRing p) :=
  Matrix.of fun c b => CyclicRing.x p ^ (T.wBC b c % (p : ℤ)).toNat

/-- Proof of Theorem 17: "the coefficient of x^r in (PQ)[a,b] is the number of c ∈ C with w(a,c) +
w(b,c) ≡ r (mod p)". -/
theorem coeff_matP_mul_matQ {p : ℕ} (hp : p ≠ 0) (a b : Fin n) (r : ℕ) (hr : r < p) :
    CyclicRing.coeff hp r ((T.matP p * T.matQ p) a b) =
      ((Finset.univ.filter fun c : Fin n =>
        T.wAC a c + T.wBC b c ≡ (r : ℤ) [ZMOD (p : ℤ)]).card : ℤ) := by
  classical
  -- `(PQ)[a,b]` is the sum over `c` of `x^(w(a,c) mod p + w(b,c) mod p)`, and the coefficient of
  -- `x^r` in each term is 1 or 0.
  rw [Matrix.mul_apply]
  simp only [matP, matQ, Matrix.of_apply, ← pow_add]
  simp [CyclicRing.coeff_x_pow]
  grind [Finset.card_filter, eq_add_toNat_emod_iff]

/-- Proof of Theorem 17: "then F(p) + Z₀ is the sum over the pairs (a,b) ∈ A × B of the coefficient
of x^{−w(a,b) mod p} in (PQ)[a,b]". -/
theorem F_add_Z₀_eq_sum_coeff {p : ℕ} (hp : p ≠ 0) :
    ((T.F p + T.Z₀ : ℕ) : ℤ) =
      ∑ a : Fin n, ∑ b : Fin n,
        CyclicRing.coeff hp ((-T.wAB a b) % (p : ℤ)).toNat ((T.matP p * T.matQ p) a b) := by
  classical
  rw [← countZeroMod_eq]
  unfold countZeroMod
  rw [Finset.card_filter, Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [T.coeff_matP_mul_matQ hp a b _ (Int.toNat_emod_lt (Nat.pos_of_ne_zero hp) _),
    Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  -- `S(a,b,c) ≡ 0` says the same as `w(a,c) + w(b,c) ≡ -w(a,b)`, and `-w(a,b)` is congruent to its
  -- residue.
  have hres : -T.wAB a b % p ≡ -T.wAB a b [ZMOD p] := Int.mod_modEq _ _
  have hiff : T.S a b c ≡ 0 [ZMOD p] ↔
      T.wAC a c + T.wBC b c ≡ (-T.wAB a b % p).toNat [ZMOD p] := by
    rw [(Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp) _), show T.wAC a c + T.wBC b c ≡ -T.wAB a b % p [ZMOD p] ↔
        T.wAC a c + T.wBC b c ≡ -T.wAB a b [ZMOD p] from
      ⟨fun h => h.trans hres, fun h => h.trans hres.symm⟩,
      Int.modEq_iff_dvd, Int.modEq_iff_dvd,
      show 0 - T.S a b c = -T.wAB a b - (T.wAC a c + T.wBC b c) by
        grind [S]]
  simp_all

end TriangleInstance

/-! ### Selecting the prime -/

namespace TriangleInstance

variable {n D p : ℕ} {κ : ℝ} (T : TriangleInstance ℤ n)

/-- Proof of Theorem 17.  There is a prime to select. -/
theorem exists_isSelectedPrime (D : ℕ) (hD : 16 ≤ D) : ∃ p, T.IsSelectedPrime D p := by
  obtain ⟨q, hq⟩ :=
    Nat.exists_prime_half_le_and_lt _ (Real.four_le_sqrt_natCast_of_sixteen_le hD)
  exact Finset.exists_min_image _ T.countZeroMod ⟨q, mem_primesInRange.2 hq⟩

/-- Proof of Theorem 17: "We select the prime with the smallest count, which is also the prime with
the fewest false positives". -/
theorem IsSelectedPrime.F_le {T : TriangleInstance ℤ n} (hp : T.IsSelectedPrime D p) :
    ∀ q ∈ primesInRange D, T.F p ≤ T.F q := by
  intro q hq
  have h := hp.2 q hq
  grind [countZeroMod_eq]

/-! ### The bound on the number of false positives of the selected prime -/

/-- Proof of Theorem 17: "|S(a,b,c)| ≤ 3n^ν". -/
theorem abs_S_le (hT : T.WeightsPolyBounded κ) (a b c : Fin n) :
    ((|T.S a b c| : ℤ) : ℝ) ≤ 3 * (n : ℝ) ^ κ := by
  obtain ⟨hAB, hBC, hAC⟩ := hT
  have habs : |T.S a b c| ≤ |T.wAB a b| + |T.wBC b c| + |T.wAC a c| := abs_add_three _ _ _
  have hcast : |T.S a b c|
      ≤ |T.wAB a b| + |T.wBC b c| + ((|T.wAC a c| : ℤ) : ℝ) := by
    exact_mod_cast habs
  grind

open Classical in
/-- Proof of Theorem 17: "a triple with S(a,b,c) ≠ 0 is a false positive exactly of the primes in
the range that divide S(a,b,c).  Since 0 < |S(a,b,c)| ≤ 3n^ν and these primes are at least √D/2,
there are at most log_{√D/2}(3n^ν) of them." -/
theorem card_falsePositive_primes_le (hD : 16 ≤ D) (hT : T.WeightsPolyBounded κ)
    (t : Fin n × Fin n × Fin n) (ht : T.S t.1 t.2.1 t.2.2 ≠ 0) :
    (((primesInRange D).filter fun p => T.IsFalsePositive p t).card : ℝ)
      ≤ Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) := by
  have hsqrt := Real.four_le_sqrt_natCast_of_sixteen_le hD
  set divisors := (primesInRange D).filter fun p => T.IsFalsePositive p t
  have hmem : ∀ p ∈ divisors,
      p.Prime ∧ Real.sqrt D / 2 ≤ p ∧ (p : ℤ) ∣ T.S t.1 t.2.1 t.2.2 := by
    intro p hp
    obtain ⟨hrange, -, hdvd⟩ := Finset.mem_filter.1 hp
    grind [mem_primesInRange]
  -- The product of these primes divides `S(a,b,c)`, so it is at most `|S(a,b,c)| ≤ 3n^κ`.
  have hprod :=
    calc ∏ p ∈ divisors, (p : ℝ) = ∏ p ∈ divisors, p := (Nat.cast_prod _ _).symm
      _ ≤ (T.S t.1 t.2.1 t.2.2).natAbs := by
          exact_mod_cast Nat.le_of_dvd (Int.natAbs_pos.2 ht) (Finset.prod_primes_dvd _ (fun p hp => (hmem p hp).1.prime)
      fun p hp => Int.natCast_dvd.1 (hmem p hp).2.2)
      _ = |T.S t.1 t.2.1 t.2.2| := Nat.cast_natAbs _
      _ ≤ 3 * n ^ κ := T.abs_S_le hT _ _ _
  -- Each of these primes is at least `√D/2`.
  have hpow : (Real.sqrt D / 2) ^ divisors.card ≤ ∏ p ∈ divisors, (p : ℝ) := by
    rw [← Finset.prod_const]
    grind [Finset.prod_le_prod₀]
  have hY := lt_of_lt_of_le (by positivity) (hpow.trans hprod)
  grind [Real.le_logb_iff_rpow_le, Real.rpow_natCast]

/-- Proof of Theorem 17: "Hence the numbers of false positives of all the primes in the range add up
to at most n³ log_{√D/2}(3n^ν)." -/
theorem sum_F_le (hD : 16 ≤ D) (hκ : 1 ≤ κ) (hT : T.WeightsPolyBounded κ) :
    ((∑ p ∈ primesInRange D, T.F p : ℕ) : ℝ)
      ≤ (n : ℝ) ^ 3 * Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) := by
  classical
  have hsqrt := Real.four_le_sqrt_natCast_of_sixteen_le hD
  -- Count the pairs (prime, false positive of that prime) triple by triple.
  have hswap : ∑ p ∈ primesInRange D, T.F p = ∑ t : Fin n × Fin n × Fin n,
      ((primesInRange D).filter fun p => T.IsFalsePositive p t).card := by
    simp only [F, Finset.card_filter]
    exact Finset.sum_comm
  have hterm : ∀ t : Fin n × Fin n × Fin n,
      ((primesInRange D).filter fun p => T.IsFalsePositive p t).card
        ≤ Real.logb (Real.sqrt D / 2) (3 * n ^ κ) := by
    intro t
    by_cases ht : T.S t.1 t.2.1 t.2.2 = 0
    · -- A zero triangle is a false positive of no prime.
      rw [Finset.filter_eq_empty_iff.2 fun p _ h => h.1 ht, Finset.card_empty, Nat.cast_zero]
      have hn : (1 : ℝ) ≤ n := by exact_mod_cast Fin.pos t.1
      grind [Real.one_le_rpow, Real.logb_nonneg]
    · -- Otherwise this is the bound of `card_falsePositive_primes_le` for this triple.
      convert T.card_falsePositive_primes_le hD hT t ht
  rw [hswap, Nat.cast_sum]
  calc ∑ t : Fin n × Fin n × Fin n,
        (((primesInRange D).filter _).card : ℝ)
      ≤ ∑ _t : Fin n × Fin n × Fin n, Real.logb _ _ :=
        Finset.sum_le_sum fun t _ => hterm t
    _ = n ^ 3 * Real.logb _ _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
          Fintype.card_fin]
        grind

end TriangleInstance

/-- Proof of Theorem 17: "By the prime number theorem there are Ω(√D/log D) primes in the range".

NOTE.  The proof of Theorem 17 needs this for every `D ≥ 16`, not only for large `D`, and so it is
stated.  It follows from a counting form of Bertrand's postulate; the prime number theorem is not
needed. -/
theorem exists_le_card_primesInRange :
    ∃ c : ℝ, 0 < c ∧ ∀ D : ℕ, 16 ≤ D →
      c * (Real.sqrt D / Real.log D) ≤ ((primesInRange D).card : ℝ) := by
  grind [Nat.exists_forall_mul_sqrt_div_log_le_card_primes, mem_primesInRange]

/-- Proof of Theorem 17: "F(p) is at most the average over them", multiplied out. -/
theorem TriangleInstance.IsSelectedPrime.F_mul_card_le_sum {n D p : ℕ} {T : TriangleInstance ℤ n}
    (hp : T.IsSelectedPrime D p) :
    T.F p * (primesInRange D).card ≤ ∑ q ∈ primesInRange D, T.F q := by
  rw [mul_comm]
  exact Finset.card_nsmul_le_sum _ _ _ hp.F_le

/-- Proof of Theorem 17: "log D = O(log(√D/2)) for D ≥ 16". -/
theorem log_le_four_mul_log_sqrt_div_two (D : ℕ) (hD : 16 ≤ D) :
    Real.log D ≤ 4 * Real.log (Real.sqrt D / 2) := by
  have hD16 : (16 : ℝ) ≤ D := by simp_all
  have hlog16 : 4 * Real.log 2 ≤ Real.log D := by
    have h := Real.log_le_log (by norm_num) (show (2 : ℝ) ^ 4 ≤ D by linarith)
    simp_all
  grind [Real.log_div, Real.log_sqrt]

/-- Proof of Theorem 17: "F(p) is at most the average over them, so [...] F(p) = O(n³
log(3n^ν)/√D)": if there are at least `c √D/log D` primes in the range, then `F(p) ≤ (4/c) n³
log(3n^κ)/√D`. -/
theorem TriangleInstance.F_le_of_le_card_primesInRange {n D p : ℕ} {κ c : ℝ}
    (T : TriangleInstance ℤ n) (hc : 0 < c)
    (hcard : c * (Real.sqrt D / Real.log D) ≤ ((primesInRange D).card : ℝ)) (hD : 16 ≤ D)
    (hDn : D ≤ n) (hκ : 1 ≤ κ) (hT : T.WeightsPolyBounded κ) (hp : T.IsSelectedPrime D p) :
    (T.F p : ℝ) ≤ 4 / c * ((n : ℝ) ^ 3 * Real.log (3 * (n : ℝ) ^ κ) / Real.sqrt D) := by
  -- The quantities of the paper's sentence: `r = √D`, `Y = 3n^κ`, and the number of primes in the
  -- range.
  set r := Real.sqrt D
  set Y := 3 * (n : ℝ) ^ κ with hY
  set numPrimes := (primesInRange D).card
  have hr := Real.four_le_sqrt_natCast_of_sixteen_le hD
  have hn : (16 : ℝ) ≤ n := by exact_mod_cast hD.trans hDn
  have hlogD_pos : 0 < Real.log D := Real.log_pos (by exact_mod_cast (by omega : 1 < D))
  have hlogr_pos : 0 < Real.log (r / 2) := Real.log_pos (by linarith)
  have hlogY_nonneg : 0 ≤ Y.log := by
    grind [Real.one_le_rpow, Real.log_nonneg]
  -- "F(p) is at most the average", multiplied out; the false positives of all the primes in the
  -- range add up to at most `n³ log_{r/2} Y`.
  have average : T.F p * numPrimes ≤ n ^ 3 * Real.logb _ Y :=
    le_trans (by exact_mod_cast hp.F_mul_card_le_sum) (T.sum_F_le hD hκ hT)
  -- The base of the logarithm changes: `log_{r/2} Y ≤ 4 log Y / log D`.
  have changeBase : Real.logb (r / 2) Y ≤ 4 * Y.log / Real.log D := by
    rw [Real.logb, div_le_div_iff₀ hlogr_pos hlogD_pos]
    linarith [mul_le_mul_of_nonneg_left (log_le_four_mul_log_sqrt_div_two D hD) hlogY_nonneg]
  rw [show 4 / c * (n ^ 3 * Real.log Y / r) = 4 * n ^ 3 * Y.log / (c * r) by
    field_simp, le_div_iff₀ (by positivity)]
  calc T.F p * (c * r) = T.F p * (c * (r / Real.log D)) * Real.log D := by field_simp
    _ ≤ T.F p * numPrimes * Real.log D := by gcongr
    _ ≤ n ^ 3 * Real.logb _ Y * Real.log D := by gcongr
    _ ≤ n ^ 3 * (4 * Real.log Y / Real.log D) * Real.log D := by gcongr
    _ = 4 * n ^ 3 * Y.log := by field_simp

/-- Proof of Theorem 17: "F(p) = O(n³ log(3n^ν)/√D) = O(ν n³ log n/√D)". -/
theorem TriangleInstance.exists_F_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {n D p : ℕ} {κ : ℝ}, 16 ≤ D → D ≤ n → 1 ≤ κ → ∀ T : TriangleInstance ℤ n,
      T.WeightsPolyBounded κ → T.IsSelectedPrime D p →
      (T.F p : ℝ) ≤ C * (κ * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D) := by
  obtain ⟨c, hc, hcard⟩ := exists_le_card_primesInRange
  refine ⟨max 1 (8 / c), by simp, fun {n D p κ} hD hDn hκ T hT hp => ?_⟩
  have hn : (16 : ℝ) ≤ n := by exact_mod_cast hD.trans hDn
  have hlogn : 0 ≤ Real.log n := by positivity
  -- `log(3n^κ) = log 3 + κ log n ≤ 2κ log n`, because `3 ≤ n` and `κ ≥ 1`.
  have hlog : Real.log (3 * n ^ κ) ≤ 2 * κ * Real.log n := by
    have hlog3 : Real.log 3 ≤ κ * Real.log n :=
      (Real.log_le_log (by norm_num) (by linarith)).trans (le_mul_of_one_le_left hlogn hκ)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow (by linarith)]
    linarith
  calc T.F p ≤ 4 / c * (n ^ 3 * Real.log _ / Real.sqrt D) :=
        T.F_le_of_le_card_primesInRange hc (by simp_all) hD hDn hκ hT hp
    _ ≤ 4 / c * (n ^ 3 * (2 * κ * Real.log n) / Real.sqrt D) := by gcongr
    _ = 8 / c * (κ * n ^ 3 * Real.log n / Real.sqrt D) := by ring
    _ ≤ max 1 _ * (κ * n ^ 3 * Real.log n / Real.sqrt D) := by
        gcongr
        simp

/-- A name for the constant in "F(p) = [...] = O(ν n³ log n/√D)", for the bounds on running times
that are built on this one. -/
def Hashing.falsePositiveConst : ℝ := Classical.choose TriangleInstance.exists_F_le

/-- The constant is at least 1. -/
theorem Hashing.one_le_falsePositiveConst : 1 ≤ Hashing.falsePositiveConst :=
  (Classical.choose_spec TriangleInstance.exists_F_le).1

/-- Proof of Theorem 17: "F(p) = [...] = O(ν n³ log n/√D)", with `Hashing.falsePositiveConst` as the
constant. -/
theorem Hashing.F_le_falsePositiveConst_mul {n D p : ℕ} {κ : ℝ} (hD : 16 ≤ D) (hDn : D ≤ n)
    (hκ : 1 ≤ κ) (T : TriangleInstance ℤ n) (hT : T.WeightsPolyBounded κ)
    (hp : T.IsSelectedPrime D p) :
    (T.F p : ℝ) ≤ Hashing.falsePositiveConst * (κ * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D) :=
  (Classical.choose_spec TriangleInstance.exists_F_le).2 hD hDn hκ T hT hp
