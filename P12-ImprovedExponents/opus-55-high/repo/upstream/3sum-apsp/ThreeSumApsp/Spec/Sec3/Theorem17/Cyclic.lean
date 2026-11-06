/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Sec3.Theorem17.Hashing
import ThreeSumApsp.Util.List

/-!
# The ring `ℤ[x]/(x^p − 1)` as vectors of `p` integers

The proof of Theorem 17 computes with matrices over the ring `ℤ[x]/(x^p − 1)`.  For a program an
element of the ring is the list of its `p` coefficients (`cycVec`).  This file shows that the
operations of the ring are operations on lists that use no division:

* zero, sums and differences are entrywise (`cycVec_zero`, `cycVec_add`, `cycVec_sub`);
* a power of `x` is a unit vector (`cycVec_x_pow`);
* multiplication is cyclic convolution, "O(p²) word operations" (`cycVec_mul`).  For the proof both
  factors are expanded in powers of `x` (`eq_sum_coeff`), and `x^i x^j` contributes to the
  coefficient of `x^r` exactly if `i + j ≡ r (mod p)`.
-/


namespace ThreeSumApsp.Spec

/-- An element of `ℤ[x]/(x^p − 1)` as the list of its coefficients of `x^0, …, x^{p-1}`. -/
noncomputable def cycVec {p : ℕ} (hp : p ≠ 0) (z : CyclicRing p) : List ℤ :=
  (List.range p).map fun r => CyclicRing.coeff hp r z

/-- Entrywise sum. -/
def vadd (u v : List ℤ) : List ℤ := List.zipWith (· + ·) u v

/-- Entrywise difference. -/
def vsub (u v : List ℤ) : List ℤ := List.zipWith (· - ·) u v

/-- The vector of `x^k`, for `k < p`. -/
def vunit (p k : ℕ) : List ℤ := (List.range p).map fun i => if i = k then 1 else 0

/-- Cyclic convolution: entry `r` is the sum of `u_i v_j` over `i + j ≡ r (mod p)`.  The index `j`
is `r - i` or `r + p - i`. -/
def cconv (p : ℕ) (u v : List ℤ) : List ℤ :=
  (List.range p).map fun r =>
    ((List.range p).map fun i => u.getD i 0 * v.getD (if i ≤ r then r - i else r + p - i) 0).sum

variable {p : ℕ} (hp : p ≠ 0)

variable {r : ℕ}

variable (z : CyclicRing p)

/-! ## Coefficients -/

/-- The representative of degree less than `p` has no coefficients from `p` on. -/
theorem coeff_eq_zero_of_le (hr : p ≤ r) :
    CyclicRing.coeff hp r z = 0 := by
  obtain ⟨f, rfl⟩ := z.mk_surjective
  refine Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le
    (Polynomial.degree_modByMonic_lt f (by grind [Polynomial.monic_X_pow_sub_C])) ?_)
  rw [Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hp)]
  simp_all

/-- An element of the ring is the combination of the powers of `x` with its coefficients. -/
theorem eq_sum_coeff :
    z = ∑ i ∈ Finset.range p, CyclicRing.coeff hp i z • CyclicRing.x p ^ i := by
  have hmk := AdjoinRoot.mk_leftInverse (by grind [Polynomial.monic_X_pow_sub_C]) z
  set f := AdjoinRoot.modByMonicHom (by grind) z with hf
  have hdeg : f.natDegree < p := by
    by_contra hc
    have hlead : f.coeff f.natDegree = 0 := coeff_eq_zero_of_le hp z (not_lt.mp hc)
    simp_all
  conv_lhs => rw [← hmk, f.as_sum_range' p hdeg, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial, zsmul_eq_mul]
  rfl

/-- For `i, j, r < p`: `i + j ≡ r (mod p)` exactly if `j` is `r - i` or `r + p - i`. -/
theorem eq_add_mod_iff {p i j : ℕ} (hi : i < p) (hj : j < p) (hr : r < p) :
    r = (i + j) % p ↔ j = if i ≤ r then r - i else r + p - i := by
  by_cases h : i + j < p
  · grind [Nat.mod_eq_of_lt]
  · rw [Nat.mod_eq_sub_mod (not_lt.mp h), Nat.mod_eq_of_lt (by omega)]
    grind

/-! ## Vectors -/

/-- A vector has `p` entries. -/
theorem length_cycVec : (cycVec hp z).length = p := by
  simp [cycVec]

/-- Entry `r` of the vector is the coefficient of `x^r`. -/
theorem getD_cycVec (hr : r < p) :
    (cycVec hp z).getD r 0 = CyclicRing.coeff hp r z :=
  List.getD_map_range _ hr 0

/-- The vector of 0. -/
theorem cycVec_zero : cycVec hp 0 = List.replicate p 0 := by
  simp_all [cycVec]

variable (w : CyclicRing p)

/-- The vector of a sum. -/
theorem cycVec_add :
    cycVec hp (z + w) = vadd (cycVec hp z) (cycVec hp w) := by
  simp_all [vadd, cycVec]

/-- The vector of a difference. -/
theorem cycVec_sub :
    cycVec hp (z - w) = vsub (cycVec hp z) (cycVec hp w) := by
  simp_all [vsub, cycVec]

/-- The vector of a power of `x`. -/
theorem cycVec_x_pow (k : ℕ) : cycVec hp (CyclicRing.x p ^ k) = vunit p (k % p) :=
  List.map_congr_left fun r _ => CyclicRing.coeff_x_pow hp k r

/-- Multiplication in the ring is cyclic convolution. -/
theorem cycVec_mul :
    cycVec hp (z * w) = cconv p (cycVec hp z) (cycVec hp w) := by
  refine List.map_congr_left fun r hr => ?_
  conv_lhs => rw [eq_sum_coeff hp z, eq_sum_coeff hp w, Finset.sum_mul_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  -- For each i, only one j contributes to the coefficient of x^r.
  have hj : (if i ≤ r then r - i else r + p - i) < p := by grind
  rw [getD_cycVec hp z hi', getD_cycVec hp w hj, map_sum]
  simp only [smul_mul_smul_comm, ← pow_add, map_zsmul, CyclicRing.coeff_x_pow, smul_eq_mul]
  rw [Finset.sum_eq_single _]
  · rw [if_pos ((eq_add_mod_iff hi' hj (List.mem_range.mp hr)).mpr rfl), mul_one]
  · simp_all [eq_add_mod_iff, Finset.mem_range, mul_zero]
  grind
