/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Theorem17.Hashing
public import ThreeSumApsp.Util.List

/-!
# The ring `ℤ[x]/(x^p − 1)` as vectors of `p` integers

The proof of Theorem 17 computes with matrices over the ring `ℤ[x]/(x^p − 1)`.  For a program an
element of the ring is the list of its `p` coefficients (`cycVec`).  This file shows that the
operations of the ring are operations on lists that use no division:

* zero, sums and differences are entrywise (`cycVec_zero`, `cycVec_add`, `cycVec_sub`);
* a power of `x` is a unit vector (`cycVec_x_pow`);
* multiplication is cyclic convolution, "O(p²) word operations" (`cycVec_mul`).
-/

@[expose] public section

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

/-! ## Vectors -/

/-- A vector has `p` entries. -/
theorem length_cycVec (z : CyclicRing p) : (cycVec hp z).length = p := by
  simp [cycVec]

/-- Entry `r` of the vector is the coefficient of `x^r`. -/
theorem getD_cycVec (z : CyclicRing p) {r : ℕ} (hr : r < p) :
    (cycVec hp z).getD r 0 = CyclicRing.coeff hp r z :=
  List.getD_map_range _ hr 0

/-- The vector of 0. -/
theorem cycVec_zero : cycVec hp 0 = List.replicate p 0 := by
  rw [cycVec, List.eq_replicate_iff]
  simp

/-- The vector of a sum. -/
theorem cycVec_add (z w : CyclicRing p) :
    cycVec hp (z + w) = vadd (cycVec hp z) (cycVec hp w) := by
  refine List.ext_getElem (by simp [vadd, length_cycVec]) fun r _ _ => ?_
  simp only [vadd, cycVec, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  simp

/-- The vector of a difference. -/
theorem cycVec_sub (z w : CyclicRing p) :
    cycVec hp (z - w) = vsub (cycVec hp z) (cycVec hp w) := by
  refine List.ext_getElem (by simp [vsub, length_cycVec]) fun r _ _ => ?_
  simp only [vsub, cycVec, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  simp

/-- The vector of a power of `x`. -/
theorem cycVec_x_pow (k : ℕ) : cycVec hp (CyclicRing.x p ^ k) = vunit p (k % p) :=
  List.map_congr_left fun r _ => CyclicRing.coeff_x_pow hp k r

/-- Multiplication in the ring is cyclic convolution. -/
theorem cycVec_mul (z w : CyclicRing p) :
    cycVec hp (z * w) = cconv p (cycVec hp z) (cycVec hp w) := by
  let : NeZero p := ⟨hp⟩
  refine List.map_congr_left fun r hr => ?_
  have hr' := List.mem_range.1 hr
  rw [CyclicRing.coeff_apply hp hr', AddMonoidAlgebra.coeff_mul_apply_left,
    Finsupp.sum_fintype _ _ (by simp), List.sum_map_range, ← Fin.sum_univ_eq_sum_range]
  symm
  refine Fintype.sum_equiv (ZMod.finEquiv p).toEquiv _ _ fun i => ?_
  have hi : (i : ℕ) < p := i.isLt
  let j := if (i : ℕ) ≤ r then r - i else r + p - i
  have hj : j < p := by dsimp [j]; split <;> omega
  have he : ZMod.finEquiv p i = (i.val : ZMod p) := by
    rw [← ZMod.natCast_zmod_val (ZMod.finEquiv p i)]
    congr 1
    cases p with
    | zero => exact (Nat.not_lt_zero _ hi).elim
    | succ p => rfl
  have hj' : (j : ZMod p) = -(i.val : ZMod p) + r := by
    dsimp only [j]
    split_ifs with h
    · rw [Nat.cast_sub h, sub_eq_neg_add]
    · rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero, sub_eq_neg_add]
  change _ = AddMonoidAlgebra.coeff z (ZMod.finEquiv p i) *
    AddMonoidAlgebra.coeff w (-(ZMod.finEquiv p i) + (r : ZMod p))
  rw [he, ← hj', getD_cycVec hp z hi, getD_cycVec hp w hj,
    CyclicRing.coeff_apply hp hi, CyclicRing.coeff_apply hp hj]

end ThreeSumApsp.Spec
