/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Spec.Sec3.Problems
public import ThreeSumApsp.Spec.Sec3.Theorem17.Hashing
public import ThreeSumApsp.Spec.Sec3.Theorem17.ZOrder
public import ThreeSumApsp.Util.Sum

/-!
# Strassen's algorithm on lists, and the count of the proof of Theorem 17

Proof of Theorem 17: "Computing PQ takes […] O(n^{log₂ 7}) with Strassen's algorithm".
`strassenList` multiplies two `2^K × 2^K` matrices over `ℤ[x]/(x^p - 1)`, given as lists in Z-order,
and `countOf` reads the number of triples `(a,b,c)` with `S(a,b,c) = w(a,b) + w(b,c) + w(a,c) ≡ 0
(mod p)` off the product.

1. `zRing hp K α` is the list of the matrix `α` over the ring.  The operations on lists are the
   operations of the ring, entry by entry (`zRing_add`, `zRing_sub`), and the quadrants of a matrix
   are the quarters of its list (`quarter_zRing`, `zRing_succ`).
2. `strassenList_zRing`: the algorithm computes the product.  By induction on `K`; Strassen's seven
   products give the four quadrants of the product by an identity that holds summand by summand.
   It makes `7^K` multiplications in the ring, which is `O(n^{log₂ 7})` (`seven_pow_clog_le`).
3. The lists that the routine fills are the matrices `P` and `Q` of the proof of Theorem 17, padded
   with zeros to `2^K` rows and columns (`matPList_eq_zRing`, `matQList_eq_zRing`), and the padding
   does not change the entries of the product (`sum_padP_mul_padQ`).
4. `countOf_eq`: the count is the count of the proof of Theorem 17.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

open Finset

/-! ## Matrices over the ring, as lists -/

section Ring

variable {p : ℕ} (hp : p ≠ 0) (K : ℕ)

/-- A matrix over the ring as a list in Z-order. -/
noncomputable def zRing (α : ℕ → ℕ → CyclicRing p) : List ℤ :=
  zList K fun a c => cycVec hp (α a c)

/-- The list of a sum of matrices. -/
theorem zRing_add (α β : ℕ → ℕ → CyclicRing p) :
    vadd (zRing hp K α) (zRing hp K β) = zRing hp K fun a c => α a c + β a c := by
  unfold zRing zList vadd
  rw [List.zipWith_flatMap_range _ _ _ _ (fun _ => length_cycVec hp _) fun _ => length_cycVec hp _]
  exact List.flatMap_congr fun z _ => (cycVec_add hp _ _).symm

/-- The list of a difference of matrices. -/
theorem zRing_sub (α β : ℕ → ℕ → CyclicRing p) :
    vsub (zRing hp K α) (zRing hp K β) = zRing hp K fun a c => α a c - β a c := by
  unfold zRing zList vsub
  rw [List.zipWith_flatMap_range _ _ _ _ (fun _ => length_cycVec hp _) fun _ => length_cycVec hp _]
  exact List.flatMap_congr fun z _ => (cycVec_sub hp _ _).symm

/-- The quadrants of a matrix are the quarters of its list. -/
theorem quarter_zRing (α : ℕ → ℕ → CyclicRing p) {t : ℕ} (ht : t < 4) :
    quarter (4 ^ K * p) t (zRing hp (K + 1) α) =
      zRing hp K fun a c => α (a + t / 2 * 2 ^ K) (c + t % 2 * 2 ^ K) :=
  quarter_zList _ (fun _ _ => length_cycVec hp _) ht

/-- A matrix is put together from its four quadrants. -/
theorem zRing_succ (α : ℕ → ℕ → CyclicRing p) :
    zRing hp (K + 1) α =
      zRing hp K (fun a c => α a c) ++ zRing hp K (fun a c => α a (c + 2 ^ K)) ++
      zRing hp K (fun a c => α (a + 2 ^ K) c) ++ zRing hp K fun a c => α (a + 2 ^ K) (c + 2 ^ K) :=
  zList_succ _ fun _ _ => length_cycVec hp _

end Ring

/-! ## Strassen's algorithm -/

/-- The zero vector. -/
abbrev zeros (len : ℕ) : List ℤ := List.replicate len 0

/-- The list that vlin writes. -/
def vlinList (s : ℤ) (A B : List ℤ) : List ℤ := List.zipWith (fun x y => x + s * y) A B

/-- With s = 1 it is the sum. -/
theorem vlinList_one (A B : List ℤ) : vlinList 1 A B = vadd A B := by
  simp [vlinList, vadd]

/-- With s = -1 it is the difference. -/
theorem vlinList_neg_one (A B : List ℤ) : vlinList (-1) A B = vsub A B := by
  unfold vlinList vsub
  lia

/-- The list that vlin writes is as long as its operands. -/
theorem length_vlinList (s : ℤ) {A B : List ℤ} {n : ℕ} (hA : A.length = n) (hB : B.length = n) :
    (vlinList s A B).length = n := by
  simp [vlinList, hA, hB]

/-- With the sign 0 the first operand is kept. -/
theorem vlinList_zero {A B : List ℤ} (h : A.length = B.length) : vlinList 0 A B = A := by
  apply List.ext_getElem
  · simp [vlinList, h]
  · intro i h1 h2
    simp [vlinList]

/-- Adding a list to zeros gives the list. -/
theorem vlinList_zeros_left {q : ℕ} {B : List ℤ} (h : B.length = q) :
    vlinList 1 (zeros q) B = B := by
  apply List.ext_getElem <;> simp [vlinList, h]

/-- A row of the table of Strassen's seven products.  With a[t], b[t] and c[t] for the quarters
number t of the operands and of the result, the product is
M = (a[a1] + sA a[a2]) · (b[b1] + sB b[b2]), and s1 M is added to c[c1] and s2 M to c[c2]. -/
structure PhaseRow : Type where
  (a1 a2 : ℕ) (sA : ℤ) (b1 b2 : ℕ) (sB : ℤ) (c1 : ℕ) (s1 : ℤ) (c2 : ℕ) (s2 : ℤ)

/-- The entries of a row are numbers of quarters and signs, and the two results are different
quarters. -/
structure PhaseRow.Ok (row : PhaseRow) : Prop where
  a1 : row.a1 < 4
  a2 : row.a2 < 4
  b1 : row.b1 < 4
  b2 : row.b2 < 4
  c1 : row.c1 < 4
  c2 : row.c2 < 4
  ne : row.c1 ≠ row.c2
  sA : |row.sA| ≤ 1
  sB : |row.sB| ≤ 1
  s1 : |row.s1| ≤ 1
  s2 : |row.s2| ≤ 1

/-- The operands and updates for each of Strassen's seven products. -/
def phaseTable : List PhaseRow :=
  [⟨0, 3, 1, 0, 3, 1, 0, 1, 3, 1⟩, ⟨2, 3, 1, 0, 0, 0, 2, 1, 3, -1⟩,
   ⟨0, 0, 0, 1, 3, -1, 1, 1, 3, 1⟩, ⟨3, 3, 0, 2, 0, -1, 0, 1, 2, 1⟩,
   ⟨0, 1, 1, 3, 3, 0, 0, -1, 1, 1⟩, ⟨2, 0, -1, 0, 1, 1, 3, 1, 0, 0⟩,
   ⟨1, 3, -1, 2, 3, 1, 0, 1, 3, 0⟩]

theorem PhaseRow.of_mem {row : PhaseRow} (h : row ∈ phaseTable) : row.Ok := by
  simp [phaseTable] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> decide

/-- The two linear combinations fed to one recursive product. -/
def phaseProduct (mul : List ℤ → List ℤ → List ℤ) (q : ℕ) (A B : List ℤ) (row : PhaseRow) :
    List ℤ :=
  mul (vlinList row.sA (quarter q row.a1 A) (quarter q row.a2 A))
    (vlinList row.sB (quarter q row.b1 B) (quarter q row.b2 B))

/-- Accumulate a phase into its two destination quarters. -/
def PhaseRow.accum (row : PhaseRow) (L : ℕ → List ℤ) (M : List ℤ) : ℕ → List ℤ :=
  Function.update (Function.update L row.c1 (vlinList row.s1 (L row.c1) M))
    row.c2 (vlinList row.s2 (L row.c2) M)

/-- Strassen's algorithm [Str69] in Z-order, over `ℤ[x]/(x^p - 1)`. -/
def strassenList (p : ℕ) : ℕ → List ℤ → List ℤ → List ℤ
  | 0, A, B => cconv p A B
  | j + 1, A, B =>
    let q := 4 ^ j * p
    let C := phaseTable.foldl (fun L row => row.accum L (phaseProduct (strassenList p j) q A B row))
      (fun _ => zeros q)
    C 0 ++ C 1 ++ C 2 ++ C 3

private theorem length_zRing {p : ℕ} (hp : p ≠ 0) (j : ℕ) (α : ℕ → ℕ → CyclicRing p) :
    (zRing hp j α).length = 4 ^ j * p := length_zList _ _ fun _ _ => length_cycVec hp _

/-- A sum over twice as many indices. -/
private theorem sum_range_two_pow_succ {R : Type} [AddCommMonoid R] (K : ℕ) (f : ℕ → R) :
    ∑ c ∈ range (2 ^ (K + 1)), f c =
      ∑ c ∈ range (2 ^ K), f c + ∑ c ∈ range (2 ^ K), f (c + 2 ^ K) := by
  rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
  lia

/-- **Strassen's algorithm computes the product**, for matrices over the ring. -/
theorem strassenList_zRing {p : ℕ} (hp : p ≠ 0) (K : ℕ) (α β : ℕ → ℕ → CyclicRing p) :
    strassenList p K (zRing hp K α) (zRing hp K β) =
      zRing hp K fun a b => ∑ c ∈ range (2 ^ K), α a c * β c b := by
  induction K generalizing α β with
  | zero => simp [strassenList, zRing, zList, zRow_zero, zCol_zero, cycVec_mul]
  | succ K ih =>
    -- The quarters of the two lists are the quadrants, and the seven products are products.
    have hq0 := fun γ => quarter_zRing hp K γ (show 0 < 4 by norm_num)
    have hq1 := fun γ => quarter_zRing hp K γ (show 1 < 4 by norm_num)
    have hq2 := fun γ => quarter_zRing hp K γ (show 2 < 4 by norm_num)
    have hq3 := fun γ => quarter_zRing hp K γ (show 3 < 4 by norm_num)
    simp only [Nat.reduceDiv, Nat.reduceMod, Nat.zero_mul, Nat.one_mul, Nat.add_zero]
      at hq0 hq1 hq2 hq3
    have lin0 (α β : ℕ → ℕ → CyclicRing p) :
        vlinList 0 (zRing hp K α) (zRing hp K β) = zRing hp K α :=
      vlinList_zero (by simp only [length_zRing])
    have linz (α : ℕ → ℕ → CyclicRing p) := vlinList_zeros_left (length_zRing hp K α)
    simp only [strassenList, phaseTable, List.foldl_cons, List.foldl_nil, PhaseRow.accum,
      Function.update_apply, phaseProduct,
      Nat.reduceEqDiff, reduceIte, OfNat.zero_ne_ofNat, OfNat.ofNat_ne_zero,
      OfNat.one_ne_ofNat, OfNat.ofNat_ne_one, zero_ne_one, one_ne_zero,
      hq0, hq1, hq2, hq3, lin0, linz, vlinList_one, vlinList_neg_one,
      zRing_add, zRing_sub, ih]
    -- Strassen's identities, one for each quadrant of the product, summand by summand.
    rw [zRing_succ]
    refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_) ?_ <;>
      refine congrArg (zRing hp K) (funext₂ fun a b => ?_) <;>
      rw [sum_range_two_pow_succ] <;>
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib] <;>
      exact Finset.sum_congr rfl fun c _ => by ring

/-- `strassenList p K` calls `cconv` seven times per level, `7^K` times in all.  For `K = ⌈log₂ n⌉`
this is the `O(n^{log₂ 7})` of the proof of Theorem 17: `7^{⌈log₂ n⌉} ≤ 7 n^{log₂ 7}`. -/
theorem seven_pow_clog_le {n : ℕ} (hn : 1 ≤ n) :
    (7 : ℝ) ^ Nat.clog 2 n ≤ 7 * (n : ℝ) ^ Real.logb 2 7 := by
  simpa using Real.pow_clog_le_mul_rpow_logb 2 hn (c := 7) (by norm_num)

/-! ## The count of the proof of Theorem 17 -/

/-- A padded matrix of residue monomials, in ordinary or transposed orientation. -/
def matList (tr : Bool) (n p K : ℕ) (R : List ℕ) : List ℤ :=
  zList K fun a c => if a < n ∧ c < n then
    vunit p (R.getD (if tr then c * n + a else a * n + c) 0) else zeros p

abbrev matPList := matList false
abbrev matQList := matList true

/-- Proof of Theorem 17: "the sum over the pairs (a,b) ∈ A × B of the coefficient of x^{-w(a,b) mod
p} in (PQ)[a,b]"; `RM` is `PQ` in Z-order. -/
def countBy (n p : ℕ) (RM : List ℤ) (RAB : List ℕ) : ℤ :=
  ((List.range (n * n)).map fun i =>
    RM.getD (zIdx (i / n) (i % n) * p + (p - RAB.getD i 0) % p) 0).sum

/-- The number `F(p) + Z₀` of triples with `p ∣ S(a,b,c)`, computed as in the proof of Theorem 17.
-/
def countOf (n p : ℕ) (AB BC AC : List ℤ) : ℤ :=
  let K := Nat.clog 2 n
  countBy n p (strassenList p K (matPList n p K (residList p AC)) (matQList n p K (residList p BC)))
    (residList p AB)

section Count

variable {n : ℕ} (T : TriangleInstance ℤ n) {p : ℕ}

/-- The matrix `P` of the proof of Theorem 17, padded with zeros. -/
noncomputable def padP (p : ℕ) (a c : ℕ) : CyclicRing p :=
  if h : a < n ∧ c < n then T.matP p ⟨a, h.1⟩ ⟨c, h.2⟩ else 0

/-- The matrix `Q` of the proof of Theorem 17, padded with zeros. -/
noncomputable def padQ (p : ℕ) (c b : ℕ) : CyclicRing p :=
  if h : c < n ∧ b < n then T.matQ p ⟨c, h.1⟩ ⟨b, h.2⟩ else 0

/-- The padding does not change the entries of the product. -/
theorem sum_padP_mul_padQ (p : ℕ) {N : ℕ} (hN : n ≤ N) (a b : Fin n) :
    ∑ c ∈ range N, padP T p a c * padQ T p c b = (T.matP p * T.matQ p) a b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hpad : ∑ x ∈ range k, padP T p a (n + x) * padQ T p (n + x) b = 0 :=
    Finset.sum_eq_zero fun x _ => by simp [padP]
  rw [Finset.sum_range_add, hpad, add_zero, Matrix.mul_apply, Finset.sum_range]
  exact Finset.sum_congr rfl fun c _ => by simp [padP, padQ]

variable (n) (AB BC AC : List ℤ)

/-- The first list that the routine fills is the matrix `P`, padded. -/
theorem matPList_eq_zRing (hp : p ≠ 0) (K : ℕ) :
    matPList n p K (residList p AC) = zRing hp K (padP (triOf n AB BC AC) p) := by
  refine congrArg (zList K) (funext₂ fun a c => ?_)
  rw [padP]
  simp only [Bool.false_eq_true, if_false]
  split_ifs with h
  · rw [cycVec_matP, getD_residList]
    rfl
  · exact (cycVec_zero hp).symm

/-- The second list that the routine fills is the matrix `Q`, padded. -/
theorem matQList_eq_zRing (hp : p ≠ 0) (K : ℕ) :
    matQList n p K (residList p BC) = zRing hp K (padQ (triOf n AB BC AC) p) := by
  refine congrArg (zList K) (funext₂ fun c b => ?_)
  rw [padQ]
  simp only [if_true]
  split_ifs with h
  · rw [cycVec_matQ, getD_residList]
    rfl
  · exact (cycVec_zero hp).symm

/-- **The count of the proof of Theorem 17**: `countOf`, computed with Strassen's algorithm from the
three lists of weights, is the number of triples `(a,b,c)` with `S(a,b,c) ≡ 0 (mod p)`. -/
theorem countOf_eq (hp : p ≠ 0) :
    countOf n p AB BC AC = (triOf n AB BC AC).countZeroMod p := by
  have hnK : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
  -- The two lists are `P` and `Q`, padded (step 3), and Strassen's algorithm gives their product
  -- (step 2); both sides become sums over the pairs `(a, b)`.
  rw [countZeroMod_eq _ hp, countOf, matPList_eq_zRing n AB BC AC hp,
    matQList_eq_zRing n AB BC AC hp, strassenList_zRing, countBy, List.sum_map_range, sum_range_mul,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun b _ => ?_
  -- The place `a n + b` has row `a` and column `b`; `(p - r) % p` is the residue of `-w(a,b)`; the
  -- number read from the list is that coefficient of `(PQ)[a,b]`.
  rw [Nat.mul_add_div_of_lt b.isLt, Nat.mul_add_mod_of_lt b.isLt, getD_residList, ← resid_neg hp,
    zRing,
    getD_zList _ (fun _ _ => length_cycVec hp _) (a.isLt.trans_le hnK) (b.isLt.trans_le hnK)
      (resid_lt hp _),
    sum_padP_mul_padQ _ p hnK a b]
  rfl

end Count

end ThreeSumApsp.Spec
