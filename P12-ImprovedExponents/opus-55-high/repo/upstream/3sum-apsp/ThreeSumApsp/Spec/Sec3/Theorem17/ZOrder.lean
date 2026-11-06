/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Util.List
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Matrices in Z-order (Morton order)

The count of the proof of Theorem 17 needs a product of matrices over `ℤ[x]/(x^p - 1)`, "O(n^{log₂
7}) with Strassen's algorithm".  For the recursion of that algorithm a `2^K × 2^K` matrix is stored
in Z-order: the entry `(a, c)` stands at the place whose digits in base 4 are `2 a_i + c_i`, where
`a_i` and `c_i` are the binary digits of `a` and `c`.

* Places: `zIdx` maps a pair to its place, `zRow` and `zCol` map back (`zRow_zIdx`, `zCol_zIdx`,
  `zIdx_zRow_zCol`).  All three are computed one digit in base 4 at a time (`zIdx_eq`, `zRow_eq`,
  `zCol_eq`), and every proof is an induction along these equations.
* Lists: the entry `(a, c)` of `zList K M` starts at `zIdx a c * p` (`getD_zList`).
* **The four quadrants of a matrix are the four quarters of its list** (`quarter_zList`,
  `zList_succ`), which is what the recursion needs.
-/


namespace ThreeSumApsp.Spec

/-! ## Places -/

/-- The binary digits of `i`, moved to the even places: the number with the same digits in
base 4. -/
def spread (i : ℕ) : ℕ := Nat.ofDigits 4 (Nat.digits 2 i)

/-- The table of `spread`. -/
def spreadList (N2 : ℕ) : List ℤ := (List.range N2).map fun i : ℕ => ((spread i : ℕ) : ℤ)

/-- The place of the entry `(a, c)` in Z-order. -/
def zIdx (a c : ℕ) : ℕ := 2 * spread a + spread c

/-- The row of the entry at place `z`. -/
def zRow (z : ℕ) : ℕ := Nat.ofDigits 2 ((Nat.digits 4 z).map (· / 2))

/-- The column of the entry at place `z`. -/
def zCol (z : ℕ) : ℕ := Nat.ofDigits 2 ((Nat.digits 4 z).map (· % 2))

/-- The last binary digit goes to the last digit in base 4. -/
theorem spread_eq (i : ℕ) : spread i = i % 2 + 4 * spread (i / 2) := by
  rcases i.eq_zero_or_pos with rfl | hi
  · rfl
  · unfold spread
    aesop

variable (z : ℕ)


/-- The row, one digit in base 4 at a time. -/
theorem zRow_eq : zRow z = z % 4 / 2 + 2 * zRow (z / 4) := by
  rcases z.eq_zero_or_pos with rfl | hz
  · rfl
  · unfold zRow
    aesop

/-- The column, one digit in base 4 at a time. -/
theorem zCol_eq : zCol z = z % 4 % 2 + 2 * zCol (z / 4) := by
  rcases z.eq_zero_or_pos with rfl | hz
  · rfl
  · unfold zCol
    aesop

/-- The place 0 is in row 0. -/
theorem zRow_zero : zRow 0 = 0 := by rfl

/-- The place 0 is in column 0. -/
theorem zCol_zero : zCol 0 = 0 := by rfl

/-- The place, one digit in base 4 at a time. -/
theorem zIdx_eq (a c : ℕ) : zIdx a c = (2 * (a % 2) + c % 2) + 4 * zIdx (a / 2) (c / 2) := by
  grind [zIdx, spread_eq]

variable {a c K : ℕ}

/-- The places of a `2^K × 2^K` matrix are below `4^K`. -/
theorem zIdx_lt (ha : a < 2 ^ K) (hc : c < 2 ^ K) : zIdx a c < 4 ^ K := by
  induction K generalizing a c with
  | zero =>
    aesop
  | succ K ih =>
    grind [zIdx_eq]

/-- The row and the column of the place of `(a, c)` are `a` and `c`. -/
theorem zRow_zCol_zIdx (a c : ℕ) : zRow (zIdx a c) = a ∧ zCol (zIdx a c) = c := by
  induction hm : a + c using Nat.strong_induction_on generalizing a c with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos (a + c) with h0 | hpos
    · aesop
    · rw [zRow_eq, zCol_eq, zIdx_eq]
      grind

/-- The row of the place of `(a, c)` is `a`. -/
theorem zRow_zIdx (a c : ℕ) : zRow (zIdx a c) = a := by grind [zRow_zCol_zIdx]

/-- The column of the place of `(a, c)` is `c`. -/
theorem zCol_zIdx (a c : ℕ) : zCol (zIdx a c) = c := by grind [zRow_zCol_zIdx]

/-- A place is the place of its row and its column. -/
theorem zIdx_zRow_zCol : zIdx (zRow z) (zCol z) = z := by
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    rcases z.eq_zero_or_pos with rfl | hz
    · rfl
    · rw [zIdx_eq, zRow_eq, zCol_eq]
      grind

variable {t : ℕ}

/-- The places of the quadrant number `t`: their rows and columns are those of the first quadrant,
moved by `2^K` down if `t ≥ 2` and to the right if `t` is odd. -/
theorem zRow_zCol_quadrant {z : ℕ} (ht : t < 4) (hz : z < 4 ^ K) :
    zRow (t * 4 ^ K + z) = zRow z + t / 2 * 2 ^ K ∧
      zCol (t * 4 ^ K + z) = zCol z + t % 2 * 2 ^ K := by
  induction K generalizing z with
  | zero =>
    obtain rfl : z = 0 := by omega
    rw [zRow_eq, zCol_eq, pow_zero, Nat.mul_one, Nat.add_zero, Nat.div_eq_of_lt ht, zRow_zero, zCol_zero]
    omega
  | succ K ih =>
    obtain ⟨hrow, hcol⟩ := ih (z := z / 4) (by omega)
    have hpow : t * 4 ^ (K + 1) = 4 * (t * 4 ^ K) := by grind
    rw [zRow_eq, zCol_eq, zRow_eq z, zCol_eq z, hpow,
      show (4 * (t * 4 ^ K) + z) / 4 = t * 4 ^ K + z / 4 by omega, hcol]
    grind

/-! ## Matrices as lists -/

/-- A `2^K × 2^K` matrix of vectors, as one list, entry after entry in Z-order. -/
def zList (K : ℕ) (M : ℕ → ℕ → List ℤ) : List ℤ :=
  (List.range (4 ^ K)).flatMap fun z => M (zRow z) (zCol z)

/-- The quarter number `t` of a list of length `4 q`. -/
def quarter (q t : ℕ) (l : List ℤ) : List ℤ := (l.drop (t * q)).take q

variable {p : ℕ}

/-- A matrix of vectors of length `p` has `4^K p` numbers. -/
theorem length_zList (K : ℕ) (M : ℕ → ℕ → List ℤ) (hM : ∀ a c, (M a c).length = p) :
    (zList K M).length = 4 ^ K * p :=
  List.length_flatMap_range _ _ fun _ _ => by simp_all

variable (M : ℕ → ℕ → List ℤ)

/-- The entry `(a, c)` of the matrix stands at the place `zIdx a c`. -/
theorem getD_zList {r : ℕ} (hM : ∀ a c, (M a c).length = p)
    (ha : a < 2 ^ K) (hc : c < 2 ^ K) (hr : r < p) :
    (zList K M).getD (zIdx a c * p + r) 0 = (M a c).getD r 0 := by
  grind [zList, List.getD_flatMap_range, zIdx_lt, zRow_zIdx, zCol_zIdx]

/-- **The quadrants of a matrix are the quarters of its list.** -/
theorem quarter_zList (hM : ∀ a c, (M a c).length = p)
    (ht : t < 4) :
    quarter (4 ^ K * p) t (zList (K + 1) M) =
      zList K fun a c => M (a + t / 2 * 2 ^ K) (c + t % 2 * 2 ^ K) := by
  have hsplit : 4 ^ (K + 1) = t * 4 ^ K + 4 ^ K + (3 - t) * 4 ^ K := by
    calc 4 ^ (K + 1) = (t + 1 + (3 - t)) * 4 ^ K := by
          grind
      _ = _ := by ring
  rw [quarter, zList, hsplit, ← Nat.mul_assoc,
    List.take_drop_flatMap_range _ _ _ _ fun _ _ => by simp_all]
  refine List.flatMap_congr fun z hz => ?_
  grind [zRow_zCol_quadrant]

/-- A list of length `4 q` is put together from its four quarters. -/
theorem eq_append_quarters {q : ℕ} {l : List ℤ} (hl : l.length = 4 * q) :
    l = quarter q 0 l ++ quarter q 1 l ++ quarter q 2 l ++ quarter q 3 l := by
  unfold quarter
  refine List.ext_getElem (by grind) fun i _ _ => ?_
  grind

/-- A matrix is put together from its four quadrants. -/
theorem zList_succ (hM : ∀ a c, (M a c).length = p) :
    zList (K + 1) M = zList K (fun a c => M a c) ++ zList K (fun a c => M a (c + 2 ^ K)) ++
      zList K (fun a c => M (a + 2 ^ K) c) ++ zList K fun a c => M (a + 2 ^ K) (c + 2 ^ K) := by
  have hlen : (zList (K + 1) M).length = 4 * (4 ^ K * p) := by
    rw [length_zList _ _ hM]
    ring
  conv_lhs => rw [eq_append_quarters hlen]
  simp_all [quarter_zList]
