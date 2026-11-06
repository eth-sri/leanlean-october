/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Spec.Sec2.Theorem5.Alphabets
public import Mathlib.Data.List.GetD

/-!
# Arrays on strings as lists

Section 2.3.1: "An array a on the left strings of length L assigns an integer a[u] to each u that is
a left string of length L."  In a program such an array is a list: an array on the strings of length
`n` over an alphabet of `b` letters is the list of its `b^n` entries in the order of the codes
(`arrStr`), so the entry at a string is the entry of the list at the code of the string
(`getD_arrStr`), and an entry of the list is 0 if the array is 0 at the string with that code
(`getD_arrStr_eq_zero`).  The arrays on left strings, on right strings and on leaves are the cases
`arrL`, `arrR` and `arrT`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Arrays on the strings over any numbered alphabet -/

section
variable {α : Type} {b : ℕ} (e : α ≃ Fin b) [NeZero b] {n : ℕ} (a : (Fin n → α) → ℤ)

/-- An array on the strings of length `n` over an alphabet numbered by `e : α ≃ Fin b`, as the list
of its `b^n` entries in the order of the codes. -/
def arrStr :=
  (List.range (b ^ n)).map fun c => a (decodeStr e n c)

/-- The list has `b^n` entries. -/
theorem length_arrStr : (arrStr e a).length = b ^ n := by
  simp [arrStr]

/-- The entry of the list at a number below `b^n`. -/
theorem getD_arrStr_of_lt {c} (hc : c < b ^ n) :
    (arrStr e a).getD c 0 = a (decodeStr e n c) := by
  simp_all [arrStr]

/-- The entry at a string is the entry of the list at its code. -/
theorem getD_arrStr u : (arrStr e a).getD (codeStr e u) 0 = a u := by
  grind [getD_arrStr_of_lt, codeStr_lt, decodeStr_codeStr]

/-- The entry of the list at `c` is 0 if the array is 0 at every string with the code `c`. -/
theorem getD_arrStr_eq_zero {c} (h : ∀ u, codeStr e u = c → a u = 0) :
    (arrStr e a).getD c 0 = 0 := by
  grind [getD_arrStr_of_lt, codeStr_decodeStr, length_arrStr]

end

/-! ## The three kinds of arrays of Section 2 that the programs store -/

/-- An array on the left strings of length `n`, as the list of its `7^n` entries. -/
def arrL {n} (a : LeftStr n → ℤ) := arrStr leftEquiv a

/-- An array on the right strings of length `n`, as the list of its `7^n` entries. -/
def arrR {n} (b : RightStr n → ℤ) := arrStr rightEquiv b

/-- An array on the leaves (for example an encoding), as the list of its `10^n` entries. -/
def arrT {n} (enc : Leaf n → ℤ) := arrStr termEquiv enc

/-- The list of an array on the left strings has `7^n` entries. -/
def length_arrL {n} (a : LeftStr n → ℤ) :=
  length_arrStr leftEquiv a

/-- The list of an array on the right strings has `7^n` entries. -/
def length_arrR {n} (b : RightStr n → ℤ) :=
  length_arrStr rightEquiv b

/-- The entry at a left string is the entry of the list at its code. -/
theorem getD_arrL {n} a (u : LeftStr n) : (arrL a).getD (codeL u) 0 = a u :=
  getD_arrStr leftEquiv a u

/-- The entry at a right string is the entry of the list at its code. -/
theorem getD_arrR {n} b (v : RightStr n) :
    (arrR b).getD (codeR v) 0 = b v :=
  getD_arrStr rightEquiv b v

/-- The entry at a leaf is the entry of the list at its code. -/
theorem getD_arrT {n} enc (τ : Leaf n) :
    (arrT enc).getD (codeT τ) 0 = enc τ :=
  getD_arrStr termEquiv enc τ

end ThreeSumApsp.Spec
