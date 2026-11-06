/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import PaperStatements
import ThreeSumApsp.Util.Digits

/-!
# The alphabets of Schönhage's identity as digits

Section 2.2 names seven left variables, seven right variables, ten output variables and
ten terms; Section 2.3.1 indexes arrays by strings over these alphabets.  Here every
letter gets a digit, so that a string becomes a number (`codeStr`).

* The left variables `x₁ x₂ x₃ p₁₁ p₁₂ p₂₁ p₂₂` are the digits `0, …, 6`; likewise the right
  variables.
* The output variables `z₁₁ z₁₂ … z₃₃ z₀` are the digits `0, …, 9`, and the terms `P₁₁ … P₃₃ P₀`
  likewise, so that `z_ij` and `P_ij` have the same digit `3(i-1) + (j-1)`, and `z₀` and `P₀` have
  the digit 9.
* Left and right strings are numbers in base 7 (`codeL`, `codeR`), output strings, vertices and
  leaves in base 10 (`codeO`, `codeT`), strings of indices of outer variables in base 3
  (`codeOuter`) and of inner variables in base 4 (`codeInner`), always with level 1 most
  significant.
* Which output variables are inner, and which term contributes to which output variable (Section
  2.2), is read off the digits (`outVar_isInner_iff`, `contributes_iff`).
* The coefficients of the linear forms `φ_λ` and `ψ_λ` (Section 2.2) are written out as the rows of
  two 10 × 7 tables, `phiTable` and `psiTable`, which the programs store row after row
  (`phiFlat_spec`, `psiFlat_spec`).
-/


namespace ThreeSumApsp.Spec

/-! ## Digits -/

/-- The digit of a left variable. -/
def leftIdx : LeftVar → Fin 7
  | .x i => ⟨i, by omega⟩
  | .p i j => ⟨3 + 2 * i + j, by omega⟩

/-- The left variable with a given digit. -/
def leftOfIdx (k : Fin 7) : LeftVar :=
  if h : (k : ℕ) < 3 then .x ⟨k, h⟩
  else .p ⟨((k : ℕ) - 3) / 2, by omega⟩ ⟨((k : ℕ) - 3) % 2, by omega⟩

/-- The digit of a right variable. -/
def rightIdx : RightVar → Fin 7
  | .y j => ⟨j, by omega⟩
  | .q i j => ⟨3 + 2 * i + j, by omega⟩

/-- The right variable with a given digit. -/
def rightOfIdx (k : Fin 7) : RightVar :=
  if h : (k : ℕ) < 3 then .y ⟨k, h⟩
  else .q ⟨((k : ℕ) - 3) / 2, by omega⟩ ⟨((k : ℕ) - 3) % 2, by omega⟩

/-- The digit of an output variable. -/
def outIdx : OutVar → Fin 10
  | .z i j => ⟨3 * i + j, by omega⟩
  | .z0 => 9

/-- The output variable with a given digit. -/
def outOfIdx (k : Fin 10) : OutVar :=
  if h : (k : ℕ) < 9 then .z ⟨(k : ℕ) / 3, by omega⟩ ⟨(k : ℕ) % 3, by omega⟩ else .z0

/-- The digit of a term. -/
def termIdx : Term → Fin 10
  | .P i j => ⟨3 * i + j, by omega⟩
  | .P0 => 9

/-- The term with a given digit. -/
def termOfIdx (k : Fin 10) : Term :=
  if h : (k : ℕ) < 9 then .P ⟨(k : ℕ) / 3, by omega⟩ ⟨(k : ℕ) % 3, by omega⟩ else .P0

/-- The digit of an index pair `(i, j)` of an inner variable. -/
def pairIdx (p : Fin 2 × Fin 2) : Fin 4 := ⟨2 * p.1 + p.2, by omega⟩

/-- The index pair with a given digit. -/
def pairOfIdx (k : Fin 4) : Fin 2 × Fin 2 := (⟨(k : ℕ) / 2, by omega⟩, ⟨(k : ℕ) % 2, by omega⟩)

/-- The left variables and their digits. -/
def leftEquiv : LeftVar ≃ Fin 7 := ⟨leftIdx, leftOfIdx, by decide, by decide⟩

/-- The right variables and their digits. -/
def rightEquiv : RightVar ≃ Fin 7 := ⟨rightIdx, rightOfIdx, by decide, by decide⟩

/-- The output variables and their digits. -/
def outEquiv : OutVar ≃ Fin 10 := ⟨outIdx, outOfIdx, by decide, by decide⟩

/-- The terms and their digits. -/
def termEquiv : Term ≃ Fin 10 := ⟨termIdx, termOfIdx, by decide, by decide⟩

/-- The term with the digit `t`, for a natural number `t` below 10 (and `P₀` from 10 on). -/
def termOfNat (t : ℕ) : Term := if h : t < 10 then termEquiv.symm ⟨t, h⟩ else .P0

/-- The digit of the term with the digit `t`. -/
theorem termIdx_termOfNat {t : ℕ} (h : t < 10) : ((termIdx (termOfNat t) : Fin 10) : ℕ) = t := by
  rw [termOfNat, dif_pos]
  exact congrArg Fin.val (termEquiv.apply_symm_apply ⟨t, h⟩)

/-- The index pairs and their digits. -/
def pairEquiv : Fin 2 × Fin 2 ≃ Fin 4 := ⟨pairIdx, pairOfIdx, by decide, by decide⟩

/-! Applying one of the five bijections gives the digit. -/



variable (z : OutVar)

@[simp] theorem outEquiv_apply : outEquiv z = outIdx z := rfl

variable (lam : Term)


@[simp] theorem pairEquiv_apply (p : Fin 2 × Fin 2) : pairEquiv p = pairIdx p := rfl

/-! ## Codes of strings -/

/-- The code of a left string, in base 7. -/
def codeL {n : ℕ} (u : LeftStr n) : ℕ := codeStr leftEquiv u

/-- The code of a right string, in base 7. -/
def codeR {n : ℕ} (v : RightStr n) : ℕ := codeStr rightEquiv v

/-- The code of an output string, in base 10. -/
def codeO {n : ℕ} (w : OutStr n) : ℕ := codeStr outEquiv w

/-- The code of a vertex or a leaf, in base 10. -/
def codeT {n : ℕ} (τ : Vertex n) : ℕ := codeStr termEquiv τ

/-- The code of a string of indices of outer variables, in base 3. -/
def codeOuter {n : ℕ} (r : Fin n → Fin 3) : ℕ := codeStr (Equiv.refl (Fin 3)) r

/-- The code of a string of index pairs of inner variables, in base 4. -/
def codeInner {n : ℕ} (π : Fin n → Fin 2 × Fin 2) : ℕ := codeStr pairEquiv π


/-- The vertex or leaf with a given code. -/
def decodeT (n c : ℕ) : Vertex n := decodeStr termEquiv n c

/-! ### Codes of output strings and of vertices

The general facts about `codeStr`, under names of their own for the two codes that occur most. -/


/-- The code of a vertex at depth `n` is less than `10^n`. -/
theorem codeT_lt {n : ℕ} (τ : Vertex n) : codeT τ < 10 ^ n :=
  codeStr_lt termEquiv τ

/-! ## The structure of the identity, in digits -/

/-- An output variable is inner exactly if its digit is 9. -/
theorem outVar_isInner_iff : z.IsInner ↔ (outIdx z : ℕ) = 9 := by
  revert z
  decide

/-- A term contributes to an output variable exactly if the variable has the digit 9 or the two
digits are equal. -/
theorem contributes_iff (z : OutVar) :
    lam.Contributes z ↔ (outIdx z : ℕ) = 9 ∨ (termIdx lam : ℕ) = (outIdx z : ℕ) := by
  revert lam z
  decide

/-- The digit of `z_ij` is `3 (i - 1) + (j - 1)`. -/
theorem outIdx_z (i j : Fin 3) : ((outIdx (.z i j) : Fin 10) : ℕ) = 3 * i + j := rfl





/-! ## The coefficients of the linear forms, as tables -/

/-- The coefficients of the forms `φ_λ`: row `λ`, column `s`, both by digits. -/
def phiTable : List (List ℤ) :=
  [[1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0],
   [0, 0, 1, -1, 0, -1, 0], [0, 0, 1, 0, -1, 0, -1], [0, 0, 1, 0, 0, 0, 0],
   [-1, -1, -1, 0, 0, 0, 0]]

/-- The coefficients of the forms `ψ_λ`: row `λ`, column `t`, both by digits. -/
def psiTable : List (List ℤ) :=
  [[1, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, -1, -1, 0, 0],
   [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, -1, -1],
   [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
   [1, 1, 1, 0, 0, 0, 0]]

/-- The table of the coefficients `φ_λ(s)`, row after row, as a program stores it. -/
def phiFlat : List ℤ := phiTable.flatten

/-- The table of the coefficients `ψ_λ(t)`, row after row, as a program stores it. -/
def psiFlat : List ℤ := psiTable.flatten

/-- The table of the `φ_λ(s)` has 70 entries. -/
@[simp] theorem length_phiFlat : phiFlat.length = 70 := rfl

/-- The table of the `ψ_λ(t)` has 70 entries. -/
@[simp] theorem length_psiFlat : psiFlat.length = 70 := rfl

/-- The entry number `7 λ + s` of the table, by digits, is the coefficient `φ_λ(s)`. -/
theorem phiFlat_spec (s : LeftVar) :
    phiFlat.getD (7 * (termIdx lam : ℕ) + (leftIdx s : ℕ)) 0 = phi lam s := by
  revert lam s
  decide

/-- The entry number `7 λ + t` of the table, by digits, is the coefficient `ψ_λ(t)`. -/
theorem psiFlat_spec (t : RightVar) :
    psiFlat.getD (7 * (termIdx lam : ℕ) + (rightIdx t : ℕ)) 0 = psi lam t := by
  revert lam t
  decide
