module

public import PaperStatements
public import ThreeSumApsp.Util.Digits
public import Mathlib.Data.List.GetD

@[expose] public section

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
def leftEquiv : LeftVar ≃ Fin 7 where
  toFun := leftIdx
  invFun := leftOfIdx
  left_inv := by decide
  right_inv := by decide

/-- The right variables and their digits. -/
def rightEquiv : RightVar ≃ Fin 7 where
  toFun := rightIdx
  invFun := rightOfIdx
  left_inv := by decide
  right_inv := by decide

/-- The output variables and their digits. -/
def outEquiv : OutVar ≃ Fin 10 where
  toFun := outIdx
  invFun := outOfIdx
  left_inv := by decide
  right_inv := by decide

/-- The terms and their digits. -/
def termEquiv : Term ≃ Fin 10 where
  toFun := termIdx
  invFun := termOfIdx
  left_inv := by decide
  right_inv := by decide

/-- The term with the digit `t`, for a natural number `t` below 10 (and `P₀` from 10 on). -/
def termOfNat (t : ℕ) : Term := if h : t < 10 then termEquiv.symm ⟨t, h⟩ else .P0

/-- The digit of the term with the digit `t`. -/
theorem termIdx_termOfNat {t : ℕ} (h : t < 10) : ((termIdx (termOfNat t) : Fin 10) : ℕ) = t := by
  rw [termOfNat, dif_pos h]
  exact congrArg Fin.val (termEquiv.apply_symm_apply ⟨t, h⟩)

/-- The index pairs and their digits. -/
def pairEquiv : Fin 2 × Fin 2 ≃ Fin 4 where
  toFun := pairIdx
  invFun := pairOfIdx
  left_inv := by decide
  right_inv := by decide

/-! Applying one of the five bijections gives the digit. -/

@[simp] theorem outEquiv_apply (z : OutVar) : outEquiv z = outIdx z := rfl

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

/-- The code of the term `λ` followed by the vertex `τ'`. -/
theorem codeT_cons {n : ℕ} (lam : Term) (τ' : Vertex n) :
    codeT (Fin.cons lam τ' : Vertex (n + 1)) = termIdx lam * 10 ^ n + codeT τ' :=
  codeStr_cons termEquiv lam τ'

/-- The code of a vertex at depth `n` is less than `10^n`. -/
theorem codeT_lt {n : ℕ} (τ : Vertex n) : codeT τ < 10 ^ n :=
  codeStr_lt termEquiv τ

/-! ## The structure of the identity, in digits -/

/-- An output variable is inner exactly if its digit is 9. -/
theorem outVar_isInner_iff (z : OutVar) : z.IsInner ↔ (outIdx z : ℕ) = 9 := by
  revert z
  decide

/-- A term contributes to an output variable exactly if the variable has the digit 9 or the two
digits are equal. -/
theorem contributes_iff (lam : Term) (z : OutVar) :
    lam.Contributes z ↔ (outIdx z : ℕ) = 9 ∨ (termIdx lam : ℕ) = (outIdx z : ℕ) := by
  revert lam z
  decide

/-- The digit of `z_ij` is `3 (i - 1) + (j - 1)`. -/
theorem outIdx_z (i j : Fin 3) : ((outIdx (.z i j) : Fin 10) : ℕ) = 3 * i + j := rfl

/-- The digit of `z₀` is 9. -/
theorem outIdx_z0 : ((outIdx .z0 : Fin 10) : ℕ) = 9 := rfl

/-- The digit of `P₀` is 9. -/
theorem termIdx_P0 : ((termIdx .P0 : Fin 10) : ℕ) = 9 := rfl

/-- The digit of the inner left variable `p_ij` is 3 plus the digit of the pair `(i, j)`. -/
theorem leftIdx_p (i j : Fin 2) : (leftIdx (.p i j) : ℕ) = 3 + pairIdx (i, j) :=
  Nat.add_assoc _ _ _

/-- The digit of the inner right variable `q_ij` is 3 plus the digit of the pair `(i, j)`. -/
theorem rightIdx_q (i j : Fin 2) : (rightIdx (.q i j) : ℕ) = 3 + pairIdx (i, j) :=
  Nat.add_assoc _ _ _

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
theorem phiFlat_spec (lam : Term) (s : LeftVar) :
    phiFlat.getD (7 * (termIdx lam : ℕ) + (leftIdx s : ℕ)) 0 = phi lam s := by
  revert lam s
  decide

/-- The entry number `7 λ + t` of the table, by digits, is the coefficient `ψ_λ(t)`. -/
theorem psiFlat_spec (lam : Term) (t : RightVar) :
    psiFlat.getD (7 * (termIdx lam : ℕ) + (rightIdx t : ℕ)) 0 = psi lam t := by
  revert lam t
  decide



/-! ## Arrays on the strings over any numbered alphabet -/

section
variable {α : Type} {b : ℕ} (e : α ≃ Fin b) [NeZero b] {n : ℕ} (a : (Fin n → α) → ℤ)

/-- An array on the strings of length `n` over an alphabet numbered by `e : α ≃ Fin b`, as the list
of its `b^n` entries in the order of the codes. -/
def arrStr : List ℤ :=
  (List.range (b ^ n)).map fun c => a (decodeStr e n c)

/-- The list has `b^n` entries. -/
theorem length_arrStr : (arrStr e a).length = b ^ n := by
  simp [arrStr]

/-- The entry of the list at a number below `b^n`. -/
theorem getD_arrStr_of_lt {c : ℕ} (hc : c < b ^ n) :
    (arrStr e a).getD c 0 = a (decodeStr e n c) := by
  rw [List.getD_eq_getElem _ _ (by rwa [length_arrStr])]
  simp [arrStr]

/-- The entry at a string is the entry of the list at its code. -/
theorem getD_arrStr (u : Fin n → α) : (arrStr e a).getD (codeStr e u) 0 = a u := by
  rw [getD_arrStr_of_lt e a (codeStr_lt e u), decodeStr_codeStr]

/-- The entry of the list at `c` is 0 if the array is 0 at every string with the code `c`. -/
theorem getD_arrStr_eq_zero {c : ℕ} (h : ∀ u, codeStr e u = c → a u = 0) :
    (arrStr e a).getD c 0 = 0 := by
  rcases Nat.lt_or_ge c (b ^ n) with hlt | hge
  · rw [getD_arrStr_of_lt e a hlt]
    exact h _ (codeStr_decodeStr e hlt)
  · exact List.getD_eq_default _ _ (by rwa [length_arrStr])

end

/-! ## The three kinds of arrays of Section 2 that the programs store -/

/-- An array on the left strings of length `n`, as the list of its `7^n` entries. -/
def arrL {n : ℕ} (a : LeftStr n → ℤ) : List ℤ := arrStr leftEquiv a

/-- An array on the right strings of length `n`, as the list of its `7^n` entries. -/
def arrR {n : ℕ} (b : RightStr n → ℤ) : List ℤ := arrStr rightEquiv b

/-- An array on the leaves (for example an encoding), as the list of its `10^n` entries. -/
def arrT {n : ℕ} (enc : Leaf n → ℤ) : List ℤ := arrStr termEquiv enc

/-- The list of an array on the left strings has `7^n` entries. -/
theorem length_arrL {n : ℕ} (a : LeftStr n → ℤ) : (arrL a).length = 7 ^ n :=
  length_arrStr leftEquiv a

/-- The list of an array on the right strings has `7^n` entries. -/
theorem length_arrR {n : ℕ} (b : RightStr n → ℤ) : (arrR b).length = 7 ^ n :=
  length_arrStr rightEquiv b

/-- The entry at a left string is the entry of the list at its code. -/
theorem getD_arrL {n : ℕ} (a : LeftStr n → ℤ) (u : LeftStr n) : (arrL a).getD (codeL u) 0 = a u :=
  getD_arrStr leftEquiv a u

/-- The entry at a right string is the entry of the list at its code. -/
theorem getD_arrR {n : ℕ} (b : RightStr n → ℤ) (v : RightStr n) :
    (arrR b).getD (codeR v) 0 = b v :=
  getD_arrStr rightEquiv b v

/-- The entry at a leaf is the entry of the list at its code. -/
theorem getD_arrT {n : ℕ} (enc : Leaf n → ℤ) (τ : Leaf n) :
    (arrT enc).getD (codeT τ) 0 = enc τ :=
  getD_arrStr termEquiv enc τ

end ThreeSumApsp.Spec
