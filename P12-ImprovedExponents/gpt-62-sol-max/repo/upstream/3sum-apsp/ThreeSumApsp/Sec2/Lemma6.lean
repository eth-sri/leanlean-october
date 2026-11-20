/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Ring

/-!
# Lemma 6: Schönhage's identity

Sections 2.1 and 2.2. After Strassen's identity (equation (1)), which the paper
recalls, this file treats Schönhage's. It has ten terms `λ`, each the product of a linear form `φ_λ`
in the seven left variables, a linear form `ψ_λ` in the seven right variables and a linear form
`χ_λ` in the ten output variables. Lemma 6 says that `∑_λ φ_λ ψ_λ χ_λ = G + E`, an identity of
polynomials in the 24 variables: `G` holds the outer product and the inner product that are wanted,
and `E` is an error.

* A linear form is the vector of its coefficients. `formL`, `formR` and `formO` turn it into a
  polynomial, and they are linear (`formL_eq_linearCombination` and its two companions).
* The proof of `lemma_6` is the paper's. The coefficient of `z_ij` comes only from the term `P_ij`.
  In the coefficient of `z₀` the products `x_i y_j` cancel, the cross terms vanish because the
  columns of `p̂` and the rows of `q̂` sum to zero (`pHat_column_sum`, `qHat_row_sum`), and what
  remains is the inner product (`sum_pHat_mul_qHat`).
* Second observation after the lemma: every term contributes to `z₀`, and only `P_ij` contributes to
  `z_ij` (`Term.contributes_z0`, `Term.contributes_z_iff`).

The later files on Section 2 use the second observation and the coefficients of the forms; none of
their proofs uses `lemma_6`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### The alphabets -/

/-- The left variables, listed: `x i` is `.inl i`, and `p i j` is `.inr (i, j)`. -/
def LeftVar.equiv : LeftVar ≃ Fin 3 ⊕ Fin 2 × Fin 2 where
  toFun
    | .x i => .inl i
    | .p i j => .inr (i, j)
  invFun
    | .inl i => .x i
    | .inr (i, j) => .p i j
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with _ | ⟨_, _⟩ <;> rfl

/-- The right variables, listed: `y j` is `.inl j`, and `q i j` is `.inr (i, j)`. -/
def RightVar.equiv : RightVar ≃ Fin 3 ⊕ Fin 2 × Fin 2 where
  toFun
    | .y j => .inl j
    | .q i j => .inr (i, j)
  invFun
    | .inl j => .y j
    | .inr (i, j) => .q i j
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | ⟨_, _⟩ <;> rfl

/-- The terms, listed: `P i j` is `some (i, j)`, and `P0` is `none`. -/
def Term.equiv : Term ≃ Option (Fin 3 × Fin 3) where
  toFun
    | .P i j => some (i, j)
    | .P0 => none
  invFun
    | some (i, j) => .P i j
    | none => .P0
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | ⟨_, _⟩ <;> rfl

/-- Section 2.2: there are "seven left variables". -/
theorem card_leftVar : Fintype.card LeftVar = 7 := by
  simp [Fintype.card_congr LeftVar.equiv]

/-- Section 2.2: there are "seven right variables". -/
theorem card_rightVar : Fintype.card RightVar = 7 := by
  simp [Fintype.card_congr RightVar.equiv]

/-- Section 2.2: "Schönhage's identity has ten terms". -/
theorem card_term : Fintype.card Term = 10 := by
  simp [Fintype.card_congr Term.equiv]

/-! ### Linear forms as polynomials -/

/-! ### Lemma 6 -/

/-! ### Which terms contribute to which output variables -/

/-- Section 2.2, second observation: "every term contributes to z₀". -/
@[simp]
theorem Term.contributes_z0 (lam : Term) : lam.Contributes .z0 := by
  cases lam <;> simp [Term.Contributes, chi, zForm, z0Form]

/-- Section 2.2, second observation: "only P_ij contributes to z_ij". -/
@[simp]
theorem Term.contributes_z_iff (lam : Term) (i j : Fin 3) :
    lam.Contributes (.z i j) ↔ lam = .P i j := by
  cases lam <;> simp [Term.Contributes, chi, zForm, z0Form, Pi.single_apply, eq_comm]

/-- The second observation in one statement: a term contributes to `z` if and only if `z` is inner,
that is `z₀`, or the term is `z.privateTerm`, which is `P_ij` for `z = z_ij`. (This is the term that
the private leaf of Section 2.4.3 has at a level with the variable `z`.) -/
theorem Term.contributes_iff (lam : Term) (z : OutVar) :
    lam.Contributes z ↔ z.IsInner ∨ lam = z.privateTerm := by
  decide +revert

/-- A sum over the terms contributing to `z` has the one summand `P_ij` for `z = z_ij`, and runs
over all terms for `z = z₀`. This is how step (4) of the recursions assembles the slice at `z`. -/
theorem Term.sum_contributes {A : Type*} [AddCommMonoid A] (c : Term → A) (z : OutVar) :
    ∑ lam : Term with lam.Contributes z, c lam
      = match z with
        | .z i j => c (.P i j)
        | .z0 => ∑ lam, c lam := by
  cases z with
  | z i j => simp [filter_eq']
  | z0 => simp

end ThreeSumApsp
