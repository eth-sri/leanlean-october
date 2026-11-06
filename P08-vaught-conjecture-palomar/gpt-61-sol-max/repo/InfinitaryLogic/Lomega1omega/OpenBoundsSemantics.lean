/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import InfinitaryLogic.Lomega1omega.Operations
import InfinitaryLogic.Util

/-!
# Semantics of `openBounds` and of relabeling by `insertLastBound`

Two semantic round-trip lemmas about the bound/free variable bookkeeping of
`Lomega1omega/Operations`, in a neutral module so that consumers below the Henkin construction and
the Scott analysis can use them without importing either:

* `realize_relabel_insertLastBound_zero` — relabeling a formula with `n + 1` free variables by
  `insertLastBound` binds the last one; evaluating with `v` and a one-element bound tuple `xs` is
  evaluating the original at `snoc v (xs 0)`;
* `realize_openBounds` — `openBounds` preserves semantics: evaluating `φ.openBounds` at a free
  assignment `xs` is evaluating `φ` with bound assignment `xs`.

Both were previously proved inside `Scott/Formula.lean` and `Methods/Henkin/Construction.lean`
respectively; the statements and names are unchanged.
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {N : Type w} [L.Structure N] {n : ℕ}

open FirstOrder  Fin BoundedFormulaω


/-- Helper lemma: the composition of `Sum.elim v xs` with `relabelAux insertLastBound k`
equals `Sum.elim (snoc v (xs 0)) (xs ∘ Fin.natAdd 1)`. This is the key for proving
semantics of relabeling for formulas with k bound variables. -/
private lemma sum_elim_relabelAux_insertLastBound {k : ℕ} (v : Fin n → N) (xs : Fin (1 + k) → N) :
    Sum.elim v xs ∘ BoundedFormulaω.relabelAux insertLastBound k =
    Sum.elim (snoc v (xs 0)) (xs ∘ Fin.natAdd 1) := by
  funext x
  cases x with
  | inl i =>
    simp_all [BoundedFormulaω.relabelAux, insertLastBound, snoc] <;> aesop
  | inr j => simp [BoundedFormulaω.relabelAux]

/-- The general semantics lemma for relabeling with `insertLastBound`:
    For a formula with k bound variables, relabeling shifts the last free variable
    to bound position 0, while bound variables shift up by 1.

This handles all cases including `all`, which appears in Scott formulas due to
`forallLastVar` applications at earlier stages. -/
private theorem realize_relabel_insertLastBound {n : ℕ} :
    ∀ {k} (φ : L.BoundedFormulaω (Fin (n + 1)) k) v (xs : Fin (1 + k) → N),
    (φ.relabel insertLastBound).Realize v xs ↔ φ.Realize (snoc v (xs 0)) (xs ∘ Fin.natAdd 1) := by
  intro k φ; induction φ <;> simp_all [relabel, realize_castLE_self, sum_elim_relabelAux_insertLastBound, Fin.snoc_comp_natAdd]



/-- The key semantics lemma for formulas with 0 bound variables: relabeling with `insertLastBound`
    shifts the last free variable to a bound variable position.

For `φ : L.Formulaω (Fin (n+1))` (a formula with n+1 free vars and 0 bound vars):
- `φ.relabel insertLastBound : L.BoundedFormulaω (Fin n) 1` has n free vars and 1 bound var
- When we evaluate with free var assignment `v : Fin n → N` and bound var assignment
  `xs : Fin 1 → N`, this corresponds to evaluating the original formula with
  `snoc v (xs 0) : Fin (n+1) → N` -/
theorem realize_relabel_insertLastBound_zero {n : ℕ} (φ : L.Formulaω (Fin (n + 1)))
    (v : Fin n → N) (xs : Fin 1 → N) :
    (φ.relabel insertLastBound).Realize v xs ↔ φ.Realize (snoc v (xs 0)) := by
  have h := realize_relabel_insertLastBound  φ v xs
  rwa [show (xs ∘ Fin.natAdd 1) = Fin.elim0 from Fin.eq_elim0 _] at h


