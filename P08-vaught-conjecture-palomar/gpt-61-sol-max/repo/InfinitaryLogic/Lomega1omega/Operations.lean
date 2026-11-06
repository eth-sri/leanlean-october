/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import InfinitaryLogic.Lomega1omega.Semantics
import InfinitaryLogic.Util

/-!
# Operations on Lω₁ω Formulas

This file defines operations on Lω₁ω formulas including relabeling, casting, and substitution.

## Main Definitions

- `BoundedFormulaω.relabel`: Relabels free variables.
- `BoundedFormulaω.castLE`: Increases the number of bound variables.
- `BoundedFormulaω.subst`: Substitutes terms for free variables.
- `BoundedFormula.toLω`: Embeds first-order formulas into Lω₁ω.

## Implementation Notes

These are the ω-facing operations, defined over `BoundedFormulaInf ℕ`. An operation that makes
sense at an arbitrary branching carrier belongs upstream on `BoundedFormulaInf`; `IndexCoding`
handles transport between carriers.
-/

universe u v u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}
variable {α β : Type u'} {n m : ℕ}


/-- Maps the last variable of `Fin (n+1)` to a bound variable position,
keeping the first `n` as free variables. Used for quantifying over the last position.

This function is used by `openBounds` (for the `all` case) and by `existsLastVar`/`forallLastVar`
in `Scott/Formula.lean`. -/
def insertLastBound {n} : Fin (n + 1) → Fin n ⊕ Fin 1 :=
  fun i => if h : i.val < n then Sum.inl ⟨i.val, h⟩ else Sum.inr 0

namespace BoundedFormulaω

/-- Casts a bounded formula to one with more bound variables. -/
@[simp]
def castLE : ∀ {m n} (_h : m ≤ n), L.BoundedFormulaω α m → L.BoundedFormulaω α n
  | _, _, _, falsum => falsum
  | _, _, h, equal t₁ t₂ =>
    equal (t₁.relabel (Sum.map id (Fin.castLE h))) (t₂.relabel (Sum.map id (Fin.castLE h)))
  | _, _, h, rel R ts => rel R (fun i => (ts i).relabel (Sum.map id (Fin.castLE h)))
  | _, _, h, imp φ ψ => (φ.castLE h).imp (ψ.castLE h)
  | _, _, h, all φ => (φ.castLE (Nat.succ_le_succ h)).all
  | _, _, h, iSup φs => iSup fun i => (φs i).castLE h
  | _, _, h, iInf φs => iInf fun i => (φs i).castLE h

/-- `castLE (le_refl n)` is the identity on formulas. -/
theorem castLE_refl : (φ : L.BoundedFormulaω α n) → φ.castLE (le_refl n) = φ := by (
  intro φ
  induction φ <;> simp_all)

variable {M : Type*} [L.Structure M]

/-- `castLE` over a proof of `m ≤ m` preserves semantics.
This is more general than matching on `le_refl` directly, as it works for any
proof `h : m ≤ m` regardless of how it was constructed. -/
theorem realize_castLE_of_eq {m n : ℕ} (φ : L.BoundedFormulaω α m) (h : m ≤ n) (heq : m = n)
    (v : α → M) (xs : Fin n → M) :
    (φ.castLE h).Realize v xs ↔ φ.Realize v (xs ∘ Fin.cast heq) := by
  subst heq
  have hcast : Fin.cast (Eq.refl m) = id := funext (fun i => rfl)
  simp  
  have : h = le_refl m := rfl
  rw [ castLE_refl]

/-- `castLE` over any proof `h : n ≤ n` preserves semantics.
This handles the case where the proof term is not definitionally `le_refl`
(e.g., constructed via rewriting or other means). -/
theorem realize_castLE_self {n : ℕ} (φ : L.BoundedFormulaω α n) (h : n ≤ n)
    (v : α → M) (xs : Fin n → M) :
    (φ.castLE h).Realize v xs ↔ φ.Realize v xs :=
  realize_castLE_of_eq φ h rfl v xs

/-- A function to help relabel the variables in bounded formulas. -/
def relabelAux (g : α → β ⊕ Fin n) (k : ℕ) : α ⊕ Fin k → β ⊕ Fin (n + k) :=
  Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id

/-- Relabels a bounded formula's free variables. -/
def relabel (g : α → β ⊕ Fin n) : ∀ {k}, L.BoundedFormulaω α k → L.BoundedFormulaω β (n + k)
  | _, falsum => falsum
  | _, equal t₁ t₂ => equal (t₁.relabel (relabelAux g _)) (t₂.relabel (relabelAux g _))
  | _, rel R ts => rel R fun i => (ts i).relabel (relabelAux g _)
  | _, imp φ ψ => (φ.relabel g).imp (ψ.relabel g)
  | k, all φ => (φ.relabel g).castLE (Nat.add_right_comm n k 1 ▸ le_refl _) |>.all
  | _, iSup φs => iSup fun i => (φs i).relabel g
  | _, iInf φs => iInf fun i => (φs i).relabel g

-- Note: The general realize_relabel lemma is complex due to castLE in the all case.
-- For Scott formulas, we only need specific lemmas for existsLastVar and forallLastVar,
-- which are proved directly in Scott/Formula.lean using a more targeted approach.
-- Below we prove realize_relabel for the specific case g = Sum.inr, needed for the C7 axioms.

/-- Renames free variables in a bounded formula using a function f : α → β.

Unlike `relabel`, which can move free variables into bound positions, `mapFreeVars`
simply renames free variables while preserving the bound variable structure. -/
def mapFreeVars (f : α → β) : ∀ {n}, L.BoundedFormulaω α n → L.BoundedFormulaω β n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (t₁.relabel (Sum.map f id)) (t₂.relabel (Sum.map f id))
  | _, .rel R ts => .rel R (fun i => (ts i).relabel (Sum.map f id))
  | _, .imp φ ψ => .imp (φ.mapFreeVars f) (ψ.mapFreeVars f)
  | _, .all φ => .all (φ.mapFreeVars f)
  | _, .iSup φs => .iSup (fun k => (φs k).mapFreeVars f)
  | _, .iInf φs => .iInf (fun k => (φs k).mapFreeVars f)

/-- Realization commutes with free variable renaming. -/
theorem realize_mapFreeVars {M : Type*} [L.Structure M]
    (f : α → β) (φ : L.BoundedFormulaω α n) (v : β → M) (xs : Fin n → M) :
    (φ.mapFreeVars f).Realize v xs ↔ φ.Realize (v ∘ f) xs := by
  induction φ <;> simp_all [mapFreeVars, Realize, Term.realize_relabel, Sum.elim_comp_map]



/-! ### Bridge: openBounds ∘ relabel Sum.inr roundtrip -/

-- Helper: relabelAux applied to Sum.inl where g returns Sum.inr

-- Helper: relabelAux applied to Sum.inr

/-! ### Language Maps -/

end BoundedFormulaω

namespace Formulaω

/-- Converts a formula with `Fin 0` free variables to a sentence (with `Empty` free variables).

Since both `Fin 0` and `Empty` are empty types, this is a purely type-theoretic conversion
that does not change the semantics of the formula. -/
def toSentenceω (φ : L.Formulaω (Fin 0)) : L.Sentenceω :=
  φ.mapFreeVars Fin.elim0

/-- `toSentenceω` preserves semantics: the sentence realizes in M iff the original
formula realizes with the `Fin.elim0` assignment. -/
theorem realize_toSentenceω {M} [L.Structure M]
    (φ : L.Formulaω (Fin 0)) :
    Sentenceω.Realize φ.toSentenceω M ↔ Formulaω.Realize φ (Fin.elim0 : Fin 0 → M) := by
  have h := BoundedFormulaω.realize_mapFreeVars Fin.elim0 φ
    Empty.elim (Fin.elim0 : Fin 0 → M)
  rw [comp_fin_elim0] at h
  exact h

end Formulaω

/-! ### Closed-term substitution -/

namespace BoundedFormula

/-- Embeds a first-order bounded formula into Lω₁ω. -/
def toLω : ∀ {n : ℕ}, L.BoundedFormula α n → L.BoundedFormulaω α n
  | _, falsum => BoundedFormulaω.falsum
  | _, equal t₁ t₂ => BoundedFormulaω.equal t₁ t₂
  | _, rel R ts => BoundedFormulaω.rel R ts
  | _, imp φ ψ => (φ.toLω).imp (ψ.toLω)
  | _, all φ => φ.toLω.all

variable {M : Type*} [L.Structure M] {v : α → M} {xs : Fin n → M}

@[simp]
theorem realize_toLω (φ : L.BoundedFormula α n) :
    φ.toLω.Realize v xs ↔ φ.Realize v xs := by
  induction φ <;> simp_all [toLω, BoundedFormula.Realize]







