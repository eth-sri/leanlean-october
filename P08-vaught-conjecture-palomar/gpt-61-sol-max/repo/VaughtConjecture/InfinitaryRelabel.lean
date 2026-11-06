/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import PalomarProof.Infinitary.QuantifierRank

/-! # Relabelling free variables in infinitary formulas

General syntax, satisfaction, and quantifier-rank transport, independent of the
Knight comparison construction. Extracted unchanged from `Knight/SentenceAgreement`.
-/

namespace FirstOrder.Language.BoundedFormulaInf

universe u v u' u'' uι w

variable {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {β : Type u''}

/-- Relabelling the free variables of an infinitary formula along `g : α → β`. -/
def relabelFree (g : α → β) : ∀ {n}, L.BoundedFormulaInf ι α n → L.BoundedFormulaInf ι β n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (t₁.relabel (Sum.map g id)) (t₂.relabel (Sum.map g id))
  | _, .rel R ts => .rel R fun i => (ts i).relabel (Sum.map g id)
  | _, .imp φ ψ => .imp (relabelFree g φ) (relabelFree g ψ)
  | _, .all φ => .all (relabelFree g φ)
  | _, .iSup φs => .iSup fun i => relabelFree g (φs i)
  | _, .iInf φs => .iInf fun i => relabelFree g (φs i)

variable {M : Type w} [L.Structure M]

/-- Relabelling free variables is realized along the composite valuation. -/
theorem realize_relabelFree g :
    ∀ {n} (φ : L.BoundedFormulaInf ι α n) (v : β → M) xs,
      (relabelFree g φ).Realize v xs ↔ φ.Realize (v ∘ g) xs := by
  intro n φ
  induction φ <;> intro v xs <;>
    simp_all [relabelFree, Realize, Term.realize_relabel, Sum.elim_comp_map]

/-- Relabelling free variables preserves the quantifier rank. -/
theorem qrank_relabelFree (g : α → β) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaInf ι α n), (relabelFree g φ).qrank = φ.qrank := by
  intro n φ
  induction φ <;> simp_all [relabelFree, qrank]
