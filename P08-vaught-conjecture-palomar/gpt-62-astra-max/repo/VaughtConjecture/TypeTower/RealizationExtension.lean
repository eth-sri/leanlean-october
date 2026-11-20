/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.TypeTower.Basic

/-! # Extension of partial realizations

Preservation of defined evaluations, without chains, request enumeration, or modelhood. -/

@[expose] public section

namespace VaughtConjecture.TypeTower.Realization

universe u v w
variable {Λ : Type v} [Preorder Λ] {T : TypeTower.{u} Λ} {α : Λ} {M : Type w}

/-- Preservation of every defined evaluation. -/
def Extends (A B : T.Realization α M) : Prop :=
  ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : T.Ty α n), A.eval t = some p → B.eval t = some p

end VaughtConjecture.TypeTower.Realization
