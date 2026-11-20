/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w

namespace KnightRealization

variable {M₁ M₂ : Type w}

variable {α : LimitStage}

variable {A₁ : KnightRealization α M₁} {A₂ : KnightRealization α M₂}

/-- One common full source chart, with no higher-stage witness attached. -/
structure CommonChartNode where
  arity : ℕ
  tuple₁ : Fin arity ↪ M₁
  tuple₂ : Fin arity ↪ M₂
  type : S α.1 arity
  eval₁ : A₁.eval tuple₁ = some type
  eval₂ : A₂.eval tuple₂ = some type

/-- One extension preserving the selected invariant and meeting a scheduled point. -/
structure CommonChartExtension
    (Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop)
    (nd : CommonChartNode (A₁ := A₁) (A₂ := A₂)) (z : M₁ ⊕ M₂) where
  next : CommonChartNode (A₁ := A₁) (A₂ := A₂)
  emb : Fin nd.arity ↪ Fin next.arity
  trans₁ : emb.trans next.tuple₁ = nd.tuple₁
  trans₂ : emb.trans next.tuple₂ = nd.tuple₂
  served : ∃ i, match z with
    | .inl x => next.tuple₁ i = x
    | .inr y => next.tuple₂ i = y
  good_next : Good next

/-- Density is required only at charts satisfying `Good`. -/
def RestrictedCommonChartStepSupply
    (Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop) : Prop :=
  ∀ nd, Good nd → ∀ z, Nonempty (CommonChartExtension Good nd z)

abbrev CommonChartStepSupply : Prop :=
  RestrictedCommonChartStepSupply (A₁ := A₁) (A₂ := A₂) fun _ => True

end KnightRealization

end VaughtConjecture.Knight
