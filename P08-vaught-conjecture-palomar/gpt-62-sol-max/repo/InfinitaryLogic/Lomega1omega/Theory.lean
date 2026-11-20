/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Lomega1omega.Semantics
public import InfinitaryLogic.Util
public import Mathlib.Data.Set.Basic

@[expose] public section

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-- Two structures are Lω₁ω-elementarily equivalent if they satisfy the same Lω₁ω sentences. -/
def LomegaEquiv (L : Language) (M N : Type*) [L.Structure M] [L.Structure N] : Prop :=
  ∀ φ : L.Sentenceω, Sentenceω.Realize φ M ↔ Sentenceω.Realize φ N

namespace LomegaEquiv

variable {M : Type w} [L.Structure M]

variable {N : Type w'} [L.Structure N]

variable {P : Type*} [L.Structure P]

/-- Isomorphic structures are Lω₁ω-equivalent.

The proof transports variable assignments along the isomorphism using
`BoundedFormulaω.realize_equiv`, then observes that `e ∘ Empty.elim = Empty.elim`
and `e ∘ Fin.elim0 = Fin.elim0` since both domains are empty. -/
theorem of_equiv {M N : Type w} [L.Structure M] [L.Structure N] (e : M ≃[L] N) :
    LomegaEquiv L M N := by
  intro φ
  have h := BoundedFormulaω.realize_equiv e φ (Empty.elim : Empty → M) (Fin.elim0 : Fin 0 → M)
  rwa [comp_empty_elim e, comp_fin_elim0 e] at h

end LomegaEquiv

end Language

end FirstOrder
