/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import InfinitaryLogic.Lomega1omega.Semantics
import InfinitaryLogic.Util
import Mathlib.Data.Set.Basic

/-!
# Lω₁ω Theories and Semantic Entailment

This file defines theories, models, semantic entailment, and elementary equivalence
in Lω₁ω (countable infinitary logic with countable conjunctions/disjunctions).

## Main Definitions

- `Theoryω`: A theory in Lω₁ω is a set of sentences.
- `Theoryω.Model`: A structure M is a model of theory T if it satisfies all sentences in T.
- `Theoryω.IsSatisfiableIn`: T has a model in a selected carrier universe.
- `LomegaEquiv`: Lω₁ω-elementary equivalence between structures.

## Main Results

- `Theoryω.Model.empty`: The empty theory has every structure as a model.
- `Theoryω.Model.mono`: Models are monotone: if T ⊆ T' and M ⊨ T', then M ⊨ T.
- `LomegaEquiv.refl`, `LomegaEquiv.symm`, `LomegaEquiv.trans`: LomegaEquiv is an equivalence relation.
- `LomegaEquiv.of_equiv`: Isomorphic structures are Lω₁ω-equivalent.
- `Formulaω.realize_comp_equiv`: realization of a formula is invariant under isomorphisms, the
  formula-level form of `BoundedFormulaω.realize_equiv` (`Lomega1omega/Semantics.lean`).

## References

- [Mar16]
- [KK04]
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}


/-! ### Theories -/


/-! ### Isomorphism Invariance of Realization -/

/-! ### Lω₁ω Elementary Equivalence -/

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
  have h := BoundedFormulaω.realize_equiv e φ (Empty.elim) (Fin.elim0)
  rwa [comp_empty_elim e, comp_fin_elim0 e] at h


/-! ### Invariance under Isomorphism -/


