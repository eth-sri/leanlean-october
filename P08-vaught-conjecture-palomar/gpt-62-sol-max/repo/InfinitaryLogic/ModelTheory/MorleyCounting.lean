/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Lomega1omega.Theory
public import InfinitaryLogic.Scott.Formula
public import InfinitaryLogic.Lomega1omega.QuantifierRank
public import InfinitaryLogic.Karp.CarrierTheorem
public import InfinitaryLogic.Scott.Sentence
public import InfinitaryLogic.Scott.RefinementCount
public import Mathlib.SetTheory.Cardinal.Regular
public import Architect
public import InfinitaryLogic.Karp.PotentialIso
public import InfinitaryLogic.Descriptive.SatisfactionBorelOn
public import InfinitaryLogic.Descriptive.Polish
public import InfinitaryLogic.Descriptive.BFTree
public import InfinitaryLogic.Descriptive.SatisfactionBorel
public import InfinitaryLogic.OrdinalUtil
public import InfinitaryLogic.Scott.BackAndForth
public import Mathlib.SetTheory.Cardinal.Aleph
public import InfinitaryLogic.Descriptive.StructureIsoSetoid
public import Mathlib.SetTheory.Cardinal.Continuum
public import InfinitaryLogic.Descriptive.StructureSpace
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

universe u v

namespace FirstOrder

namespace Language

open Cardinal Ordinal

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- The BFEquiv α equivalence relation on coded ℕ-models of φ (at the empty tuple). -/
def bfEquivSetoid (φ : L.Sentenceω) (α : Ordinal.{0}) :
    Setoid (ModelsOf φ) := (codeBFEquivSetoid L α).comap Subtype.val

omit [Countable (Σ l, L.Relations l)] in
/-- Iso implies BFEquiv α: isoSetoid refines bfEquivSetoid. -/
theorem isoSetoid_refines_bfEquivSetoid (φ : L.Sentenceω) (α : Ordinal.{0})
    {c₁ c₂ : ↥(ModelsOf φ)} :
    (isoSetoid φ).r c₁ c₂ → (bfEquivSetoid φ α).r c₁ c₂ := by
  intro ⟨e⟩
  change CodeBFEquiv α c₁.1 c₂.1
  unfold CodeBFEquiv
  conv_rhs => rw [show (Fin.elim0 : Fin 0 → ℕ) = e ∘ Fin.elim0 from
    (comp_fin_elim0 e).symm]
  exact @equiv_implies_BFEquiv L ℕ ℕ c₁.1.toStructure c₂.1.toStructure e α 0 Fin.elim0

omit [Countable (Σ l, L.Relations l)] in
/-- The depth-`α` projection of isomorphism classes onto back-and-forth classes. -/
def bfProj (φ : L.Sentenceω) (α : Ordinal.{0}) :
    Quotient (isoSetoid φ) → Quotient (bfEquivSetoid φ α) :=
  Quotient.map id (fun _a _b h => isoSetoid_refines_bfEquivSetoid φ α h)

omit [Countable (Σ l, L.Relations l)] in
@[simp] theorem bfProj_mk (φ : L.Sentenceω) (α : Ordinal.{0}) (c : ↥(ModelsOf φ)) :
    bfProj φ α (Quotient.mk _ c) = Quotient.mk _ c := rfl

end Language

end FirstOrder
