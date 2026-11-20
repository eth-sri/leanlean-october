/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.Polish
public import InfinitaryLogic.Descriptive.SatisfactionBorel
public import Architect
public import InfinitaryLogic.Descriptive.PerfectAntichain

@[expose] public section

open Cardinal Set

universe u v

namespace FirstOrder.Language

variable {L : Language.{u, v}} [L.IsRelational]

/-- **The ambient isomorphism relation**: two codes are related iff the structures they decode
on `ℕ` are `L`-isomorphic.  Stated on all of `StructureSpace L`, with no reference to any
sentence. -/
@[blueprint "def:structure-iso-setoid"
  (title := /-- Ambient isomorphism relation -/)
  (statement := /-- The equivalence relation on all of the structure space where two codes are
    related iff the structures they decode on $\mathbb{N}$ are $L$-isomorphic.  Defined without
    reference to any sentence, so that perfectness of a set of codes is a property of the ambient
    space rather than of a refinement chosen to make one model class Polish. -/)
  (uses := ["def:structure-space"])]
def structureIsoSetoid (L : Language.{u, v}) [L.IsRelational] : Setoid (StructureSpace L) where
  r c₁ c₂ := Nonempty (@Language.Equiv L ℕ ℕ c₁.toStructure c₂.toStructure)
  iseqv :=
    { refl := fun c => ⟨@Language.Equiv.refl L ℕ c.toStructure⟩
      symm := fun {c₁ c₂} ⟨e⟩ => by tauto
      trans := fun {c₁ c₂ c₃} ⟨e₁⟩ ⟨e₂⟩ =>
        ⟨@Language.Equiv.comp L ℕ ℕ c₁.toStructure c₂.toStructure ℕ c₃.toStructure e₂ e₁⟩ }

variable [Countable (Σ l, L.Relations l)]

/-- The isomorphism equivalence relation on coded ℕ-models of φ: the ambient relation
restricted to the models of `φ`.  Two codes are related iff the decoded structures on ℕ are
L-isomorphic. -/
@[blueprint "def:iso-setoid"
  (title := /-- Isomorphism setoid on coded models -/)
  (statement := /-- The equivalence relation on coded $\mathbb{N}$-models of $\varphi$
    where two codes are related iff their decoded structures are $L$-isomorphic.  It is the
    ambient relation restricted along the subtype inclusion. -/)
  (uses := ["def:structure-iso-setoid"])]
def isoSetoid (φ : L.Sentenceω) : Setoid ↥(ModelsOf φ) :=
  (structureIsoSetoid L).comap Subtype.val

omit [Countable ((l : ℕ) × L.Relations l)] in
/-- Membership in the pulled-back relation is membership in the ambient one. -/
theorem isoSetoid_r_iff {φ : L.Sentenceω} {c₁ c₂ : ↥(ModelsOf φ)} :
    (isoSetoid φ).r c₁ c₂ ↔ (structureIsoSetoid L).r c₁.1 c₂.1 := Iff.rfl

/-- `φ` is thin on its countable models: no such perfect set. -/
@[blueprint "def:thin-nat-models"
  (title := /-- Thinness on coded $\mathbb{N}$-models -/)
  (statement := /-- A sentence $\varphi$ is \emph{thin on its $\mathbb{N}$-models} if the set of
    codes of $\mathbb{N}$-models of $\varphi$ carries no perfect antichain for the ambient
    isomorphism relation on the structure space.  Stated ambiently, so no Polish refinement of
    the model subtype enters the definition. -/)
  (uses := ["def:thin-on", "def:structure-iso-setoid"])]
def Sentenceω.IsThinOnNatModels (φ : L.Sentenceω) : Prop :=
  IsThinOn (structureIsoSetoid L) (ModelsOf φ)

end FirstOrder.Language
