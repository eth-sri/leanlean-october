/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.SmallVocabularyTransport
public import InfinitaryLogic.Scott.RefinementCount
public import InfinitaryLogic.OrdinalCountability

@[expose] public section

universe u v w x

namespace FirstOrder.Language

open Set

section Abstract

variable {L : Language.{u, v}} {Q : Type w}

/-- A presentation is **Scott-isolated**: every value is picked out by one sentence. -/
def IsolatedPresentation (truth : L.Sentenceω → Q → Prop) : Prop :=
  ∀ q, ∃ σ : L.Sentenceω, ∀ s, truth σ s ↔ s = q

end Abstract

section Presentation

variable {L : Language.{u, v}} [L.IsRelational] {X : Type x} {Q : Type w}

variable [Countable (Σ l, L.Relations l)]

/-- **Isolation from a surjective, satisfaction-compatible, isomorphism-preserving presentation.**
The isolating sentence of the class of `x` is the Scott sentence of `ℕ` under the decoded structure
of `codes x`.  No reverse-isomorphism premise is used. -/
theorem isolatedPresentation_of_surjective (codes : X → StructureSpace L) (classOf : X → Q)
    (honto : Function.Surjective classOf)
    (hiso : ∀ x y, (structureIsoSetoid L).r (codes x) (codes y) → classOf x = classOf y)
    (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ φ x, truth φ (classOf x) ↔ codes x ∈ ModelsOf φ) :
    IsolatedPresentation truth := by
  intro q
  obtain ⟨x, rfl⟩ := honto q
  refine ⟨(@scottSentence L _ ℕ (codes x).toStructure _).toSentenceω, fun s => ⟨fun h => ?_,
    fun h => ?_⟩⟩
  · obtain ⟨y, rfl⟩ := honto s
    rw [htruth, SmallVocabulary.mem_modelsOf_iff_realize,
      ← Formulaω.realize_as_sentence_iff_toSentenceω] at h
    exact (hiso x y (@scottSentence_realizes_implies_equiv L _ _ ℕ (codes x).toStructure _
      ℕ (codes y).toStructure _ h)).symm
  · rw [h, htruth, SmallVocabulary.mem_modelsOf_iff_realize,
      ← Formulaω.realize_as_sentence_iff_toSentenceω]
    exact @scottSentence_self L _ _ ℕ (codes x).toStructure _

end Presentation

end FirstOrder.Language
