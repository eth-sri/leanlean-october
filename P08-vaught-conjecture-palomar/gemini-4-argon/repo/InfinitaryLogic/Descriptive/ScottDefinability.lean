/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.SmallVocabularyTransport
public import InfinitaryLogic.Scott.RefinementCount
public import InfinitaryLogic.OrdinalCountability

/-!
# Scott isolation and countable/cocountable definability on a presentation

For a presentation `truth : L.Sentenceω → Q → Prop` of a family of isomorphism classes:

* `IsolatedPresentation truth`: every value of `Q` is picked out by one sentence.
* **Abstract layer** (no relationality or signature countability): from isolation and the closure
  of `truth` under countable disjunction and falsum, every countable set of presentation values
  is sentence-definable (`exists_sentence_of_countable`, the empty and finite cases included);
  with negation and single-sentence splits, the sentence-definable sets are exactly the countable
  and the cocountable ones (`sentence_definable_iff`).
* **Presentation layer**: for a surjective `classOf : X → Q` with `truth` actual satisfaction of
  the codes (`htruth`), the closure conditions hold (`truth_esup_of_presentation`,
  `not_truth_falsum_of_presentation`, `truth_not_of_presentation`), and when isomorphic codes have
  equal presentation values, the presentation is isolated by Scott sentences
  (`isolatedPresentation_of_surjective`): the Scott sentence of `ℕ` under the decoded structure of a
  representative isolates its class.  No reverse-isomorphism premise, no measurable structure on
  `Q`, no Borelness of the family.  The corollaries `exists_sentence_of_countable_of_presentation`
  and `sentence_definable_iff_of_presentation` assemble the two layers.
* **Strict stage bounds** (abstract layer): on an isolated presentation, the isolating sentences
  have countable quantifier rank (`IsolatedPresentation.exists_qrank_lt_omega1`, from
  `Sentenceω.qrank_lt_omega1`), so antitone domains of presentation values that are nonsingleton
  and agree on every sentence of quantifier rank at most `η` at every countable `η` bound every
  value's stages strictly by a countable ordinal
  (`IsolatedPresentation.exists_countable_strict_stage_bound`, the instance of
  `InfinitaryLogic.exists_countable_strict_stage_bound_of_isolation` in `OrdinalCountability`).

## Strict stage bounds: what is and is not claimed

* The bound is the quantifier rank of *some* isolating sentence.  It is not identified with an
  internal Scott rank, nor with the stabilization ordinal of a representative, and it is not an
  attained stage (attainment is `exists_greatest_stage_lt_omega1` in `OrdinalUtil`, under further
  closure hypotheses).
* Agreement at stage `η` is for sentences of quantifier rank **at most** `η`, the convention of
  `EquivQRω`; exclusion is at the isolating sentence's own rank.
* Nonsingletonness of the domains is essential, and no countability of exceptional classes is
  assumed.  The hypotheses force the presentation type to be uncountable, so the bound applies
  to a countable presentation only vacuously.
* **Where Scott theory enters.**  Only through `IsolatedPresentation`.  The generic layer in
  `OrdinalCountability` mentions no logic: its proofs use no `FirstOrder` constant.  The wrapper
  over an abstract `IsolatedPresentation` adds only the syntactic fact
  `Sentenceω.qrank_lt_omega1`: its proof uses no Scott, Karp or back-and-forth constant, although
  this module imports them.  A consumer that obtains isolation from
  `isolatedPresentation_of_surjective` does reach `scottSentence_characterizes` and the Karp
  theory in its proof.
* Isolation concerns the given presentation, a space of isomorphism classes of countable codes;
  a Scott sentence is not claimed to isolate a structure among arbitrary uncountable ones.

The strict stage bounds were offered for upstreaming by a consumer of this library.
-/

@[expose] public section

universe u v w x

namespace FirstOrder.Language

open Set

/-! ### The abstract layer -/

section Abstract

variable {L : Language.{u, v}} {Q : Type w}

/-- A presentation is **Scott-isolated**: every value is picked out by one sentence. -/
def IsolatedPresentation (truth : L.Sentenceω → Q → Prop) : Prop :=
  ∀ q, ∃ σ : L.Sentenceω, ∀ s, truth σ s ↔ s = q

end Abstract

/-! ### The presentation layer -/

section Presentation

variable {L : Language.{u, v}} [L.IsRelational] {X : Type x} {Q : Type w}

  [Countable (Σ l, L.Relations l)]

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
