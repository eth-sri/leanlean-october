/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.SmallVocabularyLift
public import InfinitaryLogic.Descriptive.LopezEscobar
public import InfinitaryLogic.Descriptive.SentenceSplits
public import InfinitaryLogic.Descriptive.SentenceObservables

/-!
# Descriptive transport through the small-vocabulary presentation

The coded descriptive theorems are stated for `L : Language.{0, 0}`.  Through the chosen
presentation `lang L` and its code homeomorphism (`Descriptive/SmallVocabulary.lean`) and formula
lift (`Descriptive/SmallVocabularyLift.lean`), each of them yields a statement for every countable
relational `L : Language.{u, v}`.  The underlying small-universe proofs are unchanged; every
theorem here is a transport.

* **Truth sequences**: `sentenceTheory_code` (the truth sequence of a code along a list of the
  small presentation is the truth sequence of the original along the lifted list) and its image
  form `sentenceTheory_image_code`.
* **Sets of codes**: measurability and isomorphism invariance transfer along `code` in both
  directions (`measurableSet_image_code_iff`, `isomorphismInvariant_image_code_iff`).
* **López–Escobar** (`SmallVocabulary.lopezEscobar_iff`), the **relative pullbacks**
  (`SmallVocabulary.sentence_pullback_of_iso_compatible`, `…_on_antichain`), **Cantor recovery**
  (`SmallVocabulary.sentences_recover_cantor`), and **observable recovery and encoding**
  (`SmallVocabulary.sentences_recover_observable`, `…_encode_observable`), for `L`.
* **Thinness**: Cantor antichains and thinness transfer along `code`
  (`hasCantorAntichainOn_image_code_iff`, `isThinOn_image_code_iff`), giving the spectrum and
  splits endpoints for `L` (`SmallVocabulary.isThinOn_of_countable_sentence_spectra`,
  `SmallVocabulary.isThinOn_of_countable_sentence_splits`, and the sentence-specific corollary).

Names coincide with the small-universe originals inside the `SmallVocabulary` namespace; the
originals are referred to fully qualified.
-/

@[expose] public section

universe u v w x y

namespace FirstOrder.Language.SmallVocabulary

open MeasureTheory Set

variable (L : Language.{u, v}) [L.IsRelational] [Countable (Σ n, L.Relations n)]

/-! ### Truth sequences -/

omit [Countable (Σ n, L.Relations n)] in
/-- Membership in `ModelsOf` is realization of the sentence in the decoded structure (the empty
valuation is unique).  A restatement, with `L` explicit, of the root
`FirstOrder.Language.mem_modelsOf_iff_realize` (`Descriptive/SatisfactionBorel.lean`). -/
theorem mem_modelsOf_iff_realize (c : StructureSpace L) (φ : L.Sentenceω) :
    c ∈ ModelsOf φ ↔ @Sentenceω.Realize L φ ℕ c.toStructure :=
  FirstOrder.Language.mem_modelsOf_iff_realize c φ

/-! ### Sets of codes -/

/-! ### López–Escobar and the relative pullbacks -/

/-! ### Cantor and observable recovery -/

/-! ### Thinness -/

