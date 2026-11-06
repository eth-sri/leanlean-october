/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.StructureIsoSetoid
public import InfinitaryLogic.Descriptive.Polish
public import Mathlib.Logic.Small.Basic
public import InfinitaryLogic.Descriptive.SatisfactionBorel
public import InfinitaryLogic.Lomega1omega.QuantifierRank
public import InfinitaryLogic.Lomega1omega.Operations
public import Mathlib.Data.Set.Countable
public import InfinitaryLogic.Lomega1omega.Semantics
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.ModelTheory.Semantics
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.ModelTheory.Encoding
public import InfinitaryLogic.Lomega1omega.Theory
public import Mathlib.SetTheory.Ordinal.Family
public import InfinitaryLogic.Scott.Formula
public import InfinitaryLogic.Lomega1omega.OpenBoundsSemantics
public import Mathlib.Order.Zorn
public import Mathlib.Data.Fintype.Quotient
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Hom.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Order
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Pigeonhole
public import Mathlib.Order.InitialSeg
public import InfinitaryLogic.Descriptive.StructureSpace
public import Mathlib.ModelTheory.LanguageMap
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.ModelTheory.Substructures
public import Mathlib.GroupTheory.Perm.Basic
public import Architect
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Algebra.Group.Basic

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
theorem mem_modelsOf_iff_realize c φ :
    c ∈ ModelsOf φ ↔ @Sentenceω.Realize L φ ℕ c.toStructure :=
  FirstOrder.Language.mem_modelsOf_iff_realize c φ

/-! ### Sets of codes -/

/-! ### López–Escobar and the relative pullbacks -/

/-! ### Cantor and observable recovery -/

/-! ### Thinness -/

end FirstOrder.Language.SmallVocabulary
