/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import InfinitaryLogic.Descriptive.StructureIsoSetoid
import InfinitaryLogic.Descriptive.Polish
import Mathlib.Logic.Small.Basic
import InfinitaryLogic.Descriptive.SatisfactionBorel
import InfinitaryLogic.Lomega1omega.QuantifierRank
import InfinitaryLogic.Lomega1omega.Operations
import Mathlib.Data.Set.Countable
import InfinitaryLogic.Lomega1omega.Semantics
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic
import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.ModelTheory.Encoding
import InfinitaryLogic.Lomega1omega.Theory
import Mathlib.SetTheory.Ordinal.Family
import InfinitaryLogic.Scott.Formula
import InfinitaryLogic.Lomega1omega.OpenBoundsSemantics
import Mathlib.Order.Zorn
import Mathlib.Data.Fintype.Quotient
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Set.Lattice.Disjoint
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Set.Lattice.Order
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Mathlib.Order.InitialSeg
import InfinitaryLogic.Descriptive.StructureSpace
import Mathlib.ModelTheory.LanguageMap
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.ModelTheory.Substructures
import Mathlib.GroupTheory.Perm.Basic
import Architect
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Algebra.Group.Basic

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

universe u v   

namespace FirstOrder.Language.SmallVocabulary


variable (L : Language.{u, v}) [L.IsRelational] [Countable (Σ n, L.Relations n)]

/-! ### Truth sequences -/

omit [Countable (Σ n, L.Relations n)] in
/-- Membership in `ModelsOf` is realization of the sentence in the decoded structure (the empty
valuation is unique).  A restatement, with `L` explicit, of the root
`FirstOrder.Language.mem_modelsOf_iff_realize` (`Descriptive/SatisfactionBorel.lean`). -/
def mem_modelsOf_iff_realize (c : StructureSpace L) (φ : L.Sentenceω) :=
  FirstOrder.Language.mem_modelsOf_iff_realize c φ

/-! ### Sets of codes -/

/-! ### López–Escobar and the relative pullbacks -/

/-! ### Cantor and observable recovery -/

/-! ### Thinness -/

