/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.InvariantSeparation
public import InfinitaryLogic.Descriptive.StructureIsoSetoid

set_option linter.privateModule false

/-!
# Recovering Borel data by sentences

## Truth sequences

`sentenceTheory θ c` is the truth sequence of a countable list of sentences `θ` at the coded
structure `c`.  It is measurable (`measurable_sentenceTheory`) and isomorphism-invariant
(`sentenceTheory_eq_of_iso`).  These basics stay here, below any use of Silver: the spectrum
characterization (`Conditional/SentenceSpectrum.lean`) consumes them, and observable recovery
need not import it.

## Relative López–Escobar

`sentence_pullback_of_iso_compatible`: a Borel predicate on a standard Borel family of
structures that is constant on isomorphic outputs is the pullback of one sentence.  The proof
saturates the two images, separates them by `sentence_separates_analytic_classes`, and reads the
sentence back along the family.  The antichain form `sentence_pullback_on_antichain`, where
isomorphism compatibility is automatic, is a corollary.

## Cantor parameters

On a Borel Cantor isomorphism antichain, countably many sentences recover every parameter bit
(`sentences_recover_cantor`, `sentenceTheory_eq_parameter`).  Hence a class on which every
countable sentence list has countably many realized truth sequences carries no such antichain
(`no_antichain_of_countable_sentence_spectra`), so such a class is thin
(`isThinOn_of_countable_sentence_spectra`), and a sentence with that property on its countable
models is thin (`thin_of_countable_sentence_spectra`).  The converse needs Silver and lives in
`Conditional/SentenceSpectrum.lean`; the single-sentence-split form on a presentation of the
classes is `Descriptive/SentenceSplits.lean`.

## Classical background

López–Escobar is Marker, *Lectures on Infinitary Model Theory* (Cambridge, 2016),
Theorem 4.3.7; Gao, *Invariant Descriptive Set Theory* (CRC Press, 2009), Theorem 11.3.6, is
an alternative exposition.  The relative form on a Borel family and the recovery of Cantor
parameters are derived here from invariant separation; these formulations are not claimed to
occur in the sources.
-/

@[expose] public section

universe u v x

namespace FirstOrder.Language

open MeasureTheory Set

/-! ## Truth sequences

The truth-sequence basics are stated for every `L : Language.{u, v}`: they use only `ModelsOf`,
its measurability, and its isomorphism invariance, all of which are universe-polymorphic.  The
recovery theorems below them stay at `Language.{0, 0}`. -/

section TruthSequences

variable {L : Language.{u, v}} [L.IsRelational]

end TruthSequences

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ n, L.Relations n)]

/-! ## Relative López–Escobar -/

/-! ## Cantor parameters -/

/-- Cantor space is Polish: second countable and completely metrizable, from the countable
product instances.  Local to this file. -/
private theorem polishSpace_cantor : PolishSpace (ℕ → Bool) :=
  PolishSpace.mk

attribute [local instance] polishSpace_cantor

end FirstOrder.Language
