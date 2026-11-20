/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OneBlockReceiving
public import VaughtConjecture.Knight.FiniteCoverCoordinates
public import VaughtConjecture.Knight.ModelEmpty
public import VaughtConjecture.Knight.ReductModel
public import VaughtConjecture.Knight.Sentence
public import VaughtConjecture.Knight.VisibleFaceOneStep
public import VaughtConjecture.CountableQuantifierRank
public import VaughtConjecture.InfinitaryRelabel
public import InfinitaryLogic.Karp.CarrierTheorem

/-! # Logical comparison from one-block receiving

A common labelled chart at `blockStage (ω * η)` gives back-and-forth equivalence
through `η`, and hence agreement on sentences of quantifier rank at most `η`.
A finite cover costs one block per added point. No terminal classification,
stopping-rank boundedness, or descriptive thinness result is used here.

The old `OneBlockReadback` module reexports this API together with its historical
rank applications. All moved theorem statements and proofs are unchanged. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower FirstOrder Language Structure KnightRealization Cardinal

universe w u v u'

/-! ## Common charts: reduction and symmetry -/

/-! ## Extending an embedding of coordinates by one coordinate -/

/-! ## The multi-point transfer: one block per point -/

/-! ## Back-and-forth equivalence with the `ω · η` budget -/

/-! ## Compatibility with the general formula-rank theorem -/

/-- The quantifier rank of an `L_{ω₁ω}` formula (countable branching) is a countable ordinal. -/
theorem qrank_lt_ord_aleph_one {L : Language.{u, v}} {γ : Type u'} :
    ∀ {n : ℕ} (φ : L.BoundedFormulaInf ℕ γ n), φ.qrank < (aleph 1).ord :=
  VaughtConjecture.qrank_lt_ord_aleph_one

/-! ## Sentence agreement -/

end VaughtConjecture.Knight
