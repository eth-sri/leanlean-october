import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.Model

/-! # Finite request data and elementary countability

Pattern codes retain their original admissibility predicate. This module contains no
request enumeration, scheduler, or stopping-rank theory.
-/

namespace VaughtConjecture.Knight


universe w

variable {α : Ordinal₀} {n : ℕ}

/-! ### The bottom-pattern quotient theorem -/

namespace FixedHeight

/-! ### Pattern codes at an arbitrary limit stage

The stage-`ω` versions live in `Knight/Sentence.lean` (`BotPattern`, `PatternFamily`,
`IsPatternOf`); they are reproduced here at an arbitrary stage, namespaced `FixedHeight` to
keep the lane quarantined. -/

/-! ### Elementary countability -/

variable {M : Type w}

/-- Injective tuples on a countable carrier are countable. -/
instance countable_emb [Countable M] (n : ℕ) : Countable (Fin n ↪ M) :=
  Function.Injective.countable (f := fun f => (f : Fin n → M))
    DFunLike.coe_injective

/-- The ordinals strictly below a countable ordinal are countable. -/
theorem countable_lt (hβ : α.card ≤ Cardinal.aleph0) :
    Countable {γ : Ordinal₀ // γ < α} :=
  ((Ordinal.countable_Iic_of_card_le_aleph0 hβ).mono Set.Iio_subset_Iic_self).to_subtype

