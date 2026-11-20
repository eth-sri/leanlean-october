/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model

/-! # Finite request data and elementary countability

Pattern codes retain their original admissibility predicate. This module contains no
request enumeration, scheduler, or stopping-rank theory.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w

variable {α : Ordinal.{0}} {n : ℕ}

/-! ### The bottom-pattern quotient theorem -/

namespace FixedHeight

/-! ### Pattern codes at an arbitrary limit stage

The stage-`ω` versions live in `Knight/Sentence.lean` (`BotPattern`, `PatternFamily`,
`IsPatternOf`); they are reproduced here at an arbitrary stage, namespaced `FixedHeight` to
keep the lane quarantined. -/

/-! ### Elementary countability -/

variable {M : Type w}

/-- Injective tuples on a countable carrier are countable. -/
instance countable_emb [Countable M] n : Countable (Fin n ↪ M) :=
  Function.Injective.countable (f := fun f : Fin n ↪ M => (f : Fin n → M))
    DFunLike.coe_injective

end FixedHeight
end VaughtConjecture.Knight
