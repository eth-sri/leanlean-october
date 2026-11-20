/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SlotPatternRefinement

/-! # Finite normalized profile families with a preserved algebraic contract

`OrderLaw` records the properties of a class of lawful grade-one labellings
used by source refinement. `family` constructs a whole joint controller
family and proves those properties again for its output. These are row-layer
properties, not a support plan, mixed-grade bountifulness, or request forcing.
-/

@[expose] public section

namespace VaughtConjecture.Knight.NormalizedProfileFamily

open Transform Value ExtOrd SlotControllerFamily
open SlotPatternRefinement (mix)

/-- The algebraic input contract for finite source-profile saturation. Its
fields are proved for the constructed output below, not supplied anew. -/
structure OrderLaw (X : Type*) where
  holds : (X → ExtOrd) → Prop
  bottom : holds (fun _ => ⊥)
  visible : ∀ {p}, holds p → ∀ d, SelfVis 1 (p d)
  order : ∀ {p r}, holds p → (∀ d, SelfVis 1 (r d)) →
    (∀ d, p d = ⊥ → r d = ⊥) → (∀ d e, p d ≤ p e → r d ≤ r e) → holds r
  refine : ∀ {q b : X → ℕ} {a : ℕ}, 0 < a →
    holds (fun d => value (q d)) → holds (fun d => value (b d)) →
    (∀ d e, q d < a → a ≤ q e → b d < b e) → holds (fun d => value (mix q b a d))

variable {X : Type*} [Fintype X]

variable (L : OrderLaw X)

end VaughtConjecture.Knight.NormalizedProfileFamily
