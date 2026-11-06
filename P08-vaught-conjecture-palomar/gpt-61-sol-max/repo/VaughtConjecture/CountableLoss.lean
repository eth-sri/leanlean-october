import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import InfinitaryLogic.OrdinalCountability
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular

/-! # Countable successor losses and limit continuity give countable complements

A family of sets `D ξ` indexed by countable ordinals, starting at everything, losing only
countably many points at each successor step, and continuous at countable limits (the
intersection of the earlier sets is contained in the limit set), has a countable complement
at every countable index (`compl_countable_of_loss`).  The proof is transfinite induction:
the complement at `ξ + 1` is contained in the complement at `ξ` together with the successor
loss, and the complement at a limit is contained in the countable union of the earlier
complements (inclusions, not equalities: no monotonicity is assumed).

**Exact cardinality** (`mk_eq_aleph_one_of_domains`) needs more: decreasing domains whose
countable-index complements are countable, all nonempty below `ω₁`, and which every point
eventually leaves, exhaust a space of cardinality exactly `ℵ₁`.  Every point lies in some
countable-index complement (at most `ℵ₁ · ℵ₀` points), and a countable space would leave all
its points before one countable index, emptying that domain.  No rank function and no
canonical representatives are chosen.  Nothing here is construction-specific. -/

namespace VaughtConjecture.CountableLoss

open Cardinal Set

universe u

/-- **Countable successor losses and limit continuity give countable complements.** -/
theorem compl_countable_of_loss {X : Type u} (D : Ordinal₀ → Set X) (h0 : D 0 = Set.univ)
    (hsucc : ∀ ξ, ξ < (aleph 1).ord → (D ξ \ D (ξ + 1)).Countable)
    (hlim : ∀ l, Order.IsSuccLimit l → l < (aleph 1).ord → (⋂ ξ < l, D ξ) ⊆ D l) :
    ∀ β, β < (aleph 1).ord → (D β)ᶜ.Countable := by
  rw [Cardinal.ord_aleph] at hsucc hlim ⊢
  exact InfinitaryLogic.compl_countable_of_loss D h0 hsucc hlim

/-! ## Exact cardinality from decreasing domains

The space is taken in `Type 1`, where the counted quotients live; the ordinal indices are in
`Ordinal.{0}`.  A universe-polymorphic version would only add cardinal lifts. -/

/-- The ordinals below `ω₁` form a set of cardinality `ℵ₁`. -/
theorem mk_Iio_ord_aleph_one : #(Set.Iio (aleph 1).ord) = aleph 1 := by
  rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord, Cardinal.lift_aleph, Ordinal.lift_one]

