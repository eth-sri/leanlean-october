/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RowReadback
public import VaughtConjecture.Knight.CountedRecoding
public import VaughtConjecture.Knight.Semantics

/-! # The capped-offset guard: reflection, safe predicates, and two-labelling readback

After the reviewer's notes `vc-notes/newapproach2.md` and `vc-notes/README.md`
(offset-guarded comparison, 2026-09-12; ported with attribution, checked here in Lean).

**The guard.**  For a marker `a` and a cap `C` of grade `N`, `Guard N j a C f` says the capped
marker `min (f a) (f C)` is a proper ordinal of finite part `j` (`j < N`).

* **Guard reflection** (`Guard.reflect`): if `f ⇒ f'` faithfully, `Guard f'` implies `Guard f`.
  The capped coordinates of the target are one monotone scalar map of the capped coordinates of
  the source (`capped_transform`); the suppressor value is `N`-visible while the target minimum
  is not, so the shifter sends the source minimum to it under the clause-5 guard, and clause 5 at
  the source's own finite offset pins that offset to `j`.  No transitivity of transformations is
  used.
* **Safe predicates** (`Safe`, `Safe.transport`): for a predicate `Φ` preserved by faithful
  transformation, `Guard f → Φ f` is preserved too.  A row outside the guard may remain incorrect;
  no faithful retuning of it becomes guarded and incorrect.
* **Top requests** (`TopRequests`, `TopRequests.Correct`, `.transport`): the capped marker is at
  most every requested capped coordinate; preserved because the same monotone map acts on both
  sides.  Proper requests are the finite correctness predicate of `Knight/RowCorrectness.lean`.
* **Strata** (`guard_min`, `not_guard_min`): the guard and its negation are both closed under
  pointwise minimum, since the capped marker of a meet is one of the two capped markers.
* **Two-labelling readback at a selected controller** (`guarded_readback_at`): with two
  labellings respecting the same rows — `q` ordinary, `s` "stable" — a controller `Θ` labelled
  `⊤` by `q` whose row is safe, and the guard active on the stable capped target at `Θ`, the
  ordinary labelling satisfies both correctness predicates: the guard reflects along the stable
  locality to the row, safety gives the row's correctness, and ordinary locality transports it to
  `q` capped at `q Θ = ⊤`.  `select_top_controller` supplies `Θ` from ordinary availability at a
  top-labelled cap; `read_proper`/`read_top` read the exact labels.  Nothing assumes `q ⇒ s` or
  that the stable labelling satisfies model axioms.

What this does not do: construct a legal request domain whose full-scope rows are safe, nor
supply the stable labelling and its guard activation (those come from the actual model's
stable values in the reviewer's lane).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

section Guard

variable {D : Type*} {grade : D → ℕ}

/-- **Top requests**: a marker and a list of requested cells, all of grade at most the cap's. -/
structure TopRequests (D : Type*) (grade : D → ℕ) where
  /-- The threshold. -/
  N : ℕ
  /-- The cap cell, of grade `N`. -/
  cap : D
  cap_grade : grade cap = N
  /-- The trigger cell. -/
  trigger : D
  /-- The marker cell. -/
  marker : D
  marker_grade_le : grade marker ≤ N
  /-- The requested top cells. -/
  tops : List D
  top_grade_le : ∀ y ∈ tops, grade y ≤ N

end Guard

/-! ## Two-labelling readback at a selected controller -/

section Readback

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

end Readback

end VaughtConjecture.Knight
