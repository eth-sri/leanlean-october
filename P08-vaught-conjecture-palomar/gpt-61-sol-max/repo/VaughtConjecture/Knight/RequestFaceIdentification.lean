/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.RequestAttachment

/-! # The exact identification of the request face

On the cell inventory `requestInventory` over the common plan
(`Knight/RequestAttachment.lean`), the cells visible on the request face are identified with
**all** the request's cells, not only its fresh ones: a fresh request cell is its embedding
`freshCell`; a root request cell (one not containing the fresh point) is identified through
the **shared root** — the equality of the context's restriction to the root face with the
request's restriction to its initial face — and the context's own cell map `toCell`.

* `reqCell : Cell Y → Cell (requestInventory …)` is injective (`reqCell_injective`: distinct
  request cells sharing a graded index stay distinct — index equality is not cell equality),
  lands in the cells visible on the request face (`scope_reqCell_subset`), and every visible
  cell is hit (`exists_reqCell_eq`).
* **Graded-index transport** (`cell_reqCell`): the inventory's graded index of `reqCell c` is
  the request's, pushed along `onePointProj e`.
* **Lower-domain transport** (`gradedLe_reqCell_iff`, `reqBelowEquiv`): the graded order of
  the request is the graded order of the inventory on the identified cells, and the lower set
  of a request cell corresponds bijectively to the lower set of its image.  Likewise for old
  cells (`oldBelowEquiv`): the lower set of an old cell consists of old cells.
* **The rows prescribed by both faces** (`prescribedRows`): old cells carry the context's rows,
  fresh request cells the request's rows, remaining-index cells a parameter; **literal old-face
  preservation** (`prescribedRows_old`), **request-face preservation up to the explicit
  enumeration** on fresh cells (`prescribedRows_fresh`) and on root cells through the context's
  cells (`prescribedRows_root`) — the request's row there exactly when the two faces' rows agree
  on the shared root, which is `ReferenceContext.shared_root` (rows included) over the actual
  context.
* **The first mixed scope** (section `MixedScope`): a degenerate consistent row (the mute row)
  is available but mutes the cell; the diagonal row is consistent under diagonal respect of the
  lower rows (sufficient, not an equivalence); bountifulness, realization of the prescribed
  pair, and the forced reduced projection remain three separate obligations.

Two distinctions kept throughout.  The request's **rows** are prescribed literally, but its
**labels** are prescribed after reduction: a requested `⊤` is an upstairs value at least `β`,
not a literal upstairs `⊤` (`reduced_label_iff`).  And reference-row correctness remains a
sufficient construction route for readback, not a necessary interface.

Construction-private (not root-exported). -/

namespace VaughtConjecture.Knight

open  CellScheme
open CellScheme.restrictFace (toCell pushGraded gradedLe_pushGraded_iff)

/-! ## Cell transport along an equality of schemes -/


/-! ## The identification -/


/-! ## The rows prescribed by both faces -/


/-! ## The first mixed scope: a degenerate consistent row is available; adequacy is separate

At a remaining-index cell `M` (the first mixed scope: its lower set carries old cells with the
context's rows, fresh request cells with the request's rows, and lower remaining-index cells),
two candidate rows are compiled with their witnesses.

* **The mute row** (`⊥` everywhere below `M`) is a **degenerate consistent row**, available
  unconditionally: every row transforms onto constant `⊥` (`TransformsTo.to_bot`, shifter
  constantly `⊥`), availability is trivial (`respects_bot_row`).  It is semantically inadequate:
  every labelling respecting the rows reads `⊥` at `M` (`label_eq_bot_of_bot_row`, the mute
  obstruction of `Knight/Domain.lean` at one cell), and availability then pins lower same-grade
  cells whenever `M` is the only cell at its index.  Useful nonmute rows still require their
  own consistency proofs.
* **The diagonal row** (each lower cell read at its own diagonal, a dominating orderly top at
  `M`) is consistent **under** diagonal respect of the lower rows — a sufficient condition, not
  an equivalence: each lower row transforms onto the capped diagonals of its own lower set, and
  the diagonals are available (`respects_diagonal_row`, with the identity witness at `M`).
  Diagonal respect is a condition on the input rows that coding and consistency do not imply:
  a row reading `⊥` at a lower cell whose own diagonal is not `⊥` cannot transform onto the
  capped diagonals when the capping diagonal is also not `⊥` (a shifter fixes `⊥`, and the cap
  would have to be `⊥` for the target to be); both relevant diagonals must be nonbottom for
  this bottom-source obstruction — a nonbottom lower diagonal alone is not enough.

Three obligations stay separate, as the legal-glue counterexample of the coupled construction
already showed they are: **bountifulness** of the rows (respecting extensions of every
permitted labelling of the two faces), **realization of the prescribed pair**, and the
**forced reduced projection** (reduced projected correctness), to which reference-row
correctness remains a sufficient route.  None of the three is settled by either candidate row;
additional cells at an outside index (several rows at one index) are the room availability
leaves.  The slack-cut pasting theorem (#346) takes two labellings already respecting the rows
on the common lower set and pastes them at a cap self-visible one grade above the scheme, with
availability reduced to an overlap condition on their high controllers; it can simplify the
subsequent paste at slack caps, but it does not produce the first section and it does not
discharge boundary caps. -/

section

open Transform Value

/-- Every labelling transforms onto the constant bottom: the shifter constantly `⊥`. -/
theorem TransformsTo.to_bot {E : Type*} {grade : E → ℕ} {p : E → ExtOrd} :
    TransformsTo grade p (fun _ => ⊥) :=
  ⟨fun _ => ⊤, fun _ => ⊥, fun _ _ _ => le_rfl, fun _ => rfl, rfl, monotone_const,
    fun _ _ _ _ _ => (extVisibilityReplace_bot _ _).symm,
    fun _ => (min_eq_left bot_le).symm⟩

variable {ι : Type*} [DecidableEq ι]   


