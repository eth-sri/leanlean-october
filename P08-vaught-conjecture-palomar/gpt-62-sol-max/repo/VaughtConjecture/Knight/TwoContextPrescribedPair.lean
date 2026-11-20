/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TwoContextAmalgam
public import VaughtConjecture.Knight.StageReindex

/-! # The original prescribed pair: common stage, shared-face compatibility, and the source
equations of the forced identification

**The fresh face, settled** (`reindex_p₁_Q`): input B's specified labelled type `p₁` is a
reindexing of the amalgam's fresh face `Q.restrictFace embB` through the copy embedding — the
literal face equation up to the enumeration of the cells (`typeMap_embB` gives only the
restriction with the induced enumeration; the copy embedding is not monotone in the indices).

**The original pair at a common stage**: `p₀'` is input A's specified labelling `p₀` (the row
of its cap `ω+4`) at the stage `ω·3` of `p₁`.  **Exact shared-face compatibility**
(`reindex_shared`): the restrictions of `p₀'` and of `p₁` to the shared pair `{1, 2}` are
reindexings of each other — graded indices, labels and rows agree cell by cell.  So the two
specified labellings are compatible on the shared face; the obstruction to realizing both is
not on the shared face.

**The source equations of the forced identification** (`mixed_source_eq`): every non-mute
controller of the fixed glue reads the same value at input A's level-one witness `H₀old` (on the
A face) and at its copy `H₀new` (on the fresh face), because both retract to the same cell of the
three-cell family; the controller-probe lemma turns this into `forced_identification` for every
respecting labelling, while the specified labels there differ (`specified_labels_differ`:
`ω+4` versus `ω·2+3`).  Separating the two occurrences requires mixed-controller rows reading
*different* sources there — `Knight/TwoContextSeparation.lean`.

Not claimed: any logical extension-spectrum distinction, or realization inside fixed models.
Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## The fresh face, settled: input B's labelled type is a reindexing of the restriction -/

section FreshFace

end FreshFace

/-! ## The original pair at a common stage, and exact shared-face compatibility -/

section Shared

end Shared

/-! ## The source equations forcing the witness-copy identification in the fixed glue -/

section Forced

end Forced

end VaughtConjecture.Knight
