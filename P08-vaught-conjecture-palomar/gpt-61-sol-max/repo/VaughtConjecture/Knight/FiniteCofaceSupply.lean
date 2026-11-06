/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.FiniteTupleGeometry

/-! # Prescribed finite coface supply

These contracts prescribe an entire coface. Family-serving supply is kept separately in
`FiniteFamilySupply`; no strengthening is made during extraction. -/

namespace VaughtConjecture.Knight
namespace FixedHeight
variable  {β : LimitStage}

/-- **The pinned master-coface supply** (the completion gate's missing input): a coface of
the current master whose face over `g⌢last` is a PRESCRIBED coface of the base's face.
This is the exact old-pin/visibility collision: the new domain must keep the initial face
`dom P` literally (the old pin), make the face `g⌢last` VISIBLE in its plan, and restrict
there to `dom q` with the labels of `q` — a span gluing of two prescribed faces over their
common face `dom p`, where the compiled engine (`exists_respects_extends_capped`) pins ONE
face only.  The clean theorem to return to Knight-VC. -/
def PinnedCofaceSupply (β : LimitStage) : Prop :=
  ∀ {N n} P g p,
    typeMap g P = some p → ∀ q : S β.1 (n + 1), IsCoface p q →
      ∃ Q : S β.1 (N + 1), IsCoface P Q ∧ typeMap (extendFace g) Q = some q

