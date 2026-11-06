/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TwoContextSeparation
public import VaughtConjecture.Knight.WitnessAlgebra

/-! # The coupled construction: separating mixed rows at grades one to three, jointly with a
respecting labelling realizing the original prescribed pair

**The milestone**: one attachment of the two contexts realizing the prescribed data — the
specified labellings `p₀` (input A, the row of its cap `ω+4`) and `p₁` (input B, the row of its
cap `ω·2+3`) — with both input faces (cells, rows, labels) untouched (`coupled_realization`).
Legality is established except bountifulness: the modified semantics `rows₃` is **coded**
(`rows₃_coded`) and **consistent** (`rows₃_consistent`), agrees with the fixed glue `rows₂` on
both faces (`rows₃_faceA`, `rows₃_faceB`), and the labelling `qL` **respects** it on the full
grade-three lower set (`qL_respects`) and **realizes the pair** (`qL_realizes`).

**The rows.** Exactly three rows change, at the three fresh full-scope controllers that the
labels force to separate (`separating_controllers_of_realizes`):
* grade one (`U_H`, the full copy of the level-one witness): the tested row — the pulled-back
  row with the separating value `ω·2+2` at the copy `H₀new` and at the diagonal (`vU`);
* grade two (`U_S`, the full copy of the level-two witness): the pulled-back row with `ω·2+3` at
  the copies of `H₀` and `s₀`, at `U_H` and at the diagonal (`vS`) — the raised grade-one value
  propagates through the grade-two row's value at `U_H` (`locality_U_S_U_H`: a double
  `Witness.raise`), not by raising the diagonal alone;
* grade three (`ub₁`, the full copy of input B's cap): the row *is* the labelling.
The other two level-three copies (`A₁c`, `A₂c`) and the mute cell keep their pulled-back rows.

**The labelling** `qL` is input B's row pulled back (`labelQ`), lowered to `ω+4` at input A's
two witnesses `H₀old`, `s₀old`.  On the A face it is the row of input A's cap `a₂`
(`qL_castAdd`), on the B face input B's row (`qL_of_B`).

**The witnesses.** The labelling's locality at `U_H` and `U_S` is a **clamp** witness
(`Witness.clamp`, new here: `min a c` below a cutoff of finite part `> K`, the constant `c'`
from the cutoff on): the grade-one decoder must send the cap codes `ω·2+1`, `ω·2+2` *down* to
`ω+4` and the separating values *up* to `ω·2+3`, which neither `Witness.raise` nor
`Witness.lower` alone can do.  Consistency at the higher controllers uses the two generic
modifications `transformsTo_of_raise` (raised sources under a cap) and `transformsTo_of_between`
(a source replaced by the source of a cell with equal target, between the two), and the explicit
raises `witness_raise2`, `witness_raise_H`, `witness_raise_s`.  The numeric code values are
computed (`H₀c.δ = ω·2+1`, `s₀c.γ = ω·2+2`, `v₀` the only proper value).

**Not claimed**: bountifulness of `rows₃` (Def. 2.5.14; `rows₂`'s was proved from the two face
obligations, stated against the glue's rows), the `SemScheme` packaging, any logical
extension-spectrum distinction, realization inside fixed models.  Construction-private
(not root-exported). -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## The numeric codes of the three-cell family -/

section Values

/-! ### The rows of the three-cell family at `s₀` -/

end Values

/-! ## A general witness: clamp below a cutoff, constant above -/

section Clamp

end Clamp

/-! ## The cell inventory of the glued domain -/

section Inventory

/-- **The pulled-back row of a full cell of the three-cell family, as a total function.** -/
noncomputable def pull (x : family₂.X) (d : Cell D₂) : ExtOrd :=
  if mute₂ d then ⊥ else family₂.rowX x (family₂.e.symm (ret₂ d))

end Inventory

/-! ## The labelling and the three modified rows -/

section Rows

/-! ### Orderliness and coding of the modified rows -/

end Rows

/-! ## Generic transport lemmas -/

section Generic
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

end Generic

/-! ## Classification of the cells -/

section Classification

end Classification

/-! ## Values of the labelling and of the rows -/

section LabelValues

end LabelValues

/-! ## Row values at the modified controllers -/

section RowValues

/-! ### Cases below the controllers -/

/-! ### Values of the labelling -/

/-! ### Values of the grade-one row -/

/-! ### Values of the grade-two row -/

end RowValues

/-! ## The labelling respects the modified semantics -/

section Respect

end Respect

/-! ## Consistency of the modified semantics -/

section Consistency

/-! ### Scopes of the new occurrences -/

/-! ### The grade-one controller -/

/-! ### The grade-two controller -/

/-! ### The two level-three copies: raised sources under a cap, lowered sources between -/

end Consistency

/-! ## The realization -/

section Realization

end Realization

end VaughtConjecture.Knight
