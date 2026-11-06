/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledRepair

/-! # The repaired semantics at grade three: exact probes, the admissible parameters, and the
two face sections

**The exact capped-probe laws** (`probe_orbit`, `probe_ordered`, `probe_fixed`,
`probe_bottom_orbit`, `label_of_probe_orbit`; after the research scout `CappedProbeLaws.lean`,
draft #319): in a row transformed onto the probes `min (p d) (p c)` of a controller `c` of
maximal grade with `p c` self-visible there, a source orbit `E e = replace (E d) k i` is an
**exact equation** on the capped probes for every `i ≤ k ≤ grade c`, sources order the probes,
fixed sources give self-visible probes, and bottom propagates along orbits at *every* threshold
(so the threshold-four obligation at a grade-three controller is never vacuous).  All from the
existing controller-capped witness `exists_cappedWitness`.

**Instantiated on the repaired rows** (`q` respecting `rowsR` on `(univ, 3)`): at `b₁`'s
controller, `z₁ = R₃ (min v w)` exactly (`A₁c_eq_R₃_min_of_respectsR`, the source `ω+1` reaching
the `a₁` cells' `ω+3`), `min v w` is fixed by the replacement `(3, 1)`
(`min_proper_ub₁_fixed_of_respectsR`, kept separately), and `min x₀ w` is grade-three
self-visible (`selfVis_min_H₀old_ub₁_of_respectsR`, the old witnesses' new source `ω·2+3` is).

**The admissible parameters** (`Legal₃`): legal grade-two parameters plus `z₁ ≤ z₂ ≤ x₀`,
`z₂ ≤ w ≤ H`, grade-three visibility of `z₁, z₂, w, min x₀ w`, the exact orbit, the fixing law,
and the two bottom couplings `z₁ = ⊥ → z₂ = ⊥`, `min x₀ w = ⊥ → w = ⊥`.  **The value shape**
(`Shape₃`): the seven parameters at the twelve named cells (the old level-two witness at
`min x₀ H`, the duplicates on their controllers), `⊥` at proper grade-two cells, `v` at proper
grade-one cells.

**Sufficiency** (`respects_of_shape₃`): admissible parameters in the value shape respect `rowsR`
on `(univ, 3)`.  Grades one and two are the grade-two sufficiency lemma; every grade-three row is
witnessed by one new shape, **the two-block strip** (`Witness.twoStrip`: `⊥` below `ω`; on the
block at `ω` the threshold-three orbit of `t` up to finite part three and a constant from four; on
the block at `ω·2` a constant up to three and another from four; the last constant beyond) — with
`t = min v z₁`, `min v z₂`, `min v w` at the `a₁`, `a₂`, `b₁` rows respectively, the orbit values
computed by the threshold-`K` orbit calculus `orbit_eq_K` and the block arithmetic at every block
(`blockIdx_eq`, `limitPart_of_block'`, `fp_le_of_block'`).  The one algebraic fact behind the
three instantiations: for any cap `a` between `z₁` and `w`, `R₃ (min v a) = z₁`
(`Legal₃.R₃_min_eq`; if `z₁ < v` then `z₁ = w`).  **No further condition appeared.**

**Necessity** (`shape_legal_of_respectsR`): every respecting labelling has the value shape with
admissible parameters — the characterization is an iff.

**The two face sections** (`faceA_extendsR`, `faceB_extendsR`): every labelling respecting
`rowsR` on the old face `({0,1,2}, 3)`, resp. the copy face `({1,2,3}, 3)`, extends to one
respecting it on `(univ, 3)`, by the explicit sections `(v, x, x, y, a, b, b)` (`sectA`) and
`(v, x, x, y, r, r, b)` with `r = R₃ (min v b)` (`sectB`), no block-specific constants; the face
constraints are read off the faces' own rows (`a₁old_le_a₂old'`, `a₂old_le_H₀old'`,
`a₂old_le_s₀old'`, `a₁old_eq_R₃_min'`, `fix_min_a₂old'`, `a₂old_eq_bot_of_a₁old'`,
`b₁new_le_H₀new'`, `b₁new_le_s₀new'`, `fix_min_b₁new'`).  These are the cap-`⊥` instances of the
two grade-three face obligations of `ProperToFullRLow`.

Not done: the capped lift (a nonbottom comparison cap `γ` and a second labelling `q`) — the
relative pasting rule of the research handoff — and hence the two face obligations in full and
bountifulness.  Construction-private. -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## The exact capped-probe laws (after the research scout `CappedProbeLaws.lean`) -/

section ProbeLaws

variable {D : Type*} {grade : D → ℕ} {E p : D → ExtOrd} {c : D}
  (hmax : ∀ d, grade d ≤ grade c) (hvis : SelfVis (grade c) (p c))
  (hloc : TransformsTo grade E (fun d => min (p d) (p c)))

include hmax hvis hloc

end ProbeLaws

/-! ## Instantiation on the repaired rows -/

section Instances

variable {q : D₂.below (Finset.univ, 3) → ExtOrd}

end Instances

/-! ## Block arithmetic at every block, and the threshold-`K` orbit calculus -/

section Blocks

end Blocks

/-! ## The two-block strip witness at threshold three -/

section TwoStrip

variable {t c₂ c₃ c₄ : ExtOrd}

/-! ### The strip at the actual sources -/

end TwoStrip

/-! ## The admissible parameters and the sufficiency theorem -/

section Sufficiency

namespace Legal₃

variable {vP x₀ x₁ H z₁ z₂ w : ExtOrd}

end Legal₃

end Sufficiency

/-! ## The sufficiency theorem -/

section SufficiencyProof

end SufficiencyProof

/-! ## Necessity: every respecting labelling is in the value shape with admissible parameters -/

section Necessity

variable {q : D₂.below (Finset.univ, 3) → ExtOrd}

end Necessity

/-! ## The face constraints (general lower sets) -/

section FaceConstraints

variable {BJ : Finset (Fin 4) × ℕ} {r : D₂.below BJ → ExtOrd}

end FaceConstraints

/-! ## The two face sections -/

section Sections

variable {BJ : Finset (Fin 4) × ℕ} {r : D₂.below BJ → ExtOrd}

end Sections

/-! ### Cell inequalities by grade and scope -/

section Ne

end Ne

/-! ### The A-face section -/

section SectionA

end SectionA

/-! ### The B-face section -/

section SectionB

end SectionB

end VaughtConjecture.Knight
