/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledGradeThreeOrbit

/-! # The frozen coupled semantics is not bountiful

A no-go for the frozen rows `rows₃`, after the research scout `BottomFace.lean` (draft #319,
2026-09-06).  Nothing in the construction is changed: coding, consistency, availability and the
realization of the prescribed pair (`coupled_realization`) stand; the reduction
`rows₃_isBountiful_of` stands; what fails is its hypothesis `ProperToFull₃Low`, hence
`rows₃.IsBountiful` (`rows₃_not_bountiful`), so `semSchemeCoupled` has no instance.

**The legal input** (`bottomFaceB_respects`, `bottomFace_respects`): on input B's own family put
`⊥` at every proper cell and the ordinal `3` at the three full-scope cells `H₀`, `s₀`, `b₁`.  This
respects input B's semantics — locality at the full cells by the limit step at `ω·2`
(`Witness.stepLimit`: the proper sources are `⊥` or in the block at `ω`, the witness and cap
sources in the block at `ω·2`), the all-bottom transformation at the proper cells, availability
because every full label is `3` — and, transported to the actual B face `({1,2,3}, 3)` of the
coupled scheme, respects the frozen rows there (they are input B's).

**The obstruction** (`ub₁_eq_bot_of_proper_bot`), from the necessary constraints already
compiled: a bottom proper grade-one label `v` gives `z₁ ≤ R₃ v = ⊥` (the moving orbit
`A₁c_le_R₃_of_respects`), then `z₂ = ⊥` (`A₂c_eq_bot_of_A₁c`), then `min x₀ w = ⊥`
(`A₂c_eq_min_of_respects`); if `w ≠ ⊥` then `x₀ = ⊥`, so `x₁ = ⊥` (`U_H_eq_bot_of_H₀old`), and
`w ≤ q U_S ≤ x₁` (`ub₁_le_U_S_of_respects`, `U_S_le_U_H_of_respects`) forces `w = ⊥`.  But the
copy of `b₁` is labelled like `b₁`'s controller (`b₁new_eq_ub₁_of_respects`), and the face puts
`3` there (`bottomFace_no_extension`).  So the obligation fails at the pair `({1,2,3}, 3)`, cap
`⊥`, second labelling `qL` (`not_properToFull₃Low`).

**What the chain identifies.**  Every link is a construction-owned full row or an inherited
orbit: `ω+1 ↦ ω+3` in `a₁`'s controller's row (inherited from input A's cap `a₁`, and equally
present in the old cap's own row); `ω+3 ↦ ω+4` in `a₂`'s controller's row (inherited from `a₂`);
`b₁`'s controller reading the *same* source `ω+4` at the old occurrence `H₀old` and at `a₂`'s
controller (construction-owned: the lowered labelling `qL` is that row); the separating source
pair `ω·2+1 ↦ ω·2+2` in the grade-one controller's row (construction-owned); the antitone
suppressor chain `w ≤ q U_S ≤ q U_H`.  A repair must support this bottom face *and* the original
prescribed pair; moving one source to a new block need not suffice, since locality with the
inherited A rows can force the same interaction back.  Construction-private. -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd


end VaughtConjecture.Knight
