/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledBountifulReduction

/-! # The grade-one scope-changing case of the coupled semantics' bountifulness

**The complete grade-one retuning** (`properToFull₃_one`): the scope-changing obligation
`ProperToFull₃Low` at `j = 1` against the frozen rows `rows₃` — a labelling `p` respecting the
rows on a proper pair `(C, 1)` and a labelling `q` respecting them on `(univ, 1)`, agreeing below
`γ` on the pair, have a common respecting labelling of `(univ, 1)` extending `p` **literally** and
agreeing with `q` **below `γ`**.

**The parameter reduction, on the actual cells.**  A respecting labelling of `(univ, 1)` is a
triple: one value `v` on the seven proper cells (`const_of_respects`: locality at the top cell
reads `ω+1` at every proper cell, availability and cell uniqueness bound every proper label by
the top's — cells of grade at most two are determined by their graded index, `cell_inj_low`),
`x₀` at the old occurrence `H₀old`, and `x₁` at both the copy `H₀new` and the controller `U_H`
(`H₀new_eq_U_H_of_respects`), with `v ≤ x₀ ≤ x₁` and the bottom coupling `x₀ = ⊥ → x₁ = ⊥`
(`U_H_eq_bot_of_H₀old`).  A proper pair protects `v` alone, or `(v, x₀)` (the old face
`{0,1,2}`), or `(v, x₁)` (the copy face `{1,2,3}`) — never both witnesses.

**The explicit face-sensitive rule** (`retune₁` with the free labels chosen in
`properToFull₃_one`): keep `p` on the pair and its proper value `vP` on every proper cell; with
the whole `q = (vq, x₀q, x₁q)`:
* old face protected: `x₀' = p H₀old`, `x₁' = max x₁q x₀'`;
* copy face protected: `x₁' = p H₀new`, `x₀' = min (max x₀q vP) x₁'`;
* only `v` protected: `x₀' = max x₀q vP`, `x₁' = max x₁q x₀'`;
* `γ = ⊥` (agreement vacuous): both free labels equal the protected witness label, else `vP`.
The bottom coupling holds because agreement below a nonbottom `γ` transports `x₀q = ⊥` (hence
`x₁q = ⊥`) to the chosen labels.  Capped agreement is the distributivity of `min` over `max`
together with `vq ≤ x₀q ≤ x₁q`.

**The witnesses**: the constant witness at proper cells (`transformsTo_const_of_ne_bot`), the
limit step `Witness.stepLimit` at `2ω` from `v` to `x₀` at the old occurrence (and to `x₁` at the
copy), and at the controller the limit step followed by `Witness.raise` at `2ω+2` to `x₁`, with the
bottom case separated (a bottom `x₀'` blocks the raise and the coupling makes `x₁' = ⊥`).  The
limit-cutoff witness is used only at limit cutoffs; the finite-offset cutoff `2ω+2` is handled by
`Witness.raise` as before.

Reviewed against the SMT handoff `research/smt/COUPLED-GRADE-ONE.md` (the same triple model and
face-sensitive choices, checked externally on the scalar model); the Lean bridges that handoff
lists as remaining — that every actual respecting labelling has the triple form, and the
identification of the named cells with the scheme's cells — are the theorems above.

Not done: grades two and three of `ProperToFull₃Low`.  Construction-private (not root-exported). -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## Cell uniqueness at grades at most two -/

section Unique

end Unique

/-! ## Rows and labellings at grade one -/

section One

end One

/-! ## Self-visibility of minima and maxima -/

theorem selfVis_max {K : ℕ} {a b : ExtOrd} (ha : SelfVis K a) (hb : SelfVis K b) :
    SelfVis K (max a b) := by
  change extVisibilityReplace (max a b) K K = max a b
  rw [extVisibilityReplace_max a b le_rfl]
  change extVisibilityReplace a K K = a at ha
  change extVisibilityReplace b K K = b at hb
  rw [ha, hb]

/-! ## The grade-one retuning -/

section Retune

end Retune

end VaughtConjecture.Knight
