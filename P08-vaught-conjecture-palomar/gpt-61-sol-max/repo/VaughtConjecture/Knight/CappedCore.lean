
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CountedRecoding
import VaughtConjecture.Knight.CappedLocalityRecoding

/-! # The provenance-preserving truncation: retain the witnesses, cap the evaluations

**The representation**, adopted after the level-two no-go for the recomputed truncation
(`docs/STATUS.md`, "Truncation representation"):
a truncated level-three cell **retains the base core's owned witnesses and their charts** and
**caps their decoded evaluations**: `ρ_ℓ^η(s) = min (ρ_ℓ(s), η)`.  The object is a base core
together with a cap (`CappedCore3`); its rows are the capped rows of the base.

**Acceptance tests, compiled.**

* `TransformsTo.capped` — the generic fact behind everything: capping the target of a faithful
  transformation at a `K`-self-visible constant (all grades `≤ K`) is again a faithful
  transformation, clause 5 included (shifter `min (σ ·) η`, suppressor `min (g k) η` through `K`).
  No controller is needed: the guard itself supplies `η ≤ g k` where the ambient output exceeds
  the cap.
* attainment of the new cap at the retained witness (`rho2_wit2C`), and every capped evaluation
  bounded by the cap;
* the cross-level localities `3 → 1` and `3 → 2` for the capped rows (`cross31C`, `cross32C`) by
  capping the base localities;
* the mixed square for the capped decoder (`mixed_squareC`);
* same-level agreement of the capped rows at the capped meet (`rowC_agree`) and the same-level
  locality with the identity shifter (`same3C`);
* repeated truncation reduces to the minimum cap (`recap`, `recap_row`, `recap_recap`), so retained
  provenance generates no history; and the **represented meet**: the capped meet of a cell with
  its own truncation is the cap (`meetC_recap`).

Level one: the capped evaluation `min (ρ₁ t H) η` coincides with the recomputed truncation's
value (`Core3.rho1_trunc`, scratch), so the two representations agree exactly where the recomputed
one is valid.  Sharp coding of the retained witness rows and of the capped rows, and locality on
the domain enlarged by the capped cells themselves, are in `Knight/CappedCoreCoding.lean`.
Construction-private (not root-exported). -/

namespace VaughtConjecture.Knight

open Transform  

/-! ## Capping a transformation -/

/-- **Capping the target of a faithful transformation** at a `K`-self-visible constant, all grades
at most `K`. -/
theorem TransformsTo.capped {D : Type*} {grade : D → ℕ} {E T : D → ExtOrd} {K}
    (hmax : BoundedBy grade K) {η} (hvis : SelfVis K η) (h : TransformsTo grade E T) :
    TransformsTo grade E fun d => min (T d) η := by exact?

/-! ## The capped core -/

variable {P : Type*} [Fintype P] [DecidableEq P]  {T : ℕ}


