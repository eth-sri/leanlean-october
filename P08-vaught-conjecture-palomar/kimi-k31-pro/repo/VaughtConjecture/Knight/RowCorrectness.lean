/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Transform
public import VaughtConjecture.Knight.VisibilityAlgebra

/-!
# Row correctness (Def. 8.3.1, finite-value fragment) and its transport along `⇒` (Lemma 8.3.3)

Knight's Def. 8.3.1 states correctness of a *row* `f` relative to reference cells of an enlarged
context: a cap `□` of grade `N`, one representative `□_μ` per limit block `μ` occurring among the
requested finite labels, and a trigger `Σ♦`.  Its finite-value clause (clause 2), guarded by the
trigger `f Σ♦ ≥ 0`, reads

    min (f Θ) (f □) = min (f (□_μ) ⊔⁺_N i) (f □)      whenever the requested label of Θ is μ + i.

Lemma 8.3.3 asserts that correctness is preserved by `⇒`, "as a consequence of the logical form
in which correctness is defined".  This file proves the finite-value fragment of that claim on the
faithful relation (`Transform.TransformsTo`, Def. 2.3.9 verbatim, unguarded clause 5), with no
transitivity of `⇒`, and records the four facts the one-line proof leaves implicit:

1. the common cap at grade `N` absorbs the grade-dependent suppression of the lower-grade cells
   (`g N ≤ g (grade d)`), so the target equation reduces to the source equation under `σ`;
2. visibility replacement at threshold `N` commutes with the shifter (clause 5) when the
   representative's image lies under the cap, and a self-visible cap survives replacement from
   below (`le_extVisibilityReplace_of_selfVis_le`);
3. the trigger survives in the needed direction (`f' Σ♦ ≠ ⊥ → f Σ♦ ≠ ⊥`, from `σ ⊥ = ⊥`);
4. the remaining case — representative above the cap but its replacement below — is impossible:
   clause 5 applied to the *replaced* representative, re-replacement of the finite part
   (`extVisibilityReplace_extVisibilityReplace_finitePart`, which needs the offset `< N`), and
   self-visibility of `g N` contradict it.

The `∞` clauses of Def. 8.3.1 (clauses 3–5, branch-specific) are not treated here.

The transport is stated for a Def. 2.3.9 witness (`TransformWitness`) as well as for the relation
(`FiniteReferenceData.Correct.transport`), and correctness only inspects the reference and
requested cells (`FiniteReferenceData.Correct.congr`), so a row restricted to a lower set can be
transported after extension by `⊥`.  Consumed by the Lemma 10.1.1 readback (in preparation).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## Reference data and the finite-value correctness predicate -/



variable {D : Type*} {grade : D → ℕ}


/-! ## Value lemmas -/

/-- `min` distributes over a monotone shifter. -/
theorem monotone_min_apply {σ : ExtOrd → ExtOrd} (hσ : Monotone σ) (a b : ExtOrd) :
    σ (min a b) = min (σ a) (σ b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (hσ h)]
  · rw [min_eq_right h, min_eq_right (hσ h)]



/-! ## Lemma 8.3.3, finite fragment: correctness is preserved by `⇒` -/





