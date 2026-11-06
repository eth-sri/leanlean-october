/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RowCorrectness
public import VaughtConjecture.Knight.EntailmentDomainCashout

/-!
# Lemma 10.1.1, finite fragment: readback from the pattern trigger, the cap, and one controller row

On the real objects: a domain `D` extending the base `p`, a prescribed labelling `q'`, and finite
reference data `R` over the cells of `D` (`Knight/RowCorrectness.lean`: cap at grade `N`, trigger,
block representatives, finite requests).  For every coface `q` of `p` with domain `D` and the
`⊥`-pattern of `q'`:

1. the pattern makes the trigger non-`⊥`;
2. availability from the cap — an old cell, so its label is pinned by `IsCoface.label_cellOf` —
   yields a controller `Ξ` at graded index `(univ, N)` with `q □ ≤ q Ξ`;
3. locality at `Ξ` gives a Def. 2.3.9 witness carrying the row of `Ξ` (correct by hypothesis) to
   `d ↦ min (q d) (q Ξ)`; the transported correctness
   (`FiniteReferenceData.Correct.transport_witness`) then reads back every requested finite
   label exactly: `q Θ = μ + i` (`ReadbackInputs.readback`).

No availability is applied at a requested cell and no same-grade "guard" is involved: full-grade
request cells are read through the controller's row.  No general transitivity of `⇒` is used; the
printed proof's chain of two transformations is replaced by one transported correctness and one
locality.  `ReadbackInputs` lists what the producer owes: the reference cells with their base
labels (Lemma 8.1.1's context enlargement), the existence of a controller at `(univ, N)`
(completeness of `D`), and correctness of every such controller's row (Def. 8.3.2's thinning).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType CellScheme Transform Value ExtOrd

variable {α : Ordinal.{0}} {m : ℕ}

/-! ## Label transport (local copies) -/

theorem StageType.label_castCell {t₁ t₂ : S α m} (h : t₁ = t₂) (d : Cell t₁.scheme.scheme) :
    t₂.label (SemScheme.castCell (congrArg StageType.scheme h) d) = t₁.label d := by grind [SemScheme.castCell_self]

theorem IsCoface.label_cellOf {p : S α m} {q : S α (m + 1)} (h : IsCoface p q)
    (d : Cell p.scheme.scheme) : q.label (h.extendsDomain.cellOf d) = p.label d := by
  have hvis := h.extendsDomain.visible
  have hp : q.restrictFace Fin.castSuccEmb hvis = p :=
    Option.some.inj ((typeMap_eq_some _ q hvis).symm.trans h)
  rw [← StageType.label_castCell hp.symm d]
  rfl

/-! ## Rows as total functions on the cells -/




/-! ## The producer's inputs and the readback theorem -/


theorem min_ne_bot {a b : ExtOrd} (ha : a ≠ ⊥) (hb : b ≠ ⊥) : min a b ≠ ⊥ := by grind

/-- The block representative's replaced value is the requested value. -/
theorem extVisibilityReplace_rep {μ : Ordinal.{0}} {j i N : ℕ} (hμ : limitPart μ = μ)
    (hj : j < N) : extVisibilityReplace (ofOrd (μ + j)) N i = ofOrd (μ + i) := by grind [ordinalReplace, visibilityReplace, extVisibilityReplace_ofOrd, limitPart_limitPart_add_nat, finitePart_limitPart_add_nat]


