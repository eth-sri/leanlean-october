/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RowCorrectness
public import VaughtConjecture.Knight.OnePointRootedExtension
public import VaughtConjecture.Knight.ActualOccurrence

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType CellScheme Transform Value ExtOrd

variable {α : Ordinal.{0}} {m : ℕ}

theorem IsCoface.label_cellOf {p : S α m} {q : S α (m + 1)} (h : IsCoface p q)
    (d : Cell p.scheme.scheme) : q.label (h.extendsDomain.cellOf d) = p.label d := by
  have hvis := h.extendsDomain.visible
  have hp : q.restrictFace Fin.castSuccEmb hvis = p :=
    Option.some.inj ((typeMap_eq_some _ q hvis).symm.trans h)
  aesop

/-- The block representative's replaced value is the requested value. -/
theorem extVisibilityReplace_rep {μ : Ordinal.{0}} {j i N : ℕ} (hμ : limitPart μ = μ)
    (hj : j < N) : extVisibilityReplace (ofOrd (μ + j)) N i = ofOrd (μ + i) := by
  rw [extVisibilityReplace_ofOrd]
  unfold visibilityReplace
  have hfp : finitePart (μ + j) = j := by
    conv_lhs => rw [← hμ]
    exact finitePart_limitPart_add_nat μ j
  rw [hfp, if_pos hj]
  unfold ordinalReplace
  have hlp : limitPart (μ + j) = μ := by
    conv_lhs => rw [← hμ]
    rw [limitPart_limitPart_add_nat, hμ]
  rw [hlp]

end VaughtConjecture.Knight
