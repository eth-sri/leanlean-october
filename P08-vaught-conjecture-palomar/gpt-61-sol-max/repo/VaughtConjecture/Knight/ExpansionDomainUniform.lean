import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.ExpansionDomainBF

/-! # Homogeneous expansion domains at the sentence's own rank

Sentence agreement is read from the domain's projected back-and-forth comparison,
with no extra `ω`-factor in the budget. The old one-block interface is unchanged.
These statements use expansion existence directly, not stopping ranks, and
terminal countability is needed only to count the exceptional classes.
-/

namespace VaughtConjecture.Knight.ExpansionDomain

open  FirstOrder Language  StoppingRankFiltration

/-- Membership in the expansion domain at `η` suffices for agreement on all
sentences of quantifier rank at most `η`. -/
theorem realizes_iff_of_mem_domain_uniform (φ : knightLang.Sentenceω)
    {η} (hφ : φ.qrank ≤ η) {q s}
    (hq : q ∈ domain η) (hs : s ∈ domain η) : realizes φ q ↔ realizes φ s := by
  revert hq hs
  refine Quotient.inductionOn₂ q s fun R S hq hs => ?_
  have key := @BFEquiv_implies_agreeQR knightLang ℕ inferInstance ℕ ℕ
    (structureOf R.1) (structureOf S.1) η 0 Fin.elim0 Fin.elim0
    (bfEquiv_of_mem_domain hq hs)
    (φ.relabelFree (Empty.elim))
    (by grind [BoundedFormulaInf.qrank_relabelFree])
  have he : (Fin.elim0 : Fin 0 → ℕ) ∘ (Empty.elim) = Empty.elim :=
    funext fun e => e.elim
  simp  [FormulaInf.Realize, BoundedFormulaInf.realize_relabelFree, he] at key
  exact key

