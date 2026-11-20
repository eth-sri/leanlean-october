/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExpansionDomainBF

@[expose] public section

namespace VaughtConjecture.Knight.ExpansionDomain

open TypeTower FirstOrder Language KnightRealization StoppingRankFiltration

/-- Membership in the expansion domain at `η` suffices for agreement on all
sentences of quantifier rank at most `η`. -/
theorem realizes_iff_of_mem_domain_uniform (φ : knightLang.Sentenceω)
    {η : Ordinal.{0}} (hφ : φ.qrank ≤ η) {q s : Classes}
    (hq : q ∈ domain η) (hs : s ∈ domain η) : realizes φ q ↔ realizes φ s := by
  revert hq hs
  refine Quotient.inductionOn₂ q s fun R S hq hs => ?_
  have key := @BFEquiv_implies_agreeQR knightLang ℕ inferInstance ℕ ℕ
    (structureOf R.1) (structureOf S.1) η 0 Fin.elim0 Fin.elim0
    (bfEquiv_of_mem_domain hq hs)
    (φ.relabelFree (Empty.elim : Empty → Fin 0))
    (by rw [BoundedFormulaInf.qrank_relabelFree]; exact hφ)
  have he : (Fin.elim0 : Fin 0 → ℕ) ∘ (Empty.elim : Empty → Fin 0) = Empty.elim :=
    funext fun e => e.elim
  simp only [FormulaInf.Realize, BoundedFormulaInf.realize_relabelFree, he] at key
  exact key

end VaughtConjecture.Knight.ExpansionDomain
