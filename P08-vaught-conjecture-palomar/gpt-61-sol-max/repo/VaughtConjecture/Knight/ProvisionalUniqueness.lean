import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.Terminal

/-! # Lemma 5.3.2: band-index independence, and functionality of `p⁺`

Knight's Lemma 5.3.2: clause 2.(b) of
Def. 5.3.1 is well defined — the band index `i` with `E(Θ)(Ξ) = E(Θ)(Ξ) ⊔⁺_{K^p} i` does not
depend on the witnessing full-scope `∞`-cell `Θ` of grade `K^p`.

**The argument in the faithful relation.**  Let `Θ, Θ'` be two witnesses, `a := E(Θ)(Ξ)`,
`a' := E(Θ')(Ξ)`, `K := K^p`.  Consistency of the rows (Def. 2.5.12) makes `E(Θ')` respect the
semantics on its lower set, so locality at `Θ` gives `E(Θ) ⇒ min(E(Θ') ∘ incl, E(Θ')(Θ))` with
witnesses `g, σ`.  Reading it at `Θ` shows `x := E(Θ')(Θ) ≤ g K`; reading it at `Ξ` gives
`min(a', x) = min(σ a, g (grade Ξ))`.  Failure of clause 2.(a) at `Σ := Θ'`, with `E(Θ)(Θ')`
self-visible at `K` by orderliness, gives `a < E(Θ)(Θ')`; symmetrically `a' < x`.  Hence
`a' = min(σ a, g (grade Ξ))`, and since `a' < x ≤ g K ≤ g (grade Ξ)` (`g` antitone), `a' = σ a`
with `σ a ≤ g K`.  Clause 5 of `⇒` then transports the band replacement at `K`:
`a' = σ a = σ (a ⊔⁺_K i) = σ a ⊔⁺_K i = a' ⊔⁺_K i`, so `i` is the finite part of `a'`, which is
also `i'`.

* `ProvisionalBand.unique` — Lemma 5.3.2.
* `IsProvisionalValue.unique` — Def. 5.3.1 is single-valued.
* `isProvisionalValue_iff` — `someProvisionalValue` computes THE provisional value.

Construction-private (not root-exported). -/

namespace VaughtConjecture.Knight

open  Value ExtOrd

namespace StageType

variable {α : Ordinal₀} {n : ℕ}

/-- A band witness reads the band index off the finite part of an ordinal row value below the
threshold (extracted from `ProvisionalBand.lt_topGrade`). -/
theorem ProvisionalBand.exists_ordinal {p : S α n} {Xi} {i}
    (htop : p.label Xi = ⊤) (hcap : ¬ p.ProvisionalCap Xi)
    {Θ} (hXiΘ : GradedLe (p.scheme.scheme.cell Xi) (p.scheme.scheme.cell Θ))
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (hΘtop : p.label Θ = ⊤)
    (heq : p.scheme.rows.E Θ ⟨Xi, hXiΘ⟩ =
      extVisibilityReplace (p.scheme.rows.E Θ ⟨Xi, hXiΘ⟩) p.topGrade i) :
    ∃ β , p.scheme.rows.E Θ ⟨Xi, hXiΘ⟩ = ofOrd β ∧
      finitePart β < p.topGrade ∧ i = finitePart β := by
  have hnotself  := fun hself =>
    hcap ⟨Θ, hXiΘ, ⟨Xi, hXiΘ⟩, hsc, hgr, hΘtop, htop, le_of_eq hself⟩
  rcases ExtOrd.cases (p.scheme.rows.E Θ ⟨Xi, hXiΘ⟩) with hbot | htop' | ⟨β, hβ⟩
  · rw [hbot] at hnotself
    exact absurd rfl hnotself
  · rw [htop'] at hnotself
    exact absurd rfl hnotself
  · rw [hβ, ] at hnotself heq
    have hfp : finitePart β < p.topGrade := by
      by_contra hge
      exact hnotself (congrArg ofOrd ((visibilityReplace_self_iff).mpr (not_lt.mp hge)))
    have hβeq  := by
      have h0 := ofOrd_inj.mp heq
      unfold visibilityReplace ordinalReplace at h0
      rwa [ite_eq_left hfp] at h0
    have hcast : i = (finitePart β : Ordinal₀) :=
      add_left_cancel (hβeq.symm.trans (decomposition β).symm)
    exact ⟨β, hβ, hfp, by exact_mod_cast hcast⟩

/-- Under `¬` clause 2.(a), the row of a witness `Θ` at `Ξ` lies strictly below its value at
any other witness `Θ'` (orderliness makes `E(Θ)(Θ')` self-visible at `K^p`). -/
theorem row_lt_of_not_cap {p : S α n} {Xi}
    (hcap : ¬ p.ProvisionalCap Xi)
    {Θ Θ'}
    (hXiΘ : GradedLe (p.scheme.scheme.cell Xi) (p.scheme.scheme.cell Θ))
    (hΘ'Θ : GradedLe (p.scheme.scheme.cell Θ') (p.scheme.scheme.cell Θ))
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (hΘtop : p.label Θ = ⊤) (hgr' : p.scheme.scheme.grade Θ' = p.topGrade)
    (hΘ'top : p.label Θ' = ⊤) :
    p.scheme.rows.E Θ ⟨Xi, hXiΘ⟩ < p.scheme.rows.E Θ ⟨Θ', hΘ'Θ⟩ := by
  by_contra hle
  have hle'  := not_lt.mp hle
  have hself := p.scheme.rows.orderly Θ ⟨Θ', hΘ'Θ⟩
  change p.scheme.rows.E Θ ⟨Θ', hΘ'Θ⟩ =
    extVisibilityReplace (p.scheme.rows.E Θ ⟨Θ', hΘ'Θ⟩)
      (p.scheme.scheme.grade Θ') (p.scheme.scheme.grade Θ') at hself
  rw [hgr'] at hself
  exact hcap ⟨Θ, hXiΘ, ⟨Θ', hΘ'Θ⟩, hsc, hgr, hΘtop, hΘ'top, hself ▸ hle'⟩

/-- **Lemma 5.3.2**: the band index of clause 2.(b) does not depend on the witness. -/
theorem ProvisionalBand.unique {p : S α n} {Xi}
    (htop : p.label Xi = ⊤) (hcap : ¬ p.ProvisionalCap Xi) {i i'}
    (h : p.ProvisionalBand Xi i) (h' : p.ProvisionalBand Xi i') : i = i' := by
  obtain ⟨Θ, hXiΘ, hsc, hgr, hΘtop, heq⟩ := h
  obtain ⟨Θ', hXiΘ', hsc', hgr', hΘ'top, heq'⟩ := h'
  -- the two witnesses lie below each other (same graded index)
  
  have hΘΘ' : GradedLe (p.scheme.scheme.cell Θ) (p.scheme.scheme.cell Θ') := by
    change p.scheme.scheme.scope Θ ⊆ p.scheme.scheme.scope Θ' ∧
      p.scheme.scheme.grade Θ ≤ p.scheme.scheme.grade Θ'
    simp [hsc', hgr, hgr']
  set K := p.topGrade with hK
  set a := p.scheme.rows.E Θ ⟨Xi, hXiΘ⟩ with ha
  set a' := p.scheme.rows.E Θ' ⟨Xi, hXiΘ'⟩ with ha'
  set x := p.scheme.rows.E Θ' ⟨Θ, hΘΘ'⟩ with hx
  -- strict comparisons from ¬ clause 2.(a)
  have ha'x  := row_lt_of_not_cap hcap hXiΘ' hΘΘ' hsc' hgr' hΘ'top hgr hΘtop
  -- locality of the row E(Θ') at Θ
  obtain ⟨g, σ, hganti, -, -, -, hσ5, hloc⟩ :=
    (p.scheme.consistent Θ').locality ⟨Θ, hΘΘ'⟩
  have hlocΘ := hloc ⟨Θ, GradedLe.refl _⟩
  have hlocΞ := hloc ⟨Xi, hXiΘ⟩
  change min (p.scheme.rows.E Θ' ⟨Θ, _⟩) x = min (σ (p.scheme.rows.E Θ ⟨Θ, _⟩))
    (g (p.scheme.scheme.grade Θ)) at hlocΘ
  change min (p.scheme.rows.E Θ' ⟨Xi, _⟩) x = min (σ a) (g (p.scheme.scheme.grade Xi)) at hlocΞ
  have hxle : x ≤ g K := by
    grind
  have hgradeXi  := by
    have h2 : p.scheme.scheme.grade Xi ≤ p.scheme.scheme.grade Θ := hXiΘ.2
    rw [hgr] at h2
    exact h2
  have hgle : g K ≤ g (p.scheme.scheme.grade Xi) := by
    rcases hgradeXi.lt_or_eq with hlt | heqg
    · exact hganti _ _ hlt
    · rw [heqg]
  have hmin  := min_eq_left ha'x.le
  
  -- a' < g (grade Ξ), so the right-hand minimum is σ a
  
  have ha'σ : a' = σ a := by
    grind
  have hσaK : σ a ≤ g K := ha'σ ▸ (ha'x.le.trans hxle)
  -- clause 5 transports the band replacement at K
  obtain ⟨β, hβ, hfp, hi⟩ := ProvisionalBand.exists_ordinal htop hcap hXiΘ hsc hgr hΘtop heq
  obtain ⟨β', hβ', hfp', hi'⟩ :=
    ProvisionalBand.exists_ordinal htop hcap hXiΘ' hsc' hgr' hΘ'top heq'
  have hiK  := (hi ▸ hfp).le
  have h5 := hσ5 a K hσaK i hiK
  rw [← heq] at h5
  -- h5 : σ a = extVisibilityReplace (σ a) K i
  have hβ'' : a' = ofOrd β' := hβ'
  rw [← ha'σ, hβ'', extVisibilityReplace_ofOrd] at h5
  have hβ'eq  := by
    have h0 := ofOrd_inj.mp h5
    unfold visibilityReplace ordinalReplace at h0
    rwa [ite_eq_left hfp'] at h0
  have hcast : (i) = (finitePart β' : Ordinal₀) :=
    add_left_cancel (hβ'eq.symm.trans (decomposition β').symm)
  have  := by exact_mod_cast hcast
  omega

/-- **Def. 5.3.1 is single-valued**: any two provisional values of a cell agree. -/
theorem IsProvisionalValue.unique {p : S α n} {Xi} {v v'}
    (h : p.IsProvisionalValue Xi v) (h' : p.IsProvisionalValue Xi v') : v = v' := by
  rcases h with ⟨hne, rfl⟩ | ⟨htop, hcap, rfl⟩ | ⟨htop, hcap, i, hband, rfl⟩ <;>
    rcases h' with ⟨hne', rfl⟩ | ⟨htop', hcap', rfl⟩ | ⟨htop', hcap', i', hband', rfl⟩
  · rfl
  · exact absurd htop' hne
  · exact absurd htop' hne
  · exact absurd htop hne'
  · rfl
  · exact absurd hcap hcap'
  · exact absurd htop hne'
  · exact absurd hcap' hcap
  · grind only [ProvisionalBand.unique]

/-- **The chooser computes the provisional value.** -/
theorem isProvisionalValue_iff {p : S α n} {Xi} {v} :
    p.IsProvisionalValue Xi v ↔ v = p.someProvisionalValue Xi :=
  ⟨fun h => h.unique (isProvisionalValue_someProvisionalValue p Xi),
    fun h => h ▸ isProvisionalValue_someProvisionalValue p Xi⟩


