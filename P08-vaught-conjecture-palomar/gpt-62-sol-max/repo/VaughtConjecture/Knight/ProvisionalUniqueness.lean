/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Terminal

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

/-- The transform data of the locality of `E_q(Θ)` at `Ψ'`, read at a cell `d` below `Ψ'`:
`min (E_q Θ d) y = min (σ (E_q Ψ' d)) (g (grade d))`, together with `y ≤ g (grade Ψ')`. -/
theorem locality_data {q : S α n} {Θ Ψ' : Cell q.scheme.scheme}
    (hΨ'Θ : GradedLe (q.scheme.scheme.cell Ψ') (q.scheme.scheme.cell Θ)) :
    ∃ (g : ℕ → ExtOrd) (σ : ExtOrd → ExtOrd),
      Antitone g ∧ Monotone σ ∧
      (∀ (a : ExtOrd) (k : ℕ), σ a ≤ g k → ∀ i : ℕ, i ≤ k →
        σ (extVisibilityReplace a k i) = extVisibilityReplace (σ a) k i) ∧
      (∀ d : q.scheme.scheme.below (q.scheme.scheme.cell Ψ'),
        min (q.scheme.rows.E Θ ⟨d.1, d.2.trans hΨ'Θ⟩) (q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩) =
          min (σ (q.scheme.rows.E Ψ' d)) (g (q.scheme.scheme.grade d.1))) ∧
      q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩ ≤ g (q.scheme.scheme.grade Ψ') := by
  obtain ⟨g, σ, hganti, -, -, hσmono, hσ5, hloc⟩ := (q.scheme.consistent Θ).locality ⟨Ψ', hΨ'Θ⟩
  exact ⟨g, σ, antitone_iff_forall_lt.mpr hganti, hσmono, hσ5, hloc,
    (min_self _).symm.trans_le ((hloc ⟨Ψ', GradedLe.refl _⟩).trans_le (min_le_right _ _))⟩

theorem uncapped_eq {a b x y : ExtOrd} (h : min a x = min b y)
    (hx : a < x) (hy : a < y) : a = b := by
  grind

theorem band_eq_finitePart {β : Ordinal.{0}} {K i : ℕ} (h : finitePart β < K)
    (he : ofOrd β = extVisibilityReplace (ofOrd β) K i) : i = finitePart β := by
  rw [extVisibilityReplace_ofOrd, ofOrd_inj, visibilityReplace, if_pos h, ordinalReplace] at he
  simpa only [finitePart_limitPart_add_nat] using (congrArg finitePart he).symm

/-- A band witness reads the band index off the finite part of an ordinal row value below the
threshold (extracted from `ProvisionalBand.lt_topGrade`). -/
theorem ProvisionalBand.exists_ordinal {p : S α n} {Xi : Cell p.scheme.scheme} {i : ℕ}
    (htop : p.label Xi = ⊤) (hcap : ¬ p.ProvisionalCap Xi)
    {Θ : Cell p.scheme.scheme} (hXiΘ : GradedLe (p.scheme.scheme.cell Xi) (p.scheme.scheme.cell Θ))
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (hΘtop : p.label Θ = ⊤)
    (heq : p.scheme.rows.E Θ ⟨Xi, hXiΘ⟩ =
      extVisibilityReplace (p.scheme.rows.E Θ ⟨Xi, hXiΘ⟩) p.topGrade i) :
    ∃ β : Ordinal.{0}, p.scheme.rows.E Θ ⟨Xi, hXiΘ⟩ = ofOrd β ∧
      finitePart β < p.topGrade ∧ i = finitePart β := by
  have hnotself :
      extVisibilityReplace (p.scheme.rows.E Θ ⟨Xi, hXiΘ⟩) p.topGrade p.topGrade ≠
        p.scheme.rows.E Θ ⟨Xi, hXiΘ⟩ := fun hself =>
    hcap ⟨Θ, hXiΘ, ⟨Xi, hXiΘ⟩, hsc, hgr, hΘtop, htop, le_of_eq hself⟩
  rcases ExtOrd.cases (p.scheme.rows.E Θ ⟨Xi, hXiΘ⟩) with hb | ht | ⟨β, hβ⟩
  · exact (hnotself (by rw [hb]; rfl)).elim
  · exact (hnotself (by rw [ht]; rfl)).elim
  · rw [hβ] at hnotself heq
    have hfp : finitePart β < p.topGrade := by
      rw [extVisibilityReplace_ofOrd] at hnotself
      exact lt_of_not_ge fun h => hnotself (congrArg ofOrd ((visibilityReplace_self_iff β _).mpr h))
    exact ⟨β, hβ, hfp, band_eq_finitePart hfp heq⟩

/-- Under `¬` clause 2.(a), the row of a witness `Θ` at `Ξ` lies strictly below its value at
any other witness `Θ'` (orderliness makes `E(Θ)(Θ')` self-visible at `K^p`). -/
theorem row_lt_of_not_cap {p : S α n} {Xi : Cell p.scheme.scheme}
    (hcap : ¬ p.ProvisionalCap Xi)
    {Θ Θ' : Cell p.scheme.scheme}
    (hXiΘ : GradedLe (p.scheme.scheme.cell Xi) (p.scheme.scheme.cell Θ))
    (hΘ'Θ : GradedLe (p.scheme.scheme.cell Θ') (p.scheme.scheme.cell Θ))
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (hΘtop : p.label Θ = ⊤) (hgr' : p.scheme.scheme.grade Θ' = p.topGrade)
    (hΘ'top : p.label Θ' = ⊤) :
    p.scheme.rows.E Θ ⟨Xi, hXiΘ⟩ < p.scheme.rows.E Θ ⟨Θ', hΘ'Θ⟩ := by
  by_contra hle
  have hle' : p.scheme.rows.E Θ ⟨Θ', hΘ'Θ⟩ ≤ p.scheme.rows.E Θ ⟨Xi, hXiΘ⟩ := not_lt.mp hle
  have hself := p.scheme.rows.orderly Θ ⟨Θ', hΘ'Θ⟩
  change p.scheme.rows.E Θ ⟨Θ', hΘ'Θ⟩ =
    extVisibilityReplace (p.scheme.rows.E Θ ⟨Θ', hΘ'Θ⟩)
      (p.scheme.scheme.grade Θ') (p.scheme.scheme.grade Θ') at hself
  rw [hgr'] at hself
  exact hcap ⟨Θ, hXiΘ, ⟨Θ', hΘ'Θ⟩, hsc, hgr, hΘtop, hΘ'top, hself ▸ hle'⟩

/-- **Lemma 5.3.2**: the band index of clause 2.(b) does not depend on the witness. -/
theorem ProvisionalBand.unique {p : S α n} {Xi : Cell p.scheme.scheme}
    (htop : p.label Xi = ⊤) (hcap : ¬ p.ProvisionalCap Xi) {i i' : ℕ}
    (h : p.ProvisionalBand Xi i) (h' : p.ProvisionalBand Xi i') : i = i' := by
  obtain ⟨Θ, hXiΘ, hsc, hgr, hΘtop, heq⟩ := h
  obtain ⟨Θ', hXiΘ', hsc', hgr', hΘ'top, heq'⟩ := h'
  -- the two witnesses lie below each other (same graded index)
  have hΘ'Θ : GradedLe (p.scheme.scheme.cell Θ') (p.scheme.scheme.cell Θ) := by
    refine ⟨?_, ?_⟩
    · simp_all
    simp_all
  have hΘΘ' : GradedLe (p.scheme.scheme.cell Θ) (p.scheme.scheme.cell Θ') := by
    simp_all
  let a := p.scheme.rows.E Θ ⟨Xi, hXiΘ⟩
  let a' := p.scheme.rows.E Θ' ⟨Xi, hXiΘ'⟩
  let x := p.scheme.rows.E Θ' ⟨Θ, hΘΘ'⟩
  have hax : a' < x := row_lt_of_not_cap hcap hXiΘ' hΘΘ' hsc' hgr' hΘ'top hgr hΘtop
  obtain ⟨g, σ, hg, -, hσ, hloc, hx⟩ := locality_data hΘΘ'
  have he : a' = σ a := uncapped_eq (hloc ⟨Xi, hXiΘ⟩) hax
    (hax.trans_le (hx.trans (hg hXiΘ.2)))
  obtain ⟨_, -, hfp, hi⟩ := ProvisionalBand.exists_ordinal htop hcap hXiΘ hsc hgr hΘtop heq
  obtain ⟨β, hβ, hfp', hi'⟩ := ProvisionalBand.exists_ordinal htop hcap hXiΘ' hsc' hgr' hΘ'top heq'
  have hw : σ a ≤ g p.topGrade := by rw [← he, ← hgr]; exact hax.le.trans hx
  have hr := hσ a p.topGrade hw i (hi ▸ hfp.le)
  change a = extVisibilityReplace a p.topGrade i at heq
  change a' = ofOrd β at hβ
  rw [← heq, ← he, hβ] at hr
  exact (band_eq_finitePart hfp' hr).trans hi'.symm

/-- **Def. 5.3.1 is single-valued**: any two provisional values of a cell agree. -/
theorem IsProvisionalValue.unique {p : S α n} {Xi : Cell p.scheme.scheme} {v v' : ExtOrd}
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
  · rw [ProvisionalBand.unique htop hcap hband hband']

/-- **The chooser computes the provisional value.** -/
theorem isProvisionalValue_iff {p : S α n} {Xi : Cell p.scheme.scheme} {v : ExtOrd} :
    p.IsProvisionalValue Xi v ↔ v = p.someProvisionalValue Xi :=
  ⟨fun h => h.unique (isProvisionalValue_someProvisionalValue p Xi),
    fun h => h ▸ isProvisionalValue_someProvisionalValue p Xi⟩

end StageType

end VaughtConjecture.Knight
