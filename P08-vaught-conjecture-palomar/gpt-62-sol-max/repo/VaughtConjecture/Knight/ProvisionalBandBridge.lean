/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RestrictedComposition
public import VaughtConjecture.Knight.ProvisionalUniqueness
public import VaughtConjecture.Knight.FiniteRowReadback

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

/-- At a top witness, an uncapped top row belongs to a finite band. -/
theorem uncapped_row {p : S α n} {Θ : Cell p.scheme.scheme}
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (hΘ : p.label Θ = ⊤) (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ))
    (hd : p.label d.1 = ⊤) (hn : ¬ p.ProvisionalCap d.1) :
    ∃ ν, p.scheme.rows.E Θ d = ofOrd ν ∧ finitePart ν < p.topGrade ∧
      p.ProvisionalBand d.1 (finitePart ν) := by
  have he : extVisibilityReplace (p.scheme.rows.E Θ d) p.topGrade p.topGrade ≠ p.scheme.rows.E Θ d :=
    fun h => hn ⟨Θ, d.2, d, hsc, hgr, hΘ, hd, h.le⟩
  rcases ExtOrd.cases (p.scheme.rows.E Θ d) with hb | ht | ⟨ν, hν⟩
  · simp [hb] at he
  · simp [ht] at he
  · have hf : finitePart ν < p.topGrade := by simpa [hν, visibilityReplace_self_iff] using he
    refine ⟨ν, hν, hf, Θ, d.2, hsc, hgr, hΘ, ?_⟩
    change p.scheme.rows.E Θ d = extVisibilityReplace (p.scheme.rows.E Θ d) p.topGrade (finitePart ν)
    rw [hν, extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt hf, decomposition]

/-- No top row can belong to an earlier block than an uncapped one: replacement
stays in that earlier block and would cap the uncapped row. -/
theorem limitPart_le_of_not_cap {p : S α n} {Θ : Cell p.scheme.scheme}
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (hΘ : p.label Θ = ⊤) {d e : p.scheme.scheme.below (p.scheme.scheme.cell Θ)}
    (hn : ¬ p.ProvisionalCap d.1) (he : p.label e.1 = ⊤)
    {ν μ : Ordinal.{0}} (hν : p.scheme.rows.E Θ d = ofOrd ν)
    (hμ : p.scheme.rows.E Θ e = ofOrd μ) : limitPart ν ≤ limitPart μ := by
  by_contra! h
  apply hn
  refine ⟨Θ, d.2, e, hsc, hgr, hΘ, he, ?_⟩
  change extVisibilityReplace (p.scheme.rows.E Θ e) p.topGrade p.topGrade ≤ p.scheme.rows.E Θ d
  rw [hν, hμ, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd, visibilityReplace]
  apply le_trans _ ((limitPart_add_omega0_le h).trans (limitPart_le ν))
  split
  · exact (add_lt_add_right (Ordinal.natCast_lt_omega0 _) _).le
  · exact (lt_limitPart_add_omega0 μ).le

/-- **Cap transport** (the cap half of Lemma 5.3.2): a cell capped at some top witness is
capped at every top witness.  Proof: read the locality of `E(Θ)` at `Θ'`; if `d` were not
capped at `Θ`, its row `a` would lie strictly below `E(Θ)(Θ')`, hence `a = σ' (E(Θ')(d))`
with clause 5 available, and the cap inequality at `Θ'` transports to `Θ` through `σ'`. -/
theorem ProvisionalCap.transport {p : S α n} {d : Cell p.scheme.scheme} (hcap : p.ProvisionalCap d)
    {Θ : Cell p.scheme.scheme} (hdΘ : GradedLe (p.scheme.scheme.cell d) (p.scheme.scheme.cell Θ))
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (_hΘ : p.label Θ = ⊤) :
    ∃ Sg : p.scheme.scheme.below (p.scheme.scheme.cell Θ), p.label Sg.1 = ⊤ ∧
      extVisibilityReplace (p.scheme.rows.E Θ Sg) p.topGrade p.topGrade ≤
        p.scheme.rows.E Θ ⟨d, hdΘ⟩ := by
  obtain ⟨Θ', hdΘ', Sg', hsc', hgr', hΘ', hSg', hle⟩ := hcap
  let K := p.topGrade
  have hΘ'Θ : GradedLe (p.scheme.scheme.cell Θ') (p.scheme.scheme.cell Θ) := by
    constructor <;> simp_all
  let u : p.scheme.scheme.below (p.scheme.scheme.cell Θ) := ⟨Θ', hΘ'Θ⟩
  let e : p.scheme.scheme.below (p.scheme.scheme.cell Θ) := ⟨Sg'.1, Sg'.2.trans hΘ'Θ⟩
  let a := p.scheme.rows.E Θ ⟨d, hdΘ⟩
  let Y := p.scheme.rows.E Θ u
  let s := p.scheme.rows.E Θ e
  by_contra hnc
  have haY : a < Y := by
    apply lt_of_not_ge
    intro hy
    have hfix : extVisibilityReplace Y K K = Y := by
      have h := p.scheme.rows.orderly Θ u
      change Y = extVisibilityReplace Y (p.scheme.scheme.grade Θ') (p.scheme.scheme.grade Θ') at h
      rwa [hgr', eq_comm] at h
    exact hnc ⟨u, hΘ', hfix.trans_le hy⟩
  obtain ⟨g, σ, hg, hmono, hcomm, hr, hYg⟩ := locality_data hΘ'Θ
  change Y ≤ g (p.scheme.scheme.grade Θ') at hYg
  rw [hgr'] at hYg
  have hgK (v : p.scheme.scheme.below (p.scheme.scheme.cell Θ')) : g K ≤ g (p.scheme.scheme.grade v.1) :=
    hg ((show p.scheme.scheme.grade v.1 ≤ p.scheme.scheme.grade Θ' from v.2.2).trans_eq hgr')
  let b := p.scheme.rows.E Θ' ⟨d, hdΘ'⟩
  let t := p.scheme.rows.E Θ' Sg'
  have hb : σ b = a := by
    have h := hr ⟨d, hdΘ'⟩
    change min a Y = min (σ b) (g (p.scheme.scheme.grade d)) at h
    exact (uncapped_eq h haY (haY.trans_le (hYg.trans (hgK ⟨d, hdΘ'⟩)))).symm
  have ht : σ (extVisibilityReplace t K K) ≤ a := hb ▸ hmono hle
  have ht' : σ t ≤ a := (hmono (le_extVisibilityReplace_self _ _)).trans ht
  have hs : s = σ t := by
    have h := hr Sg'
    change min s Y = min (σ t) (g (p.scheme.scheme.grade Sg'.1)) at h
    exact (uncapped_eq h.symm (ht'.trans_lt haY |>.trans_le (hYg.trans (hgK Sg')))
      (ht'.trans_lt haY)).symm
  have he := hcomm t K (ht'.trans (haY.le.trans hYg)) K le_rfl
  apply hnc ⟨e, hSg', ?_⟩
  change extVisibilityReplace s K K ≤ a
  rw [hs]
  exact he.symm.trans_le ht

/-- Capped **at `Θ`**: some `∞`-cell below `Θ` caps `d` in the row of `Θ`. -/
def CapAt (p : S α n) (Θ : Cell p.scheme.scheme) (d : p.scheme.scheme.below
  (p.scheme.scheme.cell Θ)) :
    Prop :=
  ∃ Sg : p.scheme.scheme.below (p.scheme.scheme.cell Θ), p.label Sg.1 = ⊤ ∧
    extVisibilityReplace (p.scheme.rows.E Θ Sg) p.topGrade p.topGrade ≤ p.scheme.rows.E Θ d

/-- The cap of any ordinal witness lies at or above the chosen band's ceiling. -/
theorem CapAt.row_ge {p : S α n} {Θ : Cell p.scheme.scheme} {ℓ ν : Ordinal.{0}}
    (hΘ : p.label Θ = ⊤)
    (hmin : ∀ (e : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) (μ : Ordinal.{0}),
      p.label e.1 = ⊤ → p.scheme.rows.E Θ e = ofOrd μ → ℓ ≤ limitPart μ)
    {d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)} (hν : p.scheme.rows.E Θ d = ofOrd ν)
    (hc : CapAt p Θ d) : ℓ + p.topGrade ≤ ν := by
  obtain ⟨e, he, hc⟩ := hc
  rcases ExtOrd.cases (p.scheme.rows.E Θ e) with hb | ht | ⟨μ, hμ⟩
  · exact (row_ne_bot_of_label_top p hΘ e he hb).elim
  · simp [ht, hν] at hc
  · rw [hμ, hν, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at hc
    exact (add_le_add (hmin e μ he hμ) le_rfl).trans ((limitPart_add_le_visibilityReplace ..).trans hc)

/-- **The band bridge.**  Below a top witness `Θ` of a stage type `p` there is a multiple of
`ω`, `lam`, such that every `∞`-cell `d` below `Θ` has row `≥ lam` and provisional value
`bandMap α lam K^p (E(Θ)(d))`. -/
theorem exists_bandBridge (p : S α n) {Θ : Cell p.scheme.scheme}
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (hΘ : p.label Θ = ⊤) :
    ∃ lam : Ordinal.{0}, limitPart lam = lam ∧
      ∀ d : p.scheme.scheme.below (p.scheme.scheme.cell Θ), p.label d.1 = ⊤ →
        ofOrd lam ≤ p.scheme.rows.E Θ d ∧
          p.IsProvisionalValue d.1 (bandMap α lam p.topGrade (p.scheme.rows.E Θ d)) := by
  classical
  have hbase : ∃ lam, limitPart lam = lam ∧
      (∀ (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) (ν : Ordinal.{0}),
        p.label d.1 = ⊤ → p.scheme.rows.E Θ d = ofOrd ν → lam ≤ limitPart ν) ∧
      ∀ (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) (ν : Ordinal.{0}),
        p.label d.1 = ⊤ → p.scheme.rows.E Θ d = ofOrd ν → ¬ p.ProvisionalCap d.1 → limitPart ν = lam := by
    by_cases hex : ∃ d : p.scheme.scheme.below (p.scheme.scheme.cell Θ),
        p.label d.1 = ⊤ ∧ ¬ p.ProvisionalCap d.1
    · obtain ⟨d, hd, hn⟩ := hex
      obtain ⟨ν, hν, -, -⟩ := uncapped_row hsc hgr hΘ d hd hn
      refine ⟨limitPart ν, limitPart_limitPart ν, fun e μ he hμ => ?_, fun e μ he hμ hne => ?_⟩
      · exact limitPart_le_of_not_cap hsc hgr hΘ hn he hν hμ
      · exact le_antisymm (limitPart_le_of_not_cap hsc hgr hΘ hne hd hμ hν)
          (limitPart_le_of_not_cap hsc hgr hΘ hn he hν hμ)
    · exact ⟨0, by simp [limitPart], fun _ _ _ _ => zero_le, fun d _ hd _ hc => (hex ⟨d, hd, hc⟩).elim⟩
  obtain ⟨lam, hlam, hmin, hband⟩ := hbase
  refine ⟨lam, hlam, fun d hd => ?_⟩
  rcases ExtOrd.cases (p.scheme.rows.E Θ d) with hb | ht | ⟨ν, hν⟩
  · exact (row_ne_bot_of_label_top p hΘ d hd hb).elim
  · have hc : p.ProvisionalCap d.1 := ⟨Θ, d.2, d, hsc, hgr, hΘ, hd, ht ▸ le_top⟩
    rw [ht, bandMap_top]
    exact ⟨le_top, Or.inr (Or.inl ⟨hd, hc, rfl⟩)⟩
  · rw [hν]
    refine ⟨ofOrd_le_ofOrd.mpr ((hmin d ν hd hν).trans (limitPart_le ν)), ?_⟩
    by_cases hc : p.ProvisionalCap d.1
    · rw [bandMap_ofOrd_of_cap (CapAt.row_ge hΘ hmin hν (hc.transport d.2 hsc hgr hΘ))]
      exact Or.inr (Or.inl ⟨hd, hc, rfl⟩)
    · obtain ⟨μ, hμ, hf, hh⟩ := uncapped_row hsc hgr hΘ d hd hc
      have he := ofOrd_inj.mp (hμ.symm.trans hν)
      subst μ
      have hl := hband d ν hd hν hc
      have hlt : ν < lam + p.topGrade := by
        conv_lhs => rw [← decomposition ν, hl]
        simp [hf]
      rw [bandMap_ofOrd_of_band ((hmin d ν hd hν).trans (limitPart_le ν)) hlt]
      exact Or.inr (Or.inr ⟨hd, hc, _, hh, rfl⟩)

end StageType

end VaughtConjecture.Knight
