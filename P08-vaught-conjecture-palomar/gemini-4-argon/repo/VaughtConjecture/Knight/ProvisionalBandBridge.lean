/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RestrictedComposition
public import VaughtConjecture.Knight.ProvisionalUniqueness
public import VaughtConjecture.Knight.FiniteRowReadback

/-! # The provisional value is the band map of the row at a top witness

For a full-scope `∞`-cell `Θ` of grade `K = K^p` and an `∞`-cell `d` below it, the provisional
value `p⁺(d)` (Def. 5.3.1, functional by Lemma 5.3.2) is the band map of the row `E(Θ)(d)`:
`α + fp` on the active band `[lam, lam + K)` and `α + K` at cap level, where `lam` is the
common limit part of the non-cap `∞`-rows below `Θ` (band comparability + clause 2.(a)).
This is the bridge that turns `TransformsTo.comp_bandMap` into Lemma 5.3.5's top-row
transform `E(Θ) ⇒ p⁺` (`topRow_transformsTo_provisional`).

## Cap transport (an argument the paper omits)

Def. 5.3.1's cap clause is existential in the top witness, but Lemma 5.3.5 reads `p⁺` through
one fixed maximal witness `Θ`.  `ProvisionalCap.transport` shows a cell capped at some witness
`Θ'` is capped at every witness `Θ`: the locality of `E(Θ)` at `Θ'` carries the cap across
(clause 5 when the cap witness is below the row's value at `Θ'`, monotonicity otherwise).
Without it the band-map reading of `p⁺` at `Θ` is not justified. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

/-! ### Band comparability -/

namespace Value

theorem band_trichotomy (x y : Ordinal.{0}) (K : ℕ) :
    limitPart x = limitPart y ∨ limitPart x + K ≤ y ∨ limitPart y + K ≤ x := by
  have hle {a b : Ordinal.{0}} (h : limitPart a < limitPart b) : limitPart a + K ≤ b :=
    ((add_le_add le_rfl (Ordinal.natCast_lt_omega0 K).le).trans
      (add_omega0_le_limitPart_of_lt (limitPart_limitPart a) h)).trans (limitPart_le b)
  rcases lt_trichotomy (limitPart x) (limitPart y) with h | h | h
  · exact Or.inr (Or.inl (hle h))
  · exact Or.inl h
  · exact Or.inr (Or.inr (hle h))

end Value

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

private theorem fp_lt_of_not_cap {p : S α n} {Θ : Cell p.scheme.scheme}
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (hΘ : p.label Θ = ⊤) {e : p.scheme.scheme.below (p.scheme.scheme.cell Θ)}
    (he : p.label e.1 = ⊤) (hce : ¬ p.ProvisionalCap e.1) {μ : Ordinal.{0}}
    (hμ : p.scheme.rows.E Θ e = ofOrd μ) : finitePart μ < p.topGrade := by
  by_contra hge
  refine hce ⟨Θ, e.2, e, hsc, hgr, hΘ, he, ?_⟩
  change extVisibilityReplace (p.scheme.rows.E Θ e) p.topGrade p.topGrade ≤ p.scheme.rows.E Θ e
  rw [hμ, extVisibilityReplace_ofOrd, (visibilityReplace_self_iff μ _).mpr (not_lt.mp hge)]

theorem limitPart_eq_of_not_cap {p : S α n} {Θ : Cell p.scheme.scheme}
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (hΘ : p.label Θ = ⊤) {d d' : p.scheme.scheme.below (p.scheme.scheme.cell Θ)}
    (hd : p.label d.1 = ⊤) (hd' : p.label d'.1 = ⊤)
    (hcap : ¬ p.ProvisionalCap d.1) (hcap' : ¬ p.ProvisionalCap d'.1)
    {ν ν' : Ordinal.{0}} (hν : p.scheme.rows.E Θ d = ofOrd ν)
    (hν' : p.scheme.rows.E Θ d' = ofOrd ν') :
    finitePart ν < p.topGrade ∧ finitePart ν' < p.topGrade ∧ limitPart ν = limitPart ν' := by
  have h1 := fp_lt_of_not_cap hsc hgr hΘ hd hcap hν
  have h2 := fp_lt_of_not_cap hsc hgr hΘ hd' hcap' hν'
  refine ⟨h1, h2, ?_⟩
  rcases band_trichotomy ν ν' p.topGrade with h | h | h
  · exact h
  · refine (hcap' ⟨Θ, d'.2, d, hsc, hgr, hΘ, hd, ?_⟩).elim
    change extVisibilityReplace (p.scheme.rows.E Θ d) p.topGrade p.topGrade ≤ p.scheme.rows.E Θ d'
    rwa [hν, hν', extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt h1, ofOrd_le_ofOrd]
  · refine (hcap ⟨Θ, d.2, d', hsc, hgr, hΘ, hd', ?_⟩).elim
    change extVisibilityReplace (p.scheme.rows.E Θ d') p.topGrade p.topGrade ≤ p.scheme.rows.E Θ d
    rwa [hν, hν', extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt h2, ofOrd_le_ofOrd]

/-- **Cap transport** (the cap half of Lemma 5.3.2): a cell capped at some top witness is
capped at every top witness. -/
theorem ProvisionalCap.transport {p : S α n} {d : Cell p.scheme.scheme} (hcap : p.ProvisionalCap d)
    {Θ : Cell p.scheme.scheme} (hdΘ : GradedLe (p.scheme.scheme.cell d) (p.scheme.scheme.cell Θ))
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (_hΘ : p.label Θ = ⊤) :
    ∃ Sg : p.scheme.scheme.below (p.scheme.scheme.cell Θ), p.label Sg.1 = ⊤ ∧
      extVisibilityReplace (p.scheme.rows.E Θ Sg) p.topGrade p.topGrade ≤
        p.scheme.rows.E Θ ⟨d, hdΘ⟩ := by
  obtain ⟨Θ', hdΘ', Sg', hsc', hgr', hΘ', hSg', hle⟩ := hcap
  set K := p.topGrade
  have hΘ'Θ : GradedLe (p.scheme.scheme.cell Θ') (p.scheme.scheme.cell Θ) :=
    ⟨by change p.scheme.scheme.scope Θ' ⊆ p.scheme.scheme.scope Θ; rw [hsc]; exact Finset.subset_univ _,
      by change p.scheme.scheme.grade Θ' ≤ p.scheme.scheme.grade Θ; rw [hgr, hgr']⟩
  have hSgΘ : GradedLe (p.scheme.scheme.cell Sg'.1) (p.scheme.scheme.cell Θ) := Sg'.2.trans hΘ'Θ
  by_contra hnc
  push Not at hnc
  set a := p.scheme.rows.E Θ ⟨d, hdΘ⟩
  set Y := p.scheme.rows.E Θ ⟨Θ', hΘ'Θ⟩
  set s := p.scheme.rows.E Θ ⟨Sg'.1, hSgΘ⟩
  set b := p.scheme.rows.E Θ' ⟨d, hdΘ'⟩
  set t := p.scheme.rows.E Θ' Sg'
  have hYself : extVisibilityReplace Y K K = Y := by
    have := p.scheme.rows.orderly Θ ⟨Θ', hΘ'Θ⟩
    change Y = extVisibilityReplace Y (p.scheme.scheme.grade Θ') (p.scheme.scheme.grade Θ') at this
    rw [hgr'] at this; exact this.symm
  have haY : a < Y := hYself ▸ hnc ⟨Θ', hΘ'Θ⟩ hΘ'
  obtain ⟨g', σ', hganti, -, -, hσmono, hσ5, hloc⟩ :=
    (p.scheme.consistent Θ).locality ⟨Θ', hΘ'Θ⟩
  have hYg : Y ≤ g' K := by
    have hlocΘ' : min Y Y = min (σ' (p.scheme.rows.E Θ' ⟨Θ', GradedLe.refl _⟩))
        (g' (p.scheme.scheme.grade Θ')) := hloc ⟨Θ', GradedLe.refl _⟩
    rw [min_self, hgr'] at hlocΘ'
    exact hlocΘ'.le.trans (min_le_right _ _)
  have hread {x : p.scheme.scheme.below (p.scheme.scheme.cell Θ')}
      (hxY : p.scheme.rows.E Θ ⟨x.1, x.2.trans hΘ'Θ⟩ < Y) :
      p.scheme.rows.E Θ ⟨x.1, x.2.trans hΘ'Θ⟩ = σ' (p.scheme.rows.E Θ' x) := by
    have hl : min (p.scheme.rows.E Θ ⟨x.1, x.2.trans hΘ'Θ⟩) Y =
        min (σ' (p.scheme.rows.E Θ' x)) (g' (p.scheme.scheme.grade x.1)) := hloc x
    have hg : g' K ≤ g' (p.scheme.scheme.grade x.1) := by
      have h2 : p.scheme.scheme.grade x.1 ≤ K := hgr' ▸ x.2.2
      exact h2.lt_or_eq.elim (hganti _ _) fun h => h ▸ le_rfl
    rw [min_eq_left hxY.le] at hl
    rcases le_total (σ' (p.scheme.rows.E Θ' x)) (g' (p.scheme.scheme.grade x.1)) with hle' | hle'
    · rwa [min_eq_left hle'] at hl
    · rw [min_eq_right hle'] at hl
      exact absurd (hxY.trans_le (hYg.trans hg)) (not_lt.mpr hl.ge)
  have htb : σ' (extVisibilityReplace t K K) ≤ a :=
    (hσmono hle).trans_eq (hread (x := ⟨d, hdΘ'⟩) haY).symm
  rcases lt_or_ge s Y with hsY | hsY
  · have hsσ : s = σ' t := hread (x := Sg') hsY
    rw [hσ5 t K (hsσ ▸ hsY.le.trans hYg) K le_rfl, ← hsσ] at htb
    exact not_le.mpr (hnc ⟨Sg'.1, hSgΘ⟩ hSg') htb
  · have hlocS : min s Y = min (σ' t) (g' (p.scheme.scheme.grade Sg'.1)) := hloc Sg'
    rw [min_eq_right hsY] at hlocS
    exact haY.not_ge ((hlocS.le.trans (min_le_left _ _)).trans
      ((hσmono (le_extVisibilityReplace_self t K)).trans htb))

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
  set K := p.topGrade
  let CapAt (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) : Prop :=
    ∃ Sg : p.scheme.scheme.below (p.scheme.scheme.cell Θ), p.label Sg.1 = ⊤ ∧
      extVisibilityReplace (p.scheme.rows.E Θ Sg) K K ≤ p.scheme.rows.E Θ d
  have hcapval (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) (hd : p.label d.1 = ⊤)
      (hc : p.ProvisionalCap d.1) : p.IsProvisionalValue d.1 (ofOrd (α + K)) :=
    Or.inr (Or.inl ⟨hd, hc, rfl⟩)
  have hrow (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) (hd : p.label d.1 = ⊤) :
      p.scheme.rows.E Θ d = ⊤ ∨ ∃ ν, p.scheme.rows.E Θ d = ofOrd ν := by
    rcases ExtOrd.cases (p.scheme.rows.E Θ d) with hb | ht | ⟨ν, hν⟩
    · exact absurd hb (row_ne_bot_of_label_top p hΘ d hd)
    · exact Or.inl ht
    · exact Or.inr ⟨ν, hν⟩
  have htop_cap (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) (hd : p.label d.1 = ⊤)
      (ht : p.scheme.rows.E Θ d = ⊤) : p.ProvisionalCap d.1 :=
    ⟨Θ, d.2, d, hsc, hgr, hΘ, hd, by
      change extVisibilityReplace (p.scheme.rows.E Θ d) K K ≤ p.scheme.rows.E Θ d
      rw [ht]; exact le_top⟩
  by_cases hex : ∃ (d₀ : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) (ν₀ : Ordinal.{0}),
      p.label d₀.1 = ⊤ ∧ ¬ p.ProvisionalCap d₀.1 ∧ p.scheme.rows.E Θ d₀ = ofOrd ν₀
  · obtain ⟨d₀, ν₀, hd₀, hc₀, hν₀⟩ := hex
    have hrow_ge : ∀ (ν : Ordinal.{0}) (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)),
        p.label d.1 = ⊤ → p.scheme.rows.E Θ d = ofOrd ν → CapAt d → limitPart ν₀ + K ≤ ν := by
      intro ν
      induction ν using WellFoundedLT.induction with
      | _ ν ih =>
      intro d hd hν ⟨Sg, hSg, hle⟩
      rw [hν] at hle
      rcases hrow Sg hSg with ht | ⟨μ, hμ⟩
      · rw [ht, extVisibilityReplace_top] at hle
        exact absurd hle (not_le.mpr (ofOrd_lt_top _))
      · rw [hμ, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at hle
        by_cases hcapS : CapAt Sg
        · rcases lt_or_ge μ ν with hlt | hge
          · exact (ih μ hlt Sg hSg hμ hcapS).trans ((le_visibilityReplace_self μ K).trans hle)
          · have hfpμ : K ≤ finitePart μ := not_lt.mp fun hlt => by
              rw [visibilityReplace_of_finitePart_lt hlt] at hle
              exact hle.not_gt (hge.trans_lt
                ((decomposition μ).symm.trans_lt ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hlt))))
            rw [(visibilityReplace_self_iff μ K).mpr hfpμ] at hle
            obtain rfl : μ = ν := le_antisymm hle hge
            have hlp : limitPart ν₀ ≤ limitPart μ := not_lt.mp fun hlt =>
              hc₀ ⟨Θ, d₀.2, Sg, hsc, hgr, hΘ, hSg, by
                change extVisibilityReplace (p.scheme.rows.E Θ Sg) K K ≤ p.scheme.rows.E Θ d₀
                rw [hμ, hν₀, extVisibilityReplace_ofOrd, (visibilityReplace_self_iff μ K).mpr hfpμ,
                  ofOrd_le_ofOrd]
                exact ((decomposition μ).symm.trans_lt
                  ((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 _))).le.trans
                  ((add_omega0_le_limitPart_of_lt (limitPart_limitPart μ) hlt).trans
                    (limitPart_le ν₀))⟩
            exact (add_le_add hlp (Nat.cast_le.mpr hfpμ)).trans_eq (decomposition μ)
        · have hncS : ¬ p.ProvisionalCap Sg.1 := fun hc => hcapS (hc.transport Sg.2 hsc hgr hΘ)
          obtain ⟨hfpμ, -, hlp⟩ := limitPart_eq_of_not_cap hsc hgr hΘ hSg hd₀ hncS hc₀ hμ hν₀
          rwa [visibilityReplace_of_finitePart_lt hfpμ, hlp] at hle
    refine ⟨limitPart ν₀, limitPart_limitPart ν₀, fun d hd => ?_⟩
    rcases hrow d hd with ht | ⟨ν, hν⟩
    · rw [ht, bandMap_top]
      exact ⟨le_top, hcapval d hd (htop_cap d hd ht)⟩
    · rw [hν]
      by_cases hc : p.ProvisionalCap d.1
      · have hge := hrow_ge ν d hd hν (hc.transport d.2 hsc hgr hΘ)
        rw [bandMap_ofOrd_of_cap hge]
        exact ⟨ofOrd_le_ofOrd.mpr ((le_add_of_nonneg_right zero_le).trans hge), hcapval d hd hc⟩
      · obtain ⟨hfp, -, hlp⟩ := limitPart_eq_of_not_cap hsc hgr hΘ hd hd₀ hc hc₀ hν hν₀
        have hlν : limitPart ν₀ ≤ ν := hlp ▸ limitPart_le ν
        have hlt : ν < limitPart ν₀ + K := hlp ▸ (decomposition ν).symm.trans_lt
          ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hfp))
        rw [bandMap_ofOrd_of_band hlν hlt]
        refine ⟨ofOrd_le_ofOrd.mpr hlν,
          Or.inr (Or.inr ⟨hd, hc, finitePart ν, ⟨Θ, d.2, hsc, hgr, hΘ, ?_⟩, rfl⟩)⟩
        change p.scheme.rows.E Θ d = extVisibilityReplace (p.scheme.rows.E Θ d) K (finitePart ν)
        rw [hν, extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt hfp, decomposition]
  · push Not at hex
    refine ⟨0, by simp [limitPart], fun d hd => ?_⟩
    rcases hrow d hd with ht | ⟨ν, hν⟩
    · rw [ht, bandMap_top]
      exact ⟨le_top, hcapval d hd (htop_cap d hd ht)⟩
    · have hc : p.ProvisionalCap d.1 := by_contra fun hnc => hex d ν hd hnc hν
      obtain ⟨Sg₁, h1, h2⟩ := hc.transport d.2 hsc hgr hΘ
      change extVisibilityReplace (p.scheme.rows.E Θ Sg₁) K K ≤ p.scheme.rows.E Θ d at h2
      have hK : (0 : Ordinal.{0}) + K ≤ ν := by
        rw [zero_add]
        rcases hrow Sg₁ h1 with ht | ⟨μ, hμ⟩
        · rw [ht, extVisibilityReplace_top, hν] at h2
          exact absurd h2 (not_le.mpr (ofOrd_lt_top _))
        · rw [hμ, hν, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at h2
          refine le_trans ?_ h2
          unfold visibilityReplace ordinalReplace
          split_ifs with hfp
          · exact le_add_of_nonneg_left zero_le
          · exact ((Nat.cast_le.mpr (not_lt.mp hfp)).trans
              (le_add_of_nonneg_left zero_le)).trans_eq (decomposition μ)
      rw [hν, bandMap_ofOrd_of_cap hK]
      exact ⟨ofOrd_le_ofOrd.mpr zero_le, hcapval d hd hc⟩

