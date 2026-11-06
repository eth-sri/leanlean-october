import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.ProvisionalUniqueness
import VaughtConjecture.Knight.Directedness
import VaughtConjecture.Knight.FiniteOffset
import VaughtConjecture.Knight.NormalForm
import VaughtConjecture.Knight.VisibilityBandArithmetic
import VaughtConjecture.Knight.FiniteRowReadback

/-! # Lemma 5.3.7: the provisional-value ratchet, and stable-value functionality

Knight's Lemma 5.3.7: if `p` is the
exact restriction of `q`, then for every cell `Ξ` of `p`, either `p⁺(Ξ) = q⁺(Ξ)` or
`q⁺(Ξ) ≥ α + K^p`.  Consequently the stabilization sets of Def. 5.3.9 are ratcheted in the
labelled-cover poset (`isRatcheted_stableSet`), Cor. 5.3.8's dominating ⇒ coinitial upgrade
applies, and the stabilized value is unique (`StabilizesTo.unique`, `HasStableValue.unique`).

**The argument** (the paper's Case 2 made exact in the faithful `⇒`).  `Ξ' := toCell Ξ`,
`K := K^p ≤ K^q`.  Clause 1 and the `q`-cap case are immediate.  If `q` is in the band case
with witness `Θ` (full scope, grade `K^q`, `z := E_q(Θ)(Ξ') = ofOrd β'`, `fp β' = j`) and `p` has
a witness `Ψ` (full scope in `p`, grade `K`), then `Ψ' := toCell Ψ` lies below `Θ`, and
consistency of the rows gives the locality transform `E_q(Ψ') ⇒ min(E_q(Θ) ∘ incl, y)`,
`y := E_q(Θ)(Ψ')`, with witnesses `g, σ`; `E_q(Ψ')` is `E_p(Ψ)` on the cells of `p`.  Reading it
at `Ψ'` gives `y ≤ g K`.
* If `y ≤ z`: `y` is self-visible at `K` (orderly), `¬cap_q` at `Σ := Ψ'` gives
  `z < y ⊔⁺_{K^q} K^q`, so `z` sits in the band of `y` with finite part `≥ K`: `j ≥ K`.
* If `z < y`: reading the transform at `Ξ'` gives `z = min(σ t, g (grade Ξ))`, `t := E_p(Ψ)(Ξ)`;
  the `g`-branch is impossible (`z < y ≤ g K ≤ g (grade Ξ)`), so `z = σ t ≤ g K`.
  - `p` band `i`: clause 5 transports `t = t ⊔⁺_K i` to `z = z ⊔⁺_K i`: `j = i` or `j ≥ K`.
  - `p` cap with `Σ`, `u := E_p(Ψ)(Σ)`, `u ⊔⁺_K K ≤ t`: `σ u ≤ σ t = z < g K`, clause 5 gives
    `(σ u) ⊔⁺_K K ≤ z`; the row values at `∞`-cells are not `-∞`, which forces
    `E_q(Θ)(Sg) = σ u ≠ -∞`; `¬cap_q` at `Sg` gives `z < (σ u) ⊔⁺_{K^q} K^q`; band position
    yields `j ≥ K`.

Construction-private (not root-exported). -/

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

universe w

/-! ### Ordinal band arithmetic -/

namespace Value

def le_finitePart_of_ge_of_lt {μ z : Ordinal₀} {K : ℕ}
    (h1 : limitPart μ + K ≤ z) {K' : ℕ} (h2 : z < limitPart μ + K') := by
  have hlp  := (le_add_of_nonneg_right zero_le).trans h1
  have hlim := limitPart_eq_of_le_of_lt hlp h2
  have hz := decomposition z
  rw [← hz, hlim] at h1
  exact (Nat.cast_le ).mp ((add_le_add_iff_left _).mp h1)

/-- **Band position**: if `μ ⊔⁺_K K ≤ z < μ ⊔⁺_{K'} K'` with `K ≤ K'`, then `K ≤ finitePart z`. -/
theorem le_finitePart_of_visReplace_le_of_lt {μ z : Ordinal₀} {K K' : ℕ} (hK : K ≤ K')
    (hlo : visibilityReplace μ K K ≤ z) (hhi : z < visibilityReplace μ K' K') :
    K ≤ finitePart z := by
  unfold visibilityReplace ordinalReplace at hlo hhi
  by_cases hμK' : finitePart μ < K'
  · rw [ite_eq_left hμK'] at hhi
    by_cases hμK : finitePart μ < K
    · aesop (add safe apply [le_finitePart_of_ge_of_lt])
    · rw [ite_eq_right hμK] at hlo
      have hlp  := (limitPart_le).trans hlo
      have hlim := limitPart_eq_of_le_of_lt hlp hhi
      exact (not_lt.mp hμK).trans (finitePart_le_of_le hlim.symm hlo)
  · grind

/-- A self-visible label that is neither `-∞` nor `∞` is an ordinal with finite part `≥ K`. -/
theorem exists_ordinal_of_selfVis {v} {K} (h : extVisibilityReplace v K K = v)
    (hbot : v ≠ ⊥) (htop : v ≠ ⊤) : ∃ μ , v = ofOrd μ ∧ K ≤ finitePart μ := by simp_all [extVisibilityReplace_self_iff]

end Value

/-! ### Row values at `∞`-cells are not `-∞` -/

namespace StageType

variable {α : Ordinal₀} {m n : ℕ}

/-! ### Lemma 5.3.7 for a face restriction -/

open CellScheme.restrictFace (toCell belowMap)

variable {q : S α n} {f : Fin m ↪ Fin n} {hr : Finset.univ.image f ∈ q.scheme.scheme.plan}

local notation "Cell₀" => Cell (q.scheme.scheme.restrictFace f hr)

local notation "toCell₀" => toCell q.scheme.scheme f hr

/-- A full-scope witness of the restriction lies below a full-scope cell of `q` of at least
its grade. -/
theorem gradedLe_toCell_of_full Ψ
    (hsc : (q.scheme.scheme.restrictFace f hr).scope Ψ = Finset.univ)
    {Θ} (hscΘ : q.scheme.scheme.scope Θ = Finset.univ)
    (hgr : (q.scheme.scheme.restrictFace f hr).grade Ψ ≤ q.scheme.scheme.grade Θ) :
    GradedLe (q.scheme.scheme.cell (toCell₀ Ψ)) (q.scheme.scheme.cell Θ) := by
  refine ⟨?_, ?_⟩
  · simp_all
  · exact hgr

/-- **The `y ≤ z` half**: the row of the `q`-witness `Θ` at the restricted witness `Ψ'` (self-
visible at `K^p`) lies below `z`; `¬cap_q` at `Ψ'` then puts `z` in the band of `y` with finite
part `≥ K^p`. -/
theorem band_ge_of_row_le {Θ Ψ' Ξ'}
    (hΞ'Θ : GradedLe (q.scheme.scheme.cell Ξ') (q.scheme.scheme.cell Θ))
    (hΨ'Θ : GradedLe (q.scheme.scheme.cell Ψ') (q.scheme.scheme.cell Θ))
    (hscΘ : q.scheme.scheme.scope Θ = Finset.univ) (hgrΘ : q.scheme.scheme.grade Θ = q.topGrade)
    (hΘtop : q.label Θ = ⊤) (hΨ'top : q.label Ψ' = ⊤) {K}
    (hgrΨ' : q.scheme.scheme.grade Ψ' = K) (hK : K ≤ q.topGrade)
    (hcapq : ¬ q.ProvisionalCap Ξ') {β'}
    (hz : q.scheme.rows.E Θ ⟨Ξ', hΞ'Θ⟩ = ofOrd β')
    (hyz : q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩ ≤ q.scheme.rows.E Θ ⟨Ξ', hΞ'Θ⟩) :
    K ≤ finitePart β' := by
  set y := q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩ with hy
  have hself  := by
    have h := q.scheme.rows.orderly Θ ⟨Ψ', hΨ'Θ⟩
    change y = extVisibilityReplace y (q.scheme.scheme.grade Ψ') (q.scheme.scheme.grade Ψ') at h
    
    exact h.symm
  have hnotcap : ¬ extVisibilityReplace y q.topGrade q.topGrade ≤
      q.scheme.rows.E Θ ⟨Ξ', hΞ'Θ⟩ := fun hle =>
    hcapq ⟨Θ, hΞ'Θ, ⟨Ψ', hΨ'Θ⟩, hscΘ, hgrΘ, hΘtop, hΨ'top, hle⟩
  have hybot : y ≠ ⊥ := by
    aesop
  have hytop : y ≠ ⊤ := by
    aesop
  obtain ⟨μ, hμ, hKμ⟩ := exists_ordinal_of_selfVis hself hybot hytop
  
  rw [hμ, hz, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at hnotcap
  have hlo : visibilityReplace μ K K ≤ β' := by
    aesop
  exact le_finitePart_of_visReplace_le_of_lt hK hlo (not_le.mp hnotcap)

/-- The transform data of the locality of `E_q(Θ)` at `Ψ'`, read at a cell `d` below `Ψ'`:
`min (E_q Θ d) y = min (σ (E_q Ψ' d)) (g (grade d))`, together with `y ≤ g (grade Ψ')`. -/
theorem locality_data {Θ Ψ'}
    (hΨ'Θ : GradedLe (q.scheme.scheme.cell Ψ') (q.scheme.scheme.cell Θ)) :
    ∃ (g : ℕ → ExtOrd) (σ : LabelMap),
      (∀ n m : ℕ, n < m → g m ≤ g n) ∧ Monotone σ ∧
      (∀ (a : ExtOrd) (k : ℕ), σ a ≤ g k → ∀ i : ℕ, i ≤ k →
        σ (extVisibilityReplace a k i) = extVisibilityReplace (σ a) k i) ∧
      (∀ d : q.scheme.scheme.belowCell Ψ',
        min (q.scheme.rows.E Θ ⟨d.1, d.2.trans hΨ'Θ⟩) (q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩) =
          min (σ (q.scheme.rows.E Ψ' d)) (g (q.scheme.scheme.grade d.1))) ∧
      q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩ ≤ g (q.scheme.scheme.grade Ψ') := by
  obtain ⟨g, σ, hganti, -, -, hσmono, hσ5, hloc⟩ := (q.scheme.consistent Θ).locality ⟨Ψ', hΨ'Θ⟩
  refine ⟨g, σ, hganti, hσmono, hσ5, hloc, ?_⟩
  have h := hloc ⟨Ψ', GradedLe.refl _⟩
  change min (q.scheme.rows.E Θ ⟨Ψ', _⟩) (q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩) =
    min (σ (q.scheme.rows.E Ψ' ⟨Ψ', GradedLe.refl _⟩)) (g (q.scheme.scheme.grade Ψ')) at h
  rw [min_self] at h
  rw [h]
  exact min_le_right _ _

local notation "topGrade_le_of_typeMap_eq_some₀" => topGrade_le_of_typeMap_eq_some (typeMap_eq_some f q hr)

local notation "restrictFace₀" => q.restrictFace f hr

/-- **Lemma 5.3.7, band/band core**: `p` in the band case with index `i`, `q` in the band case
with index `j` (`¬cap` on both sides): `i = j` or `K^p ≤ j`. -/
theorem ratchet_core_band Ξ
    (htop : (restrictFace₀).label Ξ = ⊤)
    (hcapp : ¬ (restrictFace₀).ProvisionalCap Ξ) {i}
    (hbandp : (restrictFace₀).ProvisionalBand Ξ i)
    (hcapq : ¬ q.ProvisionalCap (toCell₀ Ξ)) {j}
    (hbandq : q.ProvisionalBand (toCell₀ Ξ) j) :
    i = j ∨ (restrictFace₀).topGrade ≤ j := by
  obtain ⟨Ψ, hΞΨ, hscΨ, hgrΨ, hΨtop, heqp⟩ := hbandp
  obtain ⟨Θ, hΞ'Θ, hscΘ, hgrΘ, hΘtop, heqq⟩ := hbandq
  have hKle  :=
    topGrade_le_of_typeMap_eq_some₀
  set K := (restrictFace₀).topGrade with hK
  -- the restricted witness in q
  set Ψ' := toCell₀ Ψ with hΨ'
  have hgrΨ' : q.scheme.scheme.grade Ψ' = K := hgrΨ
  have hΨ'top  := hΨtop
  have hΨ'Θ : GradedLe (q.scheme.scheme.cell Ψ') (q.scheme.scheme.cell Θ) :=
    gradedLe_toCell_of_full Ψ hscΨ hscΘ (by rw [hgrΘ]; exact hgrΨ ▸ hKle)
  have hΞ'Ψ'  := CellScheme.restrictFace.gradedLe_of_restrictFace _ f hr hΞΨ
  obtain ⟨g, σ, hganti, hσmono, hσ5, hloc, hyg⟩ := locality_data  hΨ'Θ
  -- values
  set z := q.scheme.rows.E Θ ⟨toCell₀ Ξ, hΞ'Θ⟩ with hz
  set y := q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩ with hy
  set t := (restrictFace₀).scheme.rows.E Ψ ⟨Ξ, hΞΨ⟩ with ht
  have hloc_Ξ := hloc ⟨toCell₀ Ξ, hΞ'Ψ'⟩
  change min z y = min (σ t) (g (q.scheme.scheme.grade (toCell₀ Ξ)))
    at hloc_Ξ
  rw [hgrΨ'] at hyg
  obtain ⟨β', hzβ, hfp', hj⟩ :=
    ProvisionalBand.exists_ordinal (show q.label (toCell₀ Ξ) = ⊤ from htop)
      hcapq hΞ'Θ hscΘ hgrΘ hΘtop heqq
  obtain ⟨τ, htτ, hfpτ, hi⟩ :=
    ProvisionalBand.exists_ordinal htop hcapp hΞΨ hscΨ hgrΨ hΨtop heqp
  rcases le_or_gt y z with hyz | hzy
  · right
    rw [hj]
    exact band_ge_of_row_le hΞ'Θ hΨ'Θ hscΘ hgrΘ hΘtop hΨ'top hgrΨ' hKle hcapq hzβ hyz
  · -- z < y: the minimum on the left is z, the one on the right is σ t
    have hgrΞ : q.scheme.scheme.grade (toCell₀ Ξ) ≤ K := by
      have h2 : (restrictFace₀).scheme.scheme.grade Ξ ≤
          (restrictFace₀).scheme.scheme.grade Ψ := hΞΨ.2
      rw [hgrΨ] at h2
      exact h2
    have hgle : g K ≤ g (q.scheme.scheme.grade (toCell₀ Ξ)) := by
      grind
    
    have hzσ : z = σ t := by
      grind
    have hσt  := hzσ ▸ (hzy.le.trans hyg)
    have hiK  := (hi ▸ hfpτ).le
    have h5 := hσ5 t K hσt i hiK
    rw [← heqp] at h5
    -- h5 : σ t = extVisibilityReplace (σ t) K i, i.e. z = z ⊔⁺_K i
    have hzβ' : z = ofOrd β' := hzβ
    rw [← hzσ, hzβ', extVisibilityReplace_ofOrd] at h5
    have hβ'eq  := ofOrd_inj.mp h5
    by_cases hlt : finitePart β' < K
    · left
      unfold visibilityReplace ordinalReplace at hβ'eq
      rw [ite_eq_left hlt] at hβ'eq
      have hcast  :=
        add_left_cancel (hβ'eq.symm.trans (decomposition β').symm)
      have : i = finitePart β' := by exact_mod_cast hcast
      omega
    · omega

/-- **Lemma 5.3.7, cap/band core**: `p` in the cap case, `q` in the band case with index `j`:
`K^p ≤ j`. -/
theorem ratchet_core_cap Ξ
    (htop : (restrictFace₀).label Ξ = ⊤)
    (hcapp : (restrictFace₀).ProvisionalCap Ξ)
    (hcapq : ¬ q.ProvisionalCap (toCell₀ Ξ)) {j}
    (hbandq : q.ProvisionalBand (toCell₀ Ξ) j) :
    (restrictFace₀).topGrade ≤ j := by
  obtain ⟨Ψ, hΞΨ, Sg, hscΨ, hgrΨ, hΨtop, hSgtop, hcapineq⟩ := hcapp
  obtain ⟨Θ, hΞ'Θ, hscΘ, hgrΘ, hΘtop, heqq⟩ := hbandq
  have hKle  :=
    topGrade_le_of_typeMap_eq_some₀
  set K := (restrictFace₀).topGrade with hK
  set Ψ' := toCell₀ Ψ with hΨ'
  have hgrΨ' : q.scheme.scheme.grade Ψ' = K := hgrΨ
  have hΨ'top  := hΨtop
  have hΨ'Θ : GradedLe (q.scheme.scheme.cell Ψ') (q.scheme.scheme.cell Θ) :=
    gradedLe_toCell_of_full Ψ hscΨ hscΘ (by rw [hgrΘ]; exact hgrΨ ▸ hKle)
  have hΞ'Ψ'  := CellScheme.restrictFace.gradedLe_of_restrictFace _ f hr hΞΨ
  -- the cap cell Σ, transported
  set Sg' : q.scheme.scheme.belowCell Ψ' := belowMap q.scheme.scheme f hr Ψ Sg
    with hSg'
  have hSg'top  := hSgtop
  have hgrSg : q.scheme.scheme.grade Sg'.1 ≤ K := by
    have h2 : (restrictFace₀).scheme.scheme.grade Sg.1 ≤
        (restrictFace₀).scheme.scheme.grade Ψ := Sg.2.2
    rw [hgrΨ] at h2
    exact h2
  obtain ⟨g, σ, hganti, hσmono, hσ5, hloc, hyg⟩ := locality_data  hΨ'Θ
  set z := q.scheme.rows.E Θ ⟨toCell₀ Ξ, hΞ'Θ⟩ with hz
  set y := q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩ with hy
  set t := (restrictFace₀).scheme.rows.E Ψ ⟨Ξ, hΞΨ⟩ with ht
  set u := (restrictFace₀).scheme.rows.E Ψ Sg with hu
  set s := q.scheme.rows.E Θ ⟨Sg'.1, Sg'.2.trans hΨ'Θ⟩ with hs
  have hloc_Ξ := hloc ⟨toCell₀ Ξ, hΞ'Ψ'⟩
  change min z y = min (σ t) (g (q.scheme.scheme.grade (toCell₀ Ξ)))
    at hloc_Ξ
  have hloc_Sg := hloc Sg'
  change min s y = min (σ u) (g (q.scheme.scheme.grade Sg'.1)) at hloc_Sg
  rw [hgrΨ'] at hyg
  obtain ⟨β', hzβ, hfp', hj⟩ :=
    ProvisionalBand.exists_ordinal (show q.label (toCell₀ Ξ) = ⊤ from htop)
      hcapq hΞ'Θ hscΘ hgrΘ hΘtop heqq
  rcases le_or_gt y z with hyz | hzy
  · rw [hj]
    exact band_ge_of_row_le hΞ'Θ hΨ'Θ hscΘ hgrΘ hΘtop hΨ'top hgrΨ' hKle hcapq hzβ hyz
  · have hgrΞ : q.scheme.scheme.grade (toCell₀ Ξ) ≤ K := by
      have h2 : (restrictFace₀).scheme.scheme.grade Ξ ≤
          (restrictFace₀).scheme.scheme.grade Ψ := hΞΨ.2
      rw [hgrΨ] at h2
      exact h2
    have hgle : g K ≤ g (q.scheme.scheme.grade (toCell₀ Ξ)) := by
      grind
    have hgleS : g K ≤ g (q.scheme.scheme.grade Sg'.1) := by
      grind
    
    have hzσ : z = σ t := by
      grind
    -- u ≤ t, hence σ u ≤ σ t = z
    have hut  := (le_extVisibilityReplace_self u K).trans hcapineq
    have hσu  := hzσ ▸ hσmono hut
    have hσuK  := hσu.trans (hzy.le.trans hyg)
    -- s = σ u
    have hsσ : s = σ u := by
      grind
    -- clause 5 at (u, K, K): (σ u) ⊔⁺_K K ≤ z
    have h5 := hσ5 u K hσuK K le_rfl
    have hlo : extVisibilityReplace (σ u) K K ≤ z := by
      rw [← h5, hzσ]
      exact hσmono hcapineq
    -- ¬cap_q at Sg: z < s ⊔⁺_{K^q} K^q
    have hnotcap : ¬ extVisibilityReplace s q.topGrade q.topGrade ≤ z := fun hle =>
      hcapq ⟨Θ, hΞ'Θ, ⟨Sg'.1, Sg'.2.trans hΨ'Θ⟩, hscΘ, hgrΘ, hΘtop, hSg'top, hle⟩
    have hsbot  := row_ne_bot_of_label_top q hΘtop ⟨Sg'.1, Sg'.2.trans hΨ'Θ⟩ hSg'top
    have hσubot : σ u ≠ ⊥ := hsσ ▸ hsbot
    have hzβ' : z = ofOrd β' := hzβ
    have hσutop : σ u ≠ ⊤ := by
      grind
    rcases ExtOrd.cases (σ u) with hb | hT | ⟨μ, hμ⟩
    · exact absurd hb hσubot
    · exact absurd hT hσutop
    rw [hμ, hzβ', extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at hlo
    rw [hsσ, hμ, hzβ', extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at hnotcap
    rw [hj]
    exact le_finitePart_of_visReplace_le_of_lt hKle hlo (not_le.mp hnotcap)

/-- **Lemma 5.3.7 (restriction form)**: for a cell `Ξ` of `p := q.restrictFace f hr` with
provisional values `v` in `p` and `w` at `toCell Ξ` in `q`: `v = w` or `α + K^p ≤ w`. -/
theorem provisional_ratchet Ξ {v w}
    (hv : (restrictFace₀).IsProvisionalValue Ξ v)
    (hw : q.IsProvisionalValue (toCell₀ Ξ) w) :
    v = w ∨ ofOrd (α + (restrictFace₀).topGrade) ≤ w := by
  have hlab : q.label (toCell₀ Ξ) = (restrictFace₀).label Ξ := rfl
  have hKle : (restrictFace₀).topGrade ≤ q.topGrade :=
    topGrade_le_of_typeMap_eq_some₀
  have hKq : ofOrd (α + (restrictFace₀).topGrade) ≤ ofOrd (α + q.topGrade) := by
    rw [ofOrd_le_ofOrd]
    exact add_le_add (le_refl α) ((Nat.cast_le ).mpr hKle)
  rcases hv with ⟨hne, rfl⟩ | ⟨htop, hcapp, rfl⟩ | ⟨htop, hcapp, i, hbandp, rfl⟩
  · rcases hw with ⟨-, rfl⟩ | ⟨htop', -, -⟩ | ⟨htop', -, -⟩
    · exact Or.inl rfl
    · exact absurd (hlab ▸ htop') hne
    · exact absurd (hlab ▸ htop') hne
  · rcases hw with ⟨hne', -⟩ | ⟨-, -, rfl⟩ | ⟨htop', hcapq, j, hbandq, rfl⟩
    · exact absurd (hlab ▸ htop) hne'
    · exact Or.inr hKq
    · right
      rw [ofOrd_le_ofOrd]
      exact add_le_add (le_refl α) ((Nat.cast_le ).mpr
        (ratchet_core_cap Ξ htop hcapp hcapq hbandq))
  · rcases hw with ⟨hne', -⟩ | ⟨-, -, rfl⟩ | ⟨htop', hcapq, j, hbandq, rfl⟩
    · exact absurd (hlab ▸ htop) hne'
    · exact Or.inr hKq
    · rcases ratchet_core_band Ξ htop hcapp hbandp hcapq hbandq with hij | hK
      · exact Or.inl (by rw [hij])
      · right
        rw [ofOrd_le_ofOrd]
        exact add_le_add (le_refl α) ((Nat.cast_le ).mpr hK)

/-- **Lemma 5.3.7 (`typeMap` form)**: along `typeMap f q = some p`, provisional values of a
cell `Ξ` of `p` and of `mapCell Ξ` in `q` agree or the latter is `≥ α + K^p`. -/
theorem provisional_ratchet' {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) Ξ {v w}
    (hv : p.IsProvisionalValue Ξ v) (hw : q.IsProvisionalValue (mapCell h Ξ) w) :
    v = w ∨ ofOrd (α + p.topGrade) ≤ w := by
  obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
    ⟨visible_of_typeMap_eq_some h, restrictFace_eq_of_typeMap_eq_some h⟩
  exact provisional_ratchet Ξ hv hw

/-- **Provisional monotonicity along an exact face.**  The ratchet (Lemma 5.3.7) and the source
bound `IsProvisionalValue.le` together give `v ≤ v'` outright.  This is the canonical home of
the inequality; the ratchet itself is retained for clients that need its gap information. -/
theorem IsProvisionalValue.le_of_typeMap {α : Ordinal₀} {n m : ℕ}
    {p : S α n} {q : S α m} {f : Fin n ↪ Fin m}
    (hf : typeMap f q = some p) {d : Cell p.scheme.scheme} {v v'}
    (hv : p.IsProvisionalValue d v) (hv' : q.IsProvisionalValue (mapCell hf d) v') :
    v ≤ v' := by
  rcases provisional_ratchet' hf d hv hv' with h | h
  · exact h.le
  · exact hv.le.trans h

end StageType

/-! ### The ratchet on the labelled-cover poset, and stable-value functionality -/

namespace KnightRealization

open StageType

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

/-- The embedding of a labelled cover into a larger one is determined by the tuples. -/
def LabelledExt.emb_unique {x y : R.LabelledExt} {f f' : Fin x.arity ↪ Fin y.arity}
    (hf : f.trans y.tuple = x.tuple) (hf' : f'.trans y.tuple = x.tuple) := by
  apply Function.Embedding.ext
  intro i
  apply y.tuple.injective
  have h1 := DFunLike.congr_fun hf i
  have h2 := DFunLike.congr_fun hf' i
  
  exact h1.trans h2.symm

/-! ### Stable-value functionality from exact consistency alone

Each stabilization witness supplies a realized extension on which the other stabilization can
be tested; provisional monotonicity along the exact face then orders the two values.  Neither
covering nor a separately chosen root realization enters. -/

/-- Any realized provisional value of a source cell lies below a stabilized value of that cell:
stabilization supplies a larger realized tuple, exact consistency identifies the face, and
provisional monotonicity compares the readings. -/
theorem StabilizesTo.provisional_le (hcons : R.IsExactParentConsistent)
    {n m} {t} {p} {u} {q}
    (hu : R.eval u = some q) {f : Fin n ↪ Fin m} (hf : f.trans u = t)
    (hpq : typeMap f q = some p) {d} {v γ}
    (hv : q.IsProvisionalValue (mapCell hpq d) v) (hγ : R.StabilizesTo t p d γ) : v ≤ γ := by
  obtain ⟨k, z, g, e, r, hpr, hz, hgz, hez, hγz⟩ := hγ u
  have hqr  := by
    have h := hcons z r g hz
    rw [hgz, hu] at h
    exact h.symm
  have hfg : (f.trans g).trans z = t := by
    aesop
  have he  := by
    apply Function.Embedding.ext
    intro i
    apply z.injective
    exact (DFunLike.congr_fun hez i).trans (DFunLike.congr_fun hfg i).symm
  subst he
  have hγz' : r.IsProvisionalValue (mapCell hqr (mapCell hpq d)) γ := by
    rw [← mapCell_trans hqr hpq hpr d]
    exact hγz
  exact hv.le_of_typeMap hqr hγz'

/-- **Functionality of the stabilized value** (Def. 5.3.9) **from exact consistency alone**. -/
theorem StabilizesTo.unique_of_consistent (hcons : R.IsExactParentConsistent)
    {n} {t} {p : S α.1 n} {d} {γ γ'}
    (h : R.StabilizesTo t p d γ) (h' : R.StabilizesTo t p d γ') : γ = γ' := by
  apply le_antisymm
  · obtain ⟨m, u, g, f, q, hpq, hu, _, hf, hv⟩ := h t
    exact StabilizesTo.provisional_le hcons hu hf hpq hv h'
  · obtain ⟨m, u, g, f, q, hpq, hu, _, hf, hv⟩ := h' t
    exact StabilizesTo.provisional_le hcons hu hf hpq hv h

/-- **Functionality of `M⁺(Ξ)`** (the graph of Def. 5.3.9 is a function), from exact
consistency alone. -/
theorem HasStableValue.unique_of_consistent (hcons : R.IsExactParentConsistent)
    {n} {t} {p : S α.1 n} {d} {γ γ'}
    (h : R.HasStableValue t p d γ) (h' : R.HasStableValue t p d γ') : γ = γ' := by
  rcases h with ⟨hlt, hs⟩ | ⟨rfl, hno⟩ <;> rcases h' with ⟨hlt', hs'⟩ | ⟨rfl, hno'⟩
  · exact?
  · exact absurd @hs (hno' γ hlt)
  · exact absurd @hs' (hno γ' hlt')
  · rfl

/-- **Functionality of `M⁺(Ξ)`** (the graph of Def. 5.3.9 is a function), in its original
interface; see `HasStableValue.unique_of_consistent`. -/
def HasStableValue.unique (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} {γ γ'}
    (h : R.HasStableValue t p Xi γ) (h' : R.HasStableValue t p Xi γ') :=
  HasStableValue.unique_of_consistent hcons h h'


