/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProvisionalUniqueness
public import VaughtConjecture.Knight.Directedness
public import VaughtConjecture.Knight.FiniteOffset
public import VaughtConjecture.Knight.NormalForm
public import VaughtConjecture.Knight.VisibilityBandArithmetic
public import VaughtConjecture.Knight.FiniteRowReadback

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

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

universe w

/-! ### Ordinal band arithmetic -/

namespace Value

theorem le_finitePart_of_ge_of_lt {μ z : Ordinal.{0}} {K : ℕ}
    (h1 : limitPart μ + K ≤ z) {K' : ℕ} (h2 : z < limitPart μ + K') : K ≤ finitePart z := by
  have hlim := limitPart_eq_of_le_of_lt ((le_add_of_nonneg_right zero_le).trans h1) h2
  rw [← decomposition z, hlim] at h1
  exact Nat.cast_le.mp ((add_le_add_iff_left _).mp h1)

/-- **Band position**: if `μ ⊔⁺_K K ≤ z < μ ⊔⁺_{K'} K'` with `K ≤ K'`, then `K ≤ finitePart z`. -/
theorem le_finitePart_of_visReplace_le_of_lt {μ z : Ordinal.{0}} {K K' : ℕ} (hK : K ≤ K')
    (hlo : visibilityReplace μ K K ≤ z) (hhi : z < visibilityReplace μ K' K') :
    K ≤ finitePart z := by
  unfold visibilityReplace ordinalReplace at hlo hhi
  by_cases hμK' : finitePart μ < K'
  · rw [ite_eq_left hμK'] at hhi
    by_cases hμK : finitePart μ < K
    · rw [ite_eq_left hμK] at hlo
      exact le_finitePart_of_ge_of_lt hlo hhi
    · rw [ite_eq_right hμK] at hlo
      have hlim := limitPart_eq_of_le_of_lt ((limitPart_le μ).trans hlo) hhi
      exact (not_lt.mp hμK).trans (finitePart_le_of_le hlim.symm hlo)
  · rw [ite_eq_right hμK'] at hhi
    rw [ite_eq_right (fun h => hμK' (h.trans_le hK))] at hlo
    exact absurd (hlo.trans_lt hhi) (lt_irrefl μ)

/-- A self-visible label that is neither `-∞` nor `∞` is an ordinal with finite part `≥ K`. -/
theorem exists_ordinal_of_selfVis {v : ExtOrd} {K : ℕ} (h : extVisibilityReplace v K K = v)
    (hbot : v ≠ ⊥) (htop : v ≠ ⊤) : ∃ μ : Ordinal.{0}, v = ofOrd μ ∧ K ≤ finitePart μ := by
  rcases (extVisibilityReplace_self_iff v K).mp h with rfl | rfl | ⟨μ, rfl, hμ⟩
  · exact absurd rfl hbot
  · exact absurd rfl htop
  · exact ⟨μ, rfl, hμ⟩

end Value

/-! ### Lemma 5.3.7 for a face restriction -/

namespace StageType

variable {α : Ordinal.{0}} {m n : ℕ}

open CellScheme.restrictFace (toCell belowMap)

variable {q : S α n} {f : Fin m ↪ Fin n} {hr : Finset.univ.image f ∈ q.scheme.scheme.plan}

/-- A full-scope witness of the restriction lies below a full-scope cell of `q` of at least
its grade. -/
theorem gradedLe_toCell_of_full (Ψ : Cell (q.scheme.scheme.restrictFace f hr))
    (hsc : (q.scheme.scheme.restrictFace f hr).scope Ψ = Finset.univ)
    {Θ : Cell q.scheme.scheme} (hscΘ : q.scheme.scheme.scope Θ = Finset.univ)
    (hgr : (q.scheme.scheme.restrictFace f hr).grade Ψ ≤ q.scheme.scheme.grade Θ) :
    GradedLe (q.scheme.scheme.cell (toCell q.scheme.scheme f hr Ψ)) (q.scheme.scheme.cell Θ) := by
  refine ⟨?_, hgr⟩
  change q.scheme.scheme.scope (toCell q.scheme.scheme f hr Ψ) ⊆ q.scheme.scheme.scope Θ
  rw [← CellScheme.restrictFace.image_scope_restrictFace q.scheme.scheme f hr Ψ, hsc, hscΘ]
  exact Finset.subset_univ _

/-- **The `y ≤ z` half**: the row of the `q`-witness `Θ` at the restricted witness `Ψ'` (self-
visible at `K^p`) lies below `z`; `¬cap_q` at `Ψ'` then puts `z` in the band of `y` with finite
part `≥ K^p`. -/
theorem band_ge_of_row_le {Θ Ψ' Ξ' : Cell q.scheme.scheme}
    (hΞ'Θ : GradedLe (q.scheme.scheme.cell Ξ') (q.scheme.scheme.cell Θ))
    (hΨ'Θ : GradedLe (q.scheme.scheme.cell Ψ') (q.scheme.scheme.cell Θ))
    (hscΘ : q.scheme.scheme.scope Θ = Finset.univ) (hgrΘ : q.scheme.scheme.grade Θ = q.topGrade)
    (hΘtop : q.label Θ = ⊤) (hΨ'top : q.label Ψ' = ⊤) {K : ℕ}
    (hgrΨ' : q.scheme.scheme.grade Ψ' = K) (hK : K ≤ q.topGrade)
    (hcapq : ¬ q.ProvisionalCap Ξ') {β' : Ordinal.{0}}
    (hz : q.scheme.rows.E Θ ⟨Ξ', hΞ'Θ⟩ = ofOrd β')
    (hyz : q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩ ≤ q.scheme.rows.E Θ ⟨Ξ', hΞ'Θ⟩) :
    K ≤ finitePart β' := by
  set y := q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩
  have hself : extVisibilityReplace y K K = y := by
    have h := q.scheme.rows.orderly Θ ⟨Ψ', hΨ'Θ⟩
    change y = extVisibilityReplace y (q.scheme.scheme.grade Ψ') (q.scheme.scheme.grade Ψ') at h
    exact (hgrΨ' ▸ h).symm
  have hnotcap : ¬ extVisibilityReplace y q.topGrade q.topGrade ≤
      q.scheme.rows.E Θ ⟨Ξ', hΞ'Θ⟩ := fun hle =>
    hcapq ⟨Θ, hΞ'Θ, ⟨Ψ', hΨ'Θ⟩, hscΘ, hgrΘ, hΘtop, hΨ'top, hle⟩
  obtain ⟨μ, hμ, hKμ⟩ := exists_ordinal_of_selfVis hself
    (fun hb => hnotcap (by simp [hb])) (fun ht => by rw [ht, hz] at hyz; exact absurd hyz (by simp))
  rw [hμ, hz, ofOrd_le_ofOrd] at hyz
  rw [hμ, hz, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at hnotcap
  exact le_finitePart_of_visReplace_le_of_lt hK
    (by rwa [(visibilityReplace_self_iff μ K).mpr hKμ]) (not_le.mp hnotcap)

/-- The transform data of the locality of `E_q(Θ)` at `Ψ'`, read at a cell `d` below `Ψ'`:
`min (E_q Θ d) y = min (σ (E_q Ψ' d)) (g (grade d))`, together with `y ≤ g (grade Ψ')`. -/
theorem locality_data {Θ Ψ' : Cell q.scheme.scheme}
    (hΨ'Θ : GradedLe (q.scheme.scheme.cell Ψ') (q.scheme.scheme.cell Θ)) :
    ∃ (g : ℕ → ExtOrd) (σ : ExtOrd → ExtOrd),
      (∀ n m : ℕ, n < m → g m ≤ g n) ∧ Monotone σ ∧
      (∀ (a : ExtOrd) (k : ℕ), σ a ≤ g k → ∀ i : ℕ, i ≤ k →
        σ (extVisibilityReplace a k i) = extVisibilityReplace (σ a) k i) ∧
      (∀ d : q.scheme.scheme.below (q.scheme.scheme.cell Ψ'),
        min (q.scheme.rows.E Θ ⟨d.1, d.2.trans hΨ'Θ⟩) (q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩) =
          min (σ (q.scheme.rows.E Ψ' d)) (g (q.scheme.scheme.grade d.1))) ∧
      q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩ ≤ g (q.scheme.scheme.grade Ψ') := by
  obtain ⟨g, σ, hganti, -, -, hσmono, hσ5, hloc⟩ := (q.scheme.consistent Θ).locality ⟨Ψ', hΨ'Θ⟩
  refine ⟨g, σ, hganti, hσmono, hσ5, fun d => hloc d, ?_⟩
  have h := hloc ⟨Ψ', GradedLe.refl _⟩
  change min (q.scheme.rows.E Θ ⟨Ψ', _⟩) (q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩) =
    min (σ (q.scheme.rows.E Ψ' ⟨Ψ', GradedLe.refl _⟩)) (g (q.scheme.scheme.grade Ψ')) at h
  rw [min_self] at h
  exact h.le.trans (min_le_right _ _)

/-- **Lemma 5.3.7, core comparison** when `q` is in the band case with witness `Θ` and `p` has a
full-scope top-grade witness `Ψ`: either `z ≥ y` (yielding `K^p ≤ j`), or `z < y` with `z = σ t ≤
g K^p` and the locality witness `(g, σ)` at `Ψ' := toCell Ψ`. -/
private theorem ratchet_core_step {P : Prop} (Ξ : Cell (q.scheme.scheme.restrictFace f hr))
    (htop : (q.restrictFace f hr).label Ξ = ⊤)
    (Ψ : Cell (q.scheme.scheme.restrictFace f hr))
    (hΞΨ : GradedLe ((q.scheme.scheme.restrictFace f hr).cell Ξ)
      ((q.scheme.scheme.restrictFace f hr).cell Ψ))
    (hscΨ : (q.scheme.scheme.restrictFace f hr).scope Ψ = Finset.univ)
    (hgrΨ : (q.scheme.scheme.restrictFace f hr).grade Ψ = (q.restrictFace f hr).topGrade)
    (hΨtop : (q.restrictFace f hr).label Ψ = ⊤)
    (hcapq : ¬ q.ProvisionalCap (toCell q.scheme.scheme f hr Ξ)) {j : ℕ}
    (hbandq : q.ProvisionalBand (toCell q.scheme.scheme f hr Ξ) j)
    (hband_or_cap :
      (∃ i ≤ (q.restrictFace f hr).topGrade,
        extVisibilityReplace ((q.restrictFace f hr).scheme.rows.E Ψ ⟨Ξ, hΞΨ⟩)
          (q.restrictFace f hr).topGrade i =
          (q.restrictFace f hr).scheme.rows.E Ψ ⟨Ξ, hΞΨ⟩ ∧
        (i = j → P)) ∨
      ((q.restrictFace f hr).topGrade ≤ j → P) ∧
        ∃ Sg : (q.restrictFace f hr).scheme.scheme.below
            ((q.scheme.scheme.restrictFace f hr).cell Ψ),
          (q.restrictFace f hr).label Sg.1 = ⊤ ∧
          extVisibilityReplace ((q.restrictFace f hr).scheme.rows.E Ψ Sg)
            (q.restrictFace f hr).topGrade (q.restrictFace f hr).topGrade ≤
            (q.restrictFace f hr).scheme.rows.E Ψ ⟨Ξ, hΞΨ⟩)
    (hK_imp : (q.restrictFace f hr).topGrade ≤ j → P) : P := by
  obtain ⟨Θ, hΞ'Θ, hscΘ, hgrΘ, hΘtop, heqq⟩ := hbandq
  have hKle : (q.restrictFace f hr).topGrade ≤ q.topGrade :=
    topGrade_le_of_typeMap_eq_some (typeMap_eq_some f q hr)
  set K := (q.restrictFace f hr).topGrade
  set Ψ' := toCell q.scheme.scheme f hr Ψ
  have hgrΨ' : q.scheme.scheme.grade Ψ' = K := hgrΨ
  have hΨ'Θ : GradedLe (q.scheme.scheme.cell Ψ') (q.scheme.scheme.cell Θ) :=
    gradedLe_toCell_of_full Ψ hscΨ hscΘ (by rw [hgrΘ]; exact hgrΨ ▸ hKle)
  have hΞ'Ψ' : GradedLe (q.scheme.scheme.cell (toCell q.scheme.scheme f hr Ξ))
      (q.scheme.scheme.cell Ψ') := CellScheme.restrictFace.gradedLe_of_restrictFace _ f hr hΞΨ
  obtain ⟨g, σ, hganti, hσmono, hσ5, hloc, hyg⟩ := locality_data (Θ := Θ) hΨ'Θ
  set z := q.scheme.rows.E Θ ⟨toCell q.scheme.scheme f hr Ξ, hΞ'Θ⟩
  set y := q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩
  set t := (q.restrictFace f hr).scheme.rows.E Ψ ⟨Ξ, hΞΨ⟩
  have hloc_Ξ := hloc ⟨toCell q.scheme.scheme f hr Ξ, hΞ'Ψ'⟩
  change min z y = min (σ t) (g (q.scheme.scheme.grade (toCell q.scheme.scheme f hr Ξ))) at hloc_Ξ
  rw [hgrΨ'] at hyg
  obtain ⟨β', hzβ, _, hj⟩ :=
    ProvisionalBand.exists_ordinal (show q.label (toCell q.scheme.scheme f hr Ξ) = ⊤ from htop)
      hcapq hΞ'Θ hscΘ hgrΘ hΘtop heqq
  rcases le_or_gt y z with hyz | hzy
  · exact hK_imp (hj ▸ band_ge_of_row_le hΞ'Θ hΨ'Θ hscΘ hgrΘ hΘtop hΨtop hgrΨ' hKle hcapq hzβ hyz)
  · have hgle {c : Cell q.scheme.scheme} (hc : q.scheme.scheme.grade c ≤ K) :
        g K ≤ g (q.scheme.scheme.grade c) := by
      rcases hc.lt_or_eq with hlt | heq; exacts [hganti _ _ hlt, heq ▸ le_rfl]
    have hgrΞ : q.scheme.scheme.grade (toCell q.scheme.scheme f hr Ξ) ≤ K := hgrΨ ▸ hΞΨ.2
    rw [min_eq_left hzy.le] at hloc_Ξ
    have hzσ : z = σ t := by
      rcases le_total (σ t) (g (q.scheme.scheme.grade (toCell q.scheme.scheme f hr Ξ))) with hle | hle
      · rwa [min_eq_left hle] at hloc_Ξ
      · exact absurd (min_eq_right hle ▸ hloc_Ξ) (hzy.trans_le (hyg.trans (hgle hgrΞ))).ne
    have hσt : σ t ≤ g K := hzσ ▸ hzy.le.trans hyg
    have hzβ' : z = ofOrd β' := hzβ
    rcases hband_or_cap with ⟨i, hiK, heqp, hi_imp⟩ | ⟨_, Sg, hSgtop, hcapineq⟩
    · have h5 := hσ5 t K hσt i hiK
      rw [heqp, ← hzσ, hzβ', extVisibilityReplace_ofOrd] at h5
      have hβ'eq : β' = visibilityReplace β' K i := ofOrd_inj.mp h5
      by_cases hlt : finitePart β' < K
      · unfold visibilityReplace ordinalReplace at hβ'eq
        rw [ite_eq_left hlt] at hβ'eq
        have : i = finitePart β' :=
          Nat.cast_injective (add_left_cancel (hβ'eq.symm.trans (decomposition β').symm))
        exact hi_imp (by omega)
      · exact hK_imp (hj ▸ not_lt.mp hlt)
    · set Sg' := belowMap q.scheme.scheme f hr Ψ Sg
      set u := (q.restrictFace f hr).scheme.rows.E Ψ Sg
      set s := q.scheme.rows.E Θ ⟨Sg'.1, Sg'.2.trans hΨ'Θ⟩
      have hloc_Sg := hloc Sg'
      change min s y = min (σ u) (g (q.scheme.scheme.grade Sg'.1)) at hloc_Sg
      have hσu : σ u ≤ z := hzσ ▸ hσmono ((le_extVisibilityReplace_self u K).trans hcapineq)
      have hsσ : s = σ u := by
        have hltg : σ u < g (q.scheme.scheme.grade Sg'.1) :=
          (hσu.trans_lt hzy).trans_le (hyg.trans (hgle (hgrΨ ▸ Sg.2.2)))
        rw [min_eq_left hltg.le] at hloc_Sg
        rcases le_total s y with hsy | hys
        · rwa [min_eq_left hsy] at hloc_Sg
        · exact absurd (min_eq_right hys ▸ hloc_Sg ▸ hσu) hzy.not_ge
      have hlo : extVisibilityReplace (σ u) K K ≤ z := by
        rw [← hσ5 u K (hσu.trans (hzy.le.trans hyg)) K le_rfl, hzσ]
        exact hσmono hcapineq
      have hnotcap : ¬ extVisibilityReplace s q.topGrade q.topGrade ≤ z := fun hle =>
        hcapq ⟨Θ, hΞ'Θ, ⟨Sg'.1, Sg'.2.trans hΨ'Θ⟩, hscΘ, hgrΘ, hΘtop, hSgtop, hle⟩
      have hσubot : σ u ≠ ⊥ := hsσ ▸ row_ne_bot_of_label_top q hΘtop ⟨Sg'.1, Sg'.2.trans hΨ'Θ⟩ hSgtop
      rcases ExtOrd.cases (σ u) with hb | hT | ⟨μ, hμ⟩
      · exact absurd hb hσubot
      · exact absurd (hT ▸ hzβ' ▸ hσu) (by simp)
      · rw [hμ, hzβ', extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at hlo
        rw [hsσ, hμ, hzβ', extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at hnotcap
        exact hK_imp (hj ▸ le_finitePart_of_visReplace_le_of_lt hKle hlo (not_le.mp hnotcap))

/-- **Provisional monotonicity along an exact face.**  The ratchet (Lemma 5.3.7) and the source
bound `IsProvisionalValue.le` together give `v ≤ v'` outright.  This is the canonical home of
the inequality; the ratchet itself is retained for clients that need its gap information. -/
theorem IsProvisionalValue.le_of_typeMap {α : Ordinal.{0}} {n m : ℕ}
    {p : S α n} {q : S α m} {f : Fin n ↪ Fin m}
    (hf : typeMap f q = some p) {d : Cell p.scheme.scheme} {v v' : ExtOrd}
    (hv : p.IsProvisionalValue d v) (hv' : q.IsProvisionalValue (mapCell hf d) v') :
    v ≤ v' := by
  obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
    ⟨visible_of_typeMap_eq_some hf, restrictFace_eq_of_typeMap_eq_some hf⟩
  have hlab : q.label (toCell q.scheme.scheme f hr d) = (q.restrictFace f hr).label d := rfl
  have hKle : (q.restrictFace f hr).topGrade ≤ q.topGrade :=
    topGrade_le_of_typeMap_eq_some (typeMap_eq_some f q hr)
  have hKq : v ≤ ofOrd (α + q.topGrade) :=
    hv.le.trans (ofOrd_le_ofOrd.mpr (add_le_add le_rfl (Nat.cast_le.mpr hKle)))
  have hKj {j : ℕ} (hj : (q.restrictFace f hr).topGrade ≤ j) : v ≤ ofOrd (α + j) :=
    hv.le.trans (ofOrd_le_ofOrd.mpr (add_le_add le_rfl (Nat.cast_le.mpr hj)))
  rcases hv with ⟨hne, rfl⟩ | ⟨htop, ⟨Ψ, hdΨ, Sg, hscΨ, hgrΨ, hΨtop, hSgtop, hcapineq⟩, rfl⟩ |
      ⟨htop, hcapp, i, ⟨Ψ, hdΨ, hscΨ, hgrΨ, hΨtop, heqp⟩, rfl⟩
  · rcases hv' with ⟨-, rfl⟩ | ⟨htop', -, -⟩ | ⟨htop', -, -⟩
    · rfl
    · exact absurd (hlab ▸ htop') hne
    · exact absurd (hlab ▸ htop') hne
  · rcases hv' with ⟨hne', -⟩ | ⟨-, -, rfl⟩ | ⟨_, hcapq, j, hbandq, rfl⟩
    · exact absurd (hlab ▸ htop) hne'
    · exact hKq
    · exact ratchet_core_step d htop Ψ hdΨ hscΨ hgrΨ hΨtop hcapq hbandq
        (Or.inr ⟨hKj, Sg, hSgtop, hcapineq⟩) hKj
  · rcases hv' with ⟨hne', -⟩ | ⟨-, -, rfl⟩ | ⟨_, hcapq, j, hbandq, rfl⟩
    · exact absurd (hlab ▸ htop) hne'
    · exact hKq
    · obtain ⟨_, _, hfpτ, hi⟩ :=
        ProvisionalBand.exists_ordinal htop hcapp hdΨ hscΨ hgrΨ hΨtop heqp
      exact ratchet_core_step d htop Ψ hdΨ hscΨ hgrΨ hΨtop hcapq hbandq
        (Or.inl ⟨i, (hi ▸ hfpτ).le, heqp.symm, fun hij => by rw [hij]⟩) hKj

end StageType

/-! ### The ratchet on the labelled-cover poset, and stable-value functionality -/

namespace KnightRealization

open StageType

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

/-- The embedding of a labelled cover into a larger one is determined by the tuples. -/
theorem LabelledExt.emb_unique {x y : R.LabelledExt} {f f' : Fin x.arity ↪ Fin y.arity}
    (hf : f.trans y.tuple = x.tuple) (hf' : f'.trans y.tuple = x.tuple) : f = f' :=
  Function.Embedding.ext fun i => y.tuple.injective
    ((DFunLike.congr_fun hf i).trans (DFunLike.congr_fun hf' i).symm)

/-! ### Stable-value functionality from exact consistency alone

Each stabilization witness supplies a realized extension on which the other stabilization can
be tested; provisional monotonicity along the exact face then orders the two values.  Neither
covering nor a separately chosen root realization enters. -/

/-- Any realized provisional value of a source cell lies below a stabilized value of that cell:
stabilization supplies a larger realized tuple, exact consistency identifies the face, and
provisional monotonicity compares the readings. -/
theorem StabilizesTo.provisional_le (hcons : R.IsExactParentConsistent)
    {n m : ℕ} {t : Fin n ↪ M} {p : S α.1 n} {u : Fin m ↪ M} {q : S α.1 m}
    (hu : R.eval u = some q) {f : Fin n ↪ Fin m} (hf : f.trans u = t)
    (hpq : typeMap f q = some p) {d : Cell p.scheme.scheme} {v γ : ExtOrd}
    (hv : q.IsProvisionalValue (mapCell hpq d) v) (hγ : R.StabilizesTo t p d γ) : v ≤ γ := by
  obtain ⟨k, z, g, e, r, hpr, hz, hgz, hez, hγz⟩ := hγ u
  have hqr : typeMap g r = some q := by
    have h := hcons z r g hz; rw [hgz, hu] at h; exact h.symm
  have hfg : (f.trans g).trans z = t := by rw [Function.Embedding.trans_assoc, hgz, hf]
  have he : e = f.trans g := Function.Embedding.ext fun i =>
    z.injective ((DFunLike.congr_fun hez i).trans (DFunLike.congr_fun hfg i).symm)
  subst he
  exact hv.le_of_typeMap hqr (mapCell_trans hqr hpq hpr d ▸ hγz)

/-- **Functionality of the stabilized value** (Def. 5.3.9) **from exact consistency alone**. -/
theorem StabilizesTo.unique_of_consistent (hcons : R.IsExactParentConsistent)
    {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n} {d : Cell p.scheme.scheme} {γ γ' : ExtOrd}
    (h : R.StabilizesTo t p d γ) (h' : R.StabilizesTo t p d γ') : γ = γ' := by
  refine le_antisymm ?_ ?_
  · obtain ⟨_, _, _, _, _, hpq, hu, _, hf, hv⟩ := h t
    exact StabilizesTo.provisional_le hcons hu hf hpq hv h'
  · obtain ⟨_, _, _, _, _, hpq, hu, _, hf, hv⟩ := h' t
    exact StabilizesTo.provisional_le hcons hu hf hpq hv h

/-- **Functionality of `M⁺(Ξ)`** (the graph of Def. 5.3.9 is a function), from exact
consistency alone. -/
theorem HasStableValue.unique_of_consistent (hcons : R.IsExactParentConsistent)
    {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n} {d : Cell p.scheme.scheme} {γ γ' : ExtOrd}
    (h : R.HasStableValue t p d γ) (h' : R.HasStableValue t p d γ') : γ = γ' := by
  rcases h with ⟨hlt, hs⟩ | ⟨rfl, hno⟩ <;> rcases h' with ⟨hlt', hs'⟩ | ⟨rfl, hno'⟩
  · exact StabilizesTo.unique_of_consistent hcons @hs @hs'
  · exact absurd @hs (hno' γ hlt)
  · exact absurd @hs' (hno γ' hlt')
  · rfl

/-- **Functionality of `M⁺(Ξ)`** (the graph of Def. 5.3.9 is a function), in its original
interface; see `HasStableValue.unique_of_consistent`. -/
theorem HasStableValue.unique (hcons : R.IsExactParentConsistent)
    (_hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (_hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} {γ γ' : ExtOrd}
    (h : R.HasStableValue t p Xi γ) (h' : R.HasStableValue t p Xi γ') : γ = γ' :=
  HasStableValue.unique_of_consistent hcons h h'
