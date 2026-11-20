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

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

universe w

namespace Value

theorem le_finitePart_of_ge_of_lt {μ z : Ordinal.{0}} {K : ℕ}
    (h1 : limitPart μ + K ≤ z) {K' : ℕ} (h2 : z < limitPart μ + K') : K ≤ finitePart z := by
  have hlp : limitPart μ ≤ z := (le_add_of_nonneg_right zero_le).trans h1
  have hlim := limitPart_eq_of_le_of_lt hlp h2
  have hz := decomposition z
  rw [← hz, hlim] at h1
  simp_all

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
      have hlp : limitPart μ ≤ z := (limitPart_le μ).trans hlo
      have hlim := limitPart_eq_of_le_of_lt hlp hhi
      exact (not_lt.mp hμK).trans (finitePart_le_of_le hlim.symm hlo)
  grind

/-- A self-visible label that is neither `-∞` nor `∞` is an ordinal with finite part `≥ K`. -/
theorem exists_ordinal_of_selfVis {v : ExtOrd} {K : ℕ} (h : extVisibilityReplace v K K = v)
    (hbot : v ≠ ⊥) (htop : v ≠ ⊤) : ∃ μ : Ordinal.{0}, v = ofOrd μ ∧ K ≤ finitePart μ := by
  rcases (extVisibilityReplace_self_iff v K).mp h with rfl | rfl | ⟨μ, rfl, hμ⟩
  all_goals lia

end Value

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
  refine ⟨?_, ?_⟩
  all_goals simp_all

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
  set y := q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩ with hy
  have hself : extVisibilityReplace y K K = y := by
    have h := q.scheme.rows.orderly Θ ⟨Ψ', hΨ'Θ⟩
    grind
  have hnotcap : ¬ extVisibilityReplace y q.topGrade q.topGrade ≤
      q.scheme.rows.E Θ ⟨Ξ', hΞ'Θ⟩ := fun hle =>
    hcapq ⟨Θ, hΞ'Θ, ⟨Ψ', hΨ'Θ⟩, hscΘ, hgrΘ, hΘtop, hΨ'top, hle⟩
  have hybot : y ≠ ⊥ := by
    intro hb
    rw [hb] at hnotcap
    aesop
  have hytop : y ≠ ⊤ := by
    intro ht
    rw [ht, hz] at hyz
    simp_all
  obtain ⟨μ, hμ, hKμ⟩ := exists_ordinal_of_selfVis hself hybot hytop
  rw [hμ, hz, ofOrd_le_ofOrd] at hyz
  rw [hμ, hz, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at hnotcap
  have hlo : visibilityReplace μ K K ≤ β' := by
    rwa [(visibilityReplace_self_iff μ K).mpr hKμ]
  exact le_finitePart_of_visReplace_le_of_lt hK hlo (not_le.mp hnotcap)

/-- Compare two full-scope witnesses, for either kind of source-side evidence. -/
private theorem ratchet_core {Ξ Ψ : Cell (q.scheme.scheme.restrictFace f hr)}
    (hΞΨ : GradedLe ((q.restrictFace f hr).scheme.scheme.cell Ξ)
      ((q.restrictFace f hr).scheme.scheme.cell Ψ))
    (hsc : (q.restrictFace f hr).scheme.scheme.scope Ψ = Finset.univ)
    (hgr : (q.restrictFace f hr).scheme.scheme.grade Ψ = (q.restrictFace f hr).topGrade)
    (hΨ : (q.restrictFace f hr).label Ψ = ⊤)
    (hΞ : (q.restrictFace f hr).label Ξ = ⊤) {i j : ℕ}
    (evidence : let p := q.restrictFace f hr
      let t := p.scheme.rows.E Ψ ⟨Ξ, hΞΨ⟩
      (i ≤ p.topGrade ∧ t = extVisibilityReplace t p.topGrade i) ∨
        ∃ s : p.scheme.scheme.below (p.scheme.scheme.cell Ψ), p.label s.1 = ⊤ ∧
          extVisibilityReplace (p.scheme.rows.E Ψ s) p.topGrade p.topGrade ≤ t)
    (hcap : ¬ q.ProvisionalCap (toCell q.scheme.scheme f hr Ξ))
    (hband : q.ProvisionalBand (toCell q.scheme.scheme f hr Ξ) j) :
    i = j ∨ (q.restrictFace f hr).topGrade ≤ j := by
  obtain ⟨Θ, hΞΘ, hΘsc, hΘgr, hΘ, heq⟩ := hband
  let K := (q.restrictFace f hr).topGrade
  have hK : K ≤ q.topGrade := topGrade_le_of_typeMap_eq_some (typeMap_eq_some f q hr)
  let Ψ' := toCell q.scheme.scheme f hr Ψ
  have hgΨ : q.scheme.scheme.grade Ψ' = K := hgr
  have hΨΘ : GradedLe (q.scheme.scheme.cell Ψ') (q.scheme.scheme.cell Θ) :=
    gradedLe_toCell_of_full Ψ hsc hΘsc (by aesop)
  let z := q.scheme.rows.E Θ ⟨toCell q.scheme.scheme f hr Ξ, hΞΘ⟩
  let y := q.scheme.rows.E Θ ⟨Ψ', hΨΘ⟩
  let t := (q.restrictFace f hr).scheme.rows.E Ψ ⟨Ξ, hΞΨ⟩
  obtain ⟨β, hz, -, hj⟩ := ProvisionalBand.exists_ordinal (p := q) hΞ hcap hΞΘ hΘsc hΘgr hΘ heq
  change z = ofOrd β at hz
  rcases le_or_gt y z with hyz | hzy
  · exact Or.inr (hj ▸ band_ge_of_row_le hΞΘ hΨΘ hΘsc hΘgr hΘ hΨ hgΨ hK hcap hz hyz)
  obtain ⟨g, σ, hg, hσm, hσ, hloc, hy⟩ := locality_data hΨΘ
  have hyK : y ≤ g K := hgΨ ▸ hy
  have read (d : (q.restrictFace f hr).scheme.scheme.below
      ((q.restrictFace f hr).scheme.scheme.cell Ψ)) := hloc (belowMap q.scheme.scheme f hr Ψ d)
  have hgK (d : (q.restrictFace f hr).scheme.scheme.below
      ((q.restrictFace f hr).scheme.scheme.cell Ψ)) :
      g K ≤ g (q.scheme.scheme.grade (toCell q.scheme.scheme f hr d.1)) :=
    hg (d.2.2.trans_eq hgr)
  have hzσ : z = σ t := uncapped_eq (read ⟨Ξ, hΞΨ⟩) hzy
    (hzy.trans_le (hyK.trans (hgK ⟨Ξ, hΞΨ⟩)))
  rcases evidence with ⟨hi, ht⟩ | ⟨d, hd, hle⟩
  · by_cases hb : finitePart β < K
    · left
      have hs : σ t ≤ g K := hzσ ▸ hzy.le.trans hyK
      have he := hσ t K hs i hi
      change t = extVisibilityReplace t K i at ht
      rw [← ht, ← hzσ, hz] at he
      exact (band_eq_finitePart hb he).trans hj.symm
    · exact Or.inr (hj ▸ le_of_not_gt hb)
  · right
    let u := (q.restrictFace f hr).scheme.rows.E Ψ d
    let d' := belowMap q.scheme.scheme f hr Ψ d
    let s := q.scheme.rows.E Θ ⟨d'.1, d'.2.trans hΨΘ⟩
    have hu : σ u ≤ z := hzσ ▸ hσm ((le_extVisibilityReplace_self u K).trans hle)
    have huy : σ u < y := hu.trans_lt hzy
    have hs : σ u = s := uncapped_eq (read d).symm
      (huy.trans_le (hyK.trans (hgK d))) huy
    have hlo : extVisibilityReplace s K K ≤ z := by
      rw [← hs, ← hσ u K (huy.le.trans hyK) K le_rfl, hzσ]
      exact hσm hle
    have hhi : z < extVisibilityReplace s q.topGrade q.topGrade :=
      lt_of_not_ge fun h => hcap ⟨Θ, hΞΘ, ⟨d'.1, d'.2.trans hΨΘ⟩, hΘsc, hΘgr, hΘ, hd, h⟩
    rcases ExtOrd.cases s with hb | ht | ⟨μ, hm⟩
    · simp [hb] at hhi
    · simp_all
    · rw [hm, hz, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at hlo
      rw [hm, hz, extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd] at hhi
      exact hj ▸ le_finitePart_of_visReplace_le_of_lt hK hlo hhi

/-- **Lemma 5.3.7 (restriction form)**: for a cell `Ξ` of `p := q.restrictFace f hr` with
provisional values `v` in `p` and `w` at `toCell Ξ` in `q`: `v = w` or `α + K^p ≤ w`. -/
theorem provisional_ratchet (Ξ : Cell (q.scheme.scheme.restrictFace f hr)) {v w : ExtOrd}
    (hv : (q.restrictFace f hr).IsProvisionalValue Ξ v)
    (hw : q.IsProvisionalValue (toCell q.scheme.scheme f hr Ξ) w) :
    v = w ∨ ofOrd (α + (q.restrictFace f hr).topGrade) ≤ w := by
  have hlab : q.label (toCell q.scheme.scheme f hr Ξ) = (q.restrictFace f hr).label Ξ := rfl
  have hKle : (q.restrictFace f hr).topGrade ≤ q.topGrade :=
    topGrade_le_of_typeMap_eq_some (typeMap_eq_some f q hr)
  have hKq : ofOrd (α + (q.restrictFace f hr).topGrade) ≤ ofOrd (α + q.topGrade) := by
    simp_all
  rcases hv with ⟨hne, rfl⟩ | ⟨htop, hcapp, rfl⟩ | ⟨htop, hcapp, i, hbandp, rfl⟩
  · rcases hw with ⟨-, rfl⟩ | ⟨htop', -, -⟩ | ⟨htop', -, -⟩
    all_goals lia
  · rcases hw with ⟨hne', -⟩ | ⟨-, -, rfl⟩ | ⟨htop', hcapq, j, hbandq, rfl⟩
    · simp_all
    · exact Or.inr hKq
    · obtain ⟨Ψ, hΞΨ, d, hsc, hgr, hΨ, hd, hle⟩ := hcapp
      have h := ratchet_core hΞΨ hsc hgr hΨ htop
        (i := (q.restrictFace f hr).topGrade) (Or.inr ⟨d, hd, hle⟩) hcapq hbandq
      right
      rw [ofOrd_le_ofOrd]
      exact add_le_add le_rfl (Nat.cast_le.mpr (h.elim le_of_eq id))
  · rcases hw with ⟨hne', -⟩ | ⟨-, -, rfl⟩ | ⟨htop', hcapq, j, hbandq, rfl⟩
    · simp_all
    · exact Or.inr hKq
    · obtain ⟨Ψ, hΞΨ, hsc, hgr, hΨ, heq⟩ := hbandp
      obtain ⟨_, -, hfp, hi⟩ := ProvisionalBand.exists_ordinal htop hcapp hΞΨ hsc hgr hΨ heq
      rcases ratchet_core hΞΨ hsc hgr hΨ htop (Or.inl ⟨hi ▸ hfp.le, heq⟩) hcapq hbandq with h | h
      · subst j; exact Or.inl rfl
      · exact Or.inr (ofOrd_le_ofOrd.mpr (add_le_add le_rfl (Nat.cast_le.mpr h)))

/-- **Lemma 5.3.7 (`typeMap` form)**: along `typeMap f q = some p`, provisional values of a
cell `Ξ` of `p` and of `mapCell Ξ` in `q` agree or the latter is `≥ α + K^p`. -/
theorem provisional_ratchet' {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (Ξ : Cell p.scheme.scheme) {v w : ExtOrd}
    (hv : p.IsProvisionalValue Ξ v) (hw : q.IsProvisionalValue (mapCell h Ξ) w) :
    v = w ∨ ofOrd (α + p.topGrade) ≤ w := by
  obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
    ⟨visible_of_typeMap_eq_some h, restrictFace_eq_of_typeMap_eq_some h⟩
  exact provisional_ratchet Ξ hv hw

/-- **Provisional monotonicity along an exact face.**  The ratchet (Lemma 5.3.7) and the source
bound `IsProvisionalValue.le` together give `v ≤ v'` outright.  This is the canonical home of
the inequality; the ratchet itself is retained for clients that need its gap information. -/
theorem IsProvisionalValue.le_of_typeMap {α : Ordinal.{0}} {n m : ℕ}
    {p : S α n} {q : S α m} {f : Fin n ↪ Fin m}
    (hf : typeMap f q = some p) {d : Cell p.scheme.scheme} {v v' : ExtOrd}
    (hv : p.IsProvisionalValue d v) (hv' : q.IsProvisionalValue (mapCell hf d) v') :
    v ≤ v' := by
  rcases provisional_ratchet' hf d hv hv' with h | h
  · exact h.le
  · exact hv.le.trans h

end StageType

namespace KnightRealization

open StageType

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

/-- The embedding of a labelled cover into a larger one is determined by the tuples. -/
theorem LabelledExt.emb_unique {x y : R.LabelledExt} {f f' : Fin x.arity ↪ Fin y.arity}
    (hf : f.trans y.tuple = x.tuple) (hf' : f'.trans y.tuple = x.tuple) : f = f' := by
  apply Function.Embedding.ext
  intro i
  apply y.tuple.injective
  have h1 := DFunLike.congr_fun hf i
  have h2 := DFunLike.congr_fun hf' i
  simp only [Function.Embedding.trans_apply] at h1 h2
  exact h1.trans h2.symm

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
    have h := hcons z r g hz
    simp_all
  have hfg : (f.trans g).trans z = t := by
    aesop
  have he : e = f.trans g := by
    apply Function.Embedding.ext
    intro i
    apply z.injective
    exact (DFunLike.congr_fun hez i).trans (DFunLike.congr_fun hfg i).symm
  subst he
  have hγz' : r.IsProvisionalValue (mapCell hqr (mapCell hpq d)) γ := by
    rwa [← mapCell_trans hqr hpq hpr d]
  exact hv.le_of_typeMap hqr hγz'

/-- **Functionality of the stabilized value** (Def. 5.3.9) **from exact consistency alone**. -/
theorem StabilizesTo.unique_of_consistent (hcons : R.IsExactParentConsistent)
    {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n} {d : Cell p.scheme.scheme} {γ γ' : ExtOrd}
    (h : R.StabilizesTo t p d γ) (h' : R.StabilizesTo t p d γ') : γ = γ' := by
  apply le_antisymm
  · obtain ⟨m, u, g, f, q, hpq, hu, _, hf, hv⟩ := h t
    exact StabilizesTo.provisional_le hcons hu hf hpq hv h'
  · obtain ⟨m, u, g, f, q, hpq, hu, _, hf, hv⟩ := h' t
    exact StabilizesTo.provisional_le hcons hu hf hpq hv h

/-- **Functionality of `M⁺(Ξ)`** (the graph of Def. 5.3.9 is a function), from exact
consistency alone. -/
theorem HasStableValue.unique_of_consistent (hcons : R.IsExactParentConsistent)
    {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n} {d : Cell p.scheme.scheme} {γ γ' : ExtOrd}
    (h : R.HasStableValue t p d γ) (h' : R.HasStableValue t p d γ') : γ = γ' := by
  rcases h with ⟨hlt, hs⟩ | ⟨rfl, hno⟩ <;> rcases h' with ⟨hlt', hs'⟩ | ⟨rfl, hno'⟩
  · exact StabilizesTo.unique_of_consistent hcons @hs @hs'
  all_goals tauto

set_option linter.unusedVariables false in
/-- **Functionality of `M⁺(Ξ)`** (the graph of Def. 5.3.9 is a function), in its original
interface; see `HasStableValue.unique_of_consistent`. -/
theorem HasStableValue.unique (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} {γ γ' : ExtOrd}
    (h : R.HasStableValue t p Xi γ) (h' : R.HasStableValue t p Xi γ') : γ = γ' :=
  HasStableValue.unique_of_consistent hcons h h'

end KnightRealization

end VaughtConjecture.Knight
