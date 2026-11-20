/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProvisionalBandBridge
public import VaughtConjecture.Knight.WitnessSplice

@[expose] public section

namespace VaughtConjecture.Knight

open Value ExtOrd

namespace Value

/-- An ordinal in the band `[lam, lam + K)` of a multiple `lam` of `ω` has limit part `lam`
and finite part `< K`. -/
theorem limitPart_eq_and_finitePart_lt_of_band {lam ν : Ordinal.{0}}
    (hlam : limitPart lam = lam) {K : ℕ} (h₁ : lam ≤ ν) (h₂ : ν < lam + K) :
    limitPart ν = lam ∧ finitePart ν < K := by
  obtain ⟨j, rfl⟩ := exists_nat_of_lt_add_omega h₁ (h₂.trans
    (add_lt_add_right (Ordinal.natCast_lt_omega0 K) lam))
  exact ⟨limitPart_add_nat_of_limitPart_eq hlam j, by
    rw [finitePart_limitPart_add_nat' hlam]
    exact Nat.cast_lt.mp ((add_lt_add_iff_left lam).mp h₂)⟩

end Value

namespace ExtOrd

/-- The band map commutes with `min` at or above `lam`. -/
theorem bandMap_min {α lam : Ordinal.{0}} (hlam : limitPart lam = lam) (K : ℕ) {x y : ExtOrd}
    (hx : ofOrd lam ≤ x) (hy : ofOrd lam ≤ y) :
    bandMap α lam K (min x y) = min (bandMap α lam K x) (bandMap α lam K y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (bandMap_mono_of_le hlam K hx h)]
  · rw [min_eq_right h, min_eq_right (bandMap_mono_of_le hlam K hy h)]

/-- At or above cap level the band map is the cap `α + K`. -/
theorem bandMap_of_cap_le {α lam : Ordinal.{0}} {K : ℕ} {x : ExtOrd}
    (hx : ofOrd (lam + K) ≤ x) : bandMap α lam K x = ofOrd (α + K) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · trivial
  · exact bandMap_top α lam K
  · exact bandMap_ofOrd_of_cap (ofOrd_le_ofOrd.mp hx)

/-- Two values at or above `lam`, strictly ordered, with the same band-map value, are both at
cap level (the band map is injective on the band `[lam, lam + K)`). -/
theorem cap_of_bandMap_eq_of_lt {α lam : Ordinal.{0}} (hlam : limitPart lam = lam) (K : ℕ)
    {x y : ExtOrd} (hx : ofOrd lam ≤ x) (hxy : x < y)
    (h : bandMap α lam K x = bandMap α lam K y) : ofOrd (lam + K) ≤ x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · trivial
  · simp_all
  · by_contra hcap
    have hν : ν < lam + K := by simp_all
    have hlν : lam ≤ ν := ofOrd_le_ofOrd.mp hx
    obtain ⟨hlimν, hfpν⟩ := limitPart_eq_and_finitePart_lt_of_band hlam hlν hν
    rw [bandMap_ofOrd_of_band hlν hν] at h
    rcases ExtOrd.cases y with rfl | rfl | ⟨ρ, rfl⟩
    · simp_all
    · rw [bandMap_top, ofOrd_inj] at h
      simp_all
    · have hνρ : ν < ρ := ofOrd_lt_ofOrd.mp hxy
      by_cases hρ : lam + K ≤ ρ
      · rw [bandMap_ofOrd_of_cap hρ, ofOrd_inj] at h
        simp_all
      · have hρ' : ρ < lam + K := not_le.mp hρ
        obtain ⟨hlimρ, _⟩ :=
          limitPart_eq_and_finitePart_lt_of_band hlam (hlν.trans hνρ.le) hρ'
        rw [bandMap_ofOrd_of_band (hlν.trans hνρ.le) hρ', ofOrd_inj] at h
        have hfp := Nat.cast_injective (R := Ordinal.{0}) (add_left_cancel h)
        have h1 := decomposition ν
        have h2 := decomposition ρ
        simp_all

end ExtOrd

private theorem evr_ge_block_iff {lam : Ordinal.{0}} (h : limitPart lam = lam)
    (x : ExtOrd) (k i : ℕ) : ofOrd lam ≤ extVisibilityReplace x k i ↔ ofOrd lam ≤ x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · rfl
  · rfl
  have hle (a : Ordinal.{0}) : lam ≤ a ↔ lam ≤ limitPart a :=
    ⟨fun ha => h ▸ limitPart_mono ha, fun ha => ha.trans (limitPart_le a)⟩
  rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd, ofOrd_le_ofOrd,
    hle (visibilityReplace β k i), limitPart_visibilityReplace, ← hle β]

/-- A finite low part can be bounded with two visible cutoffs below the limit. -/
private theorem exists_visible_bounds {D : Type*} [Fintype D] {α : Ordinal.{0}}
    (hα : Order.IsSuccLimit α) (K : ℕ) (q : D → ExtOrd) :
    ∃ u v : ExtOrd, ⊥ < u ∧ u < v ∧ v < ofOrd α ∧ SelfVis K u ∧ SelfVis K v ∧
      ∀ d, q d < ofOrd α → q d ≤ u := by
  classical
  let t := Finset.univ.sup fun d => if q d < ofOrd α then q d else ⊥
  have ht : t < ofOrd α := (Finset.sup_lt_iff (bot_lt_ofOrd α)).mpr (fun d _ => by
    split_ifs <;> first | assumption | exact bot_lt_ofOrd _)
  obtain ⟨β, hβ, htβ⟩ : ∃ β, β < α ∧ t ≤ ofOrd β := by
    rcases ExtOrd.cases t with hb | ht' | ⟨β, he⟩
    · exact ⟨0, hα.pos, hb ▸ bot_le⟩
    · exact (not_lt_of_ge (ht' ▸ le_top) ht).elim
    · exact ⟨β, ofOrd_lt_ofOrd.mp (he ▸ ht), he ▸ le_rfl⟩
  let b := max K (finitePart β)
  let μ := limitPart β
  refine ⟨ofOrd (μ + b), ofOrd (μ + (b + 1 : ℕ)), bot_lt_ofOrd _, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · exact ofOrd_lt_ofOrd.mpr ((add_lt_add_right (Ordinal.natCast_lt_omega0 _) _).trans_le
      (add_omega0_le_of_lt_isSuccLimit hα ((limitPart_le β).trans_lt hβ)))
  · exact selfVis_ofOrd_iff.mpr (by rw [finitePart_limitPart_add_nat]; exact le_max_left _ _)
  · exact selfVis_ofOrd_iff.mpr (by rw [finitePart_limitPart_add_nat]; exact (le_max_left _ _).trans (Nat.le_succ _))
  · intro d hd
    have hdt : q d ≤ t := by
      simpa only [if_pos hd] using (Finset.le_sup
        (f := fun d => if q d < ofOrd α then q d else ⊥) (Finset.mem_univ d))
    exact hdt.trans (htβ.trans (ofOrd_le_ofOrd.mpr ((decomposition β).symm.le.trans
      (add_le_add_right (Nat.cast_le.mpr (le_max_right _ _)) _))))

open Transform in
/-- Merge the exact low shifter with the band readings on top-labelled cells. -/
theorem TransformsTo.merge_bandMap {D : Type*} [Finite D] {grade : D → ℕ}
    {p q r q' : D → ExtOrd} {J K : ℕ} {σ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop J) σ) (hq : ∀ d, q d = σ (p d)) (hr : TransformsTo grade p r)
    {α lam : Ordinal.{0}} (hα : Order.IsSuccLimit α) (hlam : limitPart lam = lam)
    (hJK : J ≤ K) (hgr : ∀ d, grade d ≤ J)
    (hbound : ∀ d, q d < ofOrd α ∨ q d = ⊤)
    (hlow : ∀ d, q d < ofOrd α → q' d = q d)
    (htop : ∀ d, q d = ⊤ → ofOrd lam ≤ r d ∧ q' d = bandMap α lam K (r d)) :
    TransformsTo grade p q' := by
  classical
  let _ := Fintype.ofFinite D
  obtain ⟨u, v, hu, huv, hvα, huvis, hvvis, hqu⟩ := exists_visible_bounds hα K q
  obtain ⟨g, τ, hanti, hgvis, -, hτmono, hτcomm, hread⟩ := hr
  let F (x : ExtOrd) := if ofOrd lam ≤ x then bandMap α lam K x else v
  have hFle (x : ExtOrd) : v ≤ F x := by
    by_cases hx : ofOrd lam ≤ x
    · simpa only [F, if_pos hx] using hvα.le.trans
        (le_bandMap_of_ne_bot α lam K (ne_bot_of_le_ne_bot (ofOrd_ne_bot _) hx))
    · simp [F, hx]
  have hFmono : Monotone F := by
    intro x y hxy
    by_cases hx : ofOrd lam ≤ x
    · simpa only [F, if_pos hx, if_pos (hx.trans hxy)] using bandMap_mono_of_le hlam K hx hxy
    · simpa only [F, if_neg hx] using hFle y
  have hFevr (x : ExtOrd) {k i : ℕ} (hk : k ≤ K) (hi : i ≤ k) :
      F (extVisibilityReplace x k i) = extVisibilityReplace (F x) k i := by
    by_cases hx : ofOrd lam ≤ x
    · simpa only [F, if_pos hx, if_pos ((evr_ge_block_iff hlam x k i).mpr hx)] using
        bandMap_extVisibilityReplace (α := α) hα hlam hk hi hx
    · simpa only [F, evr_ge_block_iff hlam, if_neg hx] using
        (evr_eq_self_of_selfVis (hvvis.mono hk) (i := i)).symm
  let s (x : ExtOrd) := if σ x < ofOrd α then min (σ x) u else F (τ x)
  let G (k : ℕ) := if k ≤ J then (if ofOrd lam ≤ g k then F (g k) else u) else ⊥
  have hGu (k : ℕ) (hk : k ≤ J) : u ≤ G k := by
    simp only [G, if_pos hk]
    split_ifs
    · exact huv.le.trans (hFle _)
    · rfl
  have hcut {x : ExtOrd} {k i : ℕ} (hk : k ≤ J) (hi : i ≤ k) :
      σ (extVisibilityReplace x k i) < ofOrd α ↔ σ x < ofOrd α := by
    rw [hσ.comm x hk hi]
    exact ⟨fun h => lt_of_not_ge fun he => h.not_ge (extVisReplace_ge_of_ge_limit hα he k i),
      fun h => extVisReplace_lt_of_lt_limit hα h k i⟩
  refine ⟨G, s, ?_, ?_, by simp [s, hσ.bot, bot_lt_ofOrd], ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hj : j ≤ J
    · by_cases hgj : ofOrd lam ≤ g j
      · simpa only [G, if_pos hj, if_pos (hij.le.trans hj), if_pos hgj,
          if_pos (hgj.trans (hanti i j hij))] using hFmono (hanti i j hij)
      · simpa only [G, if_pos hj, if_neg hgj] using hGu i (hij.le.trans hj)
    · simp [G, hj]
  · intro k
    by_cases hk : k ≤ J
    · by_cases hg : ofOrd lam ≤ g k
      · simpa only [G, if_pos hk, if_pos hg, ← hFevr _ (hk.trans hJK) le_rfl, ← hgvis k]
      · simpa only [G, if_pos hk, if_neg hg] using (huvis.mono (hk.trans hJK)).symm
    · simp [G, hk]
  · intro x y hxy
    by_cases hy : σ y < ofOrd α
    · simpa only [s, if_pos hy, if_pos ((hσ.mono hxy).trans_lt hy)] using
        min_le_min_right u (hσ.mono hxy)
    · by_cases hx : σ x < ofOrd α
      · simp only [s, if_pos hx, if_neg hy]
        exact (min_le_right _ _).trans (huv.le.trans (hFle _))
      · simpa only [s, if_neg hx, if_neg hy] using hFmono (hτmono hxy)
  · intro x k hx i hi
    by_cases hk : k ≤ J
    · have hkK := hk.trans hJK
      by_cases hl : σ x < ofOrd α
      · have hm : Monotone (fun z : ExtOrd => extVisibilityReplace z k i) := fun _ _ he => evr_mono he hi
        rw [show s (extVisibilityReplace x k i) = _ from if_pos ((hcut hk hi).mpr hl),
          show s x = _ from if_pos hl, hσ.comm x hk hi, hm.map_min,
          evr_eq_self_of_selfVis (huvis.mono hkK)]
      · have hg : ofOrd lam ≤ g k := by
          by_contra hn
          have he : F (τ x) ≤ u := by simpa only [s, G, if_neg hl, if_pos hk, if_neg hn] using hx
          exact huv.not_ge ((hFle _).trans he)
        simp only [s, if_neg hl, if_neg (fun h => hl ((hcut hk hi).mp h))]
        rcases le_or_gt (τ x) (g k) with he | he
        · rw [hτcomm x k he i hi, hFevr _ hkK hi]
        · have hgx := hg.trans he.le
          have hle : F (τ x) ≤ F (g k) := by simpa only [s, G, if_neg hl, if_pos hk, if_pos hg] using hx
          have hcap := cap_of_bandMap_eq_of_lt hlam K hg he
            (by simpa only [F, if_pos hg, if_pos hgx] using le_antisymm (hFmono he.le) hle)
          have hvis : SelfVis K (ofOrd (lam + K)) := selfVis_ofOrd_iff.mpr
            ((finitePart_limitPart_add_nat' hlam K).symm ▸ le_rfl)
          have hcap₁ := hcap.trans he.le
          have hcap₂ := (cap_le_of_evr hτmono hτcomm (hvis.mono hkK) hcap (hcap.trans_lt he) hi).le
          have hlo : ofOrd lam ≤ ofOrd (lam + K) := ofOrd_le_ofOrd.mpr le_self_add
          have hαvis : SelfVis K (ofOrd (α + K)) := selfVis_ofOrd_iff.mpr (by
            rw [finitePart_succLimit_add_nat hα])
          simp only [F, if_pos (hlo.trans hcap₁), if_pos (hlo.trans hcap₂),
            bandMap_of_cap_le hcap₁, bandMap_of_cap_le hcap₂,
            evr_eq_self_of_selfVis (hαvis.mono hkK)]
    · have hs : s x = ⊥ := le_bot_iff.mp (by simpa only [G, if_neg hk] using hx)
      have hl : σ x < ofOrd α := by
        by_contra hn
        exact (hu.trans huv).not_ge ((hFle (τ x)).trans_eq (by simpa only [s, if_neg hn] using hs))
      have hb : σ x = ⊥ := (min_eq_bot.mp (by simpa only [s, if_pos hl] using hs)).resolve_right hu.ne'
      have he := hσ.clause5 x k (hb ▸ bot_le) i hi
      rw [hb, extVisibilityReplace_bot] at he
      simp [s, he, hs, bot_lt_ofOrd]
  · intro d
    have hk := hgr d
    rcases hbound d with hd | hd
    · rw [hlow d hd, hq d]
      have he : σ (p d) ≤ u := (hq d) ▸ hqu d hd
      simp only [s, if_pos ((hq d) ▸ hd), min_eq_left he, min_eq_left (he.trans (hGu _ hk))]
    · obtain ⟨hrd, hqd⟩ := htop d hd
      rw [hread d] at hrd hqd
      have ht := hrd.trans (min_le_left _ _)
      have hg := hrd.trans (min_le_right _ _)
      have hn : ¬ σ (p d) < ofOrd α := by rw [← hq d, hd]; exact not_lt_of_ge le_top
      rw [hqd, bandMap_min hlam K ht hg]
      simp only [s, G, F, if_neg hn, if_pos hk, if_pos hg, if_pos ht]

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

open Transform in
/-- **Locality of `p⁺` at an arbitrary top-labelled controller `Σ`** (Lemma 5.3.5 at `Σ`):
`E(Σ) ⇒ min (p⁺, p⁺(Σ))`.  Choose a full-scope maximal top witness `Θ` above `Σ`; the label
witness of `E(Σ)` handles the finite cells, the row-consistency witness `E(Σ) ⇒
min (E(Θ)↾, E(Θ)(Σ))` post-composed with the band map of `Θ` handles the `∞`-cells
(`exists_bandBridge`), and `TransformsTo.merge_bandMap` merges the two. -/
theorem topController_locality_provisional (p : S α n) (hα : Order.IsSuccLimit α)
    {Sg : Cell p.scheme.scheme} (hSg : p.label Sg = ⊤) :
    TransformsTo (fun d : p.scheme.scheme.below (p.scheme.scheme.cell Sg) =>
        p.scheme.scheme.grade d.1)
      (p.scheme.rows.E Sg)
      (fun d => min (p.someProvisionalValue d.1) (p.someProvisionalValue Sg)) := by
  obtain ⟨Θ, hSgΘ, hsc, hgr, hΘ⟩ := exists_top_witness hSg
  obtain ⟨σ, hσ, -, hread⟩ := p.respects.rowWitness Sg
  obtain ⟨lam, hlam, hbridge⟩ := exists_bandBridge p hsc hgr hΘ
  -- the provisional value of `Σ` itself
  obtain ⟨hlSg, hvalSg⟩ := hbridge ⟨Sg, hSgΘ⟩ hSg
  have hpSg : p.someProvisionalValue Sg =
      bandMap α lam p.topGrade (p.scheme.rows.E Θ ⟨Sg, hSgΘ⟩) :=
    (isProvisionalValue_iff.mp hvalSg).symm
  have hpSgα : ofOrd α ≤ p.someProvisionalValue Sg := by
    rw [hpSg]
    exact le_bandMap_of_ne_bot α lam p.topGrade (fun hb => by
      rw [hb] at hlSg; trivial)
  refine TransformsTo.merge_bandMap (q := fun d => p.label d.1)
    (r := fun d => min (p.scheme.rows.E Θ (CellScheme.below.incl ⟨Sg, hSgΘ⟩ d))
      (p.scheme.rows.E Θ ⟨Sg, hSgΘ⟩))
    hσ (fun d => by simpa only [hSg, min_top_right] using (hread d).symm)
    ((p.scheme.consistent Θ).locality ⟨Sg, hSgΘ⟩) hα hlam (grade_le_topGrade_of_top hSg)
    (fun d => d.2.2) (fun d => p.label_bound d.1) ?_ ?_
  · intro d hd
    rw [someProvisionalValue_of_ne_top hd.ne_top]
    grind
  · intro d hd
    obtain ⟨hle, hval⟩ := hbridge (CellScheme.below.incl ⟨Sg, hSgΘ⟩ d) hd
    have hpd : p.someProvisionalValue d.1 =
        bandMap α lam p.topGrade (p.scheme.rows.E Θ (CellScheme.below.incl ⟨Sg, hSgΘ⟩ d)) :=
      (isProvisionalValue_iff.mp hval).symm
    refine ⟨le_min hle hlSg, ?_⟩
    rw [hpd, hpSg, bandMap_min hlam p.topGrade hle hlSg]

end StageType

end VaughtConjecture.Knight
