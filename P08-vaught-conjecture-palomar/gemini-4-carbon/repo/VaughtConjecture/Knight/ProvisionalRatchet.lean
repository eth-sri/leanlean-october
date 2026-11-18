/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RestrictedComposition
public import VaughtConjecture.Knight.Directedness
public import VaughtConjecture.Knight.FiniteOffset

@[expose] public section

namespace VaughtConjecture.Knight

open Value ExtOrd

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

/-- Locality of the labelling (Def. 2.5.4(1)): the row of an `∞`-cell `Θ` at an `∞`-cell
below it is not `-∞` (else the transform could not reach the label `∞`). -/
theorem row_ne_bot_of_label_top (p : S α n) {Θ : Cell p.scheme.scheme}
    (hΘ : p.label Θ = ⊤) (Sg : p.scheme.scheme.below (p.scheme.scheme.cell Θ))
    (hSg : p.label Sg.1 = ⊤) : p.scheme.rows.E Θ Sg ≠ ⊥ := by
  obtain ⟨g, σ, -, -, hσbot, -, -, hloc⟩ := p.respects.locality Θ
  have h : min (p.label Sg.1) (p.label Θ) =
      min (σ (p.scheme.rows.E Θ Sg)) (g (p.scheme.scheme.grade Sg.1)) := hloc Sg
  rw [hSg, hΘ, min_self] at h
  intro hbot
  rw [hbot, hσbot] at h
  exact absurd h.symm (by simp)

end StageType

end VaughtConjecture.Knight

namespace VaughtConjecture.Knight
open TypeTower Value ExtOrd Transform
open CellScheme.restrictFace (toCell)
universe w

namespace Value
theorem band_trichotomy (x y : Ordinal.{0}) (K : ℕ) :
    limitPart x = limitPart y ∨ limitPart x + K ≤ y ∨ limitPart y + K ≤ x := by
  rcases lt_trichotomy (limitPart x) (limitPart y) with h | h | h
  · exact Or.inr (Or.inl (((add_le_add le_rfl (Ordinal.natCast_lt_omega0 K).le).trans
      (add_omega0_le_limitPart_of_lt (limitPart_limitPart x) h)).trans (limitPart_le y)))
  · exact Or.inl h
  · exact Or.inr (Or.inr (((add_le_add le_rfl (Ordinal.natCast_lt_omega0 K).le).trans
      (add_omega0_le_limitPart_of_lt (limitPart_limitPart y) h)).trans (limitPart_le x)))

theorem limitPart_eq_and_finitePart_lt_of_band {lam ν : Ordinal.{0}}
    (hlam : limitPart lam = lam) {K : ℕ} (h₁ : lam ≤ ν) (h₂ : ν < lam + K) :
    limitPart ν = lam ∧ finitePart ν < K := by
  have hle : lam ≤ limitPart ν := hlam ▸ limitPart_mono h₁
  have heq : limitPart ν = lam := by
    rcases hle.lt_or_eq with hlt | heq
    · exact absurd ((limitPart_le ν).trans_lt h₂) (not_lt.mpr
        (((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 K)).le.trans
          (add_omega0_le_limitPart_of_lt hlam hlt)))
    · exact heq.symm
  refine ⟨heq, ?_⟩
  have hdec := decomposition ν; rw [heq] at hdec; rw [← hdec] at h₂
  exact Nat.cast_lt.mp ((add_lt_add_iff_left lam).mp h₂)

theorem visibilityReplace_le_cap_of_lt {lam ρ : Ordinal.{0}} (hlam : limitPart lam = lam)
    {K k j : ℕ} (hρ : ρ < lam + K) (hk : k ≤ K) (hj : j ≤ k) :
    visibilityReplace ρ k j ≤ lam + K := by
  unfold visibilityReplace ordinalReplace
  split_ifs with h
  · have hlim : limitPart ρ ≤ lam := by_contra fun hlt =>
      not_lt.mpr (((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 K)).le.trans
        (add_omega0_le_limitPart_of_lt hlam (not_le.mp hlt))) ((limitPart_le ρ).trans_lt hρ)
    exact add_le_add hlim ((Nat.cast_le (α := Ordinal.{0})).mpr (hj.trans hk))
  · exact hρ.le

theorem le_visibilityReplace_of_le_of_limitPart_eq {lam ν : Ordinal.{0}}
    (hlam : limitPart lam = lam) (hν : lam ≤ ν) (k i : ℕ) : lam ≤ visibilityReplace ν k i := by
  unfold visibilityReplace ordinalReplace
  split_ifs
  · exact (hlam ▸ limitPart_mono hν).trans (le_add_of_nonneg_right zero_le)
  · exact hν

theorem visibilityReplace_visibilityReplace_finitePart {ν : Ordinal.{0}} {k i : ℕ}
    (hfp : finitePart ν < k) (hi : i < k) :
    visibilityReplace (visibilityReplace ν k i) k (finitePart ν) = ν := by
  have h1 : visibilityReplace ν k i = limitPart ν + i := by
    unfold visibilityReplace ordinalReplace; rw [ite_eq_left hfp]
  rw [h1]
  have h2 : finitePart (limitPart ν + i) < k := by rw [finitePart_limitPart_add_nat]; exact hi
  unfold visibilityReplace ordinalReplace
  rw [ite_eq_left h2, limitPart_limitPart_add_nat, decomposition]
end Value

namespace ExtOrd
theorem bandMap_min {α lam : Ordinal.{0}} (hlam : limitPart lam = lam) (K : ℕ) {x y : ExtOrd}
    (hx : ofOrd lam ≤ x) (hy : ofOrd lam ≤ y) :
    bandMap α lam K (min x y) = min (bandMap α lam K x) (bandMap α lam K y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (bandMap_mono_of_le hlam K hx h)]
  · rw [min_eq_right h, min_eq_right (bandMap_mono_of_le hlam K hy h)]

theorem bandMap_of_cap_le {α lam : Ordinal.{0}} {K : ℕ} {x : ExtOrd}
    (hx : ofOrd (lam + K) ≤ x) : bandMap α lam K x = ofOrd (α + K) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · exact absurd hx (not_le.mpr (bot_lt_ofOrd _))
  · exact bandMap_top α lam K
  · exact bandMap_ofOrd_of_cap (ofOrd_le_ofOrd.mp hx)

theorem cap_of_bandMap_eq_of_lt {α lam : Ordinal.{0}} (hlam : limitPart lam = lam) (K : ℕ)
    {x y : ExtOrd} (hx : ofOrd lam ≤ x) (hxy : x < y)
    (h : bandMap α lam K x = bandMap α lam K y) : ofOrd (lam + K) ≤ x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · exact absurd hx (not_le.mpr (bot_lt_ofOrd _))
  · exact absurd hxy (not_lt.mpr le_top)
  · by_contra hcap
    have hν : ν < lam + K := not_le.mp fun h' => hcap (ofOrd_le_ofOrd.mpr h')
    have hlν : lam ≤ ν := ofOrd_le_ofOrd.mp hx
    obtain ⟨hlimν, hfpν⟩ := limitPart_eq_and_finitePart_lt_of_band hlam hlν hν
    rw [bandMap_ofOrd_of_band hlν hν] at h
    rcases ExtOrd.cases y with rfl | rfl | ⟨ρ, rfl⟩
    · exact absurd hxy (not_lt.mpr bot_le)
    · rw [bandMap_top, ofOrd_inj] at h
      have := Nat.cast_injective (R := Ordinal.{0}) (add_left_cancel h); omega
    · have hνρ : ν < ρ := ofOrd_lt_ofOrd.mp hxy
      by_cases hρ : lam + K ≤ ρ
      · rw [bandMap_ofOrd_of_cap hρ, ofOrd_inj] at h
        have := Nat.cast_injective (R := Ordinal.{0}) (add_left_cancel h); omega
      · have hρ' : ρ < lam + K := not_le.mp hρ
        obtain ⟨hlimρ, _⟩ := limitPart_eq_and_finitePart_lt_of_band hlam (hlν.trans hνρ.le) hρ'
        rw [bandMap_ofOrd_of_band (hlν.trans hνρ.le) hρ', ofOrd_inj] at h
        have hfp := Nat.cast_injective (R := Ordinal.{0}) (add_left_cancel h)
        have h1 := decomposition ν; have h2 := decomposition ρ
        rw [hlimν] at h1; rw [hlimρ, ← hfp] at h2; rw [← h1, ← h2] at hνρ
        exact lt_irrefl _ hνρ
end ExtOrd

private theorem cap_le_of_witness {g₁ : ℕ → ExtOrd} {σ₁ : ExtOrd → ExtOrd} (hσ₁mono : Monotone σ₁)
    (hσ₁5 : ∀ (a : ExtOrd) (k : ℕ), σ₁ a ≤ g₁ k → ∀ i : ℕ, i ≤ k →
      σ₁ (extVisibilityReplace a k i) = extVisibilityReplace (σ₁ a) k i)
    {lam : Ordinal.{0}} (hlam : limitPart lam = lam) {K k i : ℕ} (hk : k ≤ K) (_hi : i ≤ k)
    {a : ExtOrd} (hcap : ofOrd (lam + K) ≤ g₁ k) (hlt : g₁ k < σ₁ a) :
    ofOrd (lam + K) ≤ σ₁ (extVisibilityReplace a k i) := by
  have hcapa : ofOrd (lam + K) ≤ σ₁ a := hcap.trans hlt.le
  rcases ExtOrd.cases a with rfl | rfl | ⟨ν, rfl⟩
  · rwa [extVisibilityReplace_bot]
  · rwa [extVisibilityReplace_top]
  · rw [extVisibilityReplace_ofOrd]
    by_cases hfp : finitePart ν < k
    · have hrep : visibilityReplace ν k i = limitPart ν + i := by
        unfold visibilityReplace ordinalReplace; rw [ite_eq_left hfp]
      by_cases hi' : finitePart ν ≤ i
      · refine hcapa.trans (hσ₁mono ?_)
        rw [hrep, ofOrd_le_ofOrd]
        exact (decomposition ν).symm.trans_le
          (add_le_add le_rfl ((Nat.cast_le (α := Ordinal.{0})).mpr hi'))
      · have hi'' : i < finitePart ν := not_le.mp hi'
        by_contra hcon
        have hb : σ₁ (ofOrd (visibilityReplace ν k i)) ≤ g₁ k := (not_le.mp hcon).le.trans hcap
        have h5 := hσ₁5 _ k hb (finitePart ν) hfp.le
        rw [extVisibilityReplace_ofOrd,
          visibilityReplace_visibilityReplace_finitePart hfp (hi''.trans hfp)] at h5
        rw [h5] at hlt
        rcases ExtOrd.cases (σ₁ (ofOrd (visibilityReplace ν k i))) with hb' | ht' | ⟨ρ, hρ⟩
        · rw [hb', extVisibilityReplace_bot] at hlt
          exact absurd (hcap.trans_lt hlt) (not_lt.mpr bot_le)
        · rw [ht'] at hcon; exact hcon le_top
        · rw [hρ] at hlt hcon
          rw [extVisibilityReplace_ofOrd] at hlt
          exact absurd (hcap.trans_lt hlt) (not_lt.mpr (ofOrd_le_ofOrd.mpr
            (visibilityReplace_le_cap_of_lt hlam (ofOrd_lt_ofOrd.mp (not_le.mp hcon)) hk hfp.le)))
    · rw [visibilityReplace_of_not_lt hfp]; exact hcapa

theorem TransformsTo.merge_bandMap {D : Type*} [Finite D] {grade : D → ℕ}
    {p q r q' : D → ExtOrd}
    (g : ℕ → ExtOrd) (σ : ExtOrd → ExtOrd)
    (hσbot : σ ⊥ = ⊥) (hσmono : Monotone σ)
    (hσ5 : ∀ (a : ExtOrd) (k : ℕ), σ a ≤ g k → ∀ i : ℕ, i ≤ k →
      σ (extVisibilityReplace a k i) = extVisibilityReplace (σ a) k i)
    (heq : ∀ d, q d = min (σ (p d)) (g (grade d)))
    (g₁ : ℕ → ExtOrd) (σ₁ : ExtOrd → ExtOrd)
    (hg₁anti : ∀ n m : ℕ, n < m → g₁ m ≤ g₁ n)
    (hg₁self : ∀ n : ℕ, g₁ n = extVisibilityReplace (g₁ n) n n)
    (hσ₁mono : Monotone σ₁)
    (hσ₁5 : ∀ (a : ExtOrd) (k : ℕ), σ₁ a ≤ g₁ k → ∀ i : ℕ, i ≤ k →
      σ₁ (extVisibilityReplace a k i) = extVisibilityReplace (σ₁ a) k i)
    (heq₁ : ∀ d, r d = min (σ₁ (p d)) (g₁ (grade d)))
    {α lam : Ordinal.{0}} (hα : Order.IsSuccLimit α) (hlam : limitPart lam = lam) (K J : ℕ)
    (hJK : J ≤ K) (hgr : ∀ d, grade d ≤ J) (hgJ : ∀ k, k ≤ J → g k = ⊤)
    (hbound : ∀ d, q d < ofOrd α ∨ q d = ⊤)
    (hlow : ∀ d, q d < ofOrd α → q' d = q d)
    (htop : ∀ d, q d = ⊤ → ofOrd lam ≤ r d ∧ q' d = bandMap α lam K (r d)) :
    TransformsTo grade p q' := by
  classical
  have := Fintype.ofFinite D
  have hα0 : (0 : Ordinal.{0}) < α := hα.pos
  have hαlam : ∀ x : ExtOrd, x ≠ ⊥ → ofOrd α ≤ bandMap α lam K x :=
    fun x hx => le_bandMap_of_ne_bot α lam K hx
  have hlam_ne_bot : ∀ x : ExtOrd, ofOrd lam ≤ x → x ≠ ⊥ := fun x hx hb => by
    rw [hb] at hx; exact absurd hx (not_le.mpr (bot_lt_ofOrd _))
  have hq : ∀ d, q d = σ (p d) := fun d => by rw [heq d, hgJ _ (hgr d), min_top_right]
  let S : Ordinal.{0} :=
    Finset.univ.sup fun d => if σ (p d) < ofOrd α then ordOrZero (σ (p d)) else 0
  have hS : S < α := by
    rw [Finset.sup_lt_iff hα0]; intro d _; split_ifs with hd
    · rcases ExtOrd.cases (σ (p d)) with hb | ht | ⟨ν, hν⟩
      · rw [hb, ordOrZero_bot]; exact hα0
      · rw [ht] at hd; exact absurd hd (not_lt.mpr le_top)
      · rw [hν, ordOrZero_ofOrd]; rw [hν] at hd; exact ofOrd_lt_ofOrd.mp hd
    · exact hα0
  let μ : Ordinal.{0} := limitPart S
  have hμ : limitPart μ = μ := limitPart_limitPart S
  let K' : ℕ := max K (finitePart S)
  have hKK' : K ≤ K' := le_max_left _ _
  let c₁ : Ordinal.{0} := μ + K'
  let c : Ordinal.{0} := μ + (K' + 1 : ℕ)
  have hμα : μ + Ordinal.omega0 ≤ α :=
    add_omega0_le_of_lt_isSuccLimit hα ((limitPart_le S).trans_lt hS)
  have hc₁ : c₁ < α := ((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 _)).trans_le hμα
  have hc : c < α := ((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 _)).trans_le hμα
  have hc₁c : c₁ < c := (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr (Nat.lt_succ_self _))
  have hc₁α : ofOrd c₁ < ofOrd α := ofOrd_lt_ofOrd.mpr hc₁
  have hcα : ofOrd c < ofOrd α := ofOrd_lt_ofOrd.mpr hc
  have hc₁c' : ofOrd c₁ < ofOrd c := ofOrd_lt_ofOrd.mpr hc₁c
  have hfpc₁ : finitePart c₁ = K' := finitePart_limitPart_add_nat' hμ K'
  have hfpc : finitePart c = K' + 1 := finitePart_limitPart_add_nat' hμ (K' + 1)
  have hc₁self (k) (hk : k ≤ K) : extVisibilityReplace (ofOrd c₁) k k = ofOrd c₁ := by
    rw [extVisibilityReplace_ofOrd, (visibilityReplace_self_iff c₁ k).mpr (hfpc₁ ▸ hk.trans hKK')]
  have hcrep (k i) (hk : k ≤ K) (_ : i ≤ k) : extVisibilityReplace (ofOrd c) k i = ofOrd c := by
    rw [extVisibilityReplace_ofOrd,
      visibilityReplace_of_not_lt (hfpc ▸ not_lt.mpr ((hk.trans hKK').trans (Nat.le_succ _)))]
  have hSc₁ : S ≤ c₁ := (decomposition S).symm.trans_le
    (add_le_add le_rfl ((Nat.cast_le (α := Ordinal.{0})).mpr (le_max_right _ _)))
  have hσc (d) (hd : σ (p d) < ofOrd α) : σ (p d) ≤ ofOrd c₁ := by
    have hxS : ordOrZero (σ (p d)) ≤ S := by
      have := Finset.le_sup
        (f := fun d => if σ (p d) < ofOrd α then ordOrZero (σ (p d)) else 0) (Finset.mem_univ d)
      rwa [ite_eq_left hd] at this
    rcases ExtOrd.cases (σ (p d)) with hb | ht | ⟨ν, hν⟩
    · rw [hb]; exact bot_le
    · rw [ht] at hd; exact absurd hd (not_lt.mpr le_top)
    · rw [hν] at hxS ⊢; rw [ordOrZero_ofOrd] at hxS; exact ofOrd_le_ofOrd.mpr (hxS.trans hSc₁)
  have hlowreg (a : ExtOrd) (k i : ℕ) (hk : k ≤ J) (hi : i ≤ k) (ha : σ a < ofOrd α) :
      σ (extVisibilityReplace a k i) = extVisibilityReplace (σ a) k i ∧
        σ (extVisibilityReplace a k i) < ofOrd α := by
    have h5 := hσ5 a k (by rw [hgJ k hk]; exact le_top) i hi
    refine ⟨h5, ?_⟩; rw [h5]
    rcases ExtOrd.cases (σ a) with hb | ht | ⟨ν, hν⟩
    · rw [hb, extVisibilityReplace_bot]; exact bot_lt_ofOrd _
    · rw [ht] at ha; exact absurd ha (not_lt.mpr le_top)
    · rw [hν] at ha ⊢; rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
      exact visibilityReplace_lt_of_lt hα (ofOrd_lt_ofOrd.mp ha) k i
  have hhighreg (a : ExtOrd) (k i : ℕ) (hk : k ≤ J) (hi : i ≤ k) (ha : ¬ σ a < ofOrd α) :
      ¬ σ (extVisibilityReplace a k i) < ofOrd α := by
    rw [hσ5 a k (by rw [hgJ k hk]; exact le_top) i hi]
    rcases ExtOrd.cases (σ a) with hb | ht | ⟨ν, hν⟩
    · rw [hb] at ha; exact absurd (bot_lt_ofOrd α) ha
    · rw [ht, extVisibilityReplace_top]; exact not_lt.mpr le_top
    · rw [hν] at ha ⊢; rw [extVisibilityReplace_ofOrd]
      intro hlt; apply ha; rw [ofOrd_lt_ofOrd] at hlt ⊢
      have hαν : α ≤ ν := not_lt.mp fun h => ha (ofOrd_lt_ofOrd.mpr h)
      unfold visibilityReplace ordinalReplace at hlt; split_ifs at hlt
      · exact absurd ((succLimit_le_limitPart hα hαν).trans (le_add_of_nonneg_right zero_le))
          (not_le.mpr hlt)
      · exact absurd hαν (not_le.mpr hlt)
  let σ' : ExtOrd → ExtOrd := fun a =>
    if σ a < ofOrd α then min (σ a) (ofOrd c₁)
    else if σ₁ a < ofOrd lam then ofOrd c else bandMap α lam K (σ₁ a)
  let g' : ℕ → ExtOrd := fun k =>
    if k ≤ J then (if ofOrd lam ≤ g₁ k then bandMap α lam K (g₁ k) else ofOrd c₁) else ⊥
  have hσ'low (a) (ha : σ a < ofOrd α) : σ' a = min (σ a) (ofOrd c₁) := ite_eq_left ha
  have hσ'free (a) (ha : ¬ σ a < ofOrd α) (hl : σ₁ a < ofOrd lam) : σ' a = ofOrd c := by
    change (if σ a < ofOrd α then _ else if σ₁ a < ofOrd lam then _ else _) = _
    rw [ite_eq_right ha, ite_eq_left hl]
  have hσ'band (a) (ha : ¬ σ a < ofOrd α) (hl : ¬ σ₁ a < ofOrd lam) :
      σ' a = bandMap α lam K (σ₁ a) := by
    change (if σ a < ofOrd α then _ else if σ₁ a < ofOrd lam then _ else _) = _
    rw [ite_eq_right ha, ite_eq_right hl]
  have hσ'high_ge (a) (ha : ¬ σ a < ofOrd α) : ofOrd c ≤ σ' a := by
    by_cases hl : σ₁ a < ofOrd lam
    · rw [hσ'free a ha hl]
    · rw [hσ'band a ha hl]; exact hcα.le.trans (hαlam _ (hlam_ne_bot _ (not_lt.mp hl)))
  have hσ'low_le (a) (ha : σ a < ofOrd α) : σ' a ≤ ofOrd c₁ := by
    rw [hσ'low a ha]; exact min_le_right _ _
  have hg'high (k) (hk : k ≤ J) (hl : ofOrd lam ≤ g₁ k) : g' k = bandMap α lam K (g₁ k) := by
    change (if k ≤ J then (if ofOrd lam ≤ g₁ k then _ else _) else _) = _
    rw [ite_eq_left hk, ite_eq_left hl]
  have hg'low (k) (hk : k ≤ J) (hl : ¬ ofOrd lam ≤ g₁ k) : g' k = ofOrd c₁ := by
    change (if k ≤ J then (if ofOrd lam ≤ g₁ k then _ else _) else _) = _
    rw [ite_eq_left hk, ite_eq_right hl]
  have hg'top (k) (hk : J < k) : g' k = ⊥ := ite_eq_right (not_le.mpr hk)
  have hg'ge (k) (hk : k ≤ J) : ofOrd c₁ ≤ g' k := by
    by_cases hl : ofOrd lam ≤ g₁ k
    · rw [hg'high k hk hl]; exact hc₁α.le.trans (hαlam _ (hlam_ne_bot _ hl))
    · rw [hg'low k hk hl]
  have hforce (a k) (hk : k ≤ J) (ha : ¬ σ a < ofOrd α) (hle : σ' a ≤ g' k) : ofOrd lam ≤ g₁ k := by
    by_contra hl; rw [hg'low k hk hl] at hle
    exact absurd (hc₁c'.trans_le ((hσ'high_ge a ha).trans hle)) (lt_irrefl _)
  refine ⟨g', σ', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k₁ k₂ hlt
    by_cases h2 : k₂ ≤ J
    · have h1 : k₁ ≤ J := hlt.le.trans h2
      by_cases hl2 : ofOrd lam ≤ g₁ k₂
      · have hl1 : ofOrd lam ≤ g₁ k₁ := hl2.trans (hg₁anti _ _ hlt)
        rw [hg'high k₂ h2 hl2, hg'high k₁ h1 hl1]
        exact bandMap_mono_of_le hlam K hl2 (hg₁anti _ _ hlt)
      · rw [hg'low k₂ h2 hl2]; exact hg'ge k₁ h1
    · rw [hg'top k₂ (not_le.mp h2)]; exact bot_le
  · intro k
    by_cases hk : k ≤ J
    · by_cases hl : ofOrd lam ≤ g₁ k
      · rw [hg'high k hk hl]
        have h1 := bandMap_extVisibilityReplace (α := α) hα hlam (hk.trans hJK) le_rfl hl
        rwa [← hg₁self k] at h1
      · rw [hg'low k hk hl, hc₁self k (hk.trans hJK)]
    · rw [hg'top k (not_le.mp hk), extVisibilityReplace_bot]
  · rw [hσ'low ⊥ (by rw [hσbot]; exact bot_lt_ofOrd _), hσbot, min_eq_left bot_le]
  · intro a b hab
    by_cases ha : σ a < ofOrd α
    · by_cases hb : σ b < ofOrd α
      · rw [hσ'low a ha, hσ'low b hb]; exact min_le_min_right _ (hσmono hab)
      · exact (hσ'low_le a ha).trans (hc₁c'.le.trans (hσ'high_ge b hb))
    · have hb : ¬ σ b < ofOrd α := fun hb => ha ((hσmono hab).trans_lt hb)
      by_cases hla : σ₁ a < ofOrd lam
      · rw [hσ'free a ha hla]; exact hσ'high_ge b hb
      · have hlb : ¬ σ₁ b < ofOrd lam := fun hlb => hla ((hσ₁mono hab).trans_lt hlb)
        rw [hσ'band a ha hla, hσ'band b hb hlb]
        exact bandMap_mono_of_le hlam K (not_lt.mp hla) (hσ₁mono hab)
  · intro a k hak i hik
    by_cases hk : k ≤ J
    · have hkK : k ≤ K := hk.trans hJK
      by_cases ha : σ a < ofOrd α
      · obtain ⟨h5, hlt⟩ := hlowreg a k i hk hik ha
        rw [hσ'low _ hlt, hσ'low a ha, h5]
        exact min_extVisibilityReplace_cap hμ hKK' hkK hik (σ a) ha.ne_top
      · have hhi := hhighreg a k i hk hik ha
        have hgk : ofOrd lam ≤ g₁ k := hforce a k hk ha hak
        by_cases hla : σ₁ a < ofOrd lam
        · have h5 := hσ₁5 a k (hla.le.trans hgk) i hik
          have hla' : σ₁ (extVisibilityReplace a k i) < ofOrd lam := by
            rw [h5]
            rcases ExtOrd.cases (σ₁ a) with hb | ht | ⟨ν, hν⟩
            · rw [hb, extVisibilityReplace_bot]; exact bot_lt_ofOrd _
            · rw [ht] at hla; exact absurd hla (not_lt.mpr le_top)
            · rw [hν] at hla ⊢; rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
              exact visibilityReplace_lt_of_lt_of_limitPart_eq hlam (ofOrd_lt_ofOrd.mp hla) k i
          rw [hσ'free _ hhi hla', hσ'free a ha hla, hcrep k i hkK hik]
        · rw [hσ'band a ha hla, hg'high k hk hgk] at hak
          have hla₀ : ofOrd lam ≤ σ₁ a := not_lt.mp hla
          rcases le_or_gt (σ₁ a) (g₁ k) with hle | hlt
          · have h5 := hσ₁5 a k hle i hik
            have hla' : ¬ σ₁ (extVisibilityReplace a k i) < ofOrd lam := by
              rw [h5]
              rcases ExtOrd.cases (σ₁ a) with hb | ht | ⟨ν, hν⟩
              · rw [hb] at hla₀; exact absurd hla₀ (not_le.mpr (bot_lt_ofOrd _))
              · rw [ht, extVisibilityReplace_top]; exact not_lt.mpr le_top
              · rw [hν] at hla₀ ⊢; rw [extVisibilityReplace_ofOrd]
                exact not_lt.mpr (ofOrd_le_ofOrd.mpr
                  (le_visibilityReplace_of_le_of_limitPart_eq hlam (ofOrd_le_ofOrd.mp hla₀) k i))
            rw [hσ'band _ hhi hla', hσ'band a ha hla, h5]
            exact bandMap_extVisibilityReplace hα hlam hkK hik hla₀
          · have heqB : bandMap α lam K (g₁ k) = bandMap α lam K (σ₁ a) :=
              le_antisymm (bandMap_mono_of_le hlam K hgk hlt.le) hak
            have hcap : ofOrd (lam + K) ≤ g₁ k := cap_of_bandMap_eq_of_lt hlam K hgk hlt heqB
            have hcapa : ofOrd (lam + K) ≤ σ₁ a := hcap.trans hlt.le
            have hcapa' : ofOrd (lam + K) ≤ σ₁ (extVisibilityReplace a k i) :=
              cap_le_of_witness hσ₁mono hσ₁5 hlam hkK hik hcap hlt
            have hla' : ¬ σ₁ (extVisibilityReplace a k i) < ofOrd lam := not_lt.mpr
              ((ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)).trans hcapa')
            rw [hσ'band _ hhi hla', hσ'band a ha hla, bandMap_of_cap_le hcapa', bandMap_of_cap_le hcapa]
            have hαlim : limitPart α = α :=
              le_antisymm (limitPart_le α) (succLimit_le_limitPart hα (le_refl α))
            rw [extVisibilityReplace_ofOrd, visibilityReplace_of_not_lt
              (by rw [finitePart_limitPart_add_nat' hαlim]; exact not_lt.mpr hkK)]
    · rw [hg'top k (not_le.mp hk)] at hak
      have hσ'a : σ' a = ⊥ := le_bot_iff.mp hak
      have ha : σ a < ofOrd α := by_contra fun h =>
        not_le.mpr (bot_lt_ofOrd c) (hσ'a ▸ hσ'high_ge a h)
      rw [hσ'low a ha] at hσ'a
      have hσab : σ a = ⊥ := by_contra fun hne =>
        lt_irrefl _ (hσ'a ▸ lt_min (bot_lt_iff_ne_bot.mpr hne) (bot_lt_ofOrd c₁))
      have h5 := hσ5 a k (by rw [hσab]; exact bot_le) i hik
      rw [hσab, extVisibilityReplace_bot] at h5
      rw [hσ'low _ (by rw [h5]; exact bot_lt_ofOrd _), h5, min_eq_left bot_le,
        hσ'low a ha, hσab, min_eq_left bot_le, extVisibilityReplace_bot]
  · intro d
    have hk := hgr d
    rcases hbound d with hd | hd
    · rw [hlow d hd, hq d]
      have hσ : σ (p d) < ofOrd α := by rwa [hq d] at hd
      rw [hσ'low _ hσ, min_eq_left (hσc d hσ)]
      exact (min_eq_left ((hσc d hσ).trans (hg'ge _ hk))).symm
    · obtain ⟨hlr, hq'⟩ := htop d hd
      rw [hq', heq₁ d]
      have hσ : ¬ σ (p d) < ofOrd α := by rw [← hq d, hd]; exact not_lt.mpr le_top
      rw [heq₁ d] at hlr
      have hl₁ : ofOrd lam ≤ σ₁ (p d) := hlr.trans (min_le_left _ _)
      have hl₂ : ofOrd lam ≤ g₁ (grade d) := hlr.trans (min_le_right _ _)
      rw [hσ'band _ hσ (not_lt.mpr hl₁), hg'high _ hk hl₂, bandMap_min hlam K hl₁ hl₂]

namespace StageType
variable {α β : Ordinal.{0}} {n : ℕ}

theorem limitPart_eq_of_not_cap {p : S α n} {Θ : Cell p.scheme.scheme}
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (hΘ : p.label Θ = ⊤) {d d' : p.scheme.scheme.below (p.scheme.scheme.cell Θ)}
    (hd : p.label d.1 = ⊤) (hd' : p.label d'.1 = ⊤)
    (hcap : ¬ p.ProvisionalCap d.1) (hcap' : ¬ p.ProvisionalCap d'.1)
    {ν ν' : Ordinal.{0}} (hν : p.scheme.rows.E Θ d = ofOrd ν)
    (hν' : p.scheme.rows.E Θ d' = ofOrd ν') :
    finitePart ν < p.topGrade ∧ finitePart ν' < p.topGrade ∧ limitPart ν = limitPart ν' := by
  have hfp (e : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) (μ : Ordinal.{0})
      (he : p.label e.1 = ⊤) (hce : ¬ p.ProvisionalCap e.1) (hμ : p.scheme.rows.E Θ e = ofOrd μ) :
      finitePart μ < p.topGrade := by_contra fun hge => hce
    ⟨Θ, e.2, e, hsc, hgr, hΘ, he, by
      change extVisibilityReplace (p.scheme.rows.E Θ e) p.topGrade p.topGrade ≤ p.scheme.rows.E Θ e
      rw [hμ, extVisibilityReplace_ofOrd, (visibilityReplace_self_iff μ _).mpr (not_lt.mp hge)]⟩
  have h1 := hfp d ν hd hcap hν; have h2 := hfp d' ν' hd' hcap' hν'
  refine ⟨h1, h2, ?_⟩
  rcases band_trichotomy ν ν' p.topGrade with h | h | h
  · exact h
  · exact False.elim (hcap' ⟨Θ, d'.2, d, hsc, hgr, hΘ, hd, by
      change extVisibilityReplace (p.scheme.rows.E Θ d) p.topGrade p.topGrade ≤ p.scheme.rows.E Θ d'
      rwa [hν, hν', extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt h1, ofOrd_le_ofOrd]⟩)
  · exact False.elim (hcap ⟨Θ, d.2, d', hsc, hgr, hΘ, hd', by
      change extVisibilityReplace (p.scheme.rows.E Θ d') p.topGrade p.topGrade ≤ p.scheme.rows.E Θ d
      rwa [hν, hν', extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt h2, ofOrd_le_ofOrd]⟩)

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
  by_contra hnc; push Not at hnc
  set a := p.scheme.rows.E Θ ⟨d, hdΘ⟩
  set Y := p.scheme.rows.E Θ ⟨Θ', hΘ'Θ⟩
  set s := p.scheme.rows.E Θ ⟨Sg'.1, hSgΘ⟩
  set b := p.scheme.rows.E Θ' ⟨d, hdΘ'⟩
  set t := p.scheme.rows.E Θ' Sg'
  have hYself : extVisibilityReplace Y K K = Y := by
    have := p.scheme.rows.orderly Θ ⟨Θ', hΘ'Θ⟩
    change Y = extVisibilityReplace Y (p.scheme.scheme.grade Θ') (p.scheme.scheme.grade Θ') at this
    rw [hgr'] at this; exact this.symm
  have haY : a < Y := by have := hnc ⟨Θ', hΘ'Θ⟩ hΘ'; rwa [hYself] at this
  have hsa : ¬ extVisibilityReplace s K K ≤ a := not_le.mpr (hnc ⟨Sg'.1, hSgΘ⟩ hSg')
  obtain ⟨g', σ', hganti, -, -, hσmono, hσ5, hloc⟩ := (p.scheme.consistent Θ).locality ⟨Θ', hΘ'Θ⟩
  have hlocΘ' := hloc ⟨Θ', GradedLe.refl _⟩
  have hlocd := hloc ⟨d, hdΘ'⟩
  have hlocS := hloc Sg'
  change min Y Y = min (σ' (p.scheme.rows.E Θ' ⟨Θ', GradedLe.refl _⟩)) (g' (p.scheme.scheme.grade Θ')) at hlocΘ'
  change min a Y = min (σ' b) (g' (p.scheme.scheme.grade d)) at hlocd
  change min s Y = min (σ' t) (g' (p.scheme.scheme.grade Sg'.1)) at hlocS
  have hYg : Y ≤ g' K := by rw [min_self, hgr'] at hlocΘ'; rw [hlocΘ']; exact min_le_right _ _
  have hgd : g' K ≤ g' (p.scheme.scheme.grade d) := by
    have h2 : p.scheme.scheme.grade d ≤ K := hgr' ▸ hdΘ'.2
    rcases h2.lt_or_eq with hlt | heq; exact hganti _ _ hlt; rw [heq]
  have hgS : g' K ≤ g' (p.scheme.scheme.grade Sg'.1) := by
    have h2 : p.scheme.scheme.grade Sg'.1 ≤ K := hgr' ▸ Sg'.2.2
    rcases h2.lt_or_eq with hlt | heq; exact hganti _ _ hlt; rw [heq]
  have hlocd' : a = min (σ' b) (g' (p.scheme.scheme.grade d)) := by
    rw [← hlocd, min_eq_left haY.le]
  have haσ : a = σ' b := by
    rcases le_total (σ' b) (g' (p.scheme.scheme.grade d)) with hle' | hle'
    · rwa [min_eq_left hle'] at hlocd'
    · rw [min_eq_right hle'] at hlocd'
      exact absurd (lt_of_lt_of_le haY (hYg.trans hgd)) (not_lt.mpr hlocd'.ge)
  have htb : σ' (extVisibilityReplace t K K) ≤ a := haσ ▸ hσmono hle
  rcases lt_or_ge s Y with hsY | hsY
  · have hlocS' : s = min (σ' t) (g' (p.scheme.scheme.grade Sg'.1)) := by
      rw [← hlocS, min_eq_left hsY.le]
    have hsσ : s = σ' t := by
      rcases le_total (σ' t) (g' (p.scheme.scheme.grade Sg'.1)) with hle' | hle'
      · rwa [min_eq_left hle'] at hlocS'
      · rw [min_eq_right hle'] at hlocS'
        exact absurd (lt_of_lt_of_le hsY (hYg.trans hgS)) (not_lt.mpr hlocS'.ge)
    rw [hσ5 t K (hsσ ▸ hsY.le.trans hYg) K le_rfl, ← hsσ] at htb
    exact hsa htb
  · rw [min_eq_right hsY] at hlocS
    exact absurd haY (not_lt.mpr ((hlocS.le.trans (min_le_left _ _)).trans
      ((hσmono (le_extVisibilityReplace_self t K)).trans htb)))

def CapAt (p : S α n) (Θ : Cell p.scheme.scheme)
    (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) : Prop :=
  ∃ Sg : p.scheme.scheme.below (p.scheme.scheme.cell Θ), p.label Sg.1 = ⊤ ∧
    extVisibilityReplace (p.scheme.rows.E Θ Sg) p.topGrade p.topGrade ≤ p.scheme.rows.E Θ d

theorem CapAt.row_ge {p : S α n} {Θ : Cell p.scheme.scheme}
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (hΘ : p.label Θ = ⊤) {d₀ : p.scheme.scheme.below (p.scheme.scheme.cell Θ)}
    (hd₀ : p.label d₀.1 = ⊤) (hc₀ : ¬ p.ProvisionalCap d₀.1) {ν₀ : Ordinal.{0}}
    (hν₀ : p.scheme.rows.E Θ d₀ = ofOrd ν₀) :
    ∀ (ν : Ordinal.{0}) (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)), p.label d.1 = ⊤ →
      p.scheme.rows.E Θ d = ofOrd ν → CapAt p Θ d → limitPart ν₀ + p.topGrade ≤ ν := by
  set K := p.topGrade
  intro ν
  induction ν using WellFoundedLT.induction with
  | _ ν ih =>
  intro d hd hν ⟨Sg, hSg, hle⟩
  rw [hν] at hle
  rcases ExtOrd.cases (p.scheme.rows.E Θ Sg) with hb | ht | ⟨μ, hμ⟩
  · exact absurd hb (row_ne_bot_of_label_top p hΘ Sg hSg)
  · rw [ht, extVisibilityReplace_top] at hle; exact absurd hle (not_le.mpr (ofOrd_lt_top _))
  · rw [hμ, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at hle
    by_cases hcapS : CapAt p Θ Sg
    · rcases lt_or_ge μ ν with hlt | hge
      · exact (ih μ hlt Sg hSg hμ hcapS).trans ((le_visibilityReplace_self μ K).trans hle)
      · have hfpμ : K ≤ finitePart μ := by_contra fun hlt => by
          rw [visibilityReplace_of_finitePart_lt (not_le.mp hlt)] at hle
          exact not_le.mpr (hge.trans_lt ((decomposition μ).symm.trans_lt
            ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr (not_le.mp hlt))))) hle
        rw [(visibilityReplace_self_iff μ K).mpr hfpμ] at hle
        obtain rfl : μ = ν := le_antisymm hle hge
        have hlp : limitPart ν₀ ≤ limitPart μ := by_contra fun hlt => hc₀
          ⟨Θ, d₀.2, Sg, hsc, hgr, hΘ, hSg, by
            change extVisibilityReplace (p.scheme.rows.E Θ Sg) K K ≤ p.scheme.rows.E Θ d₀
            rw [hμ, hν₀, extVisibilityReplace_ofOrd, (visibilityReplace_self_iff μ K).mpr hfpμ, ofOrd_le_ofOrd]
            exact (((decomposition μ).symm.trans_lt
              ((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 _))).trans_le
              (add_omega0_le_limitPart_of_lt (limitPart_limitPart μ) (not_le.mp hlt))).le.trans
              (limitPart_le ν₀)⟩
        exact (add_le_add hlp le_rfl).trans
          ((add_le_add le_rfl (Nat.cast_le.mpr hfpμ)).trans_eq (decomposition μ))
    · have hncS : ¬ p.ProvisionalCap Sg.1 := fun hc =>
        hcapS (let ⟨Sg₁, h1, h2⟩ := hc.transport Sg.2 hsc hgr hΘ; ⟨Sg₁, h1, h2⟩)
      obtain ⟨hfpμ, -, hlp⟩ := limitPart_eq_of_not_cap hsc hgr hΘ hSg hd₀ hncS hc₀ hμ hν₀
      rwa [visibilityReplace_of_finitePart_lt hfpμ, hlp] at hle

theorem exists_bandBridge (p : S α n) {Θ : Cell p.scheme.scheme}
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (hΘ : p.label Θ = ⊤) :
    ∃ lam : Ordinal.{0}, limitPart lam = lam ∧
      ∀ d : p.scheme.scheme.below (p.scheme.scheme.cell Θ), p.label d.1 = ⊤ →
        ofOrd lam ≤ p.scheme.rows.E Θ d ∧
          p.IsProvisionalValue d.1 (bandMap α lam p.topGrade (p.scheme.rows.E Θ d)) := by
  classical
  set K := p.topGrade
  have hcapval (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) (hd : p.label d.1 = ⊤)
      (hc : p.ProvisionalCap d.1) : p.IsProvisionalValue d.1 (ofOrd (α + K)) :=
    Or.inr (Or.inl ⟨hd, hc, rfl⟩)
  have hbandval (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) (ν : Ordinal.{0})
      (hd : p.label d.1 = ⊤) (hc : ¬ p.ProvisionalCap d.1) (hν : p.scheme.rows.E Θ d = ofOrd ν) :
      finitePart ν < K ∧ p.IsProvisionalValue d.1 (ofOrd (α + finitePart ν)) := by
    have hfp : finitePart ν < K := by_contra fun hge => hc
      ⟨Θ, d.2, d, hsc, hgr, hΘ, hd, by
        change extVisibilityReplace (p.scheme.rows.E Θ d) K K ≤ p.scheme.rows.E Θ d
        rw [hν, extVisibilityReplace_ofOrd, (visibilityReplace_self_iff ν _).mpr (not_lt.mp hge)]⟩
    refine ⟨hfp, Or.inr (Or.inr ⟨hd, hc, finitePart ν, ⟨Θ, d.2, hsc, hgr, hΘ, ?_⟩, rfl⟩)⟩
    change p.scheme.rows.E Θ d = extVisibilityReplace (p.scheme.rows.E Θ d) K (finitePart ν)
    rw [hν, extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt hfp, decomposition]
  have hrow (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) (hd : p.label d.1 = ⊤) :
      p.scheme.rows.E Θ d = ⊤ ∨ ∃ ν, p.scheme.rows.E Θ d = ofOrd ν := by
    rcases ExtOrd.cases (p.scheme.rows.E Θ d) with hb | ht | ⟨ν, hν⟩
    · exact absurd hb (row_ne_bot_of_label_top p hΘ d hd)
    · exact Or.inl ht
    · exact Or.inr ⟨ν, hν⟩
  by_cases hex : ∃ (d₀ : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) (ν₀ : Ordinal.{0}),
      p.label d₀.1 = ⊤ ∧ ¬ p.ProvisionalCap d₀.1 ∧ p.scheme.rows.E Θ d₀ = ofOrd ν₀
  · obtain ⟨d₀, ν₀, hd₀, hc₀, hν₀⟩ := hex
    refine ⟨limitPart ν₀, limitPart_limitPart ν₀, fun d hd => ?_⟩
    rcases hrow d hd with ht | ⟨ν, hν⟩
    · rw [ht, bandMap_top]
      exact ⟨le_top, hcapval d hd ⟨Θ, d.2, d, hsc, hgr, hΘ, hd, by
        change extVisibilityReplace (p.scheme.rows.E Θ d) K K ≤ p.scheme.rows.E Θ d
        rw [ht]; exact le_top⟩⟩
    · rw [hν]
      by_cases hc : p.ProvisionalCap d.1
      · obtain ⟨Sg₁, h1, h2⟩ := hc.transport d.2 hsc hgr hΘ
        have hge := CapAt.row_ge hsc hgr hΘ hd₀ hc₀ hν₀ ν d hd hν ⟨Sg₁, h1, h2⟩
        exact ⟨ofOrd_le_ofOrd.mpr ((le_add_of_nonneg_right zero_le).trans hge),
          bandMap_ofOrd_of_cap hge ▸ hcapval d hd hc⟩
      · obtain ⟨hfp, hval⟩ := hbandval d ν hd hc hν
        obtain ⟨-, -, hlp⟩ := limitPart_eq_of_not_cap hsc hgr hΘ hd hd₀ hc hc₀ hν hν₀
        have hlν : limitPart ν₀ ≤ ν := hlp ▸ limitPart_le ν
        have hlt : ν < limitPart ν₀ + K := hlp ▸ (decomposition ν).symm.trans_lt
          ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hfp))
        exact ⟨ofOrd_le_ofOrd.mpr hlν, bandMap_ofOrd_of_band hlν hlt ▸ hval⟩
  · push Not at hex
    refine ⟨0, by simp [limitPart], fun d hd => ?_⟩
    have hc : p.ProvisionalCap d.1 := by
      rcases hrow d hd with ht | ⟨ν, hν⟩
      · exact ⟨Θ, d.2, d, hsc, hgr, hΘ, hd, by
          change extVisibilityReplace (p.scheme.rows.E Θ d) K K ≤ p.scheme.rows.E Θ d
          rw [ht]; exact le_top⟩
      · exact by_contra fun hnc => hex d ν hd hnc hν
    rcases hrow d hd with ht | ⟨ν, hν⟩
    · rw [ht, bandMap_top]; exact ⟨le_top, hcapval d hd hc⟩
    · rw [hν]
      obtain ⟨Sg₁, h1, h2⟩ := hc.transport d.2 hsc hgr hΘ
      have hK : (0 : Ordinal.{0}) + K ≤ ν := by
        rw [zero_add]
        rcases ExtOrd.cases (p.scheme.rows.E Θ Sg₁) with hb | ht | ⟨μ, hμ⟩
        · exact absurd hb (row_ne_bot_of_label_top p hΘ Sg₁ h1)
        · change extVisibilityReplace _ K K ≤ p.scheme.rows.E Θ d at h2
          rw [ht, extVisibilityReplace_top, hν] at h2; exact absurd h2 (not_le.mpr (ofOrd_lt_top _))
        · change extVisibilityReplace (p.scheme.rows.E Θ Sg₁) K K ≤ p.scheme.rows.E Θ d at h2
          rw [hμ, hν, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at h2
          refine le_trans ?_ h2
          unfold visibilityReplace ordinalReplace; split_ifs with hfp
          · exact le_add_of_nonneg_left zero_le
          · exact ((Nat.cast_le.mpr (not_lt.mp hfp)).trans (le_add_of_nonneg_left zero_le)).trans_eq
              (decomposition μ)
      exact ⟨ofOrd_le_ofOrd.mpr zero_le, bandMap_ofOrd_of_cap hK ▸ hcapval d hd hc⟩

theorem topController_locality_provisional (p : S α n) (hα : Order.IsSuccLimit α)
    {Sg : Cell p.scheme.scheme} (hSg : p.label Sg = ⊤) :
    TransformsTo (fun d : p.scheme.scheme.below (p.scheme.scheme.cell Sg) =>
        p.scheme.scheme.grade d.1)
      (p.scheme.rows.E Sg)
      (fun d => min (p.someProvisionalValue d.1) (p.someProvisionalValue Sg)) := by
  obtain ⟨Θ, hSgΘ, hsc, hgr, hΘ⟩ := exists_top_witness hSg
  obtain ⟨g, σ, hganti, _, hσbot, hσmono, hσ5, heq⟩ := p.respects.locality Sg
  obtain ⟨g₁, σ₁, hg₁anti, hg₁self, _, hσ₁mono, hσ₁5, heq₁⟩ :=
    (p.scheme.consistent Θ).locality ⟨Sg, hSgΘ⟩
  obtain ⟨lam, hlam, hbridge⟩ := exists_bandBridge p hsc hgr hΘ
  have heq' (d : p.scheme.scheme.below (p.scheme.scheme.cell Sg)) :
      p.label d.1 = min (σ (p.scheme.rows.E Sg d)) (g (p.scheme.scheme.grade d.1)) := by
    have := heq d
    change min (p.label d.1) (p.label Sg) = _ at this
    rwa [hSg, min_top_right] at this
  have hgJ (k) (hk : k ≤ p.scheme.scheme.grade Sg) : g k = ⊤ := by
    have hSg' := heq' ⟨Sg, GradedLe.refl _⟩
    change p.label Sg = _ at hSg'; rw [hSg] at hSg'
    have hgtop : g (p.scheme.scheme.grade Sg) = ⊤ := top_le_iff.mp (hSg'.le.trans (min_le_right _ _))
    rcases hk.lt_or_eq with hlt | rfl; exact top_le_iff.mp (hgtop ▸ hganti _ _ hlt); exact hgtop
  obtain ⟨hlSg, hvalSg⟩ := hbridge ⟨Sg, hSgΘ⟩ hSg
  have hpSg : p.someProvisionalValue Sg =
      bandMap α lam p.topGrade (p.scheme.rows.E Θ ⟨Sg, hSgΘ⟩) := (isProvisionalValue_iff.mp hvalSg).symm
  have hpSgα : ofOrd α ≤ p.someProvisionalValue Sg := by
    rw [hpSg]; exact le_bandMap_of_ne_bot α lam p.topGrade fun hb =>
      not_le.mpr (bot_lt_ofOrd _) (hb ▸ hlSg)
  refine TransformsTo.merge_bandMap (q := fun d => p.label d.1)
    (r := fun d => min (p.scheme.rows.E Θ (CellScheme.below.incl ⟨Sg, hSgΘ⟩ d))
      (p.scheme.rows.E Θ ⟨Sg, hSgΘ⟩))
    g σ hσbot hσmono hσ5 heq' g₁ σ₁ hg₁anti hg₁self hσ₁mono hσ₁5 heq₁ hα hlam
    p.topGrade (p.scheme.scheme.grade Sg) (grade_le_topGrade_of_top hSg)
    (fun d => d.2.2) hgJ (fun d => p.label_bound d.1)
    (fun d hd => by rw [someProvisionalValue_of_ne_top hd.ne_top]; exact min_eq_left (hd.le.trans hpSgα))
    fun d hd => by
      obtain ⟨hle, hval⟩ := hbridge (CellScheme.below.incl ⟨Sg, hSgΘ⟩ d) hd
      have hpd : p.someProvisionalValue d.1 =
          bandMap α lam p.topGrade (p.scheme.rows.E Θ (CellScheme.below.incl ⟨Sg, hSgΘ⟩ d)) :=
        (isProvisionalValue_iff.mp hval).symm
      refine ⟨le_min hle hlSg, ?_⟩
      rw [hpd, hpSg, bandMap_min hlam p.topGrade hle hlSg]

theorem someProvisionalValue_lt_add_omega (p : S α n) (Xi : Cell p.scheme.scheme) :
    p.someProvisionalValue Xi < ofOrd (α + Ordinal.omega0) :=
  (p.someProvisionalValue_le Xi).trans_lt
    (ofOrd_lt_ofOrd.mpr ((add_lt_add_iff_left α).mpr (Ordinal.natCast_lt_omega0 p.topGrade)))

theorem le_someProvisionalValue_of_top {p : S α n} {Xi : Cell p.scheme.scheme}
    (htop : p.label Xi = ⊤) : ofOrd α ≤ p.someProvisionalValue Xi := by
  by_cases hcap : p.ProvisionalCap Xi
  · rw [someProvisionalValue_of_cap htop hcap]; exact ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)
  · obtain ⟨i, -, -, hval⟩ := someProvisionalValue_of_band htop hcap
    rw [hval]; exact ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)

theorem provisionalLift_respects (p : S α n) (hα : Order.IsSuccLimit α) :
    RespectsSemantics p.scheme.rows p.someProvisionalValue where
  orderly Xi := by
    by_cases htop : p.label Xi = ⊤
    · by_cases hcap : p.ProvisionalCap Xi
      · rw [someProvisionalValue_of_cap htop hcap, extVisibilityReplace_ofOrd]
        exact congrArg ofOrd ((visibilityReplace_self_iff _ _).mpr
          (by rw [finitePart_succLimit_add_nat hα]; exact grade_le_topGrade_of_top htop)).symm
      · obtain ⟨i, ⟨Theta, hXi, hscope, htopGrade, hThetaTop, heq⟩, _, hval⟩ :=
          someProvisionalValue_of_band htop hcap
        have hrowOrder := p.scheme.rows.orderly Theta ⟨Xi, hXi⟩
        rcases p.scheme.rows_coded Theta ⟨Xi, hXi⟩ with hbot | ⟨a, j, _, hrow⟩
        · exact absurd hbot (row_ne_bot_of_label_top p hThetaTop ⟨Xi, hXi⟩ htop)
        · rw [hrow, extVisibilityReplace_ofOrd, ofOrd_inj] at hrowOrder
          have hgradeFp := (visibilityReplace_self_iff _ _).mp hrowOrder.symm
          have hfpTop : finitePart (Ordinal.omega0 * a + j) < p.topGrade := by_contra fun hge =>
            hcap ⟨Theta, hXi, ⟨Xi, hXi⟩, hscope, htopGrade, hThetaTop, htop, by
              rw [hrow, extVisibilityReplace_ofOrd]
              exact le_of_eq (congrArg ofOrd ((visibilityReplace_self_iff _ _).mpr (not_lt.mp hge)))⟩
          rw [hrow, extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt hfpTop, ofOrd_inj] at heq
          have hfpEq : finitePart (Ordinal.omega0 * a + j) = i :=
            (congrArg finitePart heq).trans (finitePart_limitPart_add_nat _ _)
          rw [hval, extVisibilityReplace_ofOrd]
          exact congrArg ofOrd ((visibilityReplace_self_iff _ _).mpr
            (by rwa [finitePart_succLimit_add_nat hα, ← hfpEq])).symm
    · rw [someProvisionalValue_of_ne_top htop]; exact p.respects.orderly Xi
  locality Sig := by
    by_cases htop : p.label Sig = ⊤
    · exact topController_locality_provisional p hα htop
    · have hlt := (p.label_bound Sig).resolve_right htop
      have hfun : (fun d : p.scheme.scheme.below (p.scheme.scheme.cell Sig) =>
          min (p.someProvisionalValue d.1) (p.someProvisionalValue Sig)) =
          fun d => min (p.label d.1) (p.label Sig) := by
        funext d; rw [someProvisionalValue_of_ne_top htop]
        by_cases hd : p.label d.1 = ⊤
        · rw [hd, min_top_left, min_eq_right (hlt.le.trans (le_someProvisionalValue_of_top hd))]
        · rw [someProvisionalValue_of_ne_top hd]
      rw [hfun]; exact p.respects.locality Sig
  availability Sig Xi₀ hsub hgrade := by
    by_cases htop : p.label Sig = ⊤
    · obtain ⟨Θ, hSgΘ, hsc, hgr, hΘ⟩ := exists_top_witness htop
      have hXi₀Θ : GradedLe (p.scheme.scheme.cell Xi₀) (p.scheme.scheme.cell Θ) :=
        ⟨by change p.scheme.scheme.scope Xi₀ ⊆ p.scheme.scheme.scope Θ; rw [hsc]; exact Finset.subset_univ _,
         by change p.scheme.scheme.grade Xi₀ ≤ p.scheme.scheme.grade Θ; rw [← hgrade]; exact hSgΘ.2⟩
      obtain ⟨Xi, hcell, hle⟩ :=
        (p.scheme.consistent Θ).availability ⟨Sig, hSgΘ⟩ ⟨Xi₀, hXi₀Θ⟩ hsub hgrade
      obtain ⟨g, σ, hganti, _, _, hσmono, _, heq⟩ := p.respects.locality Θ
      have hlabel (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) :
          p.label d.1 = σ (p.scheme.rows.E Θ d) := by
        have hd := heq d; change min (p.label d.1) (p.label Θ) = _ at hd
        rw [hΘ, min_top_right] at hd
        have hΘ' := heq ⟨Θ, GradedLe.refl _⟩
        change min (p.label Θ) (p.label Θ) = min (σ _) (g (p.scheme.scheme.grade Θ)) at hΘ'
        rw [min_self, hΘ, hgr] at hΘ'
        have hgKtop : g p.topGrade = ⊤ := top_le_iff.mp (hΘ'.le.trans (min_le_right _ _))
        have hk : p.scheme.scheme.grade d.1 ≤ p.topGrade := hgr ▸ d.2.2
        have hgk : g (p.scheme.scheme.grade d.1) = ⊤ := by
          rcases hk.lt_or_eq with hlt | heq0
          · exact top_le_iff.mp (hgKtop ▸ hganti _ _ hlt)
          · rwa [heq0]
        rw [hd, hgk, min_top_right]
      have hXitop : p.label Xi.1 = ⊤ :=
        top_le_iff.mp ((htop ▸ hlabel ⟨Sig, hSgΘ⟩).le.trans ((hσmono hle).trans (hlabel Xi).symm.le))
      obtain ⟨lam, hlam, hbridge⟩ := exists_bandBridge p hsc hgr hΘ
      obtain ⟨hlSg, hvalSg⟩ := hbridge ⟨Sig, hSgΘ⟩ htop
      obtain ⟨_, hvalXi⟩ := hbridge Xi hXitop
      refine ⟨Xi.1, hcell, ?_⟩
      rw [← isProvisionalValue_iff.mp hvalSg, ← isProvisionalValue_iff.mp hvalXi]
      exact bandMap_mono_of_le hlam p.topGrade hlSg hle
    · obtain ⟨Xi, hcell, hle⟩ := p.respects.availability Sig Xi₀ hsub hgrade
      refine ⟨Xi, hcell, ?_⟩
      rw [someProvisionalValue_of_ne_top htop]
      by_cases hX : p.label Xi = ⊤
      · exact (((p.label_bound Sig).resolve_right htop).le).trans (le_someProvisionalValue_of_top hX)
      · rwa [someProvisionalValue_of_ne_top hX]

noncomputable def provisionalLift (p : S α n) (hα : Order.IsSuccLimit α) :
    S (α + Ordinal.omega0) n where
  scheme := p.scheme
  label := p.someProvisionalValue
  label_bound Xi := Or.inl (p.someProvisionalValue_lt_add_omega Xi)
  respects := provisionalLift_respects p hα

theorem truncExt_someProvisionalValue (p : S α n) (Xi : Cell p.scheme.scheme) :
    truncExt α (p.someProvisionalValue Xi) = p.label Xi := by
  by_cases htop : p.label Xi = ⊤
  · rw [htop]
    by_cases hcap : p.ProvisionalCap Xi
    · rw [someProvisionalValue_of_cap htop hcap]
      exact truncExt_ofOrd_of_le (le_add_of_nonneg_right zero_le)
    · obtain ⟨i, -, -, hval⟩ := someProvisionalValue_of_band htop hcap
      rw [hval]; exact truncExt_ofOrd_of_le (le_add_of_nonneg_right zero_le)
  · rw [someProvisionalValue_of_ne_top htop]
    exact truncExt_id_of_lt ((p.label_bound Xi).resolve_right htop)

theorem provisional_reduct_le_label (hα : Order.IsSuccLimit α) (hαβ : α ≤ β)
    (q : S β n) (d : Cell q.scheme.scheme) :
    (reduceType hα hαβ q).someProvisionalValue d ≤ q.label d := by
  let p := reduceType hα hαβ q
  by_cases htop : p.label d = ⊤
  · by_cases hlarge : ofOrd (α + p.topGrade) ≤ q.label d
    · exact (someProvisionalValue_le _ _).trans hlarge
    · have hge : ofOrd α ≤ q.label d := truncExt_eq_top_iff.mp htop
      obtain ⟨i, hi⟩ := exists_nat_of_mem_band hge
        ((lt_of_not_ge hlarge).trans (ofOrd_lt_ofOrd.mpr
          ((add_lt_add_iff_left α).mpr (Ordinal.natCast_lt_omega0 p.topGrade))))
      have hiK : i < p.topGrade := by
        have h := lt_of_not_ge hlarge
        rw [hi, ofOrd_lt_ofOrd, add_lt_add_iff_left] at h; exact_mod_cast h
      exact (hi.trans (isProvisionalValue_iff.mp
        (isProvisionalValue_band_of_expansion hα hαβ d hi hiK))).ge
  · have hlt : q.label d < ofOrd α := lt_of_not_ge fun h => htop (truncExt_eq_top_of_ge h)
    rw [someProvisionalValue_of_ne_top htop]; exact (truncExt_id_of_lt hlt).le

theorem provisional_le_of_lawful_lift (p : S α n) (hα : Order.IsSuccLimit α)
    (hαβ : α ≤ β) (v : Cell p.scheme.scheme → ExtOrd)
    (hbound : ∀ d, v d < ofOrd β ∨ v d = ⊤)
    (hlawful : RespectsSemantics p.scheme.rows v)
    (hreduce : ∀ d, truncExt α (v d) = p.label d) (d : Cell p.scheme.scheme) :
    p.someProvisionalValue d ≤ v d := by
  let q : S β n := ⟨p.scheme, v, hbound, hlawful⟩
  have hred : reduceType hα hαβ q = p := StageType.ext rfl (heq_of_eq (funext hreduce))
  have he : (reduceType hα hαβ q).someProvisionalValue = p.someProvisionalValue :=
    eq_of_heq (congr_arg_heq (fun t : S α n => t.someProvisionalValue) hred)
  simpa only [he] using provisional_reduct_le_label hα hαβ q d

theorem provisional_le_mapCell_of_least {m : ℕ} {p : S α m} {q : S α n}
    {f : Fin m ↪ Fin n} (hα : Order.IsSuccLimit α) (hf : typeMap f q = some p)
    (d : Cell p.scheme.scheme) :
    p.someProvisionalValue d ≤ q.someProvisionalValue (mapCell hf d) := by
  obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
    ⟨visible_of_typeMap_eq_some hf, restrictFace_eq_of_typeMap_eq_some hf⟩
  exact provisional_le_of_lawful_lift (q.restrictFace f hr) hα
    (le_add_of_nonneg_right zero_le) _
    (fun _ => Or.inl (q.someProvisionalValue_lt_add_omega _))
    ((q.provisionalLift hα).restrictFace f hr).respects
    (fun _ => q.truncExt_someProvisionalValue _) d
end StageType

namespace KnightRealization
open StageType
variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

theorem LabelledExt.emb_unique {x y : R.LabelledExt} {f f' : Fin x.arity ↪ Fin y.arity}
    (hf : f.trans y.tuple = x.tuple) (hf' : f'.trans y.tuple = x.tuple) : f = f' :=
  Function.Embedding.ext fun i => y.tuple.injective
    ((DFunLike.congr_fun hf i).trans (DFunLike.congr_fun hf' i).symm)

theorem StabilizesTo.provisional_le (hcons : R.IsExactParentConsistent)
    {n m : ℕ} {t : Fin n ↪ M} {p : S α.1 n} {u : Fin m ↪ M} {q : S α.1 m}
    (hu : R.eval u = some q) {f : Fin n ↪ Fin m} (hf : f.trans u = t)
    (hpq : typeMap f q = some p) {d : Cell p.scheme.scheme} {v γ : ExtOrd}
    (hv : q.IsProvisionalValue (mapCell hpq d) v) (hγ : R.StabilizesTo t p d γ) : v ≤ γ := by
  obtain ⟨k, z, g, e, r, hpr, hz, hgz, hez, hγz⟩ := hγ u
  have hqr : typeMap g r = some q := by
    have h := hcons z r g hz; rw [hgz, hu] at h; exact h.symm
  have hfg : (f.trans g).trans z = t := by rw [Function.Embedding.trans_assoc, hgz, hf]
  obtain rfl : e = f.trans g := Function.Embedding.ext fun i =>
    z.injective ((DFunLike.congr_fun hez i).trans (DFunLike.congr_fun hfg i).symm)
  have hγz' : r.IsProvisionalValue (mapCell hqr (mapCell hpq d)) γ := by
    rw [← mapCell_trans hqr hpq hpr d]; exact hγz
  exact (isProvisionalValue_iff.mp hv).trans_le
    ((provisional_le_mapCell_of_least α.2 hqr (mapCell hpq d)).trans_eq
      (isProvisionalValue_iff.mp hγz').symm)

theorem StabilizesTo.unique_of_consistent (hcons : R.IsExactParentConsistent)
    {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n} {d : Cell p.scheme.scheme} {γ γ' : ExtOrd}
    (h : R.StabilizesTo t p d γ) (h' : R.StabilizesTo t p d γ') : γ = γ' :=
  le_antisymm
    (let ⟨_, _, _, _, _, hpq, hu, _, hf, hv⟩ := h t; StabilizesTo.provisional_le hcons hu hf hpq hv h')
    (let ⟨_, _, _, _, _, hpq, hu, _, hf, hv⟩ := h' t; StabilizesTo.provisional_le hcons hu hf hpq hv h)

theorem HasStableValue.unique_of_consistent (hcons : R.IsExactParentConsistent)
    {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n} {d : Cell p.scheme.scheme} {γ γ' : ExtOrd}
    (h : R.HasStableValue t p d γ) (h' : R.HasStableValue t p d γ') : γ = γ' := by
  rcases h with ⟨hlt, hs⟩ | ⟨rfl, hno⟩ <;> rcases h' with ⟨hlt', hs'⟩ | ⟨rfl, hno'⟩
  · exact StabilizesTo.unique_of_consistent hcons @hs @hs'
  · exact absurd @hs (hno' γ hlt)
  · exact absurd @hs' (hno γ' hlt')
  · rfl

set_option linter.unusedVariables false in
theorem HasStableValue.unique (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} {γ γ' : ExtOrd}
    (h : R.HasStableValue t p Xi γ) (h' : R.HasStableValue t p Xi γ') : γ = γ' :=
  HasStableValue.unique_of_consistent hcons h h'

end KnightRealization
end VaughtConjecture.Knight
