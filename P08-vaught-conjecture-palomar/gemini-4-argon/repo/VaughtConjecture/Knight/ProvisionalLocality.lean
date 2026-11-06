/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProvisionalBandBridge

/-! # Locality of the provisional labelling at every top-labelled controller

Lemma 5.3.5 at an arbitrary `∞`-cell `Σ`: `E(Σ) ⇒ min (p⁺, p⁺(Σ))`.  At a maximal top witness
`Θ` the provisional value is the band map of `E(Θ)` (`ProvisionalBandBridge`); at a controller
`Σ ≠ Θ` the target `min (p⁺ d) (p⁺ Σ)` is the band map of `min (E(Θ)(d)) (E(Θ)(Σ))` on the
`∞`-cells — a function of the row of `Θ`, **not** of the row of `Σ` (row consistency
`E(Σ) ⇒ E(Θ)↾` may collapse band indices above the grade of `Σ`, so `p⁺` is not a band map of
`E(Σ)` and `TransformsTo.comp_bandMap` does not apply) — while on the finite cells it is the
label, reached from `E(Σ)` by the locality witness of the labels.

## The two-witness splice

`TransformsTo.merge_bandMap` composes the two: the label witness `⟨g, σ⟩ : E(Σ) ⇒ p↾` on the
region `σ < α`, and the band map of the row-consistency witness
`⟨g₁, σ₁⟩ : E(Σ) ⇒ min (E(Θ)↾, E(Θ)(Σ))` on the region `σ ≥ α`; the suppressor is `⊥` above
`J = grade Σ`, where `g = ⊤` keeps clause 5 honest exactly as in `comp_bandMap` (which is the
instance `σ₁ = id`, `g₁ = ⊤`).  This is not a general composite (Lemma 2.3.14 remains blocked,
#89/NC): both regions carry explicit hypotheses, and the cut between them is a constant below
`α`.

## The cap argument

Visibility replacement is **not** monotone in the value: `⊔⁺_k i a < a` when `i < fp a < k`.
So in the band region with `g₁ k < σ₁ a` (both at cap level, forced by injectivity of the band
map on the band, `cap_of_bandMap_eq_of_lt`) clause 5 cannot be read off monotonicity.
`cap_le_of_witness` instead reads clause 5 of `σ₁` at the *lowered* point `⊔⁺_k i a`, which
`⊔⁺_k (fp a)` sends back to `a`: were `σ₁ (⊔⁺_k i a)` below cap level, `σ₁ a` would be at most
`lam + K`, contradicting `g₁ k < σ₁ a`. -/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight

open Value ExtOrd

namespace Value

/-- An ordinal in the band `[lam, lam + K)` of a multiple `lam` of `ω` has limit part `lam`
and finite part `< K`. -/
theorem limitPart_eq_and_finitePart_lt_of_band {lam ν : Ordinal.{0}}
    (hlam : limitPart lam = lam) {K : ℕ} (h₁ : lam ≤ ν) (h₂ : ν < lam + K) :
    limitPart ν = lam ∧ finitePart ν < K := by
  have heq : limitPart ν = lam := by
    simpa [hlam] using limitPart_eq_of_le_of_lt (μ := lam) (by rwa [hlam]) (by rwa [hlam])
  refine ⟨heq, Nat.cast_lt.mp ((add_lt_add_iff_left lam).mp ?_)⟩
  rw [← heq, decomposition ν, heq]; exact h₂

/-- Visibility replacement does not drop below a multiple of `ω` that bounds the input. -/
theorem le_visibilityReplace_of_le_of_limitPart_eq {lam ν : Ordinal.{0}}
    (hlam : limitPart lam = lam) (hν : lam ≤ ν) (k i : ℕ) : lam ≤ visibilityReplace ν k i := by
  unfold visibilityReplace ordinalReplace
  split_ifs
  · exact (hlam ▸ limitPart_mono hν).trans (le_add_of_nonneg_right zero_le)
  · exact hν

/-- Replacing the finite part downwards (`i < fp ν < k`) is undone by replacing it back. -/
theorem visibilityReplace_visibilityReplace_finitePart {ν : Ordinal.{0}} {k i : ℕ}
    (hfp : finitePart ν < k) (hi : i < k) :
    visibilityReplace (visibilityReplace ν k i) k (finitePart ν) = ν := by
  rw [visibilityReplace_of_finitePart_lt hfp, visibilityReplace_of_finitePart_lt
    (by rw [finitePart_limitPart_add_nat]; exact hi), limitPart_limitPart_add_nat, decomposition]

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
  · exact absurd hx (not_le.mpr (bot_lt_ofOrd _))
  · exact bandMap_top α lam K
  · exact bandMap_ofOrd_of_cap (ofOrd_le_ofOrd.mp hx)

/-- Two values at or above `lam`, strictly ordered, with the same band-map value, are both at
cap level (the band map is injective on the band `[lam, lam + K)`). -/
theorem cap_of_bandMap_eq_of_lt {α lam : Ordinal.{0}} (hlam : limitPart lam = lam) (K : ℕ)
    {x y : ExtOrd} (hx : ofOrd lam ≤ x) (hxy : x < y)
    (h : bandMap α lam K x = bandMap α lam K y) : ofOrd (lam + K) ≤ x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · exact absurd hx (not_le.mpr (bot_lt_ofOrd _))
  · exact le_top
  · by_contra hcap
    have hν : ν < lam + K := not_le.mp fun h' => hcap (ofOrd_le_ofOrd.mpr h')
    have hlν : lam ≤ ν := ofOrd_le_ofOrd.mp hx
    obtain ⟨hlimν, hfpν⟩ := limitPart_eq_and_finitePart_lt_of_band hlam hlν hν
    rw [bandMap_ofOrd_of_band hlν hν] at h
    rcases le_or_gt (ofOrd (lam + K)) y with hcapy | hy
    · rw [bandMap_of_cap_le hcapy, ofOrd_inj] at h
      have := Nat.cast_injective (R := Ordinal.{0}) (add_left_cancel h)
      omega
    · rcases ExtOrd.cases y with rfl | rfl | ⟨ρ, rfl⟩
      · exact absurd hxy (not_lt.mpr bot_le)
      · exact absurd hy (not_lt.mpr le_top)
      · have hνρ : ν < ρ := ofOrd_lt_ofOrd.mp hxy
        have hρ' : ρ < lam + K := ofOrd_lt_ofOrd.mp hy
        obtain ⟨hlimρ, _⟩ := limitPart_eq_and_finitePart_lt_of_band hlam (hlν.trans hνρ.le) hρ'
        rw [bandMap_ofOrd_of_band (hlν.trans hνρ.le) hρ', ofOrd_inj] at h
        have hfp := Nat.cast_injective (R := Ordinal.{0}) (add_left_cancel h)
        have h1 : ν = ρ := by rw [← decomposition ν, ← decomposition ρ, hlimν, hlimρ, hfp]
        exact h1.not_lt hνρ

end ExtOrd

open Transform in
/-- In a transform witness `⟨g₁, σ₁⟩`, a value `a` sent strictly above a cap-level threshold
`g₁ k ≥ lam + K` stays at cap level under every visibility replacement at `k`: if the
replacement lowers `a` (`i < fp a < k`), clause 5 of `σ₁` at the lowered point `⊔⁺_k i a`
(which `⊔⁺_k (fp a)` sends back to `a`) would otherwise pin `σ₁ a ≤ lam + K`. -/
theorem cap_le_of_witness {g₁ : ℕ → ExtOrd} {σ₁ : ExtOrd → ExtOrd} (hσ₁mono : Monotone σ₁)
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
    · rcases le_or_gt (finitePart ν) i with hi' | hi''
      · refine hcapa.trans (hσ₁mono (ofOrd_le_ofOrd.mpr ?_))
        rw [visibilityReplace_of_finitePart_lt hfp]
        conv_lhs => rw [← decomposition ν]
        exact add_le_add le_rfl (Nat.cast_le.mpr hi')
      · by_contra hcon
        have h5 := hσ₁5 _ k ((not_le.mp hcon).le.trans hcap) (finitePart ν) hfp.le
        rw [extVisibilityReplace_ofOrd,
          visibilityReplace_visibilityReplace_finitePart hfp (hi''.trans hfp)] at h5
        rw [h5] at hlt
        rcases ExtOrd.cases (σ₁ (ofOrd (visibilityReplace ν k i))) with hb' | ht' | ⟨ρ, hρ⟩
        · rw [hb', extVisibilityReplace_bot] at hlt
          exact not_le_of_gt (hcap.trans_lt hlt) bot_le
        · exact hcon (ht' ▸ le_top)
        · rw [hρ, extVisibilityReplace_ofOrd] at hlt
          exact not_le_of_gt (hcap.trans_lt hlt) (ofOrd_le_ofOrd.mpr
            (visibilityReplace_le_add_of_le_of_limitPart_eq hlam
              (ofOrd_lt_ofOrd.mp (hρ ▸ not_le.mp hcon)).le k (hfp.le.trans hk)))
    · rwa [visibilityReplace_of_not_lt hfp]

open Transform in
/-- **Two-witness band-map merge.**  On a finite cell family of grades `≤ J ≤ K`:
`⟨g, σ⟩ : p ⇒ q` with `g = ⊤` up to `J` and `q` valued below `α` or `⊤`; `⟨g₁, σ₁⟩ : p ⇒ r`
arbitrary; `q'` keeps `q` where `q < α` and is the band map of `r` (a value `≥ lam`) where
`q = ⊤`.  Then `p ⇒ q'`.  (`comp_bandMap` is the instance `r = p`.) -/
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
  have hαlam (x : ExtOrd) (hx : x ≠ ⊥) : ofOrd α ≤ bandMap α lam K x :=
    le_bandMap_of_ne_bot α lam K hx
  have hlam_ne_bot (x : ExtOrd) (hx : ofOrd lam ≤ x) : x ≠ ⊥ := fun hb =>
    not_lt_of_ge (hb ▸ hx) (bot_lt_ofOrd _)
  have hq (d) : q d = σ (p d) := by rw [heq d, hgJ _ (hgr d), min_top_right]
  let S : Ordinal.{0} :=
    Finset.univ.sup fun d => if σ (p d) < ofOrd α then ordOrZero (σ (p d)) else 0
  have hS : S < α := (Finset.sup_lt_iff hα0).mpr fun d _ => by
    split_ifs with hd
    · rcases ExtOrd.cases (σ (p d)) with hb | ht | ⟨ν, hν⟩
      · rw [hb, ordOrZero_bot]; exact hα0
      · exact absurd (ht ▸ hd) (not_lt.mpr le_top)
      · rw [hν, ordOrZero_ofOrd]; exact ofOrd_lt_ofOrd.mp (hν ▸ hd)
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
  have hc₁self (k) (hk : k ≤ K) : extVisibilityReplace (ofOrd c₁) k k = ofOrd c₁ := by
    rw [extVisibilityReplace_ofOrd, (visibilityReplace_self_iff c₁ k).mpr
      (by rw [finitePart_limitPart_add_nat' hμ K']; exact hk.trans hKK')]
  have hcrep (k i) (hk : k ≤ K) (_ : i ≤ k) : extVisibilityReplace (ofOrd c) k i = ofOrd c := by
    rw [extVisibilityReplace_ofOrd, visibilityReplace_of_not_lt
      (by rw [finitePart_limitPart_add_nat' hμ (K' + 1)]; exact not_lt.mpr ((hk.trans hKK').trans (Nat.le_succ _)))]
  have hSc₁ : S ≤ c₁ := by
    conv_lhs => rw [← decomposition S]
    exact add_le_add le_rfl (Nat.cast_le.mpr (le_max_right _ _))
  have hσc (d) (hd : σ (p d) < ofOrd α) : σ (p d) ≤ ofOrd c₁ := by
    have hxS : ordOrZero (σ (p d)) ≤ S := by
      simpa [hd] using Finset.le_sup
        (f := fun d => if σ (p d) < ofOrd α then ordOrZero (σ (p d)) else 0) (Finset.mem_univ d)
    rcases ExtOrd.cases (σ (p d)) with hb | ht | ⟨ν, hν⟩
    · rw [hb]; exact bot_le
    · exact absurd (ht ▸ hd) (not_lt.mpr le_top)
    · rw [hν, ordOrZero_ofOrd] at hxS; exact hν ▸ ofOrd_le_ofOrd.mpr (hxS.trans hSc₁)
  have hlowreg (a : ExtOrd) (k i : ℕ) (hk : k ≤ J) (hi : i ≤ k) (ha : σ a < ofOrd α) :
      σ (extVisibilityReplace a k i) = extVisibilityReplace (σ a) k i ∧
        σ (extVisibilityReplace a k i) < ofOrd α := by
    have h5 := hσ5 a k (by rw [hgJ k hk]; exact le_top) i hi
    refine ⟨h5, h5 ▸ ?_⟩
    rcases ExtOrd.cases (σ a) with hb | ht | ⟨ν, hν⟩
    · rw [hb, extVisibilityReplace_bot]; exact bot_lt_ofOrd _
    · exact absurd (ht ▸ ha) (not_lt.mpr le_top)
    · rw [hν] at ha ⊢
      exact ofOrd_lt_ofOrd.mpr (visibilityReplace_lt_of_lt hα (ofOrd_lt_ofOrd.mp ha) k i)
  have hhighreg (a : ExtOrd) (k i : ℕ) (hk : k ≤ J) (hi : i ≤ k) (ha : ¬ σ a < ofOrd α) :
      ¬ σ (extVisibilityReplace a k i) < ofOrd α := by
    rw [hσ5 a k (by rw [hgJ k hk]; exact le_top) i hi]
    rcases ExtOrd.cases (σ a) with hb | ht | ⟨ν, hν⟩
    · exact absurd (hb ▸ bot_lt_ofOrd α) ha
    · rw [ht, extVisibilityReplace_top]; exact not_lt.mpr le_top
    · rw [hν] at ha ⊢
      rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
      have hαν : α ≤ ν := not_lt.mp fun h => ha (ofOrd_lt_ofOrd.mpr h)
      unfold visibilityReplace ordinalReplace
      split_ifs
      · exact not_lt.mpr ((succLimit_le_limitPart hα hαν).trans (le_add_of_nonneg_right zero_le))
      · exact not_lt.mpr hαν
  let σ' : ExtOrd → ExtOrd := fun a =>
    if σ a < ofOrd α then min (σ a) (ofOrd c₁)
    else if σ₁ a < ofOrd lam then ofOrd c else bandMap α lam K (σ₁ a)
  let g' : ℕ → ExtOrd := fun k =>
    if k ≤ J then (if ofOrd lam ≤ g₁ k then bandMap α lam K (g₁ k) else ofOrd c₁) else ⊥
  have hσ'low (a) (ha : σ a < ofOrd α) : σ' a = min (σ a) (ofOrd c₁) := ite_eq_left ha
  have hσ'free (a) (ha : ¬ σ a < ofOrd α) (hl : σ₁ a < ofOrd lam) : σ' a = ofOrd c := by
    dsimp only [σ']; rw [ite_eq_right ha, ite_eq_left hl]
  have hσ'band (a) (ha : ¬ σ a < ofOrd α) (hl : ¬ σ₁ a < ofOrd lam) :
      σ' a = bandMap α lam K (σ₁ a) := by
    dsimp only [σ']; rw [ite_eq_right ha, ite_eq_right hl]
  have hσ'high_ge (a) (ha : ¬ σ a < ofOrd α) : ofOrd c ≤ σ' a := by
    by_cases hl : σ₁ a < ofOrd lam
    · rw [hσ'free a ha hl]
    · rw [hσ'band a ha hl]; exact hcα.le.trans (hαlam _ (hlam_ne_bot _ (not_lt.mp hl)))
  have hσ'low_le (a) (ha : σ a < ofOrd α) : σ' a ≤ ofOrd c₁ := by
    rw [hσ'low a ha]; exact min_le_right _ _
  have hg'high (k) (hk : k ≤ J) (hl : ofOrd lam ≤ g₁ k) : g' k = bandMap α lam K (g₁ k) := by
    dsimp only [g']; rw [ite_eq_left hk, ite_eq_left hl]
  have hg'low (k) (hk : k ≤ J) (hl : ¬ ofOrd lam ≤ g₁ k) : g' k = ofOrd c₁ := by
    dsimp only [g']; rw [ite_eq_left hk, ite_eq_right hl]
  have hg'top (k) (hk : J < k) : g' k = ⊥ := ite_eq_right (not_le.mpr hk)
  have hg'ge (k) (hk : k ≤ J) : ofOrd c₁ ≤ g' k := by
    by_cases hl : ofOrd lam ≤ g₁ k
    · rw [hg'high k hk hl]; exact hc₁α.le.trans (hαlam _ (hlam_ne_bot _ hl))
    · rw [hg'low k hk hl]
  have hforce (a k) (hk : k ≤ J) (ha : ¬ σ a < ofOrd α) (hle : σ' a ≤ g' k) :
      ofOrd lam ≤ g₁ k := by
    by_contra hl
    exact not_le_of_gt hc₁c' ((hσ'high_ge a ha).trans (hg'low k hk hl ▸ hle))
  refine ⟨g', σ', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k₁ k₂ hlt
    by_cases h2 : k₂ ≤ J
    · have h1 : k₁ ≤ J := hlt.le.trans h2
      by_cases hl2 : ofOrd lam ≤ g₁ k₂
      · rw [hg'high k₂ h2 hl2, hg'high k₁ h1 (hl2.trans (hg₁anti _ _ hlt))]
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
    · have hb : ¬ σ b < ofOrd α := fun hb => ha (lt_of_le_of_lt (hσmono hab) hb)
      by_cases hla : σ₁ a < ofOrd lam
      · rw [hσ'free a ha hla]; exact hσ'high_ge b hb
      · have hlb : ¬ σ₁ b < ofOrd lam := fun hlb => hla (lt_of_le_of_lt (hσ₁mono hab) hlb)
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
            · exact absurd (ht ▸ hla) (not_lt.mpr le_top)
            · rw [hν] at hla ⊢
              exact ofOrd_lt_ofOrd.mpr
                (visibilityReplace_lt_of_lt_of_limitPart_eq hlam (ofOrd_lt_ofOrd.mp hla) k i)
          rw [hσ'free _ hhi hla', hσ'free a ha hla, hcrep k i hkK hik]
        · rw [hσ'band a ha hla, hg'high k hk hgk] at hak
          have hla₀ : ofOrd lam ≤ σ₁ a := not_lt.mp hla
          rcases le_or_gt (σ₁ a) (g₁ k) with hle | hlt
          · have h5 := hσ₁5 a k hle i hik
            have hla' : ¬ σ₁ (extVisibilityReplace a k i) < ofOrd lam := by
              rw [h5]
              rcases ExtOrd.cases (σ₁ a) with hb | ht | ⟨ν, hν⟩
              · exact absurd (hb ▸ hla₀) (not_le.mpr (bot_lt_ofOrd _))
              · rw [ht, extVisibilityReplace_top]; exact not_lt.mpr le_top
              · rw [hν] at hla₀ ⊢
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
            rw [hσ'band _ hhi hla', hσ'band a ha hla, bandMap_of_cap_le hcapa',
              bandMap_of_cap_le hcapa, extVisibilityReplace_ofOrd, visibilityReplace_of_not_lt]
            rw [finitePart_limitPart_add_nat' (le_antisymm (limitPart_le α)
              (succLimit_le_limitPart hα le_rfl))]
            exact not_lt.mpr hkK
    · rw [hg'top k (not_le.mp hk)] at hak
      have hσ'a : σ' a = ⊥ := le_bot_iff.mp hak
      have ha : σ a < ofOrd α := by
        by_contra h
        exact not_le_of_gt (bot_lt_ofOrd c) (hσ'a ▸ hσ'high_ge a h)
      rw [hσ'low a ha] at hσ'a
      have hσab : σ a = ⊥ := by
        by_contra hne
        exact lt_irrefl _ (hσ'a ▸ lt_min (bot_lt_iff_ne_bot.mpr hne) (bot_lt_ofOrd c₁))
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
  obtain ⟨g, σ, hganti, _hgself, hσbot, hσmono, hσ5, heq⟩ := p.respects.locality Sg
  obtain ⟨g₁, σ₁, hg₁anti, hg₁self, _hσ₁bot, hσ₁mono, hσ₁5, heq₁⟩ :=
    (p.scheme.consistent Θ).locality ⟨Sg, hSgΘ⟩
  obtain ⟨lam, hlam, hbridge⟩ := exists_bandBridge p hsc hgr hΘ
  have heq' (d : p.scheme.scheme.below (p.scheme.scheme.cell Sg)) :
      p.label d.1 = min (σ (p.scheme.rows.E Sg d)) (g (p.scheme.scheme.grade d.1)) := by
    simpa [hSg] using heq d
  have hgJ (k) (hk : k ≤ p.scheme.scheme.grade Sg) : g k = ⊤ := by
    have hgtop : g (p.scheme.scheme.grade Sg) = ⊤ :=
      top_le_iff.mp ((hSg ▸ heq' ⟨Sg, GradedLe.refl _⟩).le.trans (min_le_right _ _))
    rcases hk.lt_or_eq with hlt | rfl
    · exact top_le_iff.mp (hgtop ▸ hganti _ _ hlt)
    · exact hgtop
  obtain ⟨hlSg, hvalSg⟩ := hbridge ⟨Sg, hSgΘ⟩ hSg
  have hpSg : p.someProvisionalValue Sg =
      bandMap α lam p.topGrade (p.scheme.rows.E Θ ⟨Sg, hSgΘ⟩) :=
    (isProvisionalValue_iff.mp hvalSg).symm
  have hpSgα : ofOrd α ≤ p.someProvisionalValue Sg := by
    rw [hpSg]
    exact le_bandMap_of_ne_bot α lam p.topGrade fun hb => not_lt_of_ge (hb ▸ hlSg) (bot_lt_ofOrd _)
  refine TransformsTo.merge_bandMap (q := fun d => p.label d.1)
    (r := fun d => min (p.scheme.rows.E Θ (CellScheme.below.incl ⟨Sg, hSgΘ⟩ d))
      (p.scheme.rows.E Θ ⟨Sg, hSgΘ⟩))
    g σ hσbot hσmono hσ5 heq' g₁ σ₁ hg₁anti hg₁self hσ₁mono hσ₁5 heq₁ hα hlam
    p.topGrade (p.scheme.scheme.grade Sg) (grade_le_topGrade_of_top hSg) (fun d => d.2.2) hgJ
    (fun d => p.label_bound d.1)
    (fun d hd => by rw [someProvisionalValue_of_ne_top hd.ne_top]; exact min_eq_left (hd.le.trans hpSgα))
    fun d hd => ?_
  obtain ⟨hle, hval⟩ := hbridge (CellScheme.below.incl ⟨Sg, hSgΘ⟩ d) hd
  have hpd : p.someProvisionalValue d.1 =
      bandMap α lam p.topGrade (p.scheme.rows.E Θ (CellScheme.below.incl ⟨Sg, hSgΘ⟩ d)) :=
    (isProvisionalValue_iff.mp hval).symm
  refine ⟨le_min hle hlSg, ?_⟩
  rw [hpd, hpSg, bandMap_min hlam p.topGrade hle hlSg]
