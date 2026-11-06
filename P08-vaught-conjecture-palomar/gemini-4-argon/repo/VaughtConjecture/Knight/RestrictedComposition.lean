/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteBandReadback
public import VaughtConjecture.Knight.SuccLimitBandArithmetic
public import VaughtConjecture.Knight.NormalForm

/-! # Restricted composition: post-composition with threshold and band maps preserves `⇒`

The faithful `⇒` of Def. 2.3.9 is not generally transitive, as proved by
`SharpWitnessCompositionControls.not_transitive`. The provisional-lift route needs only
two special post-compositions, both proved
here without any general composite: the **threshold** (jump) map, which Lemma 5.3.10's `∞`
case needs, and the **band map**, which Lemma 5.3.5 needs.  In both, clause 5 is only demanded
at grades `≤ K`, where `σ`'s own clause 5 at the band mate keeps the composite honest; above
`K` the suppressor is kept below `α` (or `⊥`), where the outer map is the identity.

## The threshold map

`jump τ` is the identity at or below `τ` and `⊤`
above.  If `⟨g, σ⟩ : p ⇒ q` and every cell of grade `> K` has target `< α`, then
`p ⇒ jump (α + K) ∘ q`, with witnesses `jump ∘ σ` and a suppressor that is `jump ∘ g` up to
grade `K` and a sub-`α` self-visible bound beyond.  The clause-5 obstruction of general
transitivity does not arise: at grades `≤ K`, monotonicity and `σ`'s own clause 5 at the band
mate force `σ a ≤ τ` whenever `σ (a ⊔⁺_k i) ≤ τ`; at grades `> K` the suppressor keeps
everything below `α`, where the map is the identity. -/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight

open Value ExtOrd

namespace ExtOrd

/-- The threshold map: identity at or below `τ`, `⊤` above. -/
def jump (τ x : ExtOrd) : ExtOrd := if x ≤ τ then x else ⊤

theorem jump_of_le {τ x : ExtOrd} (h : x ≤ τ) : jump τ x = x := by
  unfold jump; rw [ite_eq_left h]

theorem jump_of_not_le {τ x : ExtOrd} (h : ¬ x ≤ τ) : jump τ x = ⊤ := by
  unfold jump; rw [ite_eq_right h]

theorem le_jump (τ x : ExtOrd) : x ≤ jump τ x := by
  unfold jump; split_ifs <;> simp

theorem jump_mono (τ : ExtOrd) : Monotone (jump τ) := by
  intro x y hxy
  by_cases hy : y ≤ τ
  · rw [jump_of_le (hxy.trans hy), jump_of_le hy]; exact hxy
  · rw [jump_of_not_le hy]; exact le_top

theorem jump_min (τ x y : ExtOrd) : jump τ (min x y) = min (jump τ x) (jump τ y) :=
  (jump_mono τ).map_min

@[simp] theorem jump_bot (τ : ExtOrd) : jump τ ⊥ = ⊥ := jump_of_le bot_le

open Classical in
/-- The sub-`α` part of a value (`0` for `⊥`, `⊤`, or values `≥ α`). -/
def ordOrZero (x : ExtOrd) : Ordinal.{0} :=
  if h : ∃ μ : Ordinal.{0}, x = ofOrd μ then h.choose else 0

theorem ordOrZero_bot : ordOrZero ⊥ = 0 := by
  unfold ordOrZero
  rw [dite_eq_right]
  rintro ⟨μ, hμ⟩
  exact ofOrd_ne_bot μ hμ.symm

theorem ordOrZero_ofOrd (μ : Ordinal.{0}) : ordOrZero (ofOrd μ) = μ := by
  unfold ordOrZero
  have h : ∃ μ' : Ordinal.{0}, ofOrd μ = ofOrd μ' := ⟨μ, rfl⟩
  rw [dite_eq_left h]
  exact (ofOrd_inj.mp h.choose_spec).symm

private theorem ordOrZero_lt_of_lt {α : Ordinal.{0}} (hα0 : 0 < α) (x : ExtOrd) :
    (if x < ofOrd α then ordOrZero x else 0) < α := by
  split_ifs with h
  · rcases ExtOrd.cases x with rfl | rfl | ⟨μ, rfl⟩
    · rwa [ordOrZero_bot]
    · exact absurd h (not_lt.mpr le_top)
    · rw [ordOrZero_ofOrd]; exact ofOrd_lt_ofOrd.mp h
  · exact hα0

private theorem le_ofOrd_of_ordOrZero_le {α c : Ordinal.{0}} {x : ExtOrd} (hx : x < ofOrd α)
    (hc : (if x < ofOrd α then ordOrZero x else 0) ≤ c) : x ≤ ofOrd c := by
  rw [ite_eq_left hx] at hc
  rcases ExtOrd.cases x with rfl | rfl | ⟨μ, rfl⟩
  · exact bot_le
  · exact absurd hx (not_lt.mpr le_top)
  · rw [ordOrZero_ofOrd] at hc; exact ofOrd_le_ofOrd.mpr hc

end ExtOrd

/-! ### Band arithmetic for the threshold -/

namespace Value

/-- Below a limit, band replacement stays below the limit. -/
theorem visibilityReplace_lt_of_lt {α μ : Ordinal.{0}} (hα : Order.IsSuccLimit α) (hμ : μ < α)
    (k i : ℕ) : visibilityReplace μ k i < α := by
  unfold visibilityReplace ordinalReplace
  split_ifs
  · exact ((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 i)).trans_le
      (add_omega0_le_of_lt_isSuccLimit hα ((limitPart_le μ).trans_lt hμ))
  · exact hμ

theorem visibilityReplace_of_not_lt {μ : Ordinal.{0}} {k i : ℕ} (h : ¬ finitePart μ < k) :
    visibilityReplace μ k i = μ := by
  unfold visibilityReplace ordinalReplace
  rw [ite_eq_right h]

/-- Below `α + K`, band replacement at threshold `k ≤ K` with `i ≤ K` stays below `α + K`. -/
theorem visibilityReplace_le_add_of_le {α μ : Ordinal.{0}} (hα : Order.IsSuccLimit α) {K i : ℕ}
    (hμ : μ ≤ α + K) (k : ℕ) (hi : i ≤ K) : visibilityReplace μ k i ≤ α + K := by
  unfold visibilityReplace ordinalReplace
  split_ifs with h
  · have hlp : limitPart μ ≤ α := by
      rcases lt_or_ge μ α with hlt | hge
      · exact (limitPart_le μ).trans hlt.le
      · have hlt : μ < α + (K + 1 : ℕ) := by
          push_cast
          exact hμ.trans_lt ((add_lt_add_iff_left α).mpr (lt_add_one _))
        have := limitPart_eq_of_le_of_lt (μ := α) (z := μ)
          (by rw [limitPart_of_succLimit hα]; exact hge)
          (by rw [limitPart_of_succLimit hα]; exact hlt)
        rw [this, limitPart_of_succLimit hα]
    exact add_le_add hlp (Nat.cast_le.mpr hi)
  · exact hμ

end Value

open Transform in
/-- **Threshold composition**: if `⟨g, σ⟩ : p ⇒ q` and every cell of grade `> K` has target
`< α`, then `p ⇒ jump (α + K) ∘ q`. -/
theorem TransformsTo.comp_jump {D : Type*} [Finite D] {grade : D → ℕ} {p q : D → ExtOrd}
    (h : TransformsTo grade p q) {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) (K n : ℕ)
    (hK_le_n : K ≤ n) (hn : ∀ d, grade d ≤ n) (hK : ∀ d, K < grade d → q d < ofOrd α) :
    TransformsTo grade p (fun d => jump (ofOrd (α + K)) (q d)) := by
  classical
  have := Fintype.ofFinite D
  obtain ⟨g, σ, hganti, hgself, hσbot, hσmono, hσ5, heq⟩ := h
  set τ : ExtOrd := ofOrd (α + K) with hτ
  have hα0 : (0 : Ordinal.{0}) < α := hα.pos
  have hατ : ofOrd α ≤ τ := ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)
  let S : Ordinal.{0} :=
    (Finset.univ.sup fun d => if q d < ofOrd α then ordOrZero (q d) else 0) ⊔
      ((Finset.range (n + 1)).sup fun k => if g k < ofOrd α then ordOrZero (g k) else 0)
  have hS : S < α := sup_lt_iff.mpr
    ⟨(Finset.sup_lt_iff hα0).mpr fun _ _ => ordOrZero_lt_of_lt hα0 _,
     (Finset.sup_lt_iff hα0).mpr fun _ _ => ordOrZero_lt_of_lt hα0 _⟩
  let c : Ordinal.{0} := limitPart S + (max n (finitePart S) : ℕ)
  have hc : c < α :=
    ((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 _)).trans_le
      (add_omega0_le_of_lt_isSuccLimit hα ((limitPart_le S).trans_lt hS))
  have hSc : S ≤ c := by
    conv_lhs => rw [← decomposition S]
    exact add_le_add le_rfl (Nat.cast_le.mpr (le_max_right _ _))
  have hcself (k) (hk : k ≤ n) : visibilityReplace c k k = c :=
    (visibilityReplace_self_iff c k).mpr
      (by rw [finitePart_limitPart_add_nat]; exact hk.trans (le_max_left _ _))
  have hqc (d) (hd : q d < ofOrd α) : q d ≤ ofOrd c :=
    le_ofOrd_of_ordOrZero_le hd
      ((Finset.le_sup (f := fun d => if q d < ofOrd α then ordOrZero (q d) else 0)
        (Finset.mem_univ d)).trans (le_sup_left.trans hSc))
  have hgc (k) (hk : k ≤ n) (hg : g k < ofOrd α) : g k ≤ ofOrd c :=
    le_ofOrd_of_ordOrZero_le hg
      ((Finset.le_sup (f := fun k => if g k < ofOrd α then ordOrZero (g k) else 0)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).trans (le_sup_right.trans hSc))
  let g' : ℕ → ExtOrd := fun k =>
    if k ≤ K then jump τ (g k) else if k ≤ n then (if g k < ofOrd α then g k else ofOrd c) else ⊥
  let σ' : ExtOrd → ExtOrd := fun x => jump τ (σ x)
  have hg'K (k) (hk : k ≤ K) : g' k = jump τ (g k) := ite_eq_left hk
  have hg'mid (k) (hk : K < k) (hkn : k ≤ n) :
      g' k = (if g k < ofOrd α then g k else ofOrd c) := by
    dsimp only [g']; rw [ite_eq_right (not_le.mpr hk), ite_eq_left hkn]
  have hg'top (k) (hk : n < k) : g' k = ⊥ := by
    dsimp only [g']
    rw [ite_eq_right (not_le.mpr (hK_le_n.trans_lt hk)), ite_eq_right (not_le.mpr hk)]
  have hg'mid_lt (k) (hk : K < k) (hkn : k ≤ n) : g' k < ofOrd α := by
    rw [hg'mid k hk hkn]; split_ifs with h; exacts [h, ofOrd_lt_ofOrd.mpr hc]
  have hg'mid_le (k) (hk : K < k) (hkn : k ≤ n) : g' k ≤ g k := by
    rw [hg'mid k hk hkn]; split_ifs with h; exacts [le_rfl, (ofOrd_lt_ofOrd.mpr hc).le.trans (not_lt.mp h)]
  have key (a : ExtOrd) (k i : ℕ) (hkK : k ≤ K) (hik : i ≤ k) (hgk : τ < g k)
      (hb : σ (extVisibilityReplace a k i) ≤ τ) : σ a ≤ τ := by
    rcases ExtOrd.cases a with rfl | rfl | ⟨ν, rfl⟩
    · rw [hσbot]; exact bot_le
    · rwa [extVisibilityReplace_top] at hb
    · rw [extVisibilityReplace_ofOrd] at hb
      by_cases hfp : finitePart ν < k
      · rw [visibilityReplace_of_finitePart_lt hfp] at hb
        rcases lt_or_eq_of_le hik with hik' | rfl
        · have h5 := hσ5 (ofOrd (limitPart ν + i)) k (hb.trans hgk.le) (finitePart ν) hfp.le
          rw [extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt
            (by rw [finitePart_limitPart_add_nat]; exact hik'), limitPart_limitPart_add_nat,
            decomposition] at h5
          rw [h5]
          rcases ExtOrd.cases (σ (ofOrd (limitPart ν + i))) with hb' | ht' | ⟨μ, hμ⟩
          · rw [hb', extVisibilityReplace_bot]; exact bot_le
          · exact absurd (ht' ▸ hb) (not_le.mpr (ofOrd_lt_top _))
          · rw [hμ] at hb ⊢
            exact ofOrd_le_ofOrd.mpr (visibilityReplace_le_add_of_le hα
              (ofOrd_le_ofOrd.mp hb) k (hfp.le.trans hkK))
        · refine (hσmono (ofOrd_le_ofOrd.mpr ?_)).trans hb
          conv_lhs => rw [← decomposition ν]
          exact add_le_add le_rfl (Nat.cast_le.mpr hfp.le)
      · rwa [visibilityReplace_of_not_lt hfp] at hb
  refine ⟨g', σ', ?_, ?_, by simp [σ', hσbot], fun _ _ hxy => jump_mono τ (hσmono hxy), ?_, ?_⟩
  · intro k₁ k₂ hlt
    have hg := hganti k₁ k₂ hlt
    by_cases h2 : k₂ ≤ K
    · rw [hg'K k₁ (hlt.le.trans h2), hg'K k₂ h2]; exact jump_mono τ hg
    by_cases h2n : k₂ ≤ n
    · rw [hg'mid k₂ (not_le.mp h2) h2n]
      by_cases h1 : k₁ ≤ K
      · rw [hg'K k₁ h1]
        split_ifs with hk₂
        · exact hg.trans (le_jump τ _)
        · exact (ofOrd_lt_ofOrd.mpr hc).le.trans ((not_lt.mp hk₂).trans (hg.trans (le_jump τ _)))
      · rw [hg'mid k₁ (not_le.mp h1) (hlt.le.trans h2n)]
        split_ifs with hk₂ hk₁ hk₁
        · exact hg
        · exact hgc k₂ h2n hk₂
        · exact absurd (hk₁.trans_le ((not_lt.mp hk₂).trans hg)) (lt_irrefl _)
        · exact le_rfl
    · rw [hg'top k₂ (not_le.mp h2n)]; exact bot_le
  · intro k
    by_cases hk : k ≤ K
    · rw [hg'K k hk]
      by_cases hgk : g k ≤ τ
      · rw [jump_of_le hgk]; exact hgself k
      · rw [jump_of_not_le hgk, extVisibilityReplace_top]
    by_cases hkn : k ≤ n
    · rw [hg'mid k (not_le.mp hk) hkn]
      split_ifs
      · exact hgself k
      · rw [extVisibilityReplace_ofOrd, hcself k hkn]
    · rw [hg'top k (not_le.mp hkn), extVisibilityReplace_bot]
  · intro a k hak i hik
    simp only [σ'] at hak ⊢
    by_cases hkK : k ≤ K
    · rw [hg'K k hkK] at hak
      by_cases hσa : σ a ≤ τ
      · rw [jump_of_le hσa] at hak ⊢
        have hσag : σ a ≤ g k := by
          by_cases hgk : g k ≤ τ
          · rwa [jump_of_le hgk] at hak
          · exact hσa.trans (not_le.mp hgk).le
        rw [hσ5 a k hσag i hik]
        refine jump_of_le ?_
        rcases ExtOrd.cases (σ a) with hb | ht | ⟨μ, hμ⟩
        · rw [hb, extVisibilityReplace_bot]; exact bot_le
        · exact absurd (ht ▸ hσa) (not_le.mpr (ofOrd_lt_top _))
        · rw [hμ] at hσa ⊢
          exact ofOrd_le_ofOrd.mpr (visibilityReplace_le_add_of_le hα
            (ofOrd_le_ofOrd.mp hσa) k (hik.trans hkK))
      · rw [jump_of_not_le hσa] at hak ⊢
        have hgk : τ < g k := not_le.mp fun hle =>
          hσa ((le_top.trans (jump_of_le hle ▸ hak)).trans hle)
        rw [extVisibilityReplace_top]
        by_contra hne
        exact hσa (key a k i hkK hik hgk (not_lt.mp fun hgt => hne (jump_of_not_le (not_le.mpr hgt))))
    · by_cases hkn : k ≤ n
      · have hσ'lt : jump τ (σ a) < ofOrd α := hak.trans_lt (hg'mid_lt k (not_le.mp hkK) hkn)
        have hσa : σ a ≤ τ := by
          by_contra h
          exact not_le_of_gt (jump_of_not_le h ▸ hσ'lt) le_top
        rw [jump_of_le hσa] at hak hσ'lt ⊢
        rw [hσ5 a k (hak.trans (hg'mid_le k (not_le.mp hkK) hkn)) i hik]
        refine jump_of_le (le_trans ?_ hατ)
        rcases ExtOrd.cases (σ a) with hb | ht | ⟨μ, hμ⟩
        · rw [hb, extVisibilityReplace_bot]; exact (bot_lt_ofOrd _).le
        · exact absurd (ht ▸ hσ'lt) (not_lt.mpr le_top)
        · rw [hμ] at hσ'lt ⊢
          exact (ofOrd_lt_ofOrd.mpr (visibilityReplace_lt_of_lt hα (ofOrd_lt_ofOrd.mp hσ'lt) k i)).le
      · rw [hg'top k (not_le.mp hkn)] at hak
        have hσa : σ a = ⊥ := le_bot_iff.mp ((le_jump τ (σ a)).trans hak)
        have h5 := hσ5 a k (hσa ▸ bot_le) i hik
        rw [hσa, extVisibilityReplace_bot] at h5
        rw [hσa, h5, jump_bot, extVisibilityReplace_bot]
  · intro d
    have hd := heq d
    change jump τ (q d) = min (jump τ (σ (p d))) (g' (grade d))
    by_cases hk : grade d ≤ K
    · rw [hg'K _ hk, hd, jump_min]
    · have hkn := hn d
      have hqd0 : q d < ofOrd α := hK d (not_le.mp hk)
      have hqd := hqd0
      rw [hg'mid _ (not_le.mp hk) hkn, jump_of_le (hqd0.le.trans hατ)]
      rw [hd] at hqd ⊢
      by_cases hg : g (grade d) < ofOrd α
      · rw [ite_eq_left hg]
        rcases le_total (σ (p d)) (g (grade d)) with hle | hle
        · rw [min_eq_left hle] at hqd ⊢
          rw [jump_of_le (hqd.le.trans hατ), min_eq_left hle]
        · rw [min_eq_right hle, min_eq_right (hle.trans (le_jump τ _))]
      · rw [ite_eq_right hg]
        have hle : σ (p d) ≤ g (grade d) := not_lt.mp fun h' => hg (min_eq_right h'.le ▸ hqd)
        rw [min_eq_left hle] at hqd ⊢
        rw [jump_of_le (hqd.le.trans hατ), min_eq_left (min_eq_left hle ▸ hd ▸ hqc d hqd0)]

/-! ## The band map -/

namespace ExtOrd

/-- The provisional band map with active band `lam` and threshold `K`. -/
def bandMap (α lam : Ordinal.{0}) (K : ℕ) : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => ofOrd (α + K)
  | some (some ν) =>
      if lam + K ≤ ν then ofOrd (α + K) else if lam ≤ ν then ofOrd (α + finitePart ν) else ofOrd α

theorem bandMap_bot (α lam : Ordinal.{0}) (K : ℕ) : bandMap α lam K ⊥ = ⊥ := rfl

theorem bandMap_top (α lam : Ordinal.{0}) (K : ℕ) : bandMap α lam K ⊤ = ofOrd (α + K) := rfl

theorem bandMap_ofOrd_of_cap {α lam : Ordinal.{0}} {K : ℕ} {ν : Ordinal.{0}} (h : lam + K ≤ ν) :
    bandMap α lam K (ofOrd ν) = ofOrd (α + K) :=
  ite_eq_left h

theorem bandMap_ofOrd_of_band {α lam : Ordinal.{0}} {K : ℕ} {ν : Ordinal.{0}} (h₁ : lam ≤ ν)
    (h₂ : ν < lam + K) : bandMap α lam K (ofOrd ν) = ofOrd (α + finitePart ν) := by
  dsimp only [bandMap, ofOrd]; rw [ite_eq_right (not_le.mpr h₂), ite_eq_left h₁]

theorem bandMap_ofOrd_of_lt {α lam : Ordinal.{0}} {K : ℕ} {ν : Ordinal.{0}} (h : ν < lam) :
    bandMap α lam K (ofOrd ν) = ofOrd α := by
  dsimp only [bandMap, ofOrd]
  rw [ite_eq_right (not_le.mpr (h.trans_le (le_add_of_nonneg_right zero_le))),
    ite_eq_right (not_le.mpr h)]

theorem le_bandMap_of_ne_bot (α lam : Ordinal.{0}) (K : ℕ) {x : ExtOrd} (hx : x ≠ ⊥) :
    ofOrd α ≤ bandMap α lam K x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · exact absurd rfl hx
  · exact ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)
  · dsimp only [bandMap, ofOrd]
    split_ifs <;> first | rfl | exact ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)

theorem bandMap_le {α lam : Ordinal.{0}} (hlam : limitPart lam = lam) (K : ℕ) (x : ExtOrd) :
    bandMap α lam K x ≤ ofOrd (α + K) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · exact bot_le
  · rfl
  · dsimp only [bandMap, ofOrd]
    split_ifs with h1 h2
    · rfl
    · have hlp : limitPart ν = lam := by
        simpa [hlam] using limitPart_eq_of_le_of_lt (μ := lam) (by rwa [hlam]) (by rw [hlam]; exact not_le.mp h1)
      refine ofOrd_le_ofOrd.mpr (add_le_add le_rfl (Nat.cast_le.mpr (not_lt.mp fun hK => h1 ?_)))
      rw [← decomposition ν, hlp]
      exact add_le_add le_rfl (Nat.cast_le.mpr hK.le)
    · exact ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)

/-- The band map is monotone on `[lam, ⊤]`. -/
theorem bandMap_mono_of_le {α lam : Ordinal.{0}} (hlam : limitPart lam = lam) (K : ℕ)
    {x y : ExtOrd} (hx : ofOrd lam ≤ x) (hxy : x ≤ y) :
    bandMap α lam K x ≤ bandMap α lam K y := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · exact absurd hx (not_le.mpr (bot_lt_ofOrd _))
  · rw [top_le_iff.mp hxy]
  · rcases ExtOrd.cases y with rfl | rfl | ⟨ν', rfl⟩
    · exact absurd hxy (not_le.mpr (bot_lt_ofOrd _))
    · exact bandMap_le hlam K _
    · have hνν' : ν ≤ ν' := ofOrd_le_ofOrd.mp hxy
      have hlν : lam ≤ ν := ofOrd_le_ofOrd.mp hx
      by_cases h1 : lam + K ≤ ν
      · rw [bandMap_ofOrd_of_cap h1, bandMap_ofOrd_of_cap (h1.trans hνν')]
      · by_cases h1' : lam + K ≤ ν'
        · rw [bandMap_ofOrd_of_cap h1']; exact bandMap_le hlam K _
        · rw [bandMap_ofOrd_of_band hlν (not_le.mp h1),
            bandMap_ofOrd_of_band (hlν.trans hνν') (not_le.mp h1'), ofOrd_le_ofOrd]
          have hlp : limitPart ν = lam := by
            simpa [hlam] using limitPart_eq_of_le_of_lt (μ := lam) (by rwa [hlam]) (by rw [hlam]; exact not_le.mp h1)
          have hlp' : limitPart ν' = lam := by
            simpa [hlam] using limitPart_eq_of_le_of_lt (μ := lam) (by rw [hlam]; exact hlν.trans hνν')
              (by rw [hlam]; exact not_le.mp h1')
          exact add_le_add le_rfl (Nat.cast_le.mpr (finitePart_le_of_le (hlp.trans hlp'.symm) hνν'))

end ExtOrd

/-! ### Multiples of `ω` -/

namespace Value

/-- `finitePart (μ + i) = i` for a multiple of `ω`. -/
theorem finitePart_limitPart_add_nat' {μ : Ordinal.{0}} (hμ : limitPart μ = μ) (i : ℕ) :
    finitePart (μ + i) = i := by
  have := finitePart_limitPart_add_nat μ i
  rwa [hμ] at this

/-- `limitPart (μ + i) = μ` for a multiple of `ω`. -/
theorem limitPart_add_nat_of_limitPart_eq {μ : Ordinal.{0}} (hμ : limitPart μ = μ) (i : ℕ) :
    limitPart (μ + i) = μ := by
  have := limitPart_limitPart_add_nat μ i
  rwa [hμ] at this

/-- A multiple of `ω` strictly below a limit part sits a whole `ω` below it. -/
theorem add_omega0_le_limitPart_of_lt {μ ν : Ordinal.{0}} (hμ : limitPart μ = μ)
    (h : μ < limitPart ν) : μ + Ordinal.omega0 ≤ limitPart ν := by
  rw [← hμ] at h ⊢
  unfold limitPart at h ⊢
  rw [← Ordinal.mul_succ]
  exact mul_le_mul_right (Order.succ_le_of_lt ((mul_lt_mul_iff_right₀ Ordinal.omega0_pos).mp h)) _

/-- Band replacement below a multiple-of-`ω` bound stays below it. -/
theorem visibilityReplace_lt_of_lt_of_limitPart_eq {μ ν : Ordinal.{0}} (hμ : limitPart μ = μ)
    (hν : ν < μ) (k i : ℕ) : visibilityReplace ν k i < μ := by
  unfold visibilityReplace ordinalReplace
  split_ifs
  · have := add_omega0_le_limitPart_of_lt (μ := limitPart ν) (ν := μ) (limitPart_limitPart ν)
      (by rw [hμ]; exact (limitPart_le ν).trans_lt hν)
    rw [hμ] at this
    exact ((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 i)).trans_le this
  · exact hν

/-- Band replacement with `i ≤ K` below `μ + K` (`μ` a multiple of `ω`) stays below `μ + K`. -/
theorem visibilityReplace_le_add_of_le_of_limitPart_eq {μ ν : Ordinal.{0}}
    (hμ : limitPart μ = μ) {K i : ℕ} (hν : ν ≤ μ + K) (k : ℕ) (hi : i ≤ K) :
    visibilityReplace ν k i ≤ μ + K := by
  unfold visibilityReplace ordinalReplace
  split_ifs
  · exact add_le_add (limitPart_add_nat_of_limitPart_eq hμ K ▸ limitPart_mono hν) (Nat.cast_le.mpr hi)
  · exact hν

/-- Band replacement at threshold `k ≤ K` with `i ≤ k` of a value above `μ + K` (`μ` a
multiple of `ω`) stays at or above `μ + K`. -/
theorem le_visibilityReplace_of_lt_of_limitPart_eq {μ ν : Ordinal.{0}} (hμ : limitPart μ = μ)
    {K k i : ℕ} (hν : μ + K < ν) (hk : k ≤ K) (_hi : i ≤ k) :
    μ + K ≤ visibilityReplace ν k i := by
  unfold visibilityReplace ordinalReplace
  split_ifs with h
  · have hlt : μ < limitPart ν := lt_of_le_of_ne
      (limitPart_add_nat_of_limitPart_eq hμ K ▸ limitPart_mono hν.le) fun heq => by
        rw [← decomposition ν, ← heq] at hν
        exact not_lt_of_ge (hk.trans (Nat.cast_lt.mp ((add_lt_add_iff_left μ).mp hν)).le) h
    exact ((add_le_add le_rfl (Ordinal.natCast_lt_omega0 K).le).trans
      (add_omega0_le_limitPart_of_lt hμ hlt)).trans (le_add_of_nonneg_right zero_le)
  · exact hν.le

end Value

namespace ExtOrd

/-- The band map commutes with band replacement at thresholds `≤ K` on `[lam, ⊤]`. -/
theorem bandMap_extVisibilityReplace {α lam : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    (hlam : limitPart lam = lam) {K k i : ℕ} (hk : k ≤ K) (hi : i ≤ k) {x : ExtOrd}
    (hx : ofOrd lam ≤ x) :
    bandMap α lam K (extVisibilityReplace x k i) =
      extVisibilityReplace (bandMap α lam K x) k i := by
  have hfpK : ¬ finitePart (α + K) < k := by
    rw [finitePart_succLimit_add_nat hα]; exact not_lt.mpr hk
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · exact absurd hx (not_le.mpr (bot_lt_ofOrd _))
  · rw [extVisibilityReplace_top, bandMap_top, extVisibilityReplace_ofOrd,
      visibilityReplace_of_not_lt hfpK]
  · have hlν : lam ≤ ν := ofOrd_le_ofOrd.mp hx
    rw [extVisibilityReplace_ofOrd]
    by_cases hcap : lam + K ≤ ν
    · rw [bandMap_ofOrd_of_cap hcap, extVisibilityReplace_ofOrd, visibilityReplace_of_not_lt hfpK]
      rcases hcap.lt_or_eq with hlt | rfl
      · exact bandMap_ofOrd_of_cap (le_visibilityReplace_of_lt_of_limitPart_eq hlam hlt hk hi)
      · rw [visibilityReplace_of_not_lt (by rw [finitePart_limitPart_add_nat' hlam]; exact not_lt.mpr hk),
          bandMap_ofOrd_of_cap le_rfl]
    · have hband := not_le.mp hcap
      rw [bandMap_ofOrd_of_band hlν hband, extVisibilityReplace_ofOrd]
      have hlp : limitPart ν = lam := by
        simpa [hlam] using limitPart_eq_of_le_of_lt (μ := lam) (by rwa [hlam]) (by rwa [hlam])
      by_cases hfp : finitePart ν < k
      · rw [visibilityReplace_of_finitePart_lt hfp, hlp,
          visibilityReplace_of_finitePart_lt (by rw [finitePart_succLimit_add_nat hα]; exact hfp),
          limitPart_succLimit_add_nat hα]
        rcases lt_or_eq_of_le (hi.trans hk) with hiK | rfl
        · rw [bandMap_ofOrd_of_band (le_add_of_nonneg_right zero_le)
            ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hiK)), finitePart_limitPart_add_nat' hlam]
        · rw [bandMap_ofOrd_of_cap le_rfl]
      · rw [visibilityReplace_of_not_lt hfp, visibilityReplace_of_not_lt
          (by rw [finitePart_succLimit_add_nat hα]; exact hfp), bandMap_ofOrd_of_band hlν hband]

end ExtOrd

/-! ### The gate: post-composition with the band map -/

open Value ExtOrd in
/-- Under a multiple-of-`ω` bound `c = μ + K'` with `K ≤ K'`, band replacement at thresholds
`≤ K` commutes with capping at `c`. -/
theorem min_extVisibilityReplace_cap {μ : Ordinal.{0}} (hμ : limitPart μ = μ) {K K' k i : ℕ}
    (hKK' : K ≤ K') (hk : k ≤ K) (hi : i ≤ k) (x : ExtOrd) (hx : x ≠ ⊤) :
    min (extVisibilityReplace x k i) (ofOrd (μ + K')) =
      extVisibilityReplace (min x (ofOrd (μ + K'))) k i := by
  have hfp : ¬ finitePart (μ + K') < k := by
    rw [finitePart_limitPart_add_nat' hμ]; exact not_lt.mpr (hk.trans hKK')
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · simp only [extVisibilityReplace_bot, min_eq_left bot_le]
  · exact absurd rfl hx
  · rw [extVisibilityReplace_ofOrd]
    rcases le_or_gt ν (μ + K') with hle | hlt
    · rw [min_eq_left (ofOrd_le_ofOrd.mpr
        (visibilityReplace_le_add_of_le_of_limitPart_eq hμ hle k ((hi.trans hk).trans hKK'))),
        min_eq_left (ofOrd_le_ofOrd.mpr hle), extVisibilityReplace_ofOrd]
    · rw [min_eq_right (ofOrd_le_ofOrd.mpr
        (le_visibilityReplace_of_lt_of_limitPart_eq hμ hlt (hk.trans hKK') hi)),
        min_eq_right (ofOrd_le_ofOrd.mpr hlt.le), extVisibilityReplace_ofOrd,
        visibilityReplace_of_not_lt hfp]
