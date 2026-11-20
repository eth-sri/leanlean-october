/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteBandReadback
public import VaughtConjecture.Knight.SuccLimitBandArithmetic
public import VaughtConjecture.Knight.NormalForm

@[expose] public section

namespace VaughtConjecture.Knight

open Value ExtOrd

namespace ExtOrd

/-- The threshold map: identity at or below `τ`, `⊤` above. -/
noncomputable def jump (τ x : ExtOrd) : ExtOrd := if x ≤ τ then x else ⊤

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

end ExtOrd

namespace Value

/-- Below a limit, band replacement stays below the limit. -/
theorem visibilityReplace_of_not_lt {μ : Ordinal.{0}} {k i : ℕ} (h : ¬ finitePart μ < k) :
    visibilityReplace μ k i = μ := by
  unfold visibilityReplace ordinalReplace
  rw [ite_eq_right h]

end Value

open Transform in
/-- Raising values above a visible cutoff preserves transformations at the bounded grades. -/
theorem TransformsTo.jump_target {D : Type*} {grade : D → ℕ} {p q : D → ExtOrd}
    (h : TransformsTo grade p q) {τ : ExtOrd} {K : ℕ} (hτ : SelfVis K τ)
    (hK : ∀ d, grade d ≤ K) : TransformsTo grade p (fun d => jump τ (q d)) := by
  obtain ⟨g, σ, hanti, hvis, hbot, hmono, hcomm, hread⟩ := h
  let r : ℕ → ExtOrd := fun k => if k ≤ K then jump τ (g k) else ⊥
  refine ⟨r, jump τ ∘ σ, ?_, ?_, by simp [Function.comp_def, hbot], (jump_mono τ).comp hmono,
    ?_, fun d => by simp only [Function.comp_apply, r, if_pos (hK d), hread d, jump_min]⟩
  · intro i j hij
    change r j ≤ r i
    by_cases hj : j ≤ K
    · simpa only [r, if_pos hj, if_pos (hij.le.trans hj)] using jump_mono τ (hanti i j hij)
    · simp [r, hj]
  · intro k
    by_cases hk : k ≤ K
    · simp only [r, if_pos hk, jump]
      split_ifs
      · exact hvis k
      · exact (extVisibilityReplace_top _ _).symm
    · simp [r, hk]
  · intro x k hx i hi
    simp only [Function.comp_apply] at hx ⊢
    by_cases hk : k ≤ K
    · have hv := hτ.mono hk
      simp only [r, if_pos hk] at hx
      by_cases hle : σ x ≤ τ
      · have hxg : σ x ≤ g k := by
          by_cases hg : g k ≤ τ
          · simpa only [jump_of_le hle, jump_of_le hg] using hx
          · exact hle.trans (le_of_not_ge hg)
        rw [hcomm x k hxg i hi, jump_of_le hle,
          jump_of_le (extVisibilityReplace_le_of_le_selfVis hi hv hle)]
      · have hτg : τ ≤ g k := by
          by_contra hg
          have ht : (⊤ : ExtOrd) ≤ g k := by
            simpa only [jump_of_not_le hle, jump_of_le (le_of_lt (not_le.mp hg))] using hx
          exact hle ((le_top.trans ht).trans (not_le.mp hg).le)
        rw [jump_of_not_le hle, extVisibilityReplace_top]
        apply jump_of_not_le
        intro hs
        exact hle (preimage_of_replacement (P := (· ≤ τ)) hmono hi
          (fun ha hb => ha.trans hb) (fun hj hy => extVisibilityReplace_le_of_le_selfVis hj hv hy)
          (fun y hy => hcomm y k (hy.trans hτg)) hs)
    · have hz : σ x = ⊥ := le_bot_iff.mp ((le_jump τ _).trans (by simpa only [r, if_neg hk] using hx))
      rw [hcomm x k (hz ▸ bot_le) i hi, hz, extVisibilityReplace_bot, jump_bot, extVisibilityReplace_bot]


namespace ExtOrd

/-- The provisional band map with active band `lam` and threshold `K`. -/
noncomputable def bandMap (α lam : Ordinal.{0}) (K : ℕ) : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => ofOrd (α + K)
  | some (some ν) =>
      if lam + K ≤ ν then ofOrd (α + K) else if lam ≤ ν then ofOrd (α + finitePart ν) else ofOrd α

theorem bandMap_bot (α lam : Ordinal.{0}) (K : ℕ) : bandMap α lam K ⊥ = ⊥ := rfl

theorem bandMap_top (α lam : Ordinal.{0}) (K : ℕ) : bandMap α lam K ⊤ = ofOrd (α + K) := rfl

theorem bandMap_ofOrd_of_cap {α lam : Ordinal.{0}} {K : ℕ} {ν : Ordinal.{0}} (h : lam + K ≤ ν) :
    bandMap α lam K (ofOrd ν) = ofOrd (α + K) := by
  change (if lam + K ≤ ν then _ else _) = _
  rw [ite_eq_left h]

theorem bandMap_ofOrd_of_band {α lam : Ordinal.{0}} {K : ℕ} {ν : Ordinal.{0}} (h₁ : lam ≤ ν)
    (h₂ : ν < lam + K) : bandMap α lam K (ofOrd ν) = ofOrd (α + finitePart ν) := by
  change (if lam + K ≤ ν then _ else if lam ≤ ν then _ else _) = _
  simp_all

theorem bandMap_ofOrd_of_lt {α lam : Ordinal.{0}} {K : ℕ} {ν : Ordinal.{0}} (h : ν < lam) :
    bandMap α lam K (ofOrd ν) = ofOrd α := by
  change (if lam + K ≤ ν then _ else if lam ≤ ν then _ else _) = _
  have h' : ¬ lam + K ≤ ν := not_le.mpr (h.trans_le (le_add_of_nonneg_right zero_le))
  grind

theorem le_bandMap_of_ne_bot (α lam : Ordinal.{0}) (K : ℕ) {x : ExtOrd} (hx : x ≠ ⊥) :
    ofOrd α ≤ bandMap α lam K x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · exact absurd rfl hx
  · rw [bandMap_top]; simp_all
  · by_cases h1 : lam + K ≤ ν
    · rw [bandMap_ofOrd_of_cap h1]; simp_all
    · by_cases h2 : lam ≤ ν
      · rw [bandMap_ofOrd_of_band h2 (not_le.mp h1)]
        simp_all
      · rw [bandMap_ofOrd_of_lt (not_le.mp h2)]

theorem bandMap_le {α lam : Ordinal.{0}} (hlam : limitPart lam = lam) (K : ℕ) (x : ExtOrd) :
    bandMap α lam K x ≤ ofOrd (α + K) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · rw [bandMap_bot]; exact bot_le
  · rw [bandMap_top]
  · by_cases h1 : lam + K ≤ ν
    · rw [bandMap_ofOrd_of_cap h1]
    · by_cases h2 : lam ≤ ν
      · rw [bandMap_ofOrd_of_band h2 (not_le.mp h1), ofOrd_le_ofOrd]
        refine add_le_add (le_refl _) ((Nat.cast_le (α := Ordinal.{0})).mpr ?_)
        -- `ν = lam + fp ν < lam + K`
        have hlp : limitPart ν = lam := by
          have := limitPart_eq_of_le_of_lt (μ := lam) (z := ν) (by rwa [hlam])
            (by rw [hlam]; exact not_le.mp h1)
          rwa [hlam] at this
        have hν : ν = lam + (finitePart ν : Ordinal.{0}) := by
          rw [← hlp]; exact (decomposition ν).symm
        rw [hν] at h1
        by_contra hK
        exact h1 (add_le_add (le_refl _) ((Nat.cast_le (α := Ordinal.{0})).mpr (not_le.mp hK).le))
      · rw [bandMap_ofOrd_of_lt (not_le.mp h2), ofOrd_le_ofOrd]
        exact le_add_of_nonneg_right zero_le

/-- The band map is monotone on `[lam, ⊤]`. -/
theorem bandMap_mono_of_le {α lam : Ordinal.{0}} (hlam : limitPart lam = lam) (K : ℕ)
    {x y : ExtOrd} (hx : ofOrd lam ≤ x) (hxy : x ≤ y) :
    bandMap α lam K x ≤ bandMap α lam K y := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · solve_by_elim
  · rw [top_le_iff.mp hxy]
  · rcases ExtOrd.cases y with rfl | rfl | ⟨ν', rfl⟩
    · trivial
    · rw [bandMap_top]; exact bandMap_le hlam K _
    · have hνν' : ν ≤ ν' := ofOrd_le_ofOrd.mp hxy
      have hlν : lam ≤ ν := ofOrd_le_ofOrd.mp hx
      by_cases h1 : lam + K ≤ ν
      · rw [bandMap_ofOrd_of_cap h1, bandMap_ofOrd_of_cap (h1.trans hνν')]
      · rw [bandMap_ofOrd_of_band hlν (not_le.mp h1)]
        by_cases h1' : lam + K ≤ ν'
        · rw [bandMap_ofOrd_of_cap h1']
          have := bandMap_le (α := α) hlam K (ofOrd ν)
          rwa [bandMap_ofOrd_of_band hlν (not_le.mp h1)] at this
        · rw [bandMap_ofOrd_of_band (hlν.trans hνν') (not_le.mp h1'), ofOrd_le_ofOrd]
          -- same limit part `lam`, so finite parts compare
          have hlp : limitPart ν = lam := by
            have := limitPart_eq_of_le_of_lt (μ := lam) (z := ν) (by rwa [hlam])
              (by rw [hlam]; exact not_le.mp h1)
            rwa [hlam] at this
          have hlp' : limitPart ν' = lam := by
            have h₁ : limitPart lam ≤ ν' := by grind
            have h₂ : ν' < limitPart lam + K := by simp_all
            have := limitPart_eq_of_le_of_lt (μ := lam) (z := ν') h₁ h₂
            rwa [hlam] at this
          have hfp : finitePart ν ≤ finitePart ν' := finitePart_le_of_le (hlp.trans hlp'.symm) hνν'
          simp_all

end ExtOrd

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
  have hq : μ / Ordinal.omega0 < ν / Ordinal.omega0 :=
    (mul_lt_mul_iff_right₀ Ordinal.omega0_pos).mp h
  rw [← Ordinal.mul_succ]
  exact mul_le_mul_right (Order.succ_le_of_lt hq) _

/-- Band replacement at threshold `k ≤ K` with `i ≤ k` of a value above `μ + K` (`μ` a
multiple of `ω`) stays at or above `μ + K`. -/
theorem le_visibilityReplace_of_lt_of_limitPart_eq {μ ν : Ordinal.{0}} (hμ : limitPart μ = μ)
    {K k i : ℕ} (hν : μ + K < ν) (hk : k ≤ K) (_hi : i ≤ k) :
    μ + K ≤ visibilityReplace ν k i := by
  unfold visibilityReplace ordinalReplace
  split_ifs with h
  · -- `limitPart ν ≠ μ`, else `ν = μ + fp ν` with `fp ν < k ≤ K`
    have hne : limitPart ν ≠ μ := by
      intro heq
      have hdec := decomposition ν
      rw [heq] at hdec
      rw [← hdec] at hν
      have : (K : Ordinal.{0}) < finitePart ν := (add_lt_add_iff_left _).mp hν
      (simp_all <;> omega)
    have hlt : μ < limitPart ν := by
      rcases lt_or_ge μ (limitPart ν) with h' | h'
      · exact h'
      · exfalso
        have h2 : μ ≤ limitPart ν := by
          have := limitPart_mono hν.le
          rwa [limitPart_add_nat_of_limitPart_eq hμ] at this
        grind
    calc μ + (K : Ordinal.{0}) ≤ μ + Ordinal.omega0 :=
          add_le_add (le_refl _) (Ordinal.natCast_lt_omega0 K).le
      _ ≤ limitPart ν := add_omega0_le_limitPart_of_lt hμ hlt
      _ ≤ limitPart ν + i := le_add_of_nonneg_right zero_le
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
      rcases hcap.lt_or_eq with hlt | heq
      · exact bandMap_ofOrd_of_cap (le_visibilityReplace_of_lt_of_limitPart_eq hlam hlt hk hi)
      · -- `ν = lam + K`: finite part `K ≥ k`, no replacement
        have hnl : ¬ finitePart (lam + K) < k := by
          rw [finitePart_limitPart_add_nat' hlam]; exact not_lt.mpr hk
        rw [← heq, visibilityReplace_of_not_lt hnl]
        exact bandMap_ofOrd_of_cap le_rfl
    · have hband := not_le.mp hcap
      rw [bandMap_ofOrd_of_band hlν hband, extVisibilityReplace_ofOrd]
      have hlp : limitPart ν = lam := by
        have := limitPart_eq_of_le_of_lt (μ := lam) (z := ν) (by rwa [hlam]) (by rwa [hlam])
        rwa [hlam] at this
      by_cases hfp : finitePart ν < k
      · rw [visibilityReplace_of_finitePart_lt hfp, hlp,
          visibilityReplace_of_finitePart_lt (by rw [finitePart_succLimit_add_nat hα]; exact hfp),
          limitPart_succLimit_add_nat hα]
        rcases lt_or_eq_of_le (hi.trans hk) with hiK | hiK
        · rw [bandMap_ofOrd_of_band (le_add_of_nonneg_right zero_le)
            ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hiK)), finitePart_limitPart_add_nat' hlam]
        · rw [hiK, bandMap_ofOrd_of_cap le_rfl]
      · rw [visibilityReplace_of_not_lt hfp, visibilityReplace_of_not_lt
          (by rw [finitePart_succLimit_add_nat hα]; exact hfp)]
        exact bandMap_ofOrd_of_band hlν hband

end ExtOrd

end VaughtConjecture.Knight
