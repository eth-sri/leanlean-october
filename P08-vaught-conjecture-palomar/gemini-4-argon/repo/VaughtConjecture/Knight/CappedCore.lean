/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CountedRecoding
public import VaughtConjecture.Knight.CappedLocalityRecoding

/-! # The provenance-preserving truncation: retain the witnesses, cap the evaluations

**The representation**, adopted after the level-two no-go for the recomputed truncation
(`docs/STATUS.md`, "Truncation representation"):
a truncated level-three cell **retains the base core's owned witnesses and their charts** and
**caps their decoded evaluations**: `ρ_ℓ^η(s) = min (ρ_ℓ(s), η)`.  The object is a base core
together with a cap (`CappedCore3`); its rows are the capped rows of the base.

**Acceptance tests, compiled.**

* `TransformsTo.capped` — the generic fact behind everything: capping the target of a faithful
  transformation at a `K`-self-visible constant (all grades `≤ K`) is again a faithful
  transformation, clause 5 included (shifter `min (σ ·) η`, suppressor `min (g k) η` through `K`).
  No controller is needed: the guard itself supplies `η ≤ g k` where the ambient output exceeds
  the cap.
* attainment of the new cap at the retained witness (`rho2_wit2C`), and every capped evaluation
  bounded by the cap;
* the cross-level localities `3 → 1` and `3 → 2` for the capped rows (`cross31C`, `cross32C`) by
  capping the base localities;
* the mixed square for the capped decoder (`mixed_squareC`);
* same-level agreement of the capped rows at the capped meet (`rowC_agree`) and the same-level
  locality with the identity shifter (`same3C`);
* repeated truncation reduces to the minimum cap (`recap`, `recap_row`, `recap_recap`), so retained
  provenance generates no history; and the **represented meet**: the capped meet of a cell with
  its own truncation is the cap (`meetC_recap`).

Level one: the capped evaluation `min (ρ₁ t H) η` coincides with the recomputed truncation's
value (`Core3.rho1_trunc`, scratch), so the two representations agree exactly where the recomputed
one is valid.  Sharp coding of the retained witness rows and of the capped rows, and locality on
the domain enlarged by the capped cells themselves, are in `Knight/CappedCoreCoding.lean`.
Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## Capping a transformation -/

/-- **Capping the target of a faithful transformation** at a `K`-self-visible constant, all grades
at most `K`. -/
theorem TransformsTo.capped {D : Type*} {grade : D → ℕ} {E T : D → ExtOrd} {K : ℕ}
    (hmax : ∀ d, grade d ≤ K) {η : ExtOrd} (hvis : SelfVis K η) (h : TransformsTo grade E T) :
    TransformsTo grade E fun d => min (T d) η := by
  by_cases hne : η = ⊥
  · subst hne
    refine ⟨fun _ => ⊥, fun _ => ⊥, fun _ _ _ => le_rfl,
      fun n => (extVisibilityReplace_bot n n).symm, rfl, fun _ _ _ => le_rfl,
      fun _ _ _ _ _ => by rw [extVisibilityReplace_bot], fun d => ?_⟩
    change min (T d) ⊥ = min ⊥ ⊥
    rw [min_eq_right bot_le, min_self]
  obtain ⟨g, σ, hanti, hgvis, hbot, hmono, hevr, hrow⟩ := h
  have h5 : ∀ x k, min (σ x) η ≤ (if k ≤ K then min (g k) η else ⊥) → ∀ i, i ≤ k →
      min (σ (extVisibilityReplace x k i)) η = extVisibilityReplace (min (σ x) η) k i := by
    intro x k hact i hi
    split_ifs at hact with hk
    · have hcapk : SelfVis k η := selfVis_mono hvis hk
      rcases le_or_gt (σ x) η with hle | hlt
      · have hτ : min (σ x) η = σ x := min_eq_left hle
        rw [hτ] at hact ⊢
        have hσact : σ x ≤ g k := hact.trans (min_le_left _ _)
        rw [hevr x k hσact i hi, min_eq_left (extVisibilityReplace_le_of_le_selfVis hi hcapk hle)]
      · have hτ : min (σ x) η = η := min_eq_right hlt.le
        rw [hτ] at hact ⊢
        have hηg : η ≤ g k := hact.trans (min_le_left _ _)
        rw [min_eq_right (cap_le_of_evr hmono hevr hcapk hηg hlt hi), evr_eq_self_of_selfVis hcapk]
    · have hτbot : min (σ x) η = ⊥ := le_bot_iff.mp hact
      have hσbot : σ x = ⊥ := by
        rcases le_total (σ x) η with h | h
        · rwa [min_eq_left h] at hτbot
        · rw [min_eq_right h] at hτbot; exact absurd hτbot hne
      have hσact : σ x ≤ g k := by rw [hσbot]; exact bot_le
      rw [hevr x k hσact i hi, hσbot, extVisibilityReplace_bot, min_eq_left bot_le,
        extVisibilityReplace_bot]
  refine ⟨fun k => if k ≤ K then min (g k) η else ⊥, fun x => min (σ x) η, ?_, ?_, ?_, ?_, h5, ?_⟩
  · intro n m hnm
    dsimp only
    split_ifs with h1 h2 h2
    · exact min_le_min (hanti n m hnm) le_rfl
    · omega
    · exact bot_le
    · exact le_rfl
  · intro n
    dsimp only
    split_ifs with h
    · exact (selfVis_min (hgvis n).symm (selfVis_mono hvis h)).symm
    · exact (selfVis_bot n).symm
  · change min (σ ⊥) η = ⊥
    rw [hbot, min_eq_left bot_le]
  · exact fun _ _ h => min_le_min (hmono h) le_rfl
  · intro d
    have h := hrow d
    dsimp only
    rw [ite_eq_left (hmax d), h, min_min_min_comm, min_self]

/-! ## The capped core -/

/-! ## Same-level agreement, the capped meet, and repeated truncation -/

/-! ### Repeated truncation and the represented meet -/
