/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Existence of stable matchings

An inductive proof of the Gale–Shapley theorem. If no two men share the same favourite woman,
matching every man to his favourite is stable. Otherwise two men `m₁ ≠ m₂` share the favourite
`w`; if `w` prefers `m₁`, the pair `(m₂, w)` may be deleted: in a stable matching of the smaller
instance, `w` is matched to someone at least as good as `m₁` (because `m₁` cannot prefer anybody
to `w`), so the deleted pair is blocked.
-/

@[expose] public section

namespace Galvin

/-- `IsTop E r m w`: `w` is an acceptable partner of `m` of minimal rank. -/
def IsTop {M W : Type*} (E : M → W → Prop) (rm : M → W → ℕ) (m : M) (w : W) : Prop :=
  E m w ∧ ∀ w', E m w' → rm m w ≤ rm m w'

/-- The stable matching property. -/
def IsStable {M W : Type*} (E : M → W → Prop) (rm : M → W → ℕ) (rw : W → M → ℕ)
    (μ : M → W → Prop) : Prop :=
  (∀ m w, μ m w → E m w) ∧
      (∀ m w w', μ m w → μ m w' → w = w') ∧ (∀ m m' w, μ m w → μ m' w → m = m') ∧
      ∀ m w, E m w → ¬ μ m w →
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m)

theorem exists_isStable {M W : Type*} [Finite M] [Finite W] (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Function.Injective (rm m))
    (hrw : ∀ w, Function.Injective (rw w)) : ∃ μ, IsStable E rm rw μ := by
  classical
  generalize hn : {p : M × W | E p.1 p.2}.ncard = n
  induction n using Nat.strong_induction_on generalizing E with
  | _ n ih =>
  by_cases hsh : ∃ m₁ m₂ w, m₁ ≠ m₂ ∧ IsTop E rm m₁ w ∧ IsTop E rm m₂ w
  · obtain ⟨m₁, m₂, w, hne, h₁, h₂⟩ := hsh
    have key : ∀ a b : M, a ≠ b → IsTop E rm a w → IsTop E rm b w → rw w a < rw w b →
        ∃ μ, IsStable E rm rw μ := by
      intro a b hab ha hb hlt
      let E' : M → W → Prop := fun m v => E m v ∧ ¬ (m = b ∧ v = w)
      have hlt' : {p : M × W | E' p.1 p.2}.ncard < n := by
        rw [← hn]
        apply Set.ncard_lt_ncard _ (Set.toFinite _)
        refine ⟨fun p hp => hp.1, fun h => ?_⟩
        have := h (show (b, w) ∈ {p : M × W | E p.1 p.2} from hb.1)
        grind
      obtain ⟨μ, hμ⟩ := ih _ hlt' E' rfl
      refine ⟨μ, ?_⟩
      unfold IsStable at hμ ⊢
      grind [IsTop]
    rcases lt_or_gt_of_ne (fun h => hne (hrw w h)) with h | h
    · exact key m₁ m₂ hne h₁ h₂ h
    · exact key m₂ m₁ (Ne.symm hne) h₂ h₁ h
  · push Not at hsh
    have ht : ∀ m w, E m w → ∃ w', IsTop E rm m w' := by
      intro m w h
      have hex : ∃ k, ∃ w, E m w ∧ rm m w = k := ⟨_, w, h, rfl⟩
      obtain ⟨w', hw', hk⟩ := Nat.find_spec hex
      refine ⟨w', hw', fun v hv => ?_⟩
      rw [hk]
      exact Nat.find_min' hex ⟨v, hv, rfl⟩
    refine ⟨IsTop E rm, ?_⟩
    unfold IsStable
    grind [IsTop]

end Galvin
