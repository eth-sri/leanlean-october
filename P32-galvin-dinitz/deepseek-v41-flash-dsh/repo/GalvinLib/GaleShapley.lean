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

variable {M W : Type*}

/-- The strict preference conditions needed for the Gale–Shapley argument. -/
def Pref (E : M → W → Prop) (rm : M → W → ℕ) (rw : W → M → ℕ) : Prop :=
  (∀ m w w', E m w → E m w' → rm m w = rm m w' → w = w') ∧
    ∀ w m m', E m w → E m' w → rw w m = rw w m' → m = m'

/-- `w` is an acceptable partner of `m` of minimal rank. -/
def IsTop (E : M → W → Prop) (r : M → W → ℕ) (m : M) (w : W) : Prop :=
  E m w ∧ ∀ w', E m w' → r m w ≤ r m w'

/-- The stable matching property. -/
def IsStable (E : M → W → Prop) (rm : M → W → ℕ) (rw : W → M → ℕ) (μ : M → W → Prop) : Prop :=
  (∀ m w, μ m w → E m w) ∧ (∀ m w w', μ m w → μ m w' → w = w') ∧
    (∀ m m' w, μ m w → μ m' w → m = m') ∧
    ∀ m w, E m w → ¬ μ m w →
      (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m)

theorem exists_isTop (E : M → W → Prop) (r : M → W → ℕ) (m : M) (w : W) (h : E m w) :
    ∃ w', IsTop E r m w' := by
  classical
  obtain ⟨w', hw', hk⟩ := Nat.find_spec (⟨_, w, h, rfl⟩ : ∃ k, ∃ w, E m w ∧ r m w = k)
  exact ⟨w', hw', fun v hv => by rw [hk]; exact Nat.find_min' _ ⟨v, hv, rfl⟩⟩

theorem isStable_del {E : M → W → Prop} {rm : M → W → ℕ} {rw : W → M → ℕ}
    {m₁ m₂ : M} {w : W} (h₁ : IsTop E rm m₁ w) (hlt : rw w m₁ < rw w m₂) {μ : M → W → Prop}
    (hμ : IsStable (fun m v => E m v ∧ ¬ (m = m₂ ∧ v = w)) rm rw μ) (hne : m₁ ≠ m₂) :
    IsStable E rm rw μ := by
  obtain ⟨hsub, hm, hw, hst⟩ := hμ
  refine ⟨fun m v h => (hsub m v h).1, hm, hw, fun m v hE hnot => ?_⟩
  by_cases hrem : m = m₂ ∧ v = w
  · obtain ⟨rfl, rfl⟩ := hrem
    right
    by_cases hμ₁ : μ m₁ v
    · exact ⟨m₁, hμ₁, hlt⟩
    · rcases hst m₁ v ⟨h₁.1, fun h => hne h.1⟩ hμ₁ with ⟨w', hw', hr⟩ | ⟨m', hm', hr⟩
      · exact absurd (h₁.2 w' (hsub m₁ w' hw').1) (not_le.mpr hr)
      · exact ⟨m', hm', hr.trans hlt⟩
  · exact hst m v ⟨hE, hrem⟩ hnot

theorem exists_isStable [Finite M] [Finite W] (E : M → W → Prop) (rm : M → W → ℕ)
    (rw : W → M → ℕ) (hm : Pref E rm rw) : ∃ μ, IsStable E rm rw μ := by
  classical
  suffices H : ∀ n (E : M → W → Prop), Pref E rm rw →
      {p : M × W | E p.1 p.2}.ncard = n → ∃ μ, IsStable E rm rw μ from H _ E hm rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E hm hn
  by_cases hsh : ∃ a b w, a ≠ b ∧ IsTop E rm a w ∧ IsTop E rm b w
  · obtain ⟨a, b, w, hab, ha, hb⟩ := hsh
    have key : ∀ c d : M, c ≠ d → IsTop E rm c w → IsTop E rm d w → rw w c < rw w d →
        ∃ μ, IsStable E rm rw μ := by
      intro c d hcd hc hd hlt
      let E' : M → W → Prop := fun m v => E m v ∧ ¬ (m = d ∧ v = w)
      have hlt' : {p : M × W | E' p.1 p.2}.ncard < n := by
        rw [← hn]
        refine Set.ncard_lt_ncard ⟨fun p hp => hp.1, fun h => ?_⟩
        exact (h (show (d, w) ∈ {p : M × W | E p.1 p.2} from hd.1)).2 ⟨rfl, rfl⟩
      obtain ⟨μ, hμ⟩ := ih _ hlt' E' ⟨fun m w w' h1 h2 h => hm.1 m w w' h1.1 h2.1 h,
        fun w m m' h1 h2 h => hm.2 w m m' h1.1 h2.1 h⟩ rfl
      exact ⟨μ, isStable_del hc hlt hμ hcd⟩
    rcases lt_or_gt_of_ne (fun h => hab (hm.2 w a b ha.1 hb.1 h)) with h | h
    · exact key a b hab ha hb h
    · exact key b a (Ne.symm hab) hb ha h
  · push Not at hsh
    refine ⟨IsTop E rm, fun m w h => h.1, fun m w w' h h' => ?_, fun m m' w h h' => ?_,
      fun m w hE hnot => ?_⟩
    · exact hm.1 m w w' h.1 h'.1 (le_antisymm (h.2 _ h'.1) (h'.2 _ h.1))
    · by_contra hc
      exact hsh m m' w hc h h'
    · obtain ⟨w', hw'⟩ := exists_isTop E rm m w hE
      left
      refine ⟨w', hw', lt_of_le_of_ne (hw'.2 w hE) fun heq => ?_⟩
      exact hnot (hm.1 m w' w hw'.1 hE heq ▸ hw')

end Galvin
