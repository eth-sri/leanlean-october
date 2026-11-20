/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorSource

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

/-- A `k`-visible value strictly below `x` stays strictly below every `k`-replacement of `x`. -/
theorem lt_evr_of_selfVis_lt {k i : ℕ} {a x : ExtOrd} (ha : SelfVis k a) (hax : a < x) :
    a < extVisibilityReplace x k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · exact absurd hax not_lt_bot
  · assumption
  · rw [extVisibilityReplace_ofOrd]
    unfold visibilityReplace
    split_ifs with hβ
    · unfold ordinalReplace
      rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
      · simp
      · exact absurd hax not_top_lt
      · rw [selfVis_ofOrd_iff] at ha
        rw [ofOrd_lt_ofOrd] at hax ⊢
        apply lt_of_limitPart_lt
        rw [limitPart_limitPart_add_nat]
        by_contra hle
        have hle' : limitPart β ≤ limitPart α := not_lt.mp hle
        have h1 : limitPart β + (k : Ordinal) ≤ α :=
          calc limitPart β + (k : Ordinal) ≤ limitPart α + k := add_le_add_left hle' _
            _ ≤ limitPart α + (finitePart α : Ordinal) :=
              by simp_all
            _ = α := decomposition α
        have h2 : β < limitPart β + (k : Ordinal) := by
          conv_lhs => rw [← decomposition β]
          aesop
        grind
    · exact hax

/-- A replacement through `k ≤ K` of a value at most a `K`-visible `b` stays at most `b`. -/
theorem evr_le_of_le_selfVis {K k i : ℕ} {b x : ExtOrd} (hb : SelfVis K b) (hk : k ≤ K)
    (hi : i ≤ k) (hx : x ≤ b) : extVisibilityReplace x k i ≤ b :=
  extVisibilityReplace_le_of_le_selfVis hi (hb.mono hk) hx

/-- Cap agreement below a cap pins every value strictly below the cap. -/
theorem eq_of_capAgree_of_lt {x y γ : ExtOrd} (h : min x γ = min y γ) (hx : x < γ) : y = x := by grind

/-- Cap agreement below a cap and a value at least the cap force the other value at least the
cap. -/
theorem le_of_capAgree_of_le {x y γ : ExtOrd} (h : min x γ = min y γ) (hx : γ ≤ x) : γ ≤ y := by aesop

namespace CappedDonor

/-- **The floor cap** (audit16 (4)): floors built from cap-equivalent data are cap-equivalent. -/
theorem floor_min {b b' e e' γ : ExtOrd} (hb : min b' γ = min b γ) (he : min e' γ = min e γ) :
    min (max b' e') γ = min (max b e) γ := by grind

end CappedDonor

end VaughtConjecture.Knight
