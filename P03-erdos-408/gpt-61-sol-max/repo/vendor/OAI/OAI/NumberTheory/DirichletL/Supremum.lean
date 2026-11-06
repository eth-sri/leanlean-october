module
public import Mathlib.Tactic

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace OAI

namespace SevenEighths.Supremum

noncomputable section

def continuationMargin (β ω σ : ℝ)  := min (β - 7 / 8 - ω) σ

section
variable {β ω σ : ℝ} {S : Set ℝ} (hne : S.Nonempty) (hbounded : BddAbove S) {a ε : ℝ}


theorem continuationMargin_pos  
    (hω : ω < β - 7 / 8) (hσ : 0 < σ) :
    0 < continuationMargin β ω σ := lt_min (sub_pos.mpr hω) hσ

theorem continuationMargin_le_gap  β ω σ  :
    continuationMargin β ω σ ≤ β - 7 / 8 - ω :=
  min_le_left _ _

theorem continuation_boundary_gt   (hω : 0 < ω) :
    7 / 8 < β - continuationMargin β ω σ := by
  have h := continuationMargin_le_gap β ω σ
  linarith

theorem max_signal_exponents  β ω σ c  :
    max (7 / 8 + c + ω) (β + c - σ) =
      β + c - continuationMargin β ω σ := by
  grind [continuationMargin]

include hne hbounded in
theorem exists_gt_supremum_sub    
        (hε : 0 < ε) :
    ∃ x ∈ S, sSup S - ε < x := by
  apply (lt_csSup_iff hbounded hne).mp
  linarith

theorem exists_gt_supremum_sub_of_insert    
    (hbounded : BddAbove (insert a S)) (hε : 0 < ε)
    (ha : a ≤ sSup (insert a S) - ε) :
    ∃ x ∈ S, sSup (insert a S) - ε < x := by
  obtain ⟨x, hx, hlt⟩ :=
    exists_gt_supremum_sub (Set.insert_nonempty a S) hbounded hε
  grind

end

end

end SevenEighths.Supremum

end OAI
