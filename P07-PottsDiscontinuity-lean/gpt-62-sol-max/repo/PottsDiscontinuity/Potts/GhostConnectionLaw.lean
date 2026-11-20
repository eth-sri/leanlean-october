module

public import PottsDiscontinuity.Potts.WiredGhostRelation
public import PottsDiscontinuity.Potts.ConditionedOuterLaw
public import PottsDiscontinuity.Potts.GhostBoxLaw
public import PottsDiscontinuity.Potts.BoolMeasureBridge

/-! The conditioned outer law preserves the full marked ghost connection data. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace
local instance connectionBoundaryFintype (n : ℕ) : Fintype (BoundaryVertex (box n)) := Fintype.ofFinite _
local instance connectionOuterEdgeFintype (n : ℕ) : Fintype (OuterBoxEdge n) := Fintype.ofFinite _

set_option maxHeartbeats 1200000 in
/-- Every event whose restored value is determined by the literal bonds has
its exact ghost-law probability under the conditioned outer law. -/
theorem conditionedOuterLaw_event_eq_ghost
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) (n : ℕ) (hn : 0 < n)
    (S : Set (FK.Configuration (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ)))))
    (T : Set (LiteralBond (box n) → Bool))
    (hST : ∀ ω η, FK.boolConfigurationEquiv _ (restoreGhostBonds n hn ω η) ∈ S ↔ ω ∈ T) :
    (conditionedOuterLaw (fkParameters q hq β hβ) n).toMeasure.real S =
      ∑ ω, ghostRCProbability q (box n) β ω * (if ω ∈ T then 1 else 0) := by
  change ((FK.law _ (fkParameters q hq β hβ) (outerBoxWiring n)).filter _ _).toMeasure.real S = _
  rw [finite_filter_measureReal]
  change (FK.measure _ (fkParameters q hq β hβ) (outerBoxWiring n) (S ∩ cornerClosureEvent n)).toReal /
    (FK.measure _ (fkParameters q hq β hβ) (outerBoxWiring n) (cornerClosureEvent n)).toReal = _
  rw [fk_measureReal_eq_bool_weight_sum, fk_measureReal_eq_bool_weight_sum,
    div_div_div_cancel_right₀ (FK.partitionFunction_pos _ _ _).ne']
  have hite (P Q : Prop) [Decidable P] [Decidable Q] [Decidable (P ∧ Q)] (w : ℝ) :
      (if P ∧ Q then w else 0) = if Q then w * (if P then 1 else 0) else 0 := by
    split <;> split <;> simp_all
  simp_rw [Set.mem_inter_iff, ← outerCornerClosed_iff_mem n, hite]
  have hs := sum_outerCornerClosed_weight_test q hq β hβ n hn
    (fun Ω => if FK.boolConfigurationEquiv _ Ω ∈ S then 1 else 0) (fun ω => if ω ∈ T then 1 else 0)
    (fun ω η => if_congr (hST ω η) rfl rfl)
  have hd := sum_outerCornerClosed_weight_test q hq β hβ n hn (fun _ => 1) (fun _ => 1) (fun _ _ => rfl)
  simp only [mul_one] at hd
  trans ((q : ℝ) * Real.exp (-β) ^ 4) * (∑ ω, ghostRCWeight q (box n) β ω * (if ω ∈ T then 1 else 0)) /
    (((q : ℝ) * Real.exp (-β) ^ 4) * ghostRCPartition q (box n) β)
  · apply congrArg₂ (fun x y : ℝ => x / y)
    · refine Eq.trans ?_ hs
      exact Finset.sum_congr (by ext Ω; simp) (fun _ _ => rfl)
    · refine Eq.trans ?_ (hd.trans ?_)
      · exact Finset.sum_congr (by ext Ω; simp only [Finset.mem_univ]) (fun _ _ => rfl)
      · unfold ghostRCPartition
        apply congrArg (fun x : ℝ => (q : ℝ) * Real.exp (-β) ^ 4 * x)
        exact Finset.sum_congr (by ext ω; simp only [Finset.mem_univ]) (fun _ _ => rfl)
  · rw [mul_div_mul_left _ _ (by positivity : (q : ℝ) * Real.exp (-β) ^ 4 ≠ 0)]
    simp_rw [ghostRCProbability, div_mul_eq_mul_div, ← Finset.sum_div]

theorem collapseOuterGhost_projection (n : ℕ) (a : Option (ℤ × ℤ)) :
    collapseOuterGhost n (boxGhostProjection (n + 1) a) = boxGhostProjection n a := by
  cases a with
  | none => rfl
  | some x =>
    by_cases hx : x ∈ box n
    · have hxo := box_subset_box_succ n hx
      simp [boxGhostProjection, collapseOuterGhost, collapseOuterBox, hx, hxo]
    · by_cases hxo : x ∈ box (n + 1) <;>
        simp [boxGhostProjection, collapseOuterGhost, collapseOuterBox, hx, hxo]

end
end PottsDiscontinuity.Potts
