module

public import PottsDiscontinuity.Potts.WiredGhostRelation
public import PottsDiscontinuity.Potts.ConditionedOuterLaw

/-! The conditioned outer law preserves the full marked ghost connection data. -/

public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace
local instance connectionBoundaryFintype (n : ℕ) : Fintype (BoundaryVertex (box n)) := Fintype.ofFinite _
local instance connectionOuterEdgeFintype (n : ℕ) : Fintype (OuterBoxEdge n) := Fintype.ofFinite _

/-- Every state in the conditioning event has a unique literal/shell decomposition. -/
theorem outerClosed_eq_restore (n : ℕ) (hn : 0 < n) (Ω : OuterBoxEdge n → Bool)
    (hΩ : outerCornerClosed n Ω) :
    restoreGhostBonds n hn (readLiteralBonds n Ω) (fun e : OuterShellEdge n => Ω e.val) = Ω := by
  have h := (outerBondEquiv n hn).left_inv Ω
  change restoreOuterBonds n hn (readLiteralBonds n Ω) (fun b => Ω (cornerCutEdge n b))
    (fun e => Ω e.val) = Ω at h
  have hc : (fun b => Ω (cornerCutEdge n b)) = fun _ => false := by aesop
  aesop

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
  have hid := ghost_expectation_eq_conditioned_wired_box q hq β hβ n hn
    (fun ω => if ω ∈ T then (1 : ℝ) else 0)
  rw [← hid]
  change (FK.measure _ (fkParameters q hq β hβ) (outerBoxWiring n)
      (S ∩ cornerClosureEvent n)).toReal /
    (FK.measure _ (fkParameters q hq β hβ) (outerBoxWiring n) (cornerClosureEvent n)).toReal = _
  rw [fk_measureReal_eq_bool_sum, fk_measureReal_eq_bool_sum]
  apply congrArg₂ (fun (a : ℝ) (b : ℝ) => a / b)
  · apply Finset.sum_congr
    · ext Ω; simp
    · intro Ω _
      have hp := FK.configurationProbability_eq_rcProb (fkParameters q hq β hβ) (box (n + 1)) 1 Ω
      change FK.configurationProbability _ _ (outerBoxWiring n) _ = _ at hp
      by_cases hB : outerCornerClosed n Ω
      · have hb := (outerCornerClosed_iff_mem n Ω).mp hB
        have hst : FK.boolConfigurationEquiv _ Ω ∈ S ↔ readLiteralBonds n Ω ∈ T := by
          rw [← outerClosed_eq_restore n hn Ω hB, readLiteralBonds_restore]
          simp_all
        simp_all
      · have hb := mt (outerCornerClosed_iff_mem n Ω).mpr hB
        simp_all
  · apply Finset.sum_congr
    · ext Ω; simp
    · intro Ω _
      have hp := FK.configurationProbability_eq_rcProb (fkParameters q hq β hβ) (box (n + 1)) 1 Ω
      change FK.configurationProbability _ _ (outerBoxWiring n) _ = _ at hp
      rw [hp]
      by_cases hB : outerCornerClosed n Ω
      · simp [hB, (outerCornerClosed_iff_mem n Ω).mp hB]
      · simp [hB, mt (outerCornerClosed_iff_mem n Ω).mpr hB]

theorem collapseOuterGhost_projection (n : ℕ) (a : Option (ℤ × ℤ)) :
    collapseOuterGhost n (boxGhostProjection (n + 1) a) = boxGhostProjection n a := by
  cases a with
  | none => rfl
  | some x =>
    grind [box, boxGhostProjection, collapseOuterGhost, collapseOuterBox]

end
end PottsDiscontinuity.Potts
