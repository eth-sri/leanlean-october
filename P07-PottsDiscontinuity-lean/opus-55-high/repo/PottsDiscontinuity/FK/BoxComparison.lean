/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.BoxCylinders
public import PottsDiscontinuity.FK.IncreasingEvents
public import PottsDiscontinuity.FK.SubgraphComparison

/-!
# Monotonicity of free box all-open cylinder probabilities

The comparison is on the actual induced graphs. A smaller box configuration is
read from the larger sample along the vertex embedding, preserving the original
lattice edges and their states.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open MeasureTheory FiniteProbability
noncomputable section

local instance boxComparisonLargeEdgeFintype (c : LatticeVertex) (r : ℕ) :
    Fintype (boxGraph c r).edgeSet := Fintype.ofFinite _

section
variable {c d : LatticeVertex} {r s : ℕ} (hbox : latticeBox c r ⊆ latticeBox d s)
/-- The actual inclusion of vertex carriers induced by containment of boxes. -/
def boxVertexEmbedding  : BoxVertex c r ↪ BoxVertex d s where
  toFun v := ⟨v.val, hbox v.property⟩
  inj' := by
    intro u v h
    simp_all

/-- The induced small graph maps into the actual induced large graph. -/
theorem boxGraph_map_boxVertexEmbedding  :
    (boxGraph c r).map (boxVertexEmbedding hbox) ≤ boxGraph d s := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨u, v, huv, rfl, rfl⟩
  tauto
end

section
variable (c : LatticeVertex) (r : ℕ) (F : Finset squareLattice.edgeSet)
def boxCylinderEvent  : Set (Configuration (boxGraph c r)) :=
  {A | F ⊆ A.map (boxEdgeEmbedding c r)}

theorem boxCylinderEvent_upper  :
    IsUpperSet (boxCylinderEvent c r F) := by
  intro A B hAB hA
  exact hA.trans (Finset.map_subset_map.mpr hAB)

theorem boxCylinderEvent_indicator_nonneg  :
    ∀ A, 0 ≤ (boxCylinderEvent c r F).indicator (fun _ => (1 : ℝ)) A := by
  grind [boxCylinderEvent, Set.indicator]

theorem boxCylinderEvent_indicator_mono  :
    Monotone ((boxCylinderEvent c r F).indicator (fun _ => (1 : ℝ))) := by
  intro A B hAB
  by_cases hA : A ∈ boxCylinderEvent c r F
  · have hB := boxCylinderEvent_upper c r F hAB hA
    simp_all
  simp_all [boxCylinderEvent_indicator_nonneg]
end

section
variable {c d : LatticeVertex} {r s : ℕ} (hbox : latticeBox c r ⊆ latticeBox d s) (hGH : (boxGraph c r).map (boxVertexEmbedding hbox) ≤ boxGraph d s)
theorem boxEdgeEmbedding_compatible (e : (boxGraph c r).edgeSet) :
    boxEdgeEmbedding d s (embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
      (boxVertexEmbedding hbox) hGH e) = boxEdgeEmbedding c r e := by
  apply Subtype.ext
  change Sym2.map (fun v : BoxVertex d s => v.val)
      (Sym2.map (boxVertexEmbedding hbox) e.val) =
    Sym2.map (fun v : BoxVertex c r => v.val) e.val
  rw [Sym2.map_map]
  rfl

theorem boxCylinderEvent_restrict_iff (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (boxEdgeEmbedding c r))
    (A : Configuration (boxGraph d s)) :
    A ∈ boxCylinderEvent d s F ↔
      embeddedConfigurationRestriction (boxGraph c r) (boxGraph d s)
        (boxVertexEmbedding hbox) hGH A ∈ boxCylinderEvent c r F := by
  constructor
  · intro hA e he
    obtain ⟨x, hx⟩ := Set.mem_range.mp (hF e he)
    have heOpen := hA he
    have hcompat := boxEdgeEmbedding_compatible hbox hGH x
    have hy' : embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
        (boxVertexEmbedding hbox) hGH x ∈ A := by grind
    have hrestrict := (mem_embeddedConfigurationRestriction _ _ _ _ A x).mpr hy'
    apply Finset.mem_map.mpr
    tauto
  · intro hA e he
    obtain ⟨x, hx⟩ := Set.mem_range.mp (hF e he)
    have heOpen := hA he
    have hrestrict : x ∈ embeddedConfigurationRestriction (boxGraph c r) (boxGraph d s)
        (boxVertexEmbedding hbox) hGH A := by grind
    have hcompat := boxEdgeEmbedding_compatible hbox hGH x
    apply Finset.mem_map.mpr
    exact ⟨embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
      (boxVertexEmbedding hbox) hGH x, ((mem_embeddedConfigurationRestriction _ _ _ _ A x).mp hrestrict), hcompat.trans hx⟩
end

section
variable (q : Parameters)
theorem boxCylinder_toReal_eq_expectation (c : LatticeVertex) (r : ℕ) (F : Finset squareLattice.edgeSet) :
    (((boxProbabilityMeasure q c r : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F)).toReal) =
      expectation (law (boxGraph c r) q (BoundaryCondition.free ∅))
        ((boxCylinderEvent c r F).indicator (fun _ => (1 : ℝ))) := by
  rw [boxProbabilityMeasure_allOpen, measure_toReal_eq_indicator_sum]
  apply Finset.sum_congr rfl
  intro A hA
  have hp := configurationProbability_pos (boxGraph c r) q (BoundaryCondition.free ∅) A
  simp only [law_apply, ENNReal.toReal_ofReal hp.le]
  rfl

/-- Free FK all-open cylinder probabilities increase under containment of the
actual induced square boxes. The finite edge set may extend outside the smaller
box, in which case its smaller-box probability is zero. -/
theorem boxProbabilityMeasure_allOpen_mono (c d : LatticeVertex) (r s : ℕ)
    (hbox : latticeBox c r ⊆ latticeBox d s)
    (F : Finset squareLattice.edgeSet) :
    (boxProbabilityMeasure q c r : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F) ≤
      (boxProbabilityMeasure q d s : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F) := by
  let f := boxVertexEmbedding hbox
  have hGH := boxGraph_map_boxVertexEmbedding hbox
  by_cases hF : ∀ e ∈ F, e ∈ Set.range (boxEdgeEmbedding c r)
  · have hcmp := embedded_free_expectation_le (boxGraph c r) (boxGraph d s) f hGH q
      ∅ ∅ ((boxCylinderEvent c r F).indicator (fun _ => (1 : ℝ)))
      (boxCylinderEvent_indicator_nonneg c r F) (boxCylinderEvent_indicator_mono c r F)
    have hleft := boxCylinder_toReal_eq_expectation q c r F
    have hright := boxCylinder_toReal_eq_expectation q d s F
    have hlarge :
        expectation (law (boxGraph d s) q (BoundaryCondition.free ∅))
          (fun A => (boxCylinderEvent c r F).indicator (fun _ => (1 : ℝ))
            (embeddedConfigurationRestriction (boxGraph c r) (boxGraph d s) f hGH A)) =
          expectation (law (boxGraph d s) q (BoundaryCondition.free ∅))
            ((boxCylinderEvent d s F).indicator (fun _ => (1 : ℝ))) := by
      apply Finset.sum_congr rfl
      intro A hA
      have heq := boxCylinderEvent_restrict_iff hbox hGH F hF A
      by_cases h : A ∈ boxCylinderEvent d s F <;> grind [embeddedConfigurationRestriction, boxGraph, boxCylinderEvent, Set.indicator]
    have hreal :
        (((boxProbabilityMeasure q c r : Measure LatticeConfiguration)
          (LatticeConfiguration.allOpen F)).toReal) ≤
        (((boxProbabilityMeasure q d s : Measure LatticeConfiguration)
          (LatticeConfiguration.allOpen F)).toReal) := by
      linarith
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

  · push Not at hF
    obtain ⟨e, heF, heRange⟩ := hF
    have hempty : boxCylinderEvent c r F = ∅ := by
      ext A
      constructor
      · intro hA
        obtain ⟨a, ha, hEq⟩ := Finset.mem_map.mp (hA heF)
        tauto
      simp
    rw [boxProbabilityMeasure_allOpen q c r F]
    change measure (boxGraph c r) q (BoundaryCondition.free ∅)
      (boxCylinderEvent c r F) ≤ _
    rw [hempty, measure_empty]
    simp
end

end
end PottsDiscontinuity.FK
