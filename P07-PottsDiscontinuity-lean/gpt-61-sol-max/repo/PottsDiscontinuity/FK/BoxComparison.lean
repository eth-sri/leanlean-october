/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module
public import Mathlib

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

local instance boxComparisonSmallEdgeFintype (c : LatticeVertex) (r : ℕ) :
    Fintype (boxGraph c r).edgeSet := Fintype.ofFinite _
local instance boxComparisonLargeEdgeFintype (c : LatticeVertex) (r : ℕ) :
    Fintype (boxGraph c r).edgeSet := Fintype.ofFinite _


/-- The actual inclusion of vertex carriers induced by containment of boxes. -/
def boxVertexEmbedding {c d : LatticeVertex} {r s : ℕ}
    (hbox : latticeBox c r ⊆ latticeBox d s) : BoxVertex c r ↪ BoxVertex d s where
  toFun v := ⟨v.val, hbox v.property⟩
  inj' := by
    intro u v h
    all_goals simp_all

/-- The induced small graph maps into the actual induced large graph. -/
theorem boxGraph_map_boxVertexEmbedding {c d : LatticeVertex} {r s : ℕ}
    (hbox : latticeBox c r ⊆ latticeBox d s) :
    (boxGraph c r).map (boxVertexEmbedding hbox) ≤ boxGraph d s := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨u, v, huv, rfl, rfl⟩
  aesop

def boxCylinderEvent (c : LatticeVertex) (r : ℕ)
    (F : Finset squareLattice.edgeSet) : Set (Configuration (boxGraph c r)) :=
  {A | F ⊆ A.map (boxEdgeEmbedding c r)}

section

variable (c : LatticeVertex) (r : ℕ) (F : Finset squareLattice.edgeSet)
include c r F

private theorem boxCylinderEvent_upper  :
    IsUpperSet (boxCylinderEvent c r F) := fun A B hAB hA => hA.trans (Finset.map_subset_map.mpr hAB)

private theorem boxCylinderEvent_indicator_nonneg  :
    ∀ A, 0 ≤ (boxCylinderEvent c r F).indicator (fun _ => (1 : ℝ)) A := by
  
  intro A
  by_cases h : A ∈ boxCylinderEvent c r F <;> simp [h]

private theorem boxCylinderEvent_indicator_mono  :
    Monotone ((boxCylinderEvent c r F).indicator  fun _ => (1 : ℝ) ) := by
  intro A B hAB
  by_cases hA : A ∈ boxCylinderEvent c r F
  · have hB := boxCylinderEvent_upper c r F hAB hA
    simp_all
  · simpa [hA] using boxCylinderEvent_indicator_nonneg c r F B

end

section

variable {c d : LatticeVertex} {r s : ℕ} (hbox : latticeBox c r ⊆ latticeBox d s) (hGH : (boxGraph c r).map (boxVertexEmbedding hbox) ≤ boxGraph d s)
include hGH

private theorem boxEdgeEmbedding_compatible 
    (e : (boxGraph c r).edgeSet) :
    boxEdgeEmbedding d s (embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
      (boxVertexEmbedding hbox) hGH e) = boxEdgeEmbedding c r e := by
  apply Subtype.ext
  change Sym2.map (fun v  => v.val)
      (Sym2.map (boxVertexEmbedding hbox) e.val) =
    Sym2.map (fun v  => v.val) e.val
  rw [Sym2.map_map]
  congr 1

private theorem boxCylinderEvent_restrict_iff 
    (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (boxEdgeEmbedding c r))
    (A : Configuration (boxGraph d s)) :
    A ∈ boxCylinderEvent d s F ↔
      embeddedConfigurationRestriction (boxGraph c r) (boxGraph d s)
        (boxVertexEmbedding hbox) hGH A ∈ boxCylinderEvent c r F := by
  constructor
  · intro hA e he
    obtain ⟨x, hx⟩ := Set.mem_range.mp (hF e he)
    
    obtain ⟨y, hy, hye⟩ := Finset.mem_map.mp (hA he)
    have hcompat := boxEdgeEmbedding_compatible hbox hGH x
    have hyx : embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
        (boxVertexEmbedding hbox) hGH x = y := by
      
      grind
    
    
    apply Finset.mem_map.mpr
    exact ⟨x,  (mem_embeddedConfigurationRestriction _ _ _ _ A x).mpr (by rw [hyx]; exact hy) , hx⟩
  · intro hA e he
    obtain ⟨x, hx⟩ := Set.mem_range.mp (hF e he)
    
    obtain ⟨y, hy, hye⟩ := Finset.mem_map.mp (hA he)
    
    
    
    
    apply Finset.mem_map.mpr
    exact ⟨embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
      (boxVertexEmbedding hbox) hGH x, ((mem_embeddedConfigurationRestriction _ _ _ _ A x).mp (by rw [← ((boxEdgeEmbedding c r).injective (hye.trans hx.symm))]; exact hy)), (boxEdgeEmbedding_compatible hbox hGH x).trans hx⟩

end

private theorem boxCylinder_toReal_eq_expectation (q : Parameters)
    (c : LatticeVertex) (r : ℕ) (F : Finset squareLattice.edgeSet) :
     ((boxProbabilityMeasure q c r : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F)).toReal  =
      expectation (law (boxGraph c r) q (BoundaryCondition.free ∅))
        ((boxCylinderEvent c r F).indicator  fun _ => (1 : ℝ) ) := by
  rw [boxProbabilityMeasure_allOpen]
  rw [measure_toReal_eq_indicator_sum]
  
  apply Finset.sum_congr rfl
  intro A hA
  
  simp only [law_apply, ENNReal.toReal_ofReal (configurationProbability_pos (boxGraph c r) q (BoundaryCondition.free ∅) A).le]
  rfl

/-- Free FK all-open cylinder probabilities increase under containment of the
actual induced square boxes. The finite edge set may extend outside the smaller
box, in which case its smaller-box probability is zero. -/
theorem boxProbabilityMeasure_allOpen_mono (q : Parameters)
    (c d : LatticeVertex) (r s : ℕ)
    (hbox : latticeBox c r ⊆ latticeBox d s)
    (F : Finset squareLattice.edgeSet) :
    (boxProbabilityMeasure q c r : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F) ≤
      (boxProbabilityMeasure q d s : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F) := by
  
  let f := boxVertexEmbedding hbox
  have hGH : (boxGraph c r).map f ≤ boxGraph d s := boxGraph_map_boxVertexEmbedding hbox
  by_cases hF : ∀ e ∈ F, e ∈ Set.range (boxEdgeEmbedding c r)
  · have hcmp := embedded_free_expectation_le (boxGraph c r) (boxGraph d s) f hGH q
      ∅ ∅ ((boxCylinderEvent c r F).indicator  fun _ => 1 )
      (boxCylinderEvent_indicator_nonneg c r F) (boxCylinderEvent_indicator_mono c r F)
    have hleft := boxCylinder_toReal_eq_expectation q c r F
    have hright := boxCylinder_toReal_eq_expectation q d s F
    have hlarge :
        expectation (law (boxGraph d s) q (BoundaryCondition.free ∅))
          (fun A => (boxCylinderEvent c r F).indicator (fun _ => 1)
            (embeddedConfigurationRestriction (boxGraph c r) (boxGraph d s) f hGH A)) =
          expectation (law (boxGraph d s) q (BoundaryCondition.free ∅))
            ((boxCylinderEvent d s F).indicator  fun _ => 1 ) := by
      
      apply Finset.sum_congr rfl
      intro A hA
      have heq := boxCylinderEvent_restrict_iff hbox hGH F hF A
      by_cases h : A ∈ boxCylinderEvent d s F
      · aesop
      · aesop
    
    
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp (by
                                                                                     linarith)

  · push Not at hF
    obtain ⟨e, heF, heRange⟩ := hF
    
    rw [boxProbabilityMeasure_allOpen q c r F]
    change measure (boxGraph c r) q (BoundaryCondition.free ∅)
      (boxCylinderEvent c r F) ≤ _
    rw [(by
           ext A
           constructor
           · intro hA
             
             obtain ⟨a, ha, hEq⟩ := Finset.mem_map.mp (hA heF)
             exact heRange ⟨a, hEq⟩
           · simp : boxCylinderEvent c r F = ∅), measure_empty]
    exact bot_le

end
end PottsDiscontinuity.FK
