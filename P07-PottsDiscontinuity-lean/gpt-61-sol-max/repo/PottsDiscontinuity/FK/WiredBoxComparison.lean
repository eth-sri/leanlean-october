/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
The comparison is reversed for wired boundaries and open exterior extension.
The interior-closure and outer-boundary avoidance proofs are original. -/
module
public import Mathlib

public import PottsDiscontinuity.FK.WiredBoxLaw
public import PottsDiscontinuity.FK.BoxComparison
public import PottsDiscontinuity.FK.EmbeddedClosedInteriorOuterComparison

/-! Wired box laws decrease on increasing cylinder events as the domain grows. -/

@[expose] public section

namespace PottsDiscontinuity.FK

open MeasureTheory
noncomputable section

section

variable {c d : LatticeVertex} {r s : ℕ} (hbox : latticeBox c r ⊆ latticeBox d s)
include hbox

section

variable {x : BoxVertex c r} (hx : x ∉ boxVertexBoundary c r)
include hx

private theorem boxInterior_neighbor_closed 
    
    {y : BoxVertex d s} (hxy : (boxGraph d s).Adj (boxVertexEmbedding hbox x) y) :
    ∃ z : BoxVertex c r, boxVertexEmbedding hbox z = y ∧ (boxGraph c r).Adj x z := have hy := Decidable.byContradiction fun hn => hx ⟨x.property, Exists.intro ↑y ⟨hxy, hn⟩⟩;
                                                                                   Exists.intro ⟨↑y, hy⟩ ⟨Subtype.ext rfl, hxy⟩

private theorem boxInterior_avoids_outerBoundary 
     :
    boxVertexEmbedding hbox x ∉
      (BoundaryCondition.wired (boxVertexBoundary d s)).boundary := by
  rintro ⟨_, y, hxy, hy⟩
  apply hx
  exact ⟨x.property, y, hxy, fun hys => hy (hbox hys)⟩

end

section

variable (hGH : (boxGraph c r).map (boxVertexEmbedding hbox) ≤ boxGraph d s)


private theorem wiredBoxEdgeEmbedding_compatible 
    
    (e : (boxGraph c r).edgeSet) :
    boxEdgeEmbedding d s (embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
      (boxVertexEmbedding hbox) hGH e) = boxEdgeEmbedding c r e := by
  apply Subtype.ext
  change Sym2.map (fun v  => v.val)
      (Sym2.map (boxVertexEmbedding hbox) e.val) =
    Sym2.map (fun v  => v.val) e.val
  rw [Sym2.map_map]
  congr 1

private theorem wiredBoxCylinderEvent_restrict_of_large
    
    
    (F : Finset squareLattice.edgeSet) (A : Configuration (boxGraph d s))
    (hA : A ∈ wiredBoxCylinderEvent d s F) :
    embeddedConfigurationRestriction (boxGraph c r) (boxGraph d s)
      (boxVertexEmbedding hbox) hGH A ∈ wiredBoxCylinderEvent c r F := by
  intro e he f hf
  rw [mem_embeddedConfigurationRestriction]
  exact hA e he
    (embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s) (boxVertexEmbedding hbox) hGH f)
    ((wiredBoxEdgeEmbedding_compatible hbox hGH f).trans hf)

end

end

/-- Wired all-open cylinder probabilities decrease under box containment.
Open exterior extension makes this valid even before the cylinder lies inside
the smaller finite volume. -/
theorem wiredBoxProbabilityMeasure_allOpen_antitone (θ : Parameters)
    (c d : LatticeVertex) (r s : ℕ)
    (hbox : latticeBox c r ⊆ latticeBox d s) (F : Finset squareLattice.edgeSet) :
    (wiredBoxProbabilityMeasure θ d s : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F) ≤
      (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F) := by
  
  
  have hGH  := boxGraph_map_boxVertexEmbedding hbox
  
  
  rw [wiredBoxProbabilityMeasure_allOpen, wiredBoxProbabilityMeasure_allOpen]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono  fun A hA => wiredBoxCylinderEvent_restrict_of_large hbox hGH F A hA )).trans (embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
                                                                                                                                                 (boxVertexEmbedding hbox) hGH θ (BoundaryCondition.wired (boxVertexBoundary d s)) (boxVertexBoundary c r)
                                                                                                                                                 (fun _ hx _ hxy => boxInterior_neighbor_closed hbox hx hxy)
                                                                                                                                                 (fun _ hx => boxInterior_avoids_outerBoundary hbox hx)
                                                                                                                                                 (wiredBoxCylinderEvent c r F) (wiredBoxCylinderEvent_upper c r F))

end
end PottsDiscontinuity.FK
