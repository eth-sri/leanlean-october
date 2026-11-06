module
public import Mathlib

public import PottsDiscontinuity.FK.ProbabilityProduct
public import PottsDiscontinuity.TorusLoops.RectangleLaw
public import PottsDiscontinuity.TorusRC.IndexedGraphBridge

/-! # The large-period torus law as an ordinary finite FK law -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open MeasureTheory Torus

attribute [local instance] FK.configurationMeasurableSpace

variable {N M : ℕ}

noncomputable section

local instance torusBridgeEdgeFintype (hN : Even N) (hM : Even M) :
    Fintype (fullDiamondGraph hN hM).edgeSet := Fintype.ofFinite _

/-- The free FK parameters corresponding to the critical torus parameter. -/
def torusRCBridgeParameters (q : Set.Ici (1 : ℝ))  :=
  torusRCFKParameters q

section

variable (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
include hN4 hM4

/-- Reindexing the torus PMF by the unique indexed-edge/simple-edge
equivalence gives the free finite FK PMF on the diamond torus. -/
theorem torusRCPMF_map_edgeEquiv  :
    (torusRCPMF hN hM q).map (torusRCConfigurationEquiv hN hM hN4 hM4) =
      FK.law (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
        (FK.BoundaryCondition.free ∅) := FK.FiniteProbability.pmf_map_equiv_of_weight_eq (torusRCConfigurationEquiv hN hM hN4 hM4) (torusRCWeight hN hM q)
                                           (FK.weight (fullDiamondGraph hN hM) (torusRCBridgeParameters q) (FK.BoundaryCondition.free ∅))
                                           (torusRCWeight_pos hN hM q)
                                           (FK.weight_pos (fullDiamondGraph hN hM) (torusRCBridgeParameters q) (FK.BoundaryCondition.free ∅))
                                           (torusRCWeight_eq_fk_weight hN hM hN4 hM4 q)

/-- The indexed and graph partition functions agree under the edge bijection. -/
theorem torusRCPartition_eq_fk  :
    torusRCPartition hN hM q =
      FK.partitionFunction (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
        (FK.BoundaryCondition.free ∅) := let e := torusRCConfigurationEquiv hN hM hN4 hM4;
                                         Trans.trans (Finset.sum_congr rfl fun A a => torusRCWeight_eq_fk_weight hN hM hN4 hM4 q A)
                                           (Equiv.sum_comp e (FK.weight (fullDiamondGraph hN hM) (torusRCBridgeParameters q) (FK.BoundaryCondition.free ∅)))

/-- Every indexed configuration mass is the free FK configuration mass after
the unique edge reindexing. -/
theorem torusRCMass_eq_fk_configurationProbability 
    (A : RCConfig N M) :
    torusRCMass hN hM q A =
      FK.configurationProbability (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
        (FK.BoundaryCondition.free ∅)
        (torusRCConfigurationEquiv hN hM hN4 hM4 A) := by
  rw [torusRCMass, torusRCWeight_eq_fk_weight hN hM hN4 hM4 q A, torusRCPartition_eq_fk hN hM hN4 hM4 q]
  rfl

/-- The torus probability measure is the image of the periodic free-boundary
FK measure under the edge-indexing equivalence. -/
theorem torusRCMeasure_map_edgeEquiv  :
    Measure.map (torusRCConfigurationEquiv hN hM hN4 hM4)
        (torusRCMeasure hN hM q) =
      FK.measure (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
        (FK.BoundaryCondition.free ∅) := by
  
  have hmeasure := congrArg
    ((@PMF.toMeasure _ (FK.configurationMeasurableSpace (fullDiamondGraph hN hM)))) (torusRCPMF_map_edgeEquiv hN hM hN4 hM4 q)
  rw [← PMF.toMeasure_map _ _  Measurable.of_discrete ] at hmeasure
  aesop

/-- Event probabilities transport exactly through the indexed-edge equivalence. -/
theorem torusRCProbability_eq_fk_image 
    (E : Set (RCConfig N M)) :
    torusRCProbability hN hM q E =
      (FK.measure (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
        (FK.BoundaryCondition.free ∅)).real
        (torusRCConfigurationEquiv hN hM hN4 hM4 '' E) := by
  rw [← torusRCMeasure_map_edgeEquiv hN hM hN4 hM4 q]
  unfold torusRCProbability Measure.real
  rw [Measure.map_apply  Measurable.of_discrete  MeasurableSpace.measurableSet_top]
  simp_all

end

end

end PottsDiscontinuity.TorusRC
