module
public import Mathlib

public import PottsDiscontinuity.FK.ComponentSupermodular
public import PottsDiscontinuity.Torus.RibbonConnectivity

/-!
# Connectivity and supermodularity for the indexed torus configurations

The map to simple-graph edge sets is used only for connectivity. It need not
be injective: loops and parallel indexed edges remain distinct in the weight.
-/

@[expose] public section

open Finset

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

/-- The underlying simple connectivity graph, with every indexed edge open. -/
def fullDiamondGraph (hN : Even N) (hM : Even M)  :=
  diamondOpenGraph hN hM true  fun _ => true 

/-- Forget multiplicity and loops only when computing open connectivity. -/
noncomputable def simpleConfiguration (hN : Even N) (hM : Even M)
    (A : RCConfig N M) : FK.Configuration (fullDiamondGraph hN hM) := by
  classical
  exact univ.filter fun e => ∃ v, A v = true ∧
    e.val = s(faceEndpoint hN hM true v false, faceEndpoint hN hM true v true)

section

variable (hN : Even N) (hM : Even M)
include hN hM

theorem openGraph_simpleConfiguration 
    (A : RCConfig N M) :
    FK.openGraph (fullDiamondGraph hN hM) (simpleConfiguration hN hM A) =
      diamondOpenGraph hN hM true A := by
  classical
  ext u v
  rw [FK.openGraph_adj]
  constructor
  · rintro ⟨e, he, heq⟩
    obtain ⟨i, hi, hie⟩ := (mem_filter.mp he).2
    
    exact ⟨⟨i, hi, heq.symm.trans hie⟩,  (fullDiamondGraph hN hM).mem_edgeSet.mp
                                           (by rw [← heq]; exact e.property) |>.ne ⟩
  · rintro ⟨⟨i, hi, hie⟩, huv⟩
    
    refine ⟨⟨s(u,v),  by
                        rw [SimpleGraph.mem_edgeSet, fullDiamondGraph, diamondOpenGraph,
                          SimpleGraph.fromEdgeSet_adj]
                        grind ⟩, mem_filter.mpr ⟨mem_univ _, ⟨i, hi, hie⟩⟩, rfl⟩

theorem clusterCount_eq_componentCount 
    (A : RCConfig N M) :
    clusterCount hN hM true A = FK.componentCount (fullDiamondGraph hN hM)
      (FK.BoundaryCondition.free ∅) (simpleConfiguration hN hM A) := by
  rw [FK.componentCount, FK.componentSetoid_free, openGraph_simpleConfiguration]
  rfl

theorem simpleConfiguration_mono 
    {A B : RCConfig N M} (hAB : A ≤ B) :
    simpleConfiguration hN hM A ⊆ simpleConfiguration hN hM B := by
  classical
  intro e he
  obtain ⟨i, hi, hie⟩ := (mem_filter.mp he).2
  
  exact mem_filter.mpr ⟨mem_univ _, ⟨i,  by
                                           aesop , hie⟩⟩

section

variable (A B : RCConfig N M)


theorem simpleConfiguration_sup 
     :
    simpleConfiguration hN hM (A ⊔ B) =
      simpleConfiguration hN hM A ∪ simpleConfiguration hN hM B := by
  
  ext e
  simp only [simpleConfiguration, mem_filter, mem_univ, true_and, mem_union]
  constructor
  · aesop
  · aesop

theorem simpleConfiguration_inf_subset 
     :
    simpleConfiguration hN hM (A ⊓ B) ⊆
      simpleConfiguration hN hM A ∩ simpleConfiguration hN hM B :=
  subset_inter (simpleConfiguration_mono hN hM inf_le_left)
    (simpleConfiguration_mono hN hM inf_le_right)

/-- The indexed component count is supermodular even for small periods.
Forgetting parallel edges preserves unions but only gives an inclusion for
intersections; component-count antitonicity has the required direction. -/
theorem clusterCount_supermodular 
     :
    clusterCount hN hM true A + clusterCount hN hM true B ≤
      clusterCount hN hM true (A ⊓ B) + clusterCount hN hM true (A ⊔ B) := by
  
  simp only [clusterCount_eq_componentCount, simpleConfiguration_sup]
  have h := FK.componentCount_supermodular (FK.BoundaryCondition.free ∅)
    (simpleConfiguration hN hM A) (simpleConfiguration hN hM B)
  have hm := FK.componentCount_antitone (G := fullDiamondGraph hN hM)
    (FK.BoundaryCondition.free ∅) (simpleConfiguration_inf_subset hN hM A B)
  omega

end

end

end PottsDiscontinuity.TorusRC
