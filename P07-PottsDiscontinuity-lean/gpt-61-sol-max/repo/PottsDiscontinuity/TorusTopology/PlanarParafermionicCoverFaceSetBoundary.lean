/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceChainUniqueness
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceOrientedBoundary

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph
open scoped symmDiff

@[instance_reducible] noncomputable def coverFaceSetLocallyFinite
    {V : Type*} [Fintype V] (G : SimpleGraph V) : LocallyFinite G := fun v =>
  Fintype.ofInjective (fun x : G.neighborSet v => x.1) Subtype.val_injective

private theorem faceSymmDiffList_even_degree {V I : Type*} [Fintype V]
    [DecidableEq V] (F : I → SimpleGraph V)
    (hF : ∀ i v, Even ((F i).neighborSet v).ncard) :
    ∀ L : List I, ∀ v, Even ((faceSymmDiffList F L).neighborSet v).ncard := by
  intro L
  induction L with
  | nil =>
    simp_all [faceSymmDiffList]
  | cons i L ih =>
    intro v
    let : LocallyFinite (F i) := coverFaceSetLocallyFinite (F i)
    let : LocallyFinite (faceSymmDiffList F L) :=
      coverFaceSetLocallyFinite (faceSymmDiffList F L)
    let : LocallyFinite (F i ∆ faceSymmDiffList F L) :=
      coverFaceSetLocallyFinite (F i ∆ faceSymmDiffList F L)
    
    
    
    change Even ((F i ∆ faceSymmDiffList F L).neighborSet v).ncard
    simpa only [SimpleGraph.ncard_neighborSet] using  degree_even_symmDiff (F i) (faceSymmDiffList F L) (by
                                                                                                                           intro w
                                                                                                                           simpa only [SimpleGraph.ncard_neighborSet] using hF i w) (by
                                                                                                                               simp_all) v 

noncomputable def parafermionicCoverFiniteFaceSetBoundaryGraph {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    SimpleGraph (ParafermionicCoverBoxVertex n) :=
  faceSymmDiffList
    (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) S.toList

section

variable {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
include S

theorem parafermionicCoverFiniteFaceSetBoundaryGraph_even_degree  :
    ∀ v : ParafermionicCoverBoxVertex n,
      Even ((parafermionicCoverFiniteFaceSetBoundaryGraph S).neighborSet v).ncard := by
  
  intro v
  let F : ParafermionicCoverFiniteFaceTopIndex n →
      SimpleGraph (ParafermionicCoverBoxVertex n) :=
    fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2
  
  have h := faceSymmDiffList_even_degree F (by
                                              intro i v
                                              
                                              simpa only [parafermionicCoverFiniteFaceBoundaryDegree] using (parafermionicCoverFiniteFaceBoundaryGraph_even_degree i.1 i.2 v)) S.toList v
  simpa only [parafermionicCoverFiniteFaceSetBoundaryGraph] using h

theorem parafermionicCoverFiniteFaceSetBoundaryGraph_eq_bot_iff  :
    parafermionicCoverFiniteFaceSetBoundaryGraph S = ⊥ ↔ S = ∅ := by
  
  constructor
  · intro h
    
    
    rw [← Finset.toList_toFinset S]
    exact  parafermionicCoverFiniteFaceChain_toFinset_unique
             S.toList [] S.nodup_toList List.nodup_nil (h) 
  · simp_all [parafermionicCoverFiniteFaceSetBoundaryGraph, faceSymmDiffList]

theorem parafermionicCoverFiniteFaceSetBoundaryGraph_ne_bot_iff  :
    parafermionicCoverFiniteFaceSetBoundaryGraph S ≠ ⊥ ↔ S.Nonempty := by
  grind [parafermionicCoverFiniteFaceSetBoundaryGraph_eq_bot_iff]

theorem parafermionicCoverFiniteFaceSetBoundaryGraph_coefficient_ne_zero_iff
    
    (u v : ParafermionicCoverBoxVertex n) :
    parafermionicCoverFaceBoundaryCoefficient S u v ≠ 0 ↔
      s(u,v) ∈ (parafermionicCoverFiniteFaceSetBoundaryGraph S).edgeSet := by
  
  
  exact parafermionicCoverFaceBoundaryCoefficient_ne_zero_iff
    S S.toList S.nodup_toList (by simp) u v

end

end PottsDiscontinuity.TorusTopology.Planar.Medial
