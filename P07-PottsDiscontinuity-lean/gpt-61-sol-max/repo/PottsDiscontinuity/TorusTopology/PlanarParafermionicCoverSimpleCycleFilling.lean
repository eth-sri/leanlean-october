/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceChainUniqueness
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceOrientedBoundary

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

private theorem coverCycle_spanningCoe_even_degree {n : ℕ}
    {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    ∀ v : ParafermionicCoverBoxVertex n,
      Even ((p.toSubgraph.spanningCoe).neighborSet v).ncard := by
  classical
  let H  := p.toSubgraph.spanningCoe
  
  intro v
  let q := p.transfer H (by
    aesop)
  have hqtrail : q.IsTrail := by
    simpa [q] using hp.isTrail
  
  
  have hdegree : Even (H.degree v) :=
    ((hqtrail.isEulerian_iff.mpr (by
                                                                  aesop)).even_degree_iff).2  fun huv => False.elim (huv rfl) 
  rw [← H.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] at hdegree
  exact hdegree

theorem parafermionicCoverSimpleCycle_unique_face_filling {n : ℕ}
    (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    ∃! S : Finset (ParafermionicCoverFiniteFaceTopIndex n),
      (∃ L : List (ParafermionicCoverFiniteFaceTopIndex n),
        L.Nodup ∧ L.toFinset = S ∧
          faceSymmDiffList
            (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) L =
              p.toSubgraph.spanningCoe) ∧
      S.Nonempty ∧
      ∀ a b : ParafermionicCoverBoxVertex n,
        parafermionicCoverFaceBoundaryCoefficient S a b ≠ 0 ↔
          s(a,b) ∈ p.edges := by
  
  let H  := p.toSubgraph.spanningCoe
  
  
  obtain ⟨S, hS, hSunique⟩ :=
    parafermionicCoverFiniteFaceChain_unique_representation hn H  p.toSubgraph.spanningCoe_le  (coverCycle_spanningCoe_even_degree p hp)
  obtain ⟨L, hL, hLS, hLH⟩ := hS
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hadj : H.Adj u p.snd := SimpleGraph.Walk.toSubgraph_adj_snd p (SimpleGraph.Walk.IsCycle.not_nil hp)
    rw [hbot] at hadj
    simp at hadj
  have hLne : L ≠ [] := by
    
    
    have hbottom : faceSymmDiffList
        (fun i : ParafermionicCoverFiniteFaceTopIndex n =>
          parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2)
         []  = ⊥ := by
      simp [faceSymmDiffList]
    grind
  have hSnonempty : S.Nonempty := by
    aesop
  
  refine ⟨S, ⟨⟨L, hL, hLS, hLH⟩, hSnonempty,  fun a b => by
                                                have hboundary := parafermionicCoverFaceBoundaryCoefficient_ne_zero_iff
                                                  S L hL hLS a b
                                                rw [hLH] at hboundary
                                                
                                                rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
                                                  SimpleGraph.Walk.edgeSet_toSubgraph] at hboundary
                                                exact hboundary ⟩, ?_⟩
  intro T hT
  have hTrep := hT.1
  
  exact  hSunique T hTrep 

end PottsDiscontinuity.TorusTopology.Planar.Medial

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

noncomputable def parafermionicCoverSimpleCycleFillingSet {n : ℕ}
    (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle)  :=
  Classical.choose (parafermionicCoverSimpleCycle_unique_face_filling hn p hp).exists

theorem parafermionicCoverSimpleCycleFillingSet_spec {n : ℕ}
    (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    (∃ L : List (ParafermionicCoverFiniteFaceTopIndex n),
      L.Nodup ∧ L.toFinset = parafermionicCoverSimpleCycleFillingSet hn p hp ∧
        faceSymmDiffList
          (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) L =
            p.toSubgraph.spanningCoe) ∧
    (parafermionicCoverSimpleCycleFillingSet hn p hp).Nonempty ∧
    ∀ a b : ParafermionicCoverBoxVertex n,
      parafermionicCoverFaceBoundaryCoefficient
          (parafermionicCoverSimpleCycleFillingSet hn p hp) a b ≠ 0 ↔
        s(a,b) ∈ p.edges := Classical.choose_spec
                        (parafermionicCoverSimpleCycle_unique_face_filling hn p hp).exists

end PottsDiscontinuity.TorusTopology.Planar.Medial
