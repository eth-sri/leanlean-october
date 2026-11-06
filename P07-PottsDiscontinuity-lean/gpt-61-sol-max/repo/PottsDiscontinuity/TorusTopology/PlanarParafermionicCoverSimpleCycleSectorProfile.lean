/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverPrimalCycleDirections
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSelectedCornerCoefficient
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSelectedCornerNeighbors
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleOrientation

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial


open SimpleGraph

section

variable {n : ℕ} {x : ParafermionicCoverBoxVertex n} (p : (parafermionicCoverBoxGraph n).Walk x x) (hp : p.IsCycle)
include hp

section

variable (v : ParafermionicCoverBoxVertex n) (hv : v ∈ p.support)


private theorem primalCycleRotate_isCycle 
     :
    (parafermionicCoverPrimalCycleRotate p v hv).IsCycle := by
  simp_all [parafermionicCoverPrimalCycleRotate]

private theorem primalCycleRotate_not_nil 
     :
    ¬ (parafermionicCoverPrimalCycleRotate p v hv).Nil := by
  have hlen := (primalCycleRotate_isCycle p hp v hv).three_le_length
  grind

end

section

variable (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) (k : ℤ) (hconst : ∀ d ∈ p.darts,
      parafermionicCoverFaceBoundaryCoefficient S d.fst d.snd = k) (v : ParafermionicCoverBoxVertex n) (hv : v ∈ p.support)
include hconst

private theorem primalCycle_selectedCoefficient_outgoing 
     :
    parafermionicCoverFaceBoundaryCoefficient S v
      (parafermionicCoverPrimalCycleRotate p v hv).snd = k := by
  let r := parafermionicCoverPrimalCycleRotate p v hv
  have hnil := primalCycleRotate_not_nil p hp v hv
  
  
  
  simpa  using  hconst (r.firstDart hnil) ((p.rotate_darts v hv).mem_iff.mp (r.firstDart_mem_darts hnil)) 

private theorem primalCycle_selectedCoefficient_incoming 
     :
    parafermionicCoverFaceBoundaryCoefficient S v
      (parafermionicCoverPrimalCycleRotate p v hv).penultimate = -k := by
  let r := parafermionicCoverPrimalCycleRotate p v hv
  have hnil := primalCycleRotate_not_nil p hp v hv
  
  
  
  have hlast : parafermionicCoverFaceBoundaryCoefficient S
      r.penultimate v = k := by simpa  using  hconst (r.lastDart hnil) ((p.rotate_darts v hv).mem_iff.mp (r.lastDart_mem_darts hnil)) 
  rw [parafermionicCoverFaceBoundaryCoefficient_antisymm]
  linarith

end

private theorem primalCycle_selectedCoefficient_nonzero_neighbor 
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (hcoeff : ∀ a b : ParafermionicCoverBoxVertex n,
      parafermionicCoverFaceBoundaryCoefficient S a b ≠ 0 ↔ s(a,b) ∈ p.edges)
    (v w : ParafermionicCoverBoxVertex n) (hv : v ∈ p.support)
    (h : parafermionicCoverFaceBoundaryCoefficient S v w ≠ 0) :
    w = (parafermionicCoverPrimalCycleRotate p v hv).snd ∨
      w = (parafermionicCoverPrimalCycleRotate p v hv).penultimate := by
  let r := parafermionicCoverPrimalCycleRotate p v hv
  
  
  
  have hmem  :=
    (r.toSubgraph.mem_neighborSet v w).mpr (r.adj_toSubgraph_iff_mem_edges.mpr ((p.rotate_edges v hv).mem_iff.mpr ((hcoeff v w).mp h)))
  rw [(primalCycleRotate_isCycle p hp v hv).neighborSet_toSubgraph_endpoint] at hmem
  simpa  using hmem

end

/-- At every vertex of the actual cycle, the selected-face sector boundary has
the single global orientation profile determined by its incoming and outgoing
travel directions. -/
theorem parafermionicCoverSimpleCycleSectorProfile {n : ℕ}
    (hn : 1 ≤ n) {x : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk x x) (hp : p.IsCycle) :
    ∃ k : ℤ, (k = -1 ∨ k = 1) ∧
      ∀ (v : ParafermionicCoverBoxVertex n) (hv : v ∈ p.support) (d : Fin 4),
          compassSectorBoundary
              (parafermionicCoverFiniteFaceSelectedCorners
                (parafermionicCoverSimpleCycleFillingSet hn p hp) v) d =
            if d = parafermionicCoverPrimalCycleOutgoingDirection p hp v hv then k
            else if d = parafermionicCoverPrimalCycleIncomingDirection p hp v hv + 2
              then -k else 0 := by
  
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  obtain ⟨k, hk, hconst⟩ :=
    parafermionicCoverSimpleCycleFilling_coefficient_orientation hn p hp
  have hspec := parafermionicCoverSimpleCycleFillingSet_spec hn p hp
  refine ⟨k, hk, ?_⟩
  intro v hv d
  let r := parafermionicCoverPrimalCycleRotate p v hv
  let din := parafermionicCoverPrimalCycleIncomingDirection p hp v hv
  let dout := parafermionicCoverPrimalCycleOutgoingDirection p hp v hv
  change compassSectorBoundary
      (parafermionicCoverFiniteFaceSelectedCorners S v) d =
    if d = dout then k else if d = din + 2 then -k else 0
  
  
  have hout : parafermionicCoverCompassNeighbor v.1 dout = r.snd.1 := by
    simpa  using
      parafermionicCoverPrimalCycleOutgoingDirection_neighbor p hp v hv
  have hprevAdj : parafermionicCoverGraph.Adj r.penultimate.1 v.1 := Walk.adj_penultimate (primalCycleRotate_not_nil p hp v hv)
  have hrevDir :
      parafermionicCoverCompassDirection v.1 r.penultimate.1 hprevAdj.symm = din + 2 := by
    simpa [din, parafermionicCoverPrimalCycleIncomingDirection] using
        parafermionicCoverCompassDirection_reverse r.penultimate.1 v.1 hprevAdj
  have hhin : parafermionicCoverCompassNeighbor v.1 (din + 2) = r.penultimate.1 := by
    have h := parafermionicCoverCompassDirection_neighbor v.1 r.penultimate.1 hprevAdj.symm
    rw [hrevDir] at h
    simpa  using h
  
  
  
  have houtCoeff : parafermionicCoverFaceBoundaryCoefficient S v r.snd = k := primalCycle_selectedCoefficient_outgoing p hp S k hconst v hv
  have hprevCoeff : parafermionicCoverFaceBoundaryCoefficient S v r.penultimate = -k := primalCycle_selectedCoefficient_incoming p hp S k hconst v hv
  by_cases hbox : parafermionicCoverCompassNeighbor v.1 d ∈
      parafermionicCoverBoxVertices n
  · let w : ParafermionicCoverBoxVertex n :=
      ⟨parafermionicCoverCompassNeighbor v.1 d, hbox⟩
    have hw : w.1 = parafermionicCoverCompassNeighbor v.1 d := rfl
    have hsector : compassSectorBoundary
        (parafermionicCoverFiniteFaceSelectedCorners S v) d =
          parafermionicCoverFaceBoundaryCoefficient S v w := by
      rw [parafermionicCoverFaceBoundaryCoefficient_eq_selectedCornerIndicators
        S v w d hw]
      rfl
    by_cases hdout : d = dout
    · simp_all
    · by_cases hdin : d = din + 2
      · simp_all
      · have hcoeffzero : parafermionicCoverFaceBoundaryCoefficient S v w = 0 := by
                                                                                   exact Decidable.byContradiction fun hnonzero =>
                                                                                           Or.casesOn (primalCycle_selectedCoefficient_nonzero_neighbor p hp S hspec.right.right v w hv hnonzero)
                                                                                             (fun hnext =>
                                                                                               hdout
                                                                                                 (parafermionicCoverCompassNeighbor_injective  ↑v 
                                                                                                   (Trans.trans (Trans.trans (Eq.symm hw) (congrArg Subtype.val hnext)) (Eq.symm hout))))
                                                                                             fun hprev =>
                                                                                             hdin
                                                                                               (parafermionicCoverCompassNeighbor_injective  ↑v 
                                                                                                 (Trans.trans (Trans.trans (Eq.symm hw) (congrArg Subtype.val hprev)) (Eq.symm hhin)))
        rw [hsector, hcoeffzero]
        simp [hdout, hdin]
  · have hmissing :=
      parafermionicCoverFiniteFaceSelectedCorners_missing_of_outside_neighbor
        S v d hbox
    have hdout : d ≠ dout := by
      grind
    have hdin : d ≠ din + 2 := by
      grind
    simp [compassSectorBoundary, hmissing.1, hmissing.2, hdout, hdin]

end PottsDiscontinuity.TorusTopology.Planar.Medial
