module
public import Mathlib

public import PottsDiscontinuity.TorusExploration.ExteriorConfig
public import PottsDiscontinuity.TorusExploration.SeamClosureWinding
public import PottsDiscontinuity.TorusExploration.CylinderIntersectionZero

/-! A bottom-to-top cluster cuts every horizontal winding cycle of its
cylinder complement. No assertion about disjointness of the seam return is used. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus TorusTopology Finset
variable {N M : ℕ}
noncomputable section


lemma seamClosure_zero_at_exterior (hN : Even N) (hM : Even M)
    {A : RCConfig N M} {u v : FaceVertex N M true}
    (p : IndexedWalk hN hM (TorusRC.torusRCSeamClosed A) u v)
    (s : IndexedWalk hN hM (seamOnlyConfig N M) v u)
    (w : FaceVertex N M true)
    (hw : (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk w ≠
      (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk u)
    (c : Port) (hc : (faceCorner w.val c).1.2.val ≠ 0) :
    fullFlowAt (closedWalkPair hN hM p s).val (faceCorner w.val c).1 = 0 := by
  
  
  change fullDiamondChainExtension _ p.chain _ + fullDiamondChainExtension _ s.chain _ = 0
  rw [ path_extension_zero_at_exterior hN hM p w hw c ]
  change 0 + extendDiamondChain (seamOnlyConfig N M) s.chain _ = 0
  rw [extendDiamondChain_closed _ _ _ (by
                                         simp only [seamOnlyConfig,hc,decide_false]),add_zero]

/-- Every conserved indexed cycle outside a bottom-to-top cylinder cluster has
zero horizontal winding. This is the topological input for unrolling the region. -/
theorem cylinderExterior_windingX_zero (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMlarge : 1 < M) {A : RCConfig N M}
    {u v : FaceVertex N M true} (hu : u.val.2.val=0) (hv : v.val.2.val+1=M)
    (hp : (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).Reachable u v)
    (D : RCConfig N M)
    (hD : ∀ e : OpenDiamondEdge D, e.val.2.val ≠ 0 ∧ ∀ b : Bool,
      (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk
        (faceEndpoint hN hM true e.val b) ≠
          (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk u)
    (g : diamondCycleSpace hN hM D) :
    diamondWindingX D g.val = 0 := by
  
  obtain ⟨p⟩ := exists_indexedWalk_of_reachable hN hM (TorusRC.torusRCSeamClosed A) hp
  obtain ⟨s,_⟩ := exists_seamClosure hN hM hNp (by omega) hu hv p
  let f := closedWalkPair hN hM p s
  let G := fullDiamondCycleExtension hN hM D g
  have hi : ribbonIntersection hN hM (openRCConfig N M) f G = 0 := by
    apply cylinder_exterior_intersection_zero
    intro e he
    
    let d : OpenDiamondEdge D := ⟨e.val, by
                                           cases hd : D e.val with
                                           | true => rfl
                                           | false =>
                                             apply False.elim
                                             apply he
                                             exact extendDiamondChain_closed D g.val e.val hd ⟩
    refine ⟨(hD d).1,?_⟩
    intro b c hc
    exact seamClosure_zero_at_exterior hN hM p s _
      ((hD d).2 b) c hc
  have hGy : diamondWindingY (openRCConfig N M) G.val = 0 := by
    rw [show G.val = fullDiamondChainExtension D g.val from rfl,windingY_fullChainExtension]
    apply sum_eq_zero
    intro e _
    simp only [diamondSeamCrossY,(hD e).1,ite_false,zero_mul]
  
  have hd := ribbonIntersection_mul_area hN hM hNp (by omega) f G
  rw [hi, ← diamondWindingY_mul_period hN hM _ G, ← diamondWindingY_mul_period hN hM _ f, ← diamondWindingX_mul_period hN hM _ G, hGy,  closedWalkPair_windingY hN hM hMlarge hu hv p s ] at hd
  
  have hmn :  M *(N : ℚ) ≠ 0 := by
                                      positivity
  have hGx := (mul_eq_zero.mp (by
                                 linarith)).resolve_left hmn
  
  unfold diamondWindingX
  rw [← sum_fullDiamondChainExtension D g.val diamondSeamCrossX]
  exact hGx

end
end PottsDiscontinuity.TorusExploration
