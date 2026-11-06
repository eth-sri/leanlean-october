module

public import PottsDiscontinuity.TorusExploration.SeamCycle
public import PottsDiscontinuity.TorusTopology.IndexedWalk

/-! Closing an indexed cylinder path through the seam band. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus TorusTopology Finset
variable {N M : ℕ}

section
variable (hN : Even N) (hM : Even M)
/-- Extension by zero preserves the entire boundary, also for nonclosed chains. -/
theorem boundary_fullChainExtension (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ) :
    diamondBoundary hN hM (openRCConfig N M) (fullDiamondChainExtension A f) =
      diamondBoundary hN hM A f := by
  funext v
  have h := sum_ribbonHalfFlow_corners_eq_neg_boundary hN hM (openRCConfig N M)
    (fullDiamondChainExtension A f) v
  simp_rw [ribbonHalfFlow_fullExtension] at h
  rw [sum_ribbonHalfFlow_corners_eq_neg_boundary] at h
  linarith

/-- A path and any reverse-endpoint path, in possibly different edge sets,
produce a genuine conserved full-torus chain. -/
noncomputable def closedWalkPair {A B : RCConfig N M} {u v : FaceVertex N M true}
    (p : IndexedWalk hN hM A u v) (s : IndexedWalk hN hM B v u) :
    diamondCycleSpace hN hM (openRCConfig N M) :=
  ⟨fullDiamondChainExtension A p.chain + fullDiamondChainExtension B s.chain, by
    change diamondBoundary hN hM (openRCConfig N M) _ = 0
    rw [map_add,boundary_fullChainExtension,boundary_fullChainExtension,
      IndexedWalk.boundary_chain,IndexedWalk.boundary_chain]
    simp⟩

/-- Every bottom-to-top cylinder path admits a conserved closure using only
seam edges for its return. -/
theorem exists_seamClosure (hNp : 0 < N) (hMp : 0 < M) {A : RCConfig N M}
    {u v : FaceVertex N M true} (hu : u.val.2.val=0) (hv : v.val.2.val+1=M)
    (p : IndexedWalk hN hM A u v) :
    ∃ s : IndexedWalk hN hM (seamOnlyConfig N M) v u,
      (closedWalkPair hN hM p s).val =
        fullDiamondChainExtension A p.chain +
          fullDiamondChainExtension (seamOnlyConfig N M) s.chain := by
  obtain ⟨s⟩ := exists_indexedWalk_of_reachable hN hM _
    (top_bottom_seam_reachable hN hM hNp hMp u v hu hv)
  tauto
end

end PottsDiscontinuity.TorusExploration
