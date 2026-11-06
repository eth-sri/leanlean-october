/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceChainDecomposition
public import PottsDiscontinuity.TorusTopology.PlanarFiniteTriangularFaceUniqueness
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph
open scoped symmDiff

/-- The actual four-edge face support makes its own top pivot unique at its
height; every other top pivot on the boundary has strictly smaller rank. -/
theorem parafermionicCoverFiniteFacePivot_boundary_classification {n : ℕ}
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (hij : parafermionicCoverFiniteFaceTopPivot n j ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet) :
    j = i ∨ parafermionicCoverFiniteFaceTopRank n j <
      parafermionicCoverFiniteFaceTopRank n i :=
  coverFiniteFacePivot_boundary_classification i j hij

theorem parafermionicCoverFiniteFaceChain_toFinset_unique {n : ℕ}
    (L M : List (ParafermionicCoverFiniteFaceTopIndex n))
    (hL : L.Nodup) (hM : M.Nodup)
    (hEq : faceSymmDiffList
      (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) L =
      faceSymmDiffList
      (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) M) :
    L.toFinset = M.toFinset := by
  classical
  let F : ParafermionicCoverFiniteFaceTopIndex n →
      SimpleGraph (ParafermionicCoverBoxVertex n) :=
    fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2
  let p : ParafermionicCoverFiniteFaceTopIndex n →
      Sym2 (ParafermionicCoverBoxVertex n) := parafermionicCoverFiniteFaceTopPivot n
  let rank : ParafermionicCoverFiniteFaceTopIndex n → ℕ :=
    parafermionicCoverFiniteFaceTopRank n
  have hpF : ∀ i, p i ∈ (F i).edgeSet := by
    intro i
    have hmem := parafermionicCoverFiniteFaceTopEdgeBox_mem_boundaryGraph i.1 i.2
    have heq : parafermionicCoverFiniteFaceTopEdgeBox i.1 i.2 = p i := by
      simp [p, parafermionicCoverFiniteFaceTopPivot,
        parafermionicCoverFiniteFaceTopEdgeBox]
    simpa [F, heq] using hmem
  have htri : ∀ i j, p j ∈ (F i).edgeSet → j = i ∨ rank j < rank i := by
    intro i j h
    exact parafermionicCoverFiniteFacePivot_boundary_classification i j
      (by simpa [F, p] using h)
  exact faceSymmDiffList_eq_implies_toFinset_eq F p rank hpF htri L M hL hM
    (by simpa [F] using hEq)

theorem parafermionicCoverFiniteFaceChain_unique_representation {n : ℕ}
    (hn : 1 ≤ n) (H : SimpleGraph (ParafermionicCoverBoxVertex n))
    (hle : H ≤ parafermionicCoverBoxGraph n)
    (hHeven : ∀ v, Even (H.neighborSet v).ncard) :
    ∃! S : Finset (ParafermionicCoverFiniteFaceTopIndex n),
      ∃ L : List (ParafermionicCoverFiniteFaceTopIndex n),
        L.Nodup ∧ L.toFinset = S ∧
          faceSymmDiffList
            (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) L = H := by
  classical
  obtain ⟨L, hL, hLH⟩ := parafermionicCoverFiniteFaceChainDecomposition hn H hle hHeven
  refine ⟨L.toFinset, ⟨L, hL, rfl, hLH⟩, ?_⟩
  intro S hS
  obtain ⟨M, hM, hMS, hMH⟩ := hS
  have hsets := parafermionicCoverFiniteFaceChain_toFinset_unique L M hL hM
    (hLH.trans hMH.symm)
  exact (hsets.trans hMS).symm

end PottsDiscontinuity.TorusTopology.Planar.Medial
