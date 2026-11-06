/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverVertexNeighbors
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

/-- Base-lattice direction encoding: `0=E`, `1=N`, `2=W`, `3=S`. -/
def parafermionicCoverCompassBaseNeighbor (u : ParafermionicCoverVertex)
    (d : Fin 4) : LatticeVertex :=
  if d.val = 0 then (u.1.1 + 1, u.1.2)
  else if d.val = 1 then (u.1.1, u.1.2 + 1)
  else if d.val = 2 then (u.1.1 - 1, u.1.2)
  else (u.1.1, u.1.2 - 1)

section
variable (u : ParafermionicCoverVertex)
/-- The unique actual cover neighbor in the specified compass direction,
including its true seam-dependent sheet shift. -/
def parafermionicCoverCompassNeighbor (d : Fin 4) : ParafermionicCoverVertex :=
  parafermionicCoverNeighborLift u (parafermionicCoverCompassBaseNeighbor u d)

theorem parafermionicCoverCompassBaseNeighbor_injective
     :
    Function.Injective (parafermionicCoverCompassBaseNeighbor u) := by
  intro d e h
  grind [parafermionicCoverCompassBaseNeighbor]

theorem parafermionicCoverCompassBaseNeighbor_adj
    (d : Fin 4) :
    squareLattice.Adj u.1 (parafermionicCoverCompassBaseNeighbor u d) := by
  fin_cases d <;> rcases u with ⟨⟨x,y⟩,k⟩ <;>
    rw [squareLattice_adj_iff] <;>
    simp [parafermionicCoverCompassBaseNeighbor]

theorem squareLattice_adj_iff_exists_compassBaseNeighbor
    (v : LatticeVertex) :
    squareLattice.Adj u.1 v ↔
      ∃ d : Fin 4, parafermionicCoverCompassBaseNeighbor u d = v := by
  rcases u with ⟨⟨x,y⟩,k⟩
  rcases v with ⟨vx,vy⟩
  constructor
  · intro h
    rcases (squareLattice_adj_iff (x,y) (vx,vy)).mp h with
      ⟨hx | hx, hy⟩ | ⟨hx, hy | hy⟩
    · refine ⟨0, ?_⟩
      aesop
    · refine ⟨2, ?_⟩
      grind [parafermionicCoverCompassBaseNeighbor]
    · refine ⟨1, ?_⟩
      aesop
    · refine ⟨3, ?_⟩
      grind [parafermionicCoverCompassBaseNeighbor]
  · rintro ⟨d, hd⟩
    rw [← hd]
    exact parafermionicCoverCompassBaseNeighbor_adj ⟨⟨x,y⟩,k⟩ d

theorem parafermionicCoverCompassBaseNeighbor_reverse
    (d : Fin 4) :
    parafermionicCoverCompassBaseNeighbor
      (parafermionicCoverNeighborLift u
        (parafermionicCoverCompassBaseNeighbor u d)) (d + 2) = u.1 := by
  grind [parafermionicCoverCompassBaseNeighbor, parafermionicCoverNeighborLift]

/-- Each compass direction specifies an actual adjacent vertex of the full
cover graph. -/
theorem parafermionicCoverCompassNeighbor_adj
    (d : Fin 4) :
    parafermionicCoverGraph.Adj u (parafermionicCoverCompassNeighbor u d) :=
  parafermionicCoverNeighborLift_adj u
    (parafermionicCoverCompassBaseNeighbor u d)
    (parafermionicCoverCompassBaseNeighbor_adj u d)

/-- The actual compass neighbors in distinct directions are distinct. -/
theorem parafermionicCoverCompassNeighbor_injective
     :
    Function.Injective (parafermionicCoverCompassNeighbor u) := by
  intro d e h
  apply parafermionicCoverCompassBaseNeighbor_injective u
  exact congrArg Prod.fst h
end

/-- Every full-cover neighbor has exactly one of the four compass directions. -/
theorem parafermionicCoverGraph_neighbor_iff_compassNeighbor
    (u w : ParafermionicCoverVertex) :
    w ∈ parafermionicCoverGraph.neighborSet u ↔
      ∃ d : Fin 4, w = parafermionicCoverCompassNeighbor u d := by
  rw [parafermionicCoverGraph_neighborSet_eq_neighborLift_image]
  constructor
  · rintro ⟨v, hv, hw⟩
    obtain ⟨d, hd⟩ :=
      (squareLattice_adj_iff_exists_compassBaseNeighbor u v).mp
        (by simp_all)
    aesop
  · rintro ⟨d, rfl⟩
    apply Set.mem_image_of_mem (parafermionicCoverNeighborLift u)
    simp [parafermionicCoverCompassBaseNeighbor_adj]

/-- Taking the opposite compass direction returns to the original lifted
vertex, including at the sheet seam. -/
theorem parafermionicCoverCompassNeighbor_reverse
    (u : ParafermionicCoverVertex) (d : Fin 4) :
    parafermionicCoverCompassNeighbor
      (parafermionicCoverCompassNeighbor u d) (d + 2) = u := by
  have hadj := parafermionicCoverCompassNeighbor_adj u d
  have hback := parafermionicCoverNeighborLift_unique
    (parafermionicCoverCompassNeighbor u d) u.1 u rfl hadj.symm
  grind [parafermionicCoverCompassNeighbor, parafermionicCoverCompassBaseNeighbor_reverse]

end PottsDiscontinuity.TorusTopology.Planar.Medial
