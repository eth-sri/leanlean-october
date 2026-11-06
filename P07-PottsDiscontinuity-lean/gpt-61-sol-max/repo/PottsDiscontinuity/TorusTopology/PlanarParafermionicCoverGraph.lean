/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.PlanarLattice
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar

/-- Vertices of the literal three-coordinate graph in DST17, p.46. -/
abbrev ParafermionicCoverVertex := LatticeVertex × ℤ

/-- The increment of the sheet coordinate when crossing the lower seam. -/
def parafermionicCoverSheetShift (p q : LatticeVertex) : ℤ :=
  if p.1 = 0 ∧ q.1 = 1 ∧ p.2 = q.2 ∧ p.2 < 0 then 1
  else if p.1 = 1 ∧ q.1 = 0 ∧ p.2 = q.2 ∧ p.2 < 0 then -1
  else 0

/-- The four actual edge types in the source, listed in both orientations:
vertical, ordinary horizontal, upper seam, and lower seam. -/
def parafermionicCoverAdjCases (u v : ParafermionicCoverVertex)  :=
   u.1.1 = v.1.1 ∧ u.1.2 + 1 = v.1.2 ∧ u.2 = v.2  ∨
   u.1.1 = v.1.1 ∧ v.1.2 + 1 = u.1.2 ∧ u.2 = v.2  ∨
   u.1.2 = v.1.2 ∧ u.2 = v.2 ∧ u.1.1 + 1 = v.1.1 ∧ u.1.1 ≠ 0  ∨
   u.1.2 = v.1.2 ∧ u.2 = v.2 ∧ v.1.1 + 1 = u.1.1 ∧ v.1.1 ≠ 0  ∨
   u.1.1 = 0 ∧ v.1.1 = 1 ∧ u.1.2 = v.1.2 ∧ 0 ≤ u.1.2 ∧ u.2 = v.2  ∨
   u.1.1 = 1 ∧ v.1.1 = 0 ∧ u.1.2 = v.1.2 ∧ 0 ≤ u.1.2 ∧ u.2 = v.2  ∨
   u.1.1 = 0 ∧ v.1.1 = 1 ∧ u.1.2 = v.1.2 ∧ u.1.2 < 0 ∧ u.2 + 1 = v.2  ∨
   u.1.1 = 1 ∧ v.1.1 = 0 ∧ u.1.2 = v.1.2 ∧ u.1.2 < 0 ∧ v.2 + 1 = u.2 



def parafermionicCoverGraph : SimpleGraph ParafermionicCoverVertex where
  Adj u v := squareLattice.Adj u.1 v.1 ∧
    v.2 = u.2 + parafermionicCoverSheetShift u.1 v.1
  symm := ⟨by
    intro u v h
    rcases h with ⟨hbase, hsheet⟩
    refine ⟨?_, ?_⟩
    · exact SimpleGraph.Adj.symm hbase
    · grind +locals⟩
  loopless := ⟨by
    simp_all⟩

instance : DecidableRel parafermionicCoverGraph.Adj := by
  intro u v
  unfold parafermionicCoverGraph
  infer_instance

theorem parafermionicCoverGraph_adj_iff_cases (u v : ParafermionicCoverVertex) :
    parafermionicCoverGraph.Adj u v ↔ parafermionicCoverAdjCases u v := by
  rcases u with ⟨⟨x, y⟩, k⟩
  rcases v with ⟨⟨x', y'⟩, k'⟩
  change  squareLattice.Adj (x, y) (x', y') ∧
      k' = k + parafermionicCoverSheetShift (x, y) (x', y')  ↔
    parafermionicCoverAdjCases ((x, y), k) ((x', y'), k')
  rw [squareLattice_adj_iff]
  unfold parafermionicCoverAdjCases parafermionicCoverSheetShift
  dsimp only
  constructor
  · rintro ⟨hbase, hsheet⟩
    rcases hbase with ⟨hx | hx, hy⟩ | ⟨hx, hy | hy⟩
    · split_ifs at hsheet <;> omega
    · split_ifs at hsheet <;> omega
    all_goals aesop
  · aesop

/-- The canonical height of the unique lift of a base neighbor from a given vertex. -/
def parafermionicCoverNeighborLift (u : ParafermionicCoverVertex) (v : LatticeVertex) :
    ParafermionicCoverVertex := (v, u.2 + parafermionicCoverSheetShift u.1 v)

theorem parafermionicCoverNeighborLift_adj (u : ParafermionicCoverVertex)
    (v : LatticeVertex) (h : squareLattice.Adj u.1 v) :
    parafermionicCoverGraph.Adj u (parafermionicCoverNeighborLift u v) := ⟨h, rfl⟩

theorem parafermionicCover_sheetShift_of_adj {u v : ParafermionicCoverVertex}
    (h : parafermionicCoverGraph.Adj u v) :
    v.2 = u.2 + parafermionicCoverSheetShift u.1 v.1 := h.2

theorem parafermionicCoverNeighborLift_unique (u : ParafermionicCoverVertex)
    (v : LatticeVertex) (w : ParafermionicCoverVertex)
    (hw : w.1 = v) (hadj : parafermionicCoverGraph.Adj u w) :
    w = parafermionicCoverNeighborLift u v := by
  grind +locals

/-- The finite vertex set `U_n` from the source, including every sheet in `[-n^5,n^5]`. -/
def parafermionicCoverBoxFinset (n : ℕ) : Finset ParafermionicCoverVertex :=
  latticeBox (0, 0) n ×ˢ Finset.Icc (-(n ^ 5 : ℕ) : ℤ) (n ^ 5 : ℤ)

abbrev parafermionicCoverBoxVertices (n : ℕ) : Set ParafermionicCoverVertex :=
  parafermionicCoverBoxFinset n

theorem parafermionicCoverBoxVertices_mem (n : ℕ) (v : ParafermionicCoverVertex) :
    v ∈ parafermionicCoverBoxVertices n ↔
      -(n : ℤ) ≤ v.1.1 ∧ v.1.1 ≤ (n : ℤ) ∧
      -(n : ℤ) ≤ v.1.2 ∧ v.1.2 ≤ (n : ℤ) ∧
      -((n ^ 5 : ℕ) : ℤ) ≤ v.2 ∧ v.2 ≤ ((n ^ 5 : ℕ) : ℤ) := by
  
  simp [parafermionicCoverBoxFinset, mem_latticeBox]
  omega

theorem parafermionicCoverBoxFinset_card (n : ℕ) :
    (parafermionicCoverBoxFinset n).card = (2 * n + 1) ^ 2 * (2 * n ^ 5 + 1) := by
                                                                                  rw [parafermionicCoverBoxFinset, Finset.card_product, card_latticeBox, Int.card_Icc]
                                                                                  grind

abbrev ParafermionicCoverBoxVertex (n : ℕ) := ↥(parafermionicCoverBoxFinset n)

def parafermionicCoverBoxGraph (n : ℕ) : SimpleGraph (ParafermionicCoverBoxVertex n) :=
  parafermionicCoverGraph.induce (parafermionicCoverBoxVertices n)

instance parafermionicCoverBoxGraphDecidableRel (n : ℕ) :
    DecidableRel (parafermionicCoverBoxGraph n).Adj := by
  unfold parafermionicCoverBoxGraph
  infer_instance

theorem parafermionicCoverBoxVertex_card (n : ℕ) :
    Fintype.card (ParafermionicCoverBoxVertex n) = (2 * n + 1) ^ 2 * (2 * n ^ 5 + 1) := by
                                                                                          simp_all [ParafermionicCoverBoxVertex, parafermionicCoverBoxVertices, parafermionicCoverBoxFinset_card]

end PottsDiscontinuity.TorusTopology.Planar
