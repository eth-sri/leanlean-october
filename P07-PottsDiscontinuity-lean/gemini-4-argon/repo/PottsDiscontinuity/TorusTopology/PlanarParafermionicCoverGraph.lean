module

public import PottsDiscontinuity.TorusTopology.PlanarLattice
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar

abbrev ParafermionicCoverVertex := LatticeVertex × ℤ

def parafermionicCoverSheetShift (_ _ : LatticeVertex) : ℤ := 0

def parafermionicCoverGraph : SimpleGraph ParafermionicCoverVertex where
  Adj u v := squareLattice.Adj u.1 v.1 ∧
    v.2 = u.2 + parafermionicCoverSheetShift u.1 v.1
  symm := ⟨fun _ _ ⟨ha, hs⟩ => ⟨ha.symm, by simp [parafermionicCoverSheetShift] at hs ⊢; omega⟩⟩
  loopless := ⟨fun u ⟨ha, _⟩ => squareLattice.loopless.irrefl u.1 ha⟩

instance : DecidableRel parafermionicCoverGraph.Adj := by
  intro u v
  unfold parafermionicCoverGraph
  infer_instance

def parafermionicCoverNeighborLift (u : ParafermionicCoverVertex) (v : LatticeVertex) :
    ParafermionicCoverVertex := (v, u.2 + parafermionicCoverSheetShift u.1 v)

theorem parafermionicCoverNeighborLift_adj (u : ParafermionicCoverVertex)
    (v : LatticeVertex) (h : squareLattice.Adj u.1 v) :
    parafermionicCoverGraph.Adj u (parafermionicCoverNeighborLift u v) :=
  ⟨h, rfl⟩

theorem parafermionicCoverNeighborLift_unique (u : ParafermionicCoverVertex)
    (v : LatticeVertex) (w : ParafermionicCoverVertex)
    (hw : w.1 = v) (hadj : parafermionicCoverGraph.Adj u w) :
    w = parafermionicCoverNeighborLift u v :=
  Prod.ext hw hadj.2

def parafermionicCoverBoxFinset (n : ℕ) : Finset ParafermionicCoverVertex :=
  latticeBox (0, 0) n ×ˢ Finset.Icc (-(n ^ 5 : ℕ) : ℤ) (n ^ 5 : ℤ)

abbrev parafermionicCoverBoxVertices (n : ℕ) : Set ParafermionicCoverVertex :=
  parafermionicCoverBoxFinset n

theorem parafermionicCoverBoxVertices_mem (n : ℕ) (v : ParafermionicCoverVertex) :
    v ∈ parafermionicCoverBoxVertices n ↔
      -(n : ℤ) ≤ v.1.1 ∧ v.1.1 ≤ (n : ℤ) ∧
      -(n : ℤ) ≤ v.1.2 ∧ v.1.2 ≤ (n : ℤ) ∧
      -((n ^ 5 : ℕ) : ℤ) ≤ v.2 ∧ v.2 ≤ ((n ^ 5 : ℕ) : ℤ) := by
  change v ∈ (parafermionicCoverBoxFinset n : Set _) ↔ _
  simp [parafermionicCoverBoxFinset, mem_latticeBox, Nat.cast_pow]
  omega

abbrev ParafermionicCoverBoxVertex (n : ℕ) := ↥(parafermionicCoverBoxFinset n)

def parafermionicCoverBoxGraph (n : ℕ) : SimpleGraph (ParafermionicCoverBoxVertex n) :=
  parafermionicCoverGraph.induce (parafermionicCoverBoxVertices n)

instance parafermionicCoverBoxGraphDecidableRel (n : ℕ) :
    DecidableRel (parafermionicCoverBoxGraph n).Adj := by
  unfold parafermionicCoverBoxGraph
  infer_instance

end PottsDiscontinuity.TorusTopology.Planar
