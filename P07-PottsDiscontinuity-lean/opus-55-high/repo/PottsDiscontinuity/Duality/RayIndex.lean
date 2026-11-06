module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.WholePlaneDualGraph

/-! Signed intersections with the horizontal ray from a primal vertex.
Dual vertices are face bases; their geometric centers are shifted by (1/2,1/2).
Thus a dual upward edge from (x,y-1) to (x,y) crosses the primal row y. -/

@[expose] public section

namespace PottsDiscontinuity.Duality
open FK FK.Medial
noncomputable section

/-- Signed intersection contribution of an oriented dual unit step. -/
def rayStep (v u w : LatticeVertex) : ℤ :=
  ((if u.2 < v.2 then 1 else 0) - (if w.2 < v.2 then 1 else 0)) *
    (if v.1 ≤ u.1 then 1 else 0)

/-- The integer intersection number of a dual walk with the rightward primal ray. -/
def rayIndex (v : LatticeVertex) : {u w : LatticeVertex} → squareLattice.Walk u w → ℤ
  | _, _, .nil => 0
  | u, _, .cons (v := w) _ p => rayStep v u w + rayIndex v p

 def rowMarker (x y : ℤ) (z : LatticeVertex) : ℤ :=
  if z.2 = y ∧ x ≤ z.1 then 1 else 0

section
variable (x y : ℤ) (u w : LatticeVertex) (h : squareLattice.Adj u w)
include h
theorem rayStep_horizontal_invariant (hne : s(u,w) ≠ s((x,y-1),(x,y))) :
    rayStep (x,y) u w = rayStep (x+1,y) u w := by
  simp only [squareLattice_adj_iff] at h
  grind [rayStep]

theorem rayStep_vertical_difference (hne : s(u,w) ≠ s((x-1,y),(x,y))) :
    rayStep (x,y+1) u w - rayStep (x,y) u w =
      rowMarker x y u - rowMarker x y w := by
  simp only [squareLattice_adj_iff] at h
  grind [rayStep, rowMarker]
end

section
variable (x y : ℤ) {u w : LatticeVertex} (p : squareLattice.Walk u w)
theorem rayIndex_horizontal_invariant (hne : s((x,y-1),(x,y)) ∉ p.edges) :
    rayIndex (x,y) p = rayIndex (x+1,y) p := by
  induction p with
  | nil => rfl
  | @cons u z w h p ih =>
    have hhead : s(u,z) ≠ s((x,y-1),(x,y)) := by
      intro he
      simp_all
    simp_all [rayIndex, rayStep_horizontal_invariant]

theorem rayIndex_vertical_difference (hne : s((x-1,y),(x,y)) ∉ p.edges) :
    rayIndex (x,y+1) p - rayIndex (x,y) p = rowMarker x y u - rowMarker x y w := by
  induction p with
  | nil => aesop
  | @cons u z w h p ih =>
    have hhead : s(u,z) ≠ s((x-1,y),(x,y)) := by
      intro he
      simp_all
    have htail : s((x-1,y),(x,y)) ∉ p.edges := by
      simp_all
    grind [rayStep_vertical_difference, rayIndex]
end

/-- Removing precisely the primal edges crossing the given dual walk. -/
def circuitAvoidanceGraph {z : LatticeVertex} (p : squareLattice.Walk z z) :
    SimpleGraph LatticeVertex where
  Adj u w := squareLattice.Adj u w ∧ ∀ b : LatticeBond, b.toSym2 = s(u,w) →
    (dualBondOfPrimal b).toSym2 ∉ p.edges
  symm := ⟨by
    intro u w h
    refine ⟨h.1.symm, ?_⟩
    simp_all⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

section
variable {z : LatticeVertex} (p : squareLattice.Walk z z) {u w : LatticeVertex}
/-- The intersection number is constant along every primal edge avoiding the circuit. -/
theorem rayIndex_eq_of_avoidance_adj (h : (circuitAvoidanceGraph p).Adj u w) :
    rayIndex u p = rayIndex w p := by
  rcases u with ⟨a,b⟩
  rcases w with ⟨c,d⟩
  have hs := (squareLattice_adj_iff _ _).1 h.1
  dsimp at hs
  rcases hs with ⟨hx | hx, hy⟩ | ⟨hx, hy | hy⟩
  · subst c; subst d
    exact rayIndex_horizontal_invariant a b p
      (by simpa [dualBondOfPrimal, LatticeBond.toSym2, LatticeBond.source,
        LatticeBond.target] using h.2 ⟨(a,b), .horizontal⟩ rfl)
  · subst a; subst d
    exact (rayIndex_horizontal_invariant c b p
      (by simpa [dualBondOfPrimal, LatticeBond.toSym2, LatticeBond.source,
        LatticeBond.target] using h.2 ⟨(c,b), .horizontal⟩ Sym2.eq_swap)).symm
  · subst c; subst d
    have hd := rayIndex_vertical_difference a b p
      (by simpa [dualBondOfPrimal, LatticeBond.toSym2, LatticeBond.source,
        LatticeBond.target] using h.2 ⟨(a,b), .vertical⟩ rfl)
    omega
  · subst c; subst b
    have hd := rayIndex_vertical_difference a d p
      (by simpa [dualBondOfPrimal, LatticeBond.toSym2, LatticeBond.source,
        LatticeBond.target] using h.2 ⟨(a,d), .vertical⟩ Sym2.eq_swap)
    omega

theorem rayIndex_eq_of_avoidance_reachable (h : (circuitAvoidanceGraph p).Reachable u w) : rayIndex u p = rayIndex w p := by
  obtain ⟨q⟩ := h
  induction q with
  | nil => rfl
  | cons h q ih => grind [rayIndex_eq_of_avoidance_adj]
end

end
end PottsDiscontinuity.Duality
