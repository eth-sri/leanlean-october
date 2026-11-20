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

lemma rayStep_horizontal_invariant (x y : ℤ) (u w : LatticeVertex)
    (h : squareLattice.Adj u w)
    (hne : s(u,w) ≠ s((x,y-1),(x,y))) :
    rayStep (x,y) u w = rayStep (x+1,y) u w := by
  rcases u with ⟨a,b⟩
  rcases w with ⟨c,d⟩
  simp only [squareLattice_adj_iff] at h
  simp only [ne_eq, Sym2.eq_iff, Prod.mk.injEq, not_or, not_and] at hne
  rcases h with ⟨h | h, hy⟩ | ⟨hx, h | h⟩ <;>
    dsimp [rayStep] <;> split_ifs <;> omega

lemma rayStep_vertical_difference (x y : ℤ) (u w : LatticeVertex)
    (h : squareLattice.Adj u w)
    (hne : s(u,w) ≠ s((x-1,y),(x,y))) :
    rayStep (x,y+1) u w - rayStep (x,y) u w =
      rowMarker x y u - rowMarker x y w := by
  rcases u with ⟨a,b⟩
  rcases w with ⟨c,d⟩
  simp only [squareLattice_adj_iff] at h
  simp only [ne_eq, Sym2.eq_iff, Prod.mk.injEq, not_or, not_and] at hne
  rcases h with ⟨h | h, hy⟩ | ⟨hx, h | h⟩ <;>
    dsimp [rayStep, rowMarker] <;> split_ifs <;> omega

lemma rayIndex_horizontal_invariant (x y : ℤ) {u w : LatticeVertex}
    (p : squareLattice.Walk u w)
    (hne : s((x,y-1),(x,y)) ∉ p.edges) :
    rayIndex (x,y) p = rayIndex (x+1,y) p := by
  induction p with
  | nil => rfl
  | @cons u z w h p ih =>
    have hhead : s(u,z) ≠ s((x,y-1),(x,y)) := by
      intro he
      simp_all
    have htail : s((x,y-1),(x,y)) ∉ p.edges := by
      simp_all
    simp [rayIndex, rayStep_horizontal_invariant x y u z h hhead, ih htail]

lemma rayIndex_vertical_difference (x y : ℤ) {u w : LatticeVertex}
    (p : squareLattice.Walk u w)
    (hne : s((x-1,y),(x,y)) ∉ p.edges) :
    rayIndex (x,y+1) p - rayIndex (x,y) p = rowMarker x y u - rowMarker x y w := by
  induction p with
  | nil => aesop
  | @cons u z w h p ih =>
    have hhead : s(u,z) ≠ s((x-1,y),(x,y)) := by
      intro he
      simp_all
    have htail : s((x-1,y),(x,y)) ∉ p.edges := by
      simp_all
    have hl := rayStep_vertical_difference x y u z h hhead
    have ht := ih htail
    simp only [rayIndex]
    omega

section

variable {x y : LatticeVertex} (p : squareLattice.Walk x y)

/-- Removing precisely the primal edges crossing the given dual walk. -/
def circuitAvoidanceGraph :
    SimpleGraph LatticeVertex where
  Adj u w := squareLattice.Adj u w ∧ ∀ b : LatticeBond, b.toSym2 = s(u,w) →
    (dualBondOfPrimal b).toSym2 ∉ p.edges
  symm := ⟨by
    intro u w h
    refine ⟨h.1.symm, ?_⟩
    simp_all⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- The ray index is locally constant across uncrossed primal edges away from the
levels of the two endpoints. -/
theorem rayIndex_eq_of_avoidance_adj_of_markers
    {u w : LatticeVertex} (h : (circuitAvoidanceGraph p).Adj u w)
    (hrow : ∀ a : ℤ, u.2 ≠ w.2 →
      rowMarker a (min u.2 w.2) x = rowMarker a (min u.2 w.2) y) :
    rayIndex u p = rayIndex w p := by
  rcases u with ⟨a,b⟩
  rcases w with ⟨c,d⟩
  have hs := (squareLattice_adj_iff _ _).1 h.1
  dsimp only at hs
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
    have hh := hrow a (by dsimp; omega)
    change rowMarker a (min b (b+1)) x = rowMarker a (min b (b+1)) y at hh
    rw [min_eq_left (by omega : b ≤ b+1)] at hh
    omega
  · subst c; subst b
    have hd := rayIndex_vertical_difference a d p
      (by simpa [dualBondOfPrimal, LatticeBond.toSym2, LatticeBond.source,
        LatticeBond.target] using h.2 ⟨(a,d), .vertical⟩ Sym2.eq_swap)
    have hh := hrow a (by dsimp; omega)
    change rowMarker a (min (d+1) d) x = rowMarker a (min (d+1) d) y at hh
    rw [min_eq_right (by omega : d ≤ d+1)] at hh
    omega

/-- Along a primal walk between the dual endpoint levels, the ray index is
constant if none of its edges crosses the dual walk. -/
theorem rayIndex_eq_of_walk_between {V : Type*} {G : SimpleGraph V} (f : V → LatticeVertex)
    {u v : V} (r : G.Walk u v)
    (havoid : ∀ {a b}, G.Adj a b → (circuitAvoidanceGraph p).Adj (f a) (f b))
    (hlevels : ∀ a ∈ r.support, x.2 < (f a).2 ∧ (f a).2 ≤ y.2) :
    rayIndex (f u) p = rayIndex (f v) p := by
  induction r with
  | nil => rfl
  | @cons a b c h r ih =>
    apply Eq.trans _ (ih (fun z hz => hlevels z (by simp [hz])))
    apply rayIndex_eq_of_avoidance_adj_of_markers p (havoid h)
    intro k hne
    have ha := hlevels a (by simp)
    have hb := hlevels b (by simp)
    have hl : x.2 ≠ min (f a).2 (f b).2 := by omega
    have hr : y.2 ≠ min (f a).2 (f b).2 := by omega
    simp [rowMarker, hl, hr]

end

section

variable {z : LatticeVertex} (p : squareLattice.Walk z z)

end

end
end PottsDiscontinuity.Duality
