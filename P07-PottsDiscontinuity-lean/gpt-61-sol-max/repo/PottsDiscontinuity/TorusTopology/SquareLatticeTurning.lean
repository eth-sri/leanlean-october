module
public import Mathlib

public import PottsDiscontinuity.FK.Lattice
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverCycleCompassTurn

/-! The discrete Umlaufsatz on the project's literal square lattice.
A finite polygon is translated above the cover seam and embedded in sheet zero.
Its ordered edge directions, including the closing turn, are preserved. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open SimpleGraph
open Planar.Medial

/-- Compass label of an actual directed square-lattice edge: east, north,
west, south in positive cyclic order. Adjacency exhausts these four cases. -/
def squareDartCompass (d : FK.squareLattice.Dart) : Fin 4 :=
  if d.fst.1 < d.snd.1 then 0 else if d.fst.2 < d.snd.2 then 1
  else if d.snd.1 < d.fst.1 then 2 else 3

/-- The ordered geometric directions of every edge of a lattice walk. -/
def squareWalkCompassDirections {u v : ℤ × ℤ} (p : FK.squareLattice.Walk u v)  := p.darts.map squareDartCompass

/-- The signed quarter-turn sum, including the last-to-first edge pair. -/
def squareWalkCyclicTurn {u : ℤ × ℤ} (p : FK.squareLattice.Walk u u)  :=
  ((squareWalkCompassDirections p).zipWith primalCompassQuarterTurn
    ((squareWalkCompassDirections p).rotate 1)).sum

def upperCoverHom (k : ℤ) :
    FK.squareLattice.induce {v | 0 ≤ v.2 + k} →g Planar.parafermionicCoverGraph where
  toFun v := ((v.val.1, v.val.2+k),0)
  map_rel' := by
    intro u v h
    refine ⟨?_,?_⟩
    · rw [Planar.squareLattice_adj_iff]
      have hh := (FK.squareLattice_adj_iff _ _).mp h
      dsimp at hh ⊢
      omega
    · grind [Planar.parafermionicCoverSheetShift]

private lemma upperCoverHom_injective (k : ℤ) : Function.Injective (upperCoverHom k) := by
  intro u v h
  
  have hh := congrArg Prod.fst h
  change (u.val.1,u.val.2+k) = (v.val.1,v.val.2+k) at hh
  aesop

private lemma upperCoverHom_direction (k : ℤ)
    (u v : {v : ℤ × ℤ | 0 ≤ v.2+k}) (h : FK.squareLattice.Adj u.val v.val) :
    parafermionicCoverCompassDirection
      (upperCoverHom k u) (upperCoverHom k v)
      ((upperCoverHom k).map_rel h) = squareDartCompass ⟨⟨u.val,v.val⟩,h⟩ := by
  apply parafermionicCoverCompassDirection_eq_of_neighbor
  change parafermionicCoverCompassNeighbor ((u.val.1,u.val.2+k),0)
    (if u.val.1 < v.val.1 then 0 else if u.val.2 < v.val.2 then 1
     else if v.val.1 < u.val.1 then 2 else 3) = ((v.val.1,v.val.2+k),0)
  unfold parafermionicCoverCompassNeighbor Planar.parafermionicCoverNeighborLift
  apply Prod.ext
  · 
    rcases  (FK.squareLattice_adj_iff u.val v.val).mp h  with ⟨hx|hx,hy⟩ | ⟨hx,hy|hy⟩
    all_goals
      simp only [parafermionicCoverCompassBaseNeighbor]
      grind
  · grind [Planar.parafermionicCoverSheetShift]

private lemma upperCoverHom_walkDirections (k : ℤ)
    {u v : {v : ℤ × ℤ | 0 ≤ v.2+k}}
    (p : (FK.squareLattice.induce {v | 0 ≤ v.2+k}).Walk u v) :
    parafermionicCoverWalkCompassDirections (p.map (upperCoverHom k)) =
      squareWalkCompassDirections
        (p.map (Embedding.induce {v : ℤ × ℤ | 0 ≤ v.2+k}).toHom) := by
  simp only [parafermionicCoverWalkCompassDirections, squareWalkCompassDirections,
    Walk.darts_map,List.map_map]
  apply List.map_congr_left
  intro d hd
  exact upperCoverHom_direction k d.fst d.snd d.adj

private lemma exists_upper_height (l : List (ℤ × ℤ)) :
    ∃ k : ℤ, ∀ v ∈ l, 0 ≤ v.2+k := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a l ih =>
    obtain ⟨k,hk⟩ := ih
    refine ⟨max k (-a.2),?_⟩
    grind

/-- Every simple square-lattice cycle has total signed turn +4 or -4. -/
theorem squareWalkCyclicTurn_eq_four_or_neg_four {u : ℤ × ℤ}
    (p : FK.squareLattice.Walk u u) (hp : p.IsCycle) :
    squareWalkCyclicTurn p = 4 ∨ squareWalkCyclicTurn p = -4 := by
  obtain ⟨k,hk⟩ := exists_upper_height p.support
  let q := p.induce {v : ℤ × ℤ | 0 ≤ v.2+k} hk
  have hq : q.IsCycle := by
    apply (Walk.isCycle_map_iff_of_injective
      (f := (Embedding.induce (G := FK.squareLattice) {v : ℤ × ℤ | 0 ≤ v.2+k}).toHom)
      (Embedding.induce (G := FK.squareLattice) {v : ℤ × ℤ | 0 ≤ v.2+k}).injective).mp
    aesop
  
  have ht := parafermionicCoverWalkCyclicCompassTurn_eq_four_or_neg_four
    (q.map (upperCoverHom k)) ((Walk.isCycle_map_iff_of_injective (upperCoverHom_injective k)).mpr hq)
  have hd := upperCoverHom_walkDirections k q
  simp only [q,Walk.map_induce] at hd
  unfold parafermionicCoverWalkCyclicCompassTurn at ht
  rw [hd] at ht
  exact ht

end PottsDiscontinuity.TorusTopology
