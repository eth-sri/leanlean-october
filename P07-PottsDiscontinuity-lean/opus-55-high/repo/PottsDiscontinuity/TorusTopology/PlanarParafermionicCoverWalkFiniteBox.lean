/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: namespace/import relocation; generic walk API only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverGraph
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph
open Classical

def parafermionicCoverWalkVertexHeight (v : ParafermionicCoverVertex) : ℕ :=
  max v.1.1.natAbs (max v.1.2.natAbs v.2.natAbs)

theorem exists_box_height_for_list (l : List ParafermionicCoverVertex) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ v ∈ l, parafermionicCoverWalkVertexHeight v ≤ N := by
  induction l with
  | nil => aesop
  | cons a l ih =>
      obtain ⟨N, hN, hbound⟩ := ih
      refine ⟨max N (parafermionicCoverWalkVertexHeight a),
        le_trans hN (Nat.le_max_left _ _), ?_⟩
      simp_all

section
variable {u v : ParafermionicCoverVertex} (p : parafermionicCoverGraph.Walk u v)
include u v p
/-- Every finite actual full-cover walk support lies in some genuine box whose
sheet interval is the prescribed fifth-power interval. -/
theorem parafermionicCoverWalk_support_subset_some_box
     :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ z ∈ p.support,
      z ∈ parafermionicCoverBoxVertices N := by
  obtain ⟨N, hN, hbound⟩ := exists_box_height_for_list p.support
  refine ⟨N, hN, ?_⟩
  intro z hz
  have hh := hbound z hz
  have hxN :=
    (Nat.le_max_left _ _).trans hh
  have hyN :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hh)
  have hkN :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hh)
  have hNpow :=
    Nat.le_self_pow (n := 5) (by decide) N
  rw [parafermionicCoverBoxVertices_mem]
  omega

/-- Restrict an actual full-cover walk to a sufficiently large actual finite
box, retaining the same lifted vertices and exact walk after mapping back. -/
theorem parafermionicCoverWalk_exists_box_restriction
     :
    ∃ N : ℕ, 1 ≤ N ∧
      ∃ hbox : ∀ z ∈ p.support, z ∈ parafermionicCoverBoxVertices N,
        (p.induce (parafermionicCoverBoxVertices N) hbox).map
          (SimpleGraph.Embedding.induce
            (parafermionicCoverBoxVertices N)).toHom = p := by
  obtain ⟨N, hN, hbox⟩ := parafermionicCoverWalk_support_subset_some_box p
  refine ⟨N, hN, hbox, ?_⟩
  simpa [parafermionicCoverBoxGraph] using
    (SimpleGraph.Walk.map_induce p hbox)
end

/-- A genuine simple cycle in the full cover can be placed inside one actual
finite box without changing its closed walk or its simple-cycle property. -/
theorem parafermionicCoverCycle_exists_box_restriction
    {u : ParafermionicCoverVertex} (p : parafermionicCoverGraph.Walk u u)
    (hp : p.IsCycle) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∃ hbox : ∀ z ∈ p.support, z ∈ parafermionicCoverBoxVertices N,
        (p.induce (parafermionicCoverBoxVertices N) hbox).IsCycle ∧
          (p.induce (parafermionicCoverBoxVertices N) hbox).map
            (SimpleGraph.Embedding.induce
              (parafermionicCoverBoxVertices N)).toHom = p := by
  obtain ⟨N, hN, hboxExists⟩ := parafermionicCoverWalk_exists_box_restriction p
  obtain ⟨hbox, hmap⟩ := hboxExists
  have hqcycle : (p.induce (parafermionicCoverBoxVertices N) hbox).IsCycle := by
    have hmapped :
        ((p.induce (parafermionicCoverBoxVertices N) hbox).map (SimpleGraph.Embedding.induce
          (parafermionicCoverBoxVertices N)).toHom).IsCycle := by
      simp_all
    exact (SimpleGraph.Walk.isCycle_map_iff_of_injective
      (SimpleGraph.Embedding.induce (G := parafermionicCoverGraph)
        (parafermionicCoverBoxVertices N)).injective).mp hmapped
  exact ⟨N, hN, hbox, hqcycle, hmap⟩

end PottsDiscontinuity.TorusTopology.Planar.Medial
