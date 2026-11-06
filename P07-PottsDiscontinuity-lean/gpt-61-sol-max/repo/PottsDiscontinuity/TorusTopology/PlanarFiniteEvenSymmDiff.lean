/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph
open scoped symmDiff

private theorem card_symmDiff_add_two_card_inter {α : Type*} [DecidableEq α]
    (s t : Finset α) :
    (s ∆ t).card + 2 * (s ∩ t).card = s.card + t.card := by
  
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
  · grind
  · rw [Finset.disjoint_left]
    simp_all

section

variable {V : Type*} [DecidableEq V] (G H : SimpleGraph V) [LocallyFinite G] [LocallyFinite H] [LocallyFinite (G ∆ H)]
include V G H

theorem neighborFinset_symmDiff  (v : V) :
    (G ∆ H).neighborFinset v = G.neighborFinset v ∆ H.neighborFinset v := by
  
  ext w
  rw [Finset.mem_symmDiff]
  aesop

theorem degree_even_symmDiff 
    (hG : ∀ v, Even (G.degree v)) (hH : ∀ v, Even (H.degree v)) :
    ∀ v, Even ((G ∆ H).degree v) := by
  
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_symmDiff]
  have hg : Even (G.neighborFinset v).card := by
    simp_all
  have hh : Even (H.neighborFinset v).card := by
    simp_all
  have hcard := card_symmDiff_add_two_card_inter
    (G.neighborFinset v) (H.neighborFinset v)
  grind

end

end PottsDiscontinuity.TorusTopology.Planar.Medial
