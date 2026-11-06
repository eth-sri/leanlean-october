module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos821.S2.HistorySizes

public import Erdos821.S2.MemoryGhost
public import Erdos821.Blueprint.Graph

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Adj

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {P : PrimeGroups} {g : P.Group}

/-- Index enumeration counts each particle value correctly. -/
lemma count_eq_card_filter (z : P.Memory g) (u : P.Particle g) :
    z.count u = (Finset.univ.filter (fun i : Fin z.card => memoryEntry z i = u)).card := by
  have hlen : z.toList.length = z.card := Multiset.length_toList z
  have hcount : z.count u = z.toList.count u := by
    conv_lhs => rw [← Multiset.coe_toList z]
    rw [Multiset.coe_count]
  rw [hcount]
  let v : List.Vector (P.Particle g) z.card := ⟨z.toList, by rw [hlen]⟩
  
  have hcard := Fin.card_filter_univ_eq_vector_get_eq_count u v
  solve_by_elim

/-- Deletion keeps exactly the unremoved indices. -/
lemma delete_card (z : P.Memory g) (A : Finset (Fin z.card)) :
    (deleteMemoryIndices z A).card = (Finset.univ \ A).card := by
  unfold deleteMemoryIndices
  rw [Multiset.coe_card, List.length_map, Finset.length_toList]

/-- Deletion count per particle value via remaining indices. -/
lemma delete_count_eq (s : P.Memory g) (A : Finset (Fin s.card))
    (v : P.Particle g) :
    (deleteMemoryIndices s A).count v =
    ((Finset.univ \ A).filter (fun i => memoryEntry s i = v)).card := by
  unfold deleteMemoryIndices
  have h1 : ((((Finset.univ \ A).toList.map (memoryEntry s) : List (P.Particle g)) : P.Memory g))
      = (((Finset.univ \ A).val).map (memoryEntry s)) := by
    rw [← Finset.coe_toList, Multiset.map_coe]
  rw [h1, Multiset.count_map]
  have hpred : (((Finset.univ \ A).val).filter (fun a => v = memoryEntry s a))
      = (((Finset.univ \ A).val).filter (fun a => memoryEntry s a = v)) := by
    apply Multiset.filter_congr
    intro a _
    exact eq_comm
  solve_by_elim

/-- Ordered birth batch has the declared length. -/
alias birth_card := _root_.Erdos821.S2Core.zeroBirthBatch_card


end Erdos821.P3Adj
