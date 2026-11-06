module
import Batteries.Tactic.Alias
import Erdos821.P3Edge.ColumnBound

public import Erdos821.P3Clean.Symmetry
public import Erdos821.P3Clean.Structure

/-! Active-list permutations preserve the literal memory measure. -/

@[expose] public section

section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {P : PrimeGroups}

alias smallPhysical_act := _root_.Erdos821.P3Edge.smallPhysical_permuteActive_iff

theorem memoryMass_permuteActive  F   J n 
     π   s  :
    P.memoryMass F J n (permuteActive π s) = P.memoryMass F J n s := by
  classical
  have ha : (∏ g : P.BigGroup, ∏ i : Fin (J + F.ell),
      tiltedMu F P n g.val ((P.act π s.2.1) g.val i)) =
      ∏ g : P.BigGroup, ∏ i : Fin (J + F.ell), tiltedMu F P n g.val (s.2.1 g.val i) := by
    apply Finset.prod_congr rfl
    intro g _
    exact Equiv.prod_comp (π g.val) (fun i => tiltedMu F P n g.val (s.2.1 g.val i))
  simp only [PrimeGroups.memoryMass, permuteActive, smallPhysical_act, ha]

end Erdos821.P3Clean
