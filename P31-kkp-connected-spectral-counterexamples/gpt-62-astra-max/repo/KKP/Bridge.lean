module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fin.VecNotation
@[expose] public section

/-! # A balanced complete tripartite graph joined to a four-clique by one edge -/

namespace KKP
open SimpleGraph

variable (s : ℕ)

abbrev BridgeVertex := (Fin 3 × Fin s) ⊕ Fin 4

-- Vertices in the tripartite graph (part, coordinate) and the clique, respectively.
scoped notation "L" i:arg a:arg => Sum.inl (i, a)
scoped prefix:max "R" => Sum.inr

/-- Tripartite adjacency, clique adjacency, and the unique zero-coordinate bridge. -/
def bridgeAdj : BridgeVertex s → BridgeVertex s → Prop
  | L i _, L j _ => i ≠ j
  | R a, R b => a ≠ b
  | L i a, R b | R b, L i a => i.val = 0 ∧ a.val = 0 ∧ b.val = 0

/-- The literal simple graph in the counterexample family. -/
def bridgeGraph : SimpleGraph (BridgeVertex s) where
  Adj := bridgeAdj s
  symm := ⟨fun
    | L _ _, L _ _ | R _, R _ => fun h => Ne.symm h
    | L _ _, R _ | R _, L _ _ => fun h => h⟩
  loopless := ⟨fun
    | L _ _ | R _ => fun h => h rfl⟩

instance bridgeAdjDecidable : DecidableRel (bridgeGraph s).Adj
  | L _ _, L _ _ | R _, R _ => inferInstanceAs (Decidable (_ ≠ _))
  | L _ _, R _ | R _, L _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The complete graph on five vertices with only the edge `{3,4}` removed. -/
def forbiddenGraph : SimpleGraph (Fin 5) where
  Adj i j := i ≠ j ∧ ¬ (3 ≤ i.val ∧ 3 ≤ j.val)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, fun t => h.2 ⟨t.2, t.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance forbiddenAdjDecidable : DecidableRel forbiddenGraph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ ¬ _))

/-- Four colors suffice, and the first four vertices form a clique. -/
theorem forbidden_chromaticNumber : forbiddenGraph.chromaticNumber = 4 := by
  apply le_antisymm (Colorable.chromaticNumber_le ⟨.mk ![0, 1, 2, 3, 3] (by decide)⟩)
  exact le_chromaticNumber_of_pairwise_adj (by simp) Fin.castSucc (by unfold Pairwise; decide)

end KKP
