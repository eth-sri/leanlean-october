import Mathlib.Tactic

import RequestProject.TreeChainFinsupp
import RequestProject.FreshLoopTreeStrictness
import RequestProject.PresWordDiskTopologicalChains

/-! Collapse a chain along compatible spanning trees, preserving the
initial tree literally and retaining strictness from fresh loops/faces.
The final topology comparison is displayed as an explicit input here;
it is not claimed to be constructed by this file. Pending Lean check. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb.TopChainFS
open SpanningTree
variable {K : Complex2} {n : ℕ} (c : TopChainFS K n)
  (T₀ : SpanningTree (c.X 0))

def stageTree (i : ℕ) : SpanningTree (c.X i) :=
  Nat.rec T₀ (fun i U =>
    (exists_extension (c.inc i) (c.conn (i + 1)) U.root U
      (c.incV i) (c.incE i)).choose) i

abbrev stageTree_compatible (i : ℕ) (e : (c.X i).E)  :=
  (exists_extension (c.inc i) (c.conn (i + 1)) (c.stageTree T₀ i).root
    (c.stageTree T₀ i) (c.incV i) (c.incE i)).choose_spec.2 e

def treePresentationTopChain : PresChainTopFS (treeRel T₀) n where
  gen i := NonTree (c.stageTree T₀ i)
  cell i := (c.X i).F
  decGen _ := inferInstance
  rel i := treeRel (c.stageTree T₀ i)
  genIncl i := nonTreeIncl (c.stageTree_compatible T₀ i)
  genIncl_injective i := nonTreeIncl_injective (c.stageTree_compatible T₀ i) (c.incE i)
  cellIncl i := (c.inc i).onF
  cellIncl_injective := c.incF
  rel_incl i := treeRel_onF (c.stageTree_compatible T₀ i)
  baseGen := id
  baseGen_injective := Function.injective_id
  baseCell := id
  baseCell_injective := Function.injective_id
  rel_base j := by
    change treeRel T₀ j = FreeGroup.map id (treeRel T₀ j)
    rw [FreeGroup.map.id]
  zero_pi2 i hi := zeroPi2_presInclHom_of_zeroPi2
    (c.stageTree_compatible T₀ i) (c.incE i) (c.zero_pi2 i hi)

def treePresentationChain : PresChainFS (treeRel T₀) n :=
  (c.treePresentationTopChain T₀).toPresChainFS

abbrev treePresentationChain_proper
    (hp : ∀ i, i < n → FreshLoopOrFace (c.inc i)) (i : ℕ) (hi : i < n)  :=
  nonTree_or_face_fresh (c.stageTree_compatible T₀ i) (hp i hi)

/-- All stages and their vanishing maps are now actual relative word-disk
extensions. Only the initial topological comparison remains to instantiate. -/
abbrev hasOriginalChain_of_initial_tree_comparison (X : Whitehead.TwoComplex)
    (a : NonTree T₀)
    (e₀ : ContinuousMap.HomotopyEquiv
      (PresModel.ClassicalPresWordDisks (PresModel.presCanonicalWords (treeRel T₀) a)
        (PresModel.presCanonicalWords_ne_nil (treeRel T₀) a)) X)
    (hp : ∀ i, i < n → FreshLoopOrFace (c.inc i))  :=
  (c.treePresentationChain T₀).hasOriginalTopologicalChain X a e₀
    (c.treePresentationChain_proper T₀ hp) false (by simp)

end FiniteChains.Comb.TopChainFS
