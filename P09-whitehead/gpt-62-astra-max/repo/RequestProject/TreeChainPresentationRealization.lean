module

public import RequestProject.TreeChainFinsupp
public import RequestProject.FreshLoopTreeStrictness
public import RequestProject.PresWordDiskTopologicalChains

@[expose] public section

/-! Collapse a chain along compatible spanning trees, preserving the
initial tree literally and retaining strictness from fresh loops/faces.
The final topology comparison is displayed as an explicit input here;
it is not claimed to be constructed by this file. Pending Lean check. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb.TopChainFS
open SpanningTree
variable {n : ℕ} (c : TopChainFS.{0} n)
  (T₀ : SpanningTree (c.X 0))

variable (i : ℕ)

def stageTree : SpanningTree (c.X i) :=
  Nat.rec T₀ (fun i U =>
    (exists_extension (c.inc i) (c.conn (i + 1)) U.root U
      (c.incV i) (c.incE i)).choose) i

theorem stageTree_compatible (e : (c.X i).E) :
    (c.stageTree T₀ (i + 1)).isTree ((c.inc i).onE e) ↔
      (c.stageTree T₀ i).isTree e :=
  (exists_extension (c.inc i) (c.conn (i + 1)) (c.stageTree T₀ i).root
    (c.stageTree T₀ i) (c.incV i) (c.incE i)).choose_spec.2 e

def treePresentationChain : PresChainFS (treeRel T₀) n where
  gen i := NonTree (c.stageTree T₀ i)
  cell i := (c.X i).F
  decGen _ := inferInstance
  rel i := treeRel (c.stageTree T₀ i)
  genIncl i := ⟨_, nonTreeIncl_injective (c.stageTree_compatible T₀ i) (c.incE i)⟩
  cellIncl i := ⟨_, c.incF i⟩
  rel_incl i := treeRel_onF (c.stageTree_compatible T₀ i)
  baseGen := Function.Embedding.refl _
  baseCell := Function.Embedding.refl _
  rel_base j := by
    change treeRel T₀ j = FreeGroup.map id (treeRel T₀ j)
    simp
  zero_pi2 i hi := (zeroPi2_presInclHom_iff (ρ := treeRel (c.stageTree T₀ i)) (σ := treeRel (c.stageTree T₀ (i + 1))) (nonTreeIncl (c.stageTree_compatible T₀ i))
    (nonTreeIncl_injective (c.stageTree_compatible T₀ i) (c.incE i))
    (c.inc i).onF (treeRel_onF (c.stageTree_compatible T₀ i))).mp
      (zeroPi2_presInclHom_of_zeroPi2 (c.stageTree_compatible T₀ i) (c.incE i) (c.zero_pi2 i hi))

theorem treePresentationChain_proper
    (hp : ∀ i, i < n → FreshLoopOrFace (c.inc i)) (i : ℕ) (hi : i < n) :
    (∃ a : (c.treePresentationChain T₀).gen (i + 1),
      a ∉ Set.range ((c.treePresentationChain T₀).genIncl i)) ∨
    ∃ f : (c.treePresentationChain T₀).cell (i + 1),
      f ∉ Set.range ((c.treePresentationChain T₀).cellIncl i) :=
  nonTree_or_face_fresh (c.stageTree_compatible T₀ i) (hp i hi)

/-- All stages and their vanishing maps are now actual relative word-disk
extensions. Only the initial topological comparison remains to instantiate. -/
theorem hasOriginalChain_of_initial_tree_comparison (X : Whitehead.TwoComplex)
    (a : NonTree T₀)
    (e₀ : ContinuousMap.HomotopyEquiv
      (PresModel.ClassicalPresWordDisks (PresModel.presCanonicalWords (treeRel T₀) a)
        (PresModel.presCanonicalWords_ne_nil (treeRel T₀) a)) X)
    (hp : ∀ i, i < n → FreshLoopOrFace (c.inc i)) :
    Whitehead.HasChain X n false :=
  (c.treePresentationChain T₀).hasOriginalTopologicalChain X a e₀
    (c.treePresentationChain_proper T₀ hp) false (by simp)

end FiniteChains.Comb.TopChainFS
