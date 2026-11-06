import RequestProject.HomeomorphContinuousMap
import RequestProject.ClassicalGraphTreeWords
import RequestProject.ClassicalGraphBoundaryWords
import RequestProject.Tac


/-! Collapsing the graph's spanning tree changes the actual boundary
map to the word obtained by deleting tree letters. The homotopy is
constructed on all four sides with fixed corner values. Unverified. -/

noncomputable section
bwd

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped Classical unitInterval
variable {V J : Type} [TopologicalSpace V] [DiscreteTopology V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V) (hr : Continuous r)
  (T : Comb.SpanningTree (graphCx r))

def BoundaryWords.eraseTree (W : BoundaryWords r) :
    BoundaryWords (roseAttaching {j : J // ¬T.isTree j}) where
  vertex := fun _ => PUnit.unit
  word s := treeLetters r T (W.word s)
  isPath _ := rose_word_isPath _

omit [TopologicalSpace V] [DiscreteTopology V] in
theorem BoundaryWords.eraseTree_loopWord (W : BoundaryWords r) :
    (W.eraseTree r T).loopWord = treeLetters r T W.loopWord := by
  simp [BoundaryWords.loopWord, BoundaryWords.eraseTree,
    List.append_eq, treeLetters_append, treeLetters_revPath]

omit [TopologicalSpace V] [DiscreteTopology V] in
theorem BoundaryWords.eraseTree_mk (W : BoundaryWords r) :
    FreeGroup.mk (W.eraseTree r T).loopWord = Comb.SpanningTree.pathWord T W.loopWord := by
  rw [W.eraseTree_loopWord, treeLetters_mk]

theorem BoundaryWords.collapse_homotopic_eraseTree (W : BoundaryWords r) :
    ((graphRoseHomotopyEquiv r hr T).toFun.comp W.boundaryMap).Homotopic
      (W.eraseTree r T).boundaryMap := by
  let W' := W.eraseTree r T
  let H (s : SquareSide) := Classical.choice
    (collapsedWordPath_homotopic_treeWord r hr T _ (W.isPath s))
  have hend : ∀ s t u, u = 0 ∨ u = 1 →
      H s (t, u) = roseVertex _ := by
    simp
  let G := squareBoundaryHomotopyPasting _
    (fun _ _ => roseVertex _) hend
  let HG : ((graphRoseHomotopyEquiv r hr T).toFun.comp W.squareMap).Homotopy W'.squareMap := {
    toContinuousMap := G
    map_zero_left := by
      intro z
      obtain ⟨⟨s, u⟩, rfl⟩ := squareSideQuotient_surjective z
      change squareBoundaryHomotopyPasting _ _ hend (0, squareSideMap s u) = _
      rw [squareBoundaryHomotopyPasting_side]
      change H s (0, u) = graphRoseHomotopyEquiv r hr T (W.squareMap (squareSideMap s u))
      aesop
    map_one_left := by
      intro z
      obtain ⟨⟨s, u⟩, rfl⟩ := squareSideQuotient_surjective z
      change squareBoundaryHomotopyPasting _ _ hend (1, squareSideMap s u) = _
      rw [squareBoundaryHomotopyPasting_side]
      change H s (1, u) = W'.squareMap (squareSideMap s u)
      aesop }
  exact ⟨HG.compContinuousMap unitBoundarySquareHomeomorph.toContinuousMap⟩
