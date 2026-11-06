import RequestProject.ClassicalGraphTreeBoundaryWords
import RequestProject.BoundaryWordNaturality


/-! Tree deletion commutes literally with compatible graph inclusions.
Thus the resulting rose relators retain their original cell labels and
the expected generator injection, before taking free-group quotients.
Unverified source. -/

noncomputable section
namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped Classical
variable {V W J K : Type} [TopologicalSpace V] [TopologicalSpace W]
  [DiscreteTopology V] [DiscreteTopology W]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V)
  (s : BoundaryFamily K (Fin 1 → ℝ) → W)
  (T : Comb.SpanningTree (graphCx r)) (U : Comb.SpanningTree (graphCx s))
  (h : Comb.Hom (graphCx r) (graphCx s))
  (ht : ∀ j, U.isTree (h.onE j) ↔ T.isTree j)

omit [TopologicalSpace V] [TopologicalSpace W] [DiscreteTopology V] [DiscreteTopology W]

theorem treeLetters_map (l : List (J × Bool)) :
    treeLetters s U (Comb.mapPath h l) =
      (treeLetters r T l).map (fun g => (graphNonTreeMap r s T U h ht g.1, g.2)) := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    change treeLetters s U ((h.onE g.1, g.2) :: Comb.mapPath h l) = _
    by_cases hg : T.isTree g.1
    · have hu := (ht g.1).mpr hg
      simp_all [treeLetters, dif_pos hg]
    · have hu : ¬U.isTree (h.onE g.1) := by grind
      simp [treeLetters, dif_neg hg, dif_neg hu, List.map_cons]
      tauto

theorem BoundaryWords.eraseTree_natural (b : BoundaryWords r) :
    (b.map h).eraseTree s U =
      (b.eraseTree r T).map (graphRoseCombinatorialMap r s T U h ht) := by
  have hw : ∀ i, ((b.map h).eraseTree s U).word i =
      ((b.eraseTree r T).map (graphRoseCombinatorialMap r s T U h ht)).word i :=
    fun i => treeLetters_map r s T U h ht _
  have extWords (x y : BoundaryWords (roseAttaching {k : K // ¬U.isTree k}))
      (hv : x.vertex = y.vertex) (hw : x.word = y.word) : x = y := by
    cases x
    simp_all
  apply extWords
  · rfl
  grind

theorem BoundaryWords.eraseTree_loop_natural (b : BoundaryWords r) :
    ((b.map h).eraseTree s U).loopWord =
      ((b.eraseTree r T).loopWord).map
        (fun g => (graphNonTreeMap r s T U h ht g.1, g.2)) := by
  rw [BoundaryWords.eraseTree_natural r s T U h ht b]
  exact BoundaryWords.loopWord_map _ _
