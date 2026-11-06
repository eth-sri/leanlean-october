import Mathlib.Tactic

import RequestProject.ClassicalGraphRoseNaturality
import RequestProject.ContinuousEdgeWords
import RequestProject.TreePresentation

/-! The exact finite word read by collapsing a spanning tree. The word
is obtained by deleting the tree letters; the corresponding continuous
path homotopy removes precisely the resulting constant pauses. Unverified. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment ContinuousEdgeWords
open scoped Classical unitInterval
variable {V J : Type} [TopologicalSpace V] [DiscreteTopology V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V) (hr : Continuous r)
  (T : Comb.SpanningTree (graphCx r))

def treeLetters : List (J × Bool) → List ({j : J // ¬T.isTree j} × Bool)
  | [] => []
  | g :: l => if h : T.isTree g.1 then treeLetters l
      else (⟨g.1, h⟩, g.2) :: treeLetters l

section
omit [TopologicalSpace V] [DiscreteTopology V]
theorem treeLetters_append (l m : List (J × Bool)) :
    treeLetters r T (l ++ m) = treeLetters r T l ++ treeLetters r T m := by
  induction l <;> aesop (add simp [treeLetters])

variable (l : List (J × Bool))
theorem treeLetters_revPath  :
    treeLetters r T (Comb.revPath (X := graphCx r) l) =
      Comb.revPath (X := graphCx (roseAttaching {j : J // ¬T.isTree j})) (treeLetters r T l) := by
  induction l <;> aesop (add simp [treeLetters_append, treeLetters, Comb.revGerm, Comb.revPath])

theorem treeLetters_mk  :
    FreeGroup.mk (treeLetters r T l) = Comb.SpanningTree.pathWord T l := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    by_cases h : T.isTree g.1
    · rw [treeLetters, dif_pos h, Comb.SpanningTree.pathWord_cons T g l,
        Comb.SpanningTree.germWord_of_isTree T h, one_mul, ih]
    · rw [treeLetters, dif_neg h, Comb.SpanningTree.pathWord_cons]
      change FreeGroup.mk ([(⟨g.1, h⟩, g.2)] ++ treeLetters r T l) = _
      rw [← FreeGroup.mul_mk, ih]
      aesop (add simp [Comb.SpanningTree.germWord])
end

theorem rose_word_isPath {A : Type} (l : List (A × Bool)) :
    Comb.IsPath (graphCx (roseAttaching A)).src (graphCx (roseAttaching A)).tgt l
      PUnit.unit PUnit.unit := by
  induction l <;> aesop

variable (l : List (J × Bool))
def treeRoseWordPath   :=
  realize _ _ (old (roseAttaching _) _) (graphEdgePath (roseAttaching _))
    (treeLetters r T l) (rose_word_isPath _)

def collapsedWordPath  {a b : V}
    (hl : Comb.IsPath (graphSrc r) (graphTgt r) l a b)  :=
  ((realize _ _ (old r _) (graphEdgePath r) l hl).map
    (graphRoseHomotopyEquiv r hr T).continuous).cast
      (graphRoseHomotopyEquiv_old r hr T a).symm
      (graphRoseHomotopyEquiv_old r hr T b).symm

variable (g : J × Bool)
def collapsedGermPath   :=
  ((graphGermPath r g).map (graphRoseHomotopyEquiv r hr T).continuous).cast
    (graphRoseHomotopyEquiv_old r hr T _).symm
    (graphRoseHomotopyEquiv_old r hr T _).symm

theorem collapsedGermPath_tree  (h : T.isTree g.1) :
    collapsedGermPath r hr T g = Path.refl _ := by
  apply Path.ext
  funext t
  cases g with
  | mk j o =>
    cases o <;> exact graphRoseHomotopyEquiv_treePath r hr T ⟨j, h⟩ _

theorem collapsedGermPath_nonTree  (h : ¬T.isTree g.1) :
    collapsedGermPath r hr T g =
      germPath (graphSrc (roseAttaching _)) (graphTgt (roseAttaching _))
        (old (roseAttaching _) _) (graphEdgePath (roseAttaching _)) (⟨g.1, h⟩, g.2) := by
  apply Path.ext
  funext t
  cases g with
  | mk j o =>
    cases o <;> exact graphRoseHomotopyEquiv_nonTreeCell r hr T ⟨⟨j, h⟩, graphDiskHomeomorph _⟩

theorem collapsedWordPath_cons  (l : List (J × Bool)) {a b : V}
    (hl : Comb.IsPath (graphSrc r) (graphTgt r) (g :: l) a b) :
    collapsedWordPath r hr T (g :: l) hl =
      (collapsedGermPath r hr T g).trans (collapsedWordPath r hr T l hl.2) := by
  apply Path.ext
  funext t
  simp only [collapsedWordPath, realize, Path.cast_coe, Path.map_coe, Function.comp_apply, Path.trans_apply]
  split_ifs
  · cases g with | mk j o => cases o <;> rfl
  · rfl

theorem collapsedWordPath_homotopic_treeWord  {a b : V}
    (hl : Comb.IsPath (graphSrc r) (graphTgt r) l a b) :
    (collapsedWordPath r hr T l hl).Homotopic (treeRoseWordPath r T l) := by
  induction l generalizing a with
  | nil => exact Path.Homotopic.refl _
  | cons g l ih =>
    rw [collapsedWordPath_cons]
    by_cases hg : T.isTree g.1
    · rw [collapsedGermPath_tree r hr T g hg]
      have ht : treeRoseWordPath r T (g :: l) = treeRoseWordPath r T l := by
        simp_all [treeRoseWordPath, treeLetters]
      rw [ht]
      exact ((Path.Homotopic.refl _).hcomp (ih hl.2)).trans (Path.Homotopic.refl_trans _)
    · rw [collapsedGermPath_nonTree r hr T g hg]
      have ht : treeRoseWordPath r T (g :: l) =
          (germPath (graphSrc (roseAttaching _)) (graphTgt (roseAttaching _))
            (old (roseAttaching _) _) (graphEdgePath (roseAttaching _))
              (⟨g.1, hg⟩, g.2)).trans (treeRoseWordPath r T l) := by
        simp_all [treeRoseWordPath, treeLetters, realize]
      rw [ht]
      exact (Path.Homotopic.refl _).hcomp (ih hl.2)

end FiniteChains.ClassicalGraphModel
