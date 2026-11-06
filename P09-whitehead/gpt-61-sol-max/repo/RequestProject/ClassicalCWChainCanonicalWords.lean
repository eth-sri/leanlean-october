import Mathlib.Tactic

import RequestProject.ClassicalCWChainRoseModels
import RequestProject.StabilizedDiskNaturality
import RequestProject.ClassicalRoseWordNaturality
import RequestProject.PresCircleWordParametrization
import RequestProject.PresCanonicalWords
import RequestProject.PresWordDiskNaturality

/-! Nonempty canonical presentation words for the entire original CW
filtration. Both generator and relator embeddings are actual injective
maps of the retained labels. Unverified source. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel
open Set Topology
open scoped Classical
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C]
  [TreeChoice K C]

variable (i : Fin (n + 1))
def roseWord  (j : RelCWComplex.cell (C i : Set K) 2) :
    BoundaryWords (roseAttaching (RoseGen K C hC hconn i)) := by
  letI := subcomplexZeroSkeleton_discrete (C i)
  exact (word C hC i j).eraseTree (skeletonAttachingMap (C i : Set K) 1)
    (chainTree K C hC hconn i)

theorem roseWord_loop_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set K) 2) :
    (roseWord K C hC hconn k (subcomplexCellInclusion (hC hik) 2 j)).loopWord =
      ((roseWord K C hC hconn i j).loopWord).map
        (fun p => (roseGenInclusion K C hC hconn hik p.1, p.2)) := by
  letI := subcomplexZeroSkeleton_discrete (C i)
  letI := subcomplexZeroSkeleton_discrete (C k)
  unfold roseWord
  rw  [word_natural C hC hik j]
  exact BoundaryWords.eraseTree_loop_natural _ _ _ _
    (subcomplexGraphInclusion (hC hik)) (chainTree_compatible K C hC hconn hik) _

abbrev CanonicalGen  := RoseGen K C hC hconn i ⊕ PUnit.{1}
abbrev CanonicalRel  := RelCWComplex.cell (C i : Set K) 2 ⊕ PUnit.{1}

def canonicalGenInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :
    CanonicalGen K C hC hconn i ↪ CanonicalGen K C hC hconn k :=
  StabilizedDiskPresentation.withDummy (roseGenInclusion K C hC hconn hik)

def canonicalCellInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :
    CanonicalRel K C i ↪ CanonicalRel K C k :=
  StabilizedDiskPresentation.withDummy (subcomplexCellInclusion (hC hik) 2)



def canonicalRelators  :
    CanonicalRel K C i → FreeGroup (CanonicalGen K C hC hconn i)
  | .inl j => FreeGroup.map Sum.inl (FreeGroup.mk (roseWord K C hC hconn i j).loopWord)
  | .inr _ => FreeGroup.of (Sum.inr PUnit.unit)

theorem canonicalRelators_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : CanonicalRel K C i) :
    canonicalRelators K C hC hconn k (canonicalCellInclusion K C hC hik j) =
      FreeGroup.map (canonicalGenInclusion K C hC hconn hik) (canonicalRelators K C hC hconn i j) := by
  cases j with
  | inl j =>
      simp only [canonicalRelators, canonicalCellInclusion, StabilizedDiskPresentation.withDummy, Function.Embedding.coeFn_mk, Sum.map_inl]
      rw (config := { transparency := .default }) [roseWord_loop_natural K C hC hconn hik j]
      simp 
      rfl
  | inr u =>
      rfl

def canonicalWords   :=
  presCanonicalWords (canonicalRelators K C hC hconn i) (Sum.inr PUnit.unit)

variable (j : CanonicalRel K C i)
abbrev canonicalWords_ne_nil    :=
  FiniteChains.PresModel.presCanonicalWords_ne_nil (FiniteChains.ClassicalCW.ChainWords.canonicalRelators K C hC hconn i)
    (Sum.inr PUnit.unit) j

abbrev canonicalWords_mk    :=
  FiniteChains.PresModel.mk_presCanonicalWords (FiniteChains.ClassicalCW.ChainWords.canonicalRelators K C hC hconn i)
    (Sum.inr PUnit.unit) j

def canonicalWordEmbedding {i k : Fin (n + 1)} (hik : i ≤ k)  :=
  canonicalPresWordEmbedding _ _ (canonicalGenInclusion K C hC hconn hik)
    (canonicalCellInclusion K C hC hik) (canonicalRelators_natural K C hC hconn hik)
    (Sum.inr PUnit.unit)

def stabilizedAttaching  :=
  StabilizedDiskPresentation.attaching (collapsedAttaching K C hC hconn i)

def stabilizedCellBoundary   :=
  (stabilizedAttaching K C hC hconn i).comp
    (⟨fun a => ⟨j, a⟩, by
        grind [continuous_sigmaMk]⟩ : C(UnitBoundary (Fin 2 → ℝ),
      BoundaryFamily (CanonicalRel K C i) (Fin 2 → ℝ)))

theorem stabilizedCellBoundary_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : CanonicalRel K C i) :
    (diskRoseMap (canonicalGenInclusion K C hC hconn hik)).comp
        (stabilizedCellBoundary K C hC hconn i j) =
      stabilizedCellBoundary K C hC hconn k (canonicalCellInclusion K C hC hik j) := by
  classical solve_by_elim (transparency := .default) (maxDepth := 10) [ContinuousMap.ext, FiniteChains.RelativeAttachment.StabilizedDiskPresentation.attaching_natural, Whitehead.TwoComplex.hausdorff, FiniteChains.ClassicalCW.ChainWords.collapsedAttaching_natural]

theorem stabilizedCellBoundary_homotopic   :
    (stabilizedCellBoundary K C hC hconn i j).Homotopic
      (classicalPresCellBoundary (canonicalWords K C hC hconn i) j
        (canonicalWords_ne_nil K C hC hconn i)) := by
  cases j with
  | inl j =>
      letI := subcomplexZeroSkeleton_discrete (C i)
      have H₀ := (word C hC i j).collapse_homotopic_eraseTree
        (skeletonAttachingMap (C i : Set K) 1) (skeletonAttachingMap (C i : Set K) 1).continuous
        (chainTree K C hC hconn i)
      have H₁ := H₀.trans (boundaryWords_homotopic_classicalWord (roseWord K C hC hconn i j))
      have H := (ContinuousMap.Homotopic.refl (diskRoseMap
        (Sum.inl : RoseGen K C hC hconn i → CanonicalGen K C hC hconn i))).comp H₁
      rw  [classicalRoseWordBoundary_map] at H
      have he : FreeGroup.mk (((roseWord K C hC hconn i j).loopWord).map
          (fun p => (Sum.inl p.1, p.2))) =
          FreeGroup.mk (canonicalWords K C hC hconn i (Sum.inl j)) := by
        rw (config := { transparency := .default }) [canonicalWords_mk]
        rfl
      exact H.trans ((classicalRoseWordBoundary_homotopic_of_mk_eq he).trans
        (classicalPresWordAttaching_homotopic_read (canonicalWords K C hC hconn i)
          (Sum.inl j) (canonicalWords_ne_nil K C hC hconn i)).symm)
  | inr u =>
      cases u
      have H := (ContinuousMap.Homotopic.refl (diskRoseMap
        (Sum.inr : PUnit → CanonicalGen K C hC hconn i))).comp
          dummyCircleBoundaryHomeomorph_homotopic_word
      rw  [classicalRoseWordBoundary_map] at H
      have he  :=
        (canonicalWords_mk K C hC hconn i (Sum.inr PUnit.unit)).symm
      exact H.trans ((classicalRoseWordBoundary_homotopic_of_mk_eq he).trans
        (classicalPresWordAttaching_homotopic_read (canonicalWords K C hC hconn i)
          (Sum.inr PUnit.unit) (canonicalWords_ne_nil K C hC hconn i)).symm)

end FiniteChains.ClassicalCW.ChainWords
