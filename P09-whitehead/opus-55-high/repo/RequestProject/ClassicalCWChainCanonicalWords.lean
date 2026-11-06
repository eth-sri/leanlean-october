import RequestProject.ClassicalCWChainRoseModels
import RequestProject.StabilizedDiskNaturality
import RequestProject.ClassicalRoseWordNaturality
import RequestProject.PresCircleWordParametrization
import RequestProject.PresCanonicalWords
import RequestProject.PresWordDiskNaturality
import RequestProject.Tac


/-! Nonempty canonical presentation words for the entire original CW
filtration. Both generator and relator embeddings are actual injective
maps of the retained labels. Unverified source. -/

noncomputable section
bwd

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel
open Set Topology
open scoped Classical
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C]
  [TreeChoice K C]

def roseWord i (j : RelCWComplex.cell (C i : Set K) 2) :
    BoundaryWords (roseAttaching (RoseGen K C hC hconn i)) := (word C hC i j).eraseTree _
    _

theorem roseWord_loop_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    j :
    (roseWord K C hC hconn k (subcomplexCellInclusion (hC hik) 2 j)).loopWord =
      ((roseWord K C hC hconn i j).loopWord).map
        (fun p => (roseGenInclusion K C hC hconn hik p.1, p.2)) := by
  unfold roseWord
  rwd [word_natural C hC hik j]
  exact BoundaryWords.eraseTree_loop_natural _ _ _ _
    _ (chainTree_compatible K C hC hconn hik) _

abbrev CanonicalGen (i : Fin (n + 1)) := RoseGen K C hC hconn i ⊕ PUnit.{1}
abbrev CanonicalRel (i : Fin (n + 1)) := RelCWComplex.cell (C i : Set K) 2 ⊕ PUnit.{1}

def canonicalGenInclusion (hik : i ≤ k) :
    CanonicalGen K C hC hconn i ↪ CanonicalGen K C hC hconn k :=
  StabilizedDiskPresentation.withDummy (roseGenInclusion K C hC hconn hik)

def canonicalCellInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :
    CanonicalRel K C i ↪ CanonicalRel K C k :=
  StabilizedDiskPresentation.withDummy (subcomplexCellInclusion (hC hik) 2)


def canonicalRelators (i : Fin (n + 1)) :
    CanonicalRel K C i → FreeGroup (CanonicalGen K C hC hconn i)
  | .inl j => FreeGroup.map Sum.inl (FreeGroup.mk (roseWord K C hC hconn i j).loopWord)
  | .inr _ => FreeGroup.of (Sum.inr PUnit.unit)

theorem canonicalRelators_natural hik
    (j : CanonicalRel K C i) :
    canonicalRelators K C hC hconn k (canonicalCellInclusion K C hC hik j) =
      FreeGroup.map (canonicalGenInclusion K C hC hconn hik) (canonicalRelators K C hC hconn i j) := by
  cases j with
  | inl j =>
      simp only [canonicalRelators, canonicalCellInclusion, StabilizedDiskPresentation.withDummy,
        Function.Embedding.coeFn_mk, Sum.map_inl]
      rwd [roseWord_loop_natural K C hC hconn hik j]
      aesop
  | inr u =>
      rfl

def canonicalWords i :
    CanonicalRel K C i → List (CanonicalGen K C hC hconn i × Bool) :=
  presCanonicalWords (canonicalRelators K C hC hconn i) (Sum.inr PUnit.unit)

theorem canonicalWords_ne_nil i j :
    canonicalWords K C hC hconn i j ≠ [] := presCanonicalWords_ne_nil _ _ _

theorem canonicalWords_mk i j :
    FreeGroup.mk (canonicalWords K C hC hconn i j) = canonicalRelators K C hC hconn i j :=
  mk_presCanonicalWords _ _ _

def canonicalWordEmbedding (hik : i ≤ k) :
    PresWordEmbedding (canonicalWords K C hC hconn i) (canonicalWords K C hC hconn k) :=
  canonicalPresWordEmbedding _ _ _
    _ (canonicalRelators_natural K C hC hconn hik)
    _

def stabilizedAttaching (i : Fin (n + 1)) :=
  StabilizedDiskPresentation.attaching (collapsedAttaching K C hC hconn i)

def stabilizedCellBoundary (i : Fin (n + 1)) (j : CanonicalRel K C i) :=
  (stabilizedAttaching K C hC hconn i).comp
    (⟨fun a => ⟨j, a⟩, continuous_sigmaMk (σ := fun _ : CanonicalRel K C i => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩ : C(UnitBoundary (Fin 2 → ℝ),
      BoundaryFamily (CanonicalRel K C i) (Fin 2 → ℝ)))

theorem stabilizedCellBoundary_natural hik
    j :
    (diskRoseMap (canonicalGenInclusion K C hC hconn hik)).comp
        (stabilizedCellBoundary K C hC hconn i j) =
      stabilizedCellBoundary K C hC hconn k (canonicalCellInclusion K C hC hik j) := by
  ext a
  exact StabilizedDiskPresentation.attaching_natural
    _ _
    _ _
    (fun z => collapsedAttaching_natural K C hC hconn hik z.1 z.2) _

theorem stabilizedCellBoundary_homotopic i j :
    (stabilizedCellBoundary K C hC hconn i j).Homotopic
      (classicalPresCellBoundary (canonicalWords K C hC hconn i) j
        (canonicalWords_ne_nil K C hC hconn i)) := by
  cases j with
  | inl j =>
      letI := subcomplexZeroSkeleton_discrete (C i)
      have H₀ := (word C hC i j).collapse_homotopic_eraseTree
        _ (skeletonAttachingMap (C i : Set K) 1).continuous
        (chainTree K C hC hconn i)
      have H₁ := H₀.trans (boundaryWords_homotopic_classicalWord _)
      have H := (ContinuousMap.Homotopic.refl (diskRoseMap
        (Sum.inl : RoseGen K C hC hconn i → CanonicalGen K C hC hconn i))).comp H₁
      rwd [classicalRoseWordBoundary_map] at H
      have he : FreeGroup.mk (((roseWord K C hC hconn i j).loopWord).map
          (fun p => (Sum.inl p.1, p.2))) =
          FreeGroup.mk (canonicalWords K C hC hconn i (Sum.inl j)) := by
        rwd [canonicalWords_mk]
        rfl
      exact H.trans ((classicalRoseWordBoundary_homotopic_of_mk_eq he).trans
        (classicalPresWordAttaching_homotopic_read _
          _ _).symm)
  | inr u =>
      cases u
      have H := (ContinuousMap.Homotopic.refl (diskRoseMap
        (Sum.inr : PUnit → CanonicalGen K C hC hconn i))).comp
          dummyCircleBoundaryHomeomorph_homotopic_word
      rwd [classicalRoseWordBoundary_map] at H
      have he :=
        (canonicalWords_mk K C hC hconn i (Sum.inr PUnit.unit)).symm
      exact H.trans ((classicalRoseWordBoundary_homotopic_of_mk_eq he).trans
        (classicalPresWordAttaching_homotopic_read _
          _ _).symm)
