module

public import RequestProject.ClassicalCWChainRoseModels
public import RequestProject.StabilizedDiskNaturality
public import RequestProject.ClassicalRoseWordNaturality
public import RequestProject.PresCircleWordParametrization
public import RequestProject.PresCanonicalWords
public import RequestProject.PresWordDiskNaturality

@[expose] public section

/-! Nonempty canonical presentation words for the entire original CW
filtration. Both generator and relator embeddings are actual injective
maps of the retained labels. Unverified source. -/

noncomputable section

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel
open Set Topology
open scoped Classical
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C]
  [TreeChoice K C]

def roseWord (i : Fin _) (j : RelCWComplex.cell (C i : Set K) 2) :
    BoundaryWords (roseAttaching (RoseGen K C hC hconn i)) := (word C hC i j).eraseTree _
    _

theorem roseWord_loop_natural {i k : Fin _} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set K) 2) :
    (roseWord K C hC hconn k (subcomplexCellInclusion (hC hik) 2 j)).loopWord =
      ((roseWord K C hC hconn i j).loopWord).map
        (fun p => (roseGenInclusion K C hC hconn hik p.1, p.2)) := by
  unfold roseWord; erw [word_natural C hC hik j]; exact BoundaryWords.eraseTree_loop_natural _ _ _ _
    _ (chainTree_compatible K C hC hconn hik) _

variable (i : Fin (n + 1))

abbrev CanonicalGen := RoseGen K C hC hconn i ⊕ PUnit.{1}
abbrev CanonicalRel := RelCWComplex.cell (C i : Set K) 2 ⊕ PUnit.{1}

variable {i k : Fin (n + 1)} (hik : i ≤ k)

def canonicalGenInclusion :
    CanonicalGen K C hC hconn i ↪ CanonicalGen K C hC hconn k :=
  StabilizedDiskPresentation.withDummy (roseGenInclusion K C hC hconn hik)

def canonicalCellInclusion :
    CanonicalRel K C i ↪ CanonicalRel K C k :=
  StabilizedDiskPresentation.withDummy (subcomplexCellInclusion (hC hik) 2)

theorem canonicalGenInclusion_comp {i k l : Fin _} (hik : i ≤ k) (hkl : k ≤ l)
    (a : CanonicalGen K C hC hconn i) :
    canonicalGenInclusion K C hC hconn hkl (canonicalGenInclusion K C hC hconn hik a) =
      canonicalGenInclusion K C hC hconn (hik.trans hkl) a := by
  cases a <;> rfl

def canonicalRelators (i : Fin _) :
    CanonicalRel K C i → FreeGroup (CanonicalGen K C hC hconn i)
  | .inl j => FreeGroup.map Sum.inl (FreeGroup.mk (roseWord K C hC hconn i j).loopWord)
  | .inr _ => FreeGroup.of (Sum.inr PUnit.unit)

theorem canonicalRelators_natural {i k : Fin _} (hik : i ≤ k)
    (j : CanonicalRel K C i) :
    canonicalRelators K C hC hconn k (canonicalCellInclusion K C hC hik j) =
      FreeGroup.map (canonicalGenInclusion K C hC hconn hik) (canonicalRelators K C hC hconn i j) := by
  cases j with
  | inl j =>
      simp only [canonicalRelators, canonicalCellInclusion, StabilizedDiskPresentation.withDummy,
        Function.Embedding.coeFn_mk, Sum.map_inl]
      erw [roseWord_loop_natural K C hC hconn hik j] <;> aesop
  | inr u =>
      rfl

variable (i : Fin (n + 1))

def canonicalWords :=
  presCanonicalWords (canonicalRelators K C hC hconn i) (Sum.inr PUnit.unit)

variable (j : CanonicalRel K C i)

theorem canonicalWords_ne_nil :
    canonicalWords K C hC hconn i j ≠ [] := presCanonicalWords_ne_nil _ _ _

theorem canonicalWords_mk :
    FreeGroup.mk (canonicalWords K C hC hconn i j) = canonicalRelators K C hC hconn i j :=
  mk_presCanonicalWords _ _ _

def canonicalWordEmbedding {i k : Fin _} (hik : i ≤ k) :
    PresWordEmbedding (canonicalWords K C hC hconn i) (canonicalWords K C hC hconn k) :=
  canonicalPresWordEmbedding _ _ _
    _ (canonicalRelators_natural K C hC hconn hik)
    _

variable (i : Fin (n + 1))

def stabilizedAttaching :=
  StabilizedDiskPresentation.attaching (collapsedAttaching K C hC hconn i)

def stabilizedCellBoundary (j : CanonicalRel K C i) :=
  (stabilizedAttaching K C hC hconn i).comp
    (⟨fun a => ⟨j, a⟩, continuous_sigmaMk (σ := fun _ : CanonicalRel K C i => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩)

theorem stabilizedCellBoundary_natural {i k : Fin _} (hik : i ≤ k)
    (j : CanonicalRel K C i) :
    (diskRoseMap (canonicalGenInclusion K C hC hconn hik)).comp
        (stabilizedCellBoundary K C hC hconn i j) =
      stabilizedCellBoundary K C hC hconn k (canonicalCellInclusion K C hC hik j) := by
  ext a
  solve_by_elim [StabilizedDiskPresentation.attaching_natural, collapsedAttaching_natural]

theorem stabilizedCellBoundary_homotopic (i : Fin _) (j : CanonicalRel K C i) :
    (stabilizedCellBoundary K C hC hconn i j).Homotopic
      (classicalPresCellBoundary (canonicalWords K C hC hconn i) j
        (canonicalWords_ne_nil K C hC hconn i)) := by
  cases j with
  | inl j =>
      letI := subcomplexZeroSkeleton_discrete (C i)
      have H₀ := (word C hC i j).collapse_homotopic_eraseTree
        _ (skeletonAttachingMap (C i : Set K) 1).continuous
        (chainTree K C hC hconn i)
      have H := (ContinuousMap.Homotopic.refl (diskRoseMap
        (Sum.inl : RoseGen K C hC hconn i → CanonicalGen K C hC hconn i))).comp (H₀.trans (boundaryWords_homotopic_classicalWord (roseWord K C hC hconn i j)))
      erw [classicalRoseWordBoundary_map] at H
      have he : FreeGroup.mk (((roseWord K C hC hconn i j).loopWord).map
          (fun p => (Sum.inl p.1, p.2))) =
          FreeGroup.mk (canonicalWords K C hC hconn i (Sum.inl j)) := by
        erw [canonicalWords_mk]
        rfl
      exact H.trans ((classicalRoseWordBoundary_homotopic_of_mk_eq he).trans
        (classicalPresWordAttaching_homotopic_read (canonicalWords K C hC hconn i)
          (Sum.inl j) (canonicalWords_ne_nil K C hC hconn i)).symm)
  | inr u =>
      have H := (ContinuousMap.Homotopic.refl (diskRoseMap
        (Sum.inr : PUnit → CanonicalGen K C hC hconn i))).comp
          dummyCircleBoundaryHomeomorph_homotopic_word; erw [classicalRoseWordBoundary_map] at H; exact H.trans ((classicalRoseWordBoundary_homotopic_of_mk_eq (canonicalWords_mk K C hC hconn i (Sum.inr PUnit.unit)).symm).trans
        (classicalPresWordAttaching_homotopic_read (canonicalWords K C hC hconn i)
          (Sum.inr PUnit.unit) (canonicalWords_ne_nil K C hC hconn i)).symm)

end FiniteChains.ClassicalCW.ChainWords
