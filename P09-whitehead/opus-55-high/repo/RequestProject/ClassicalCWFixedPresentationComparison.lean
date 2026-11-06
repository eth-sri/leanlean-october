import RequestProject.HomeomorphContinuousMap
import RequestProject.ClassicalCWChainFixedInitial
import RequestProject.PresClassicalDiskComparison
import RequestProject.Tac


/-! The fixed presentation used for necessity has an actual homotopy
equivalence with the original CW space. Its words and tree are independent
of every ambient chain, and the only stabilization is one filled loop.
Unverified source. -/

noncomputable section
bwd

namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel
open Set Topology
open scoped Classical unitInterval ContinuousMap
variable (K : Whitehead.TwoComplex) (T : Comb.SpanningTree (originalGraph K))

def fixedGraphAttaching :
    C(BoundaryFamily (RelCWComplex.cell (Set.univ : Set K) 2) (Fin 2 → ℝ),
      DiskAttachment (originalGraphAttaching K)) :=
  (skeletonAsDiskAttachment _ 1).toContinuousMap.comp
    (skeletonAttachingMap _ 2)

def fixedGraphWordAttaching :
    C(BoundaryFamily (RelCWComplex.cell (Set.univ : Set K) 2) (Fin 2 → ℝ),
      DiskAttachment (originalGraphAttaching K)) :=
  ⟨fun a => (fixedGraphWord K a.1).boundaryMap a.2,
    continuous_sigma (fun j => (fixedGraphWord K j).boundaryMap.continuous)⟩

def fixedGraphAttachingHomotopy : (fixedGraphAttaching K).Homotopy (fixedGraphWordAttaching K) := by
  let H j := Classical.choice (fixedGraphWord_spec K j)
  let F : C(BoundaryFamily (RelCWComplex.cell (Set.univ : Set K) 2) (Fin 2 → ℝ),
      C(I, DiskAttachment (originalGraphAttaching K))) :=
    ⟨fun a => ((H a.1).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry a.2,
      continuous_sigma (fun j =>
        ((H j).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry.continuous)⟩
  exact {
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := by aesop
    map_one_left := by aesop }

def fixedGraphWordDiskEquiv : K ≃ₕ DiskAttachment (fixedGraphWordAttaching K) :=
  (((originalAsDiskAttachment K).toHomotopyEquiv.trans
    (diskAttachmentBaseChangeHomotopyEquiv (skeletonAttachingMap _ 2)
      (skeletonAsDiskAttachment (Set.univ : Set K) 1).toHomotopyEquiv)).trans
        (diskAttachingHomotopyEquiv _ _ (fixedGraphAttachingHomotopy K)))

def fixedGraphCollapse : DiskAttachment (originalGraphAttaching K) ≃ₕ
    ClassicalGraphModel.Rose (Comb.SpanningTree.NonTree T) := by
  letI := zeroSkeleton_discrete (X := K)
  exact graphRoseHomotopyEquiv _ (originalGraphAttaching K).continuous T

def fixedRoseAttaching :=
  (fixedGraphCollapse K T).toFun.comp (fixedGraphWordAttaching K)

def fixedRoseDiskEquiv : K ≃ₕ DiskAttachment (fixedRoseAttaching K T) :=
  (fixedGraphWordDiskEquiv K).trans
    (diskAttachmentBaseChangeHomotopyEquiv _ (fixedGraphCollapse K T))

def fixedCanonicalWords : FixedRel K → List (FixedGen K T × Bool) :=
  presCanonicalWords (fixedRelators K T) (Sum.inr PUnit.unit)

theorem fixedCanonicalWords_ne_nil j : fixedCanonicalWords K T j ≠ [] :=
  presCanonicalWords_ne_nil _ _ _

theorem fixedCanonicalWords_mk j :
    FreeGroup.mk (fixedCanonicalWords K T j) = fixedRelators K T j := mk_presCanonicalWords _ _ _

def fixedStabilizedBoundary (j : FixedRel K) :
    C(UnitBoundary (Fin 2 → ℝ), ClassicalGraphModel.Rose (FixedGen K T)) :=
  (StabilizedDiskPresentation.attaching (fixedRoseAttaching K T)).comp
    (⟨fun a => ⟨j, a⟩, continuous_sigmaMk («σ» := fun _ : FixedRel K => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩ :
        C(UnitBoundary (Fin 2 → ℝ), BoundaryFamily (FixedRel K) (Fin 2 → ℝ)))

theorem fixedStabilizedBoundary_homotopic j :
    (fixedStabilizedBoundary K T j).Homotopic
      (classicalPresCellBoundary (fixedCanonicalWords K T) j (fixedCanonicalWords_ne_nil K T)) := by
  cases j with
  | inl j =>
      letI := zeroSkeleton_discrete (X := K)
      let W := (fixedGraphWord K j).eraseTree _ T
      have H₀ := (fixedGraphWord K j).collapse_homotopic_eraseTree
        _ (originalGraphAttaching K).continuous T
      have H₁ := H₀.trans (boundaryWords_homotopic_classicalWord W)
      have H := (ContinuousMap.Homotopic.refl (diskRoseMap
        (Sum.inl : T.NonTree → FixedGen K T))).comp H₁
      rwd [classicalRoseWordBoundary_map] at H
      have he : FreeGroup.mk (W.loopWord.map (fun p => ((Sum.inl p.1), p.2))) =
          FreeGroup.mk (fixedCanonicalWords K T (Sum.inl j)) := by
        rwd [fixedCanonicalWords_mk]
        change FreeGroup.map Sum.inl (FreeGroup.mk W.loopWord) = _
        rwd [BoundaryWords.eraseTree_mk]
        rfl
      exact H.trans ((classicalRoseWordBoundary_homotopic_of_mk_eq he).trans
        (classicalPresWordAttaching_homotopic_read _ _
          _).symm)
  | inr u =>
      cases u
      have H := (ContinuousMap.Homotopic.refl (diskRoseMap
        (Sum.inr : PUnit → FixedGen K T))).comp dummyCircleBoundaryHomeomorph_homotopic_word
      rwd [classicalRoseWordBoundary_map] at H
      have he :=
        (fixedCanonicalWords_mk K T (Sum.inr PUnit.unit)).symm
      exact H.trans ((classicalRoseWordBoundary_homotopic_of_mk_eq he).trans
        (classicalPresWordAttaching_homotopic_read _ _
          _).symm)

def fixedCanonicalAttachingHomotopy :
    (StabilizedDiskPresentation.attaching (fixedRoseAttaching K T)).Homotopy
      (classicalPresWordAttaching (fixedCanonicalWords K T) (fixedCanonicalWords_ne_nil K T)) := by
  let H j := Classical.choice (fixedStabilizedBoundary_homotopic K T j)
  let F : C(BoundaryFamily (FixedRel K) (Fin 2 → ℝ), C(I, ClassicalGraphModel.Rose (FixedGen K T))) :=
    ⟨fun a => ((H a.1).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry a.2,
      continuous_sigma (fun j =>
        ((H j).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry.continuous)⟩
  exact {
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := by aesop
    map_one_left := by aesop }

def fixedClassicalPresWordDiskEquiv : K ≃ₕ
    ClassicalPresWordDisks (fixedCanonicalWords K T) (fixedCanonicalWords_ne_nil K T) :=
  ((fixedRoseDiskEquiv K T).trans (StabilizedDiskPresentation.homotopyEquiv _)).trans
    (diskAttachingHomotopyEquiv _ _ (fixedCanonicalAttachingHomotopy K T))

def fixedCanonicalRealizationEquiv :=
  (fixedClassicalPresWordDiskEquiv K T).trans
    (presClassicalDiskComparison _ _).symm
