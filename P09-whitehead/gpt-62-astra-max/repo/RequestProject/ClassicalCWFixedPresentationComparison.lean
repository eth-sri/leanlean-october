module


public import RequestProject.ClassicalCWChainFixedInitial


@[expose] public section

/-! The fixed presentation used for necessity has an actual homotopy
equivalence with the original CW space. Its words and tree are independent
of every ambient chain, and the only stabilization is one filled loop.
Unverified source. -/

noncomputable section

namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel
open Set Topology
open scoped Classical unitInterval ContinuousMap
variable (K : Whitehead.TwoComplex) (T : Comb.SpanningTree (originalGraph K))

def fixedGraphAttaching :=
  (skeletonAsDiskAttachment (Set.univ : Set K) 1).toContinuousMap.comp
    (skeletonAttachingMap (Set.univ : Set K) 2)

def fixedGraphWordAttaching :
    C(BoundaryFamily (RelCWComplex.cell (Set.univ : Set K) 2) (Fin 2 → ℝ),
      DiskAttachment (originalGraphAttaching K)) :=
  ⟨fun a => (fixedGraphWord K a.1).boundaryMap a.2,
    continuous_sigma (fun j => (fixedGraphWord K j).boundaryMap.continuous)⟩

def fixedGraphAttachingHomotopy : (fixedGraphAttaching K).Homotopy (fixedGraphWordAttaching K) := by
  let H j := Classical.choice (fixedGraphWord_spec K j)
  exact FiniteChains.sigmaHomotopy H

def fixedGraphWordDiskEquiv :=
  (((originalAsDiskAttachment K).toHomotopyEquiv.trans
    (diskAttachmentBaseChangeHomotopyEquiv (skeletonAttachingMap (Set.univ : Set K) 2)
      (skeletonAsDiskAttachment (Set.univ : Set K) 1).toHomotopyEquiv)).trans
        (diskAttachingHomotopyEquiv _ _ (fixedGraphAttachingHomotopy K)))

def fixedGraphCollapse : DiskAttachment (originalGraphAttaching K) ≃ₕ
    ClassicalGraphModel.Rose (Comb.SpanningTree.NonTree T) := by
  letI := zeroSkeleton_discrete (X := K)
  exact graphRoseHomotopyEquiv (originalGraphAttaching K) (originalGraphAttaching K).continuous T

def fixedRoseAttaching :=
  (fixedGraphCollapse K T).toFun.comp (fixedGraphWordAttaching K)

def fixedRoseDiskEquiv : K ≃ₕ DiskAttachment (fixedRoseAttaching K T) :=
  (fixedGraphWordDiskEquiv K).trans
    (diskAttachmentBaseChangeHomotopyEquiv (fixedGraphWordAttaching K) (fixedGraphCollapse K T))

def fixedCanonicalWords :=
  presCanonicalWords (fixedRelators K T) (Sum.inr PUnit.unit)

variable (j : FixedRel K)

theorem fixedCanonicalWords_ne_nil : fixedCanonicalWords K T j ≠ [] :=
  presCanonicalWords_ne_nil _ _ _

theorem fixedCanonicalWords_mk :
    FreeGroup.mk (fixedCanonicalWords K T j) = fixedRelators K T j := mk_presCanonicalWords _ _ _

def fixedStabilizedBoundary :=
  (StabilizedDiskPresentation.attaching (fixedRoseAttaching K T)).comp
    (⟨fun a => ⟨j, a⟩, continuous_sigmaMk («σ» := fun _ : FixedRel K => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩ :
        C(UnitBoundary (Fin 2 → ℝ), BoundaryFamily (FixedRel K) (Fin 2 → ℝ)))

theorem fixedStabilizedBoundary_homotopic :
    (fixedStabilizedBoundary K T j).Homotopic
      (classicalPresCellBoundary (fixedCanonicalWords K T) j (fixedCanonicalWords_ne_nil K T)) := by
  cases j with
  | inl j =>
      letI := zeroSkeleton_discrete (X := K)
      let W := (fixedGraphWord K j).eraseTree (originalGraphAttaching K) T
      have H₀ := (fixedGraphWord K j).collapse_homotopic_eraseTree
        (originalGraphAttaching K) (originalGraphAttaching K).continuous T
      have H₁ := H₀.trans (boundaryWords_homotopic_classicalWord W)
      have H := (ContinuousMap.Homotopic.refl (diskRoseMap
        (Sum.inl : Comb.SpanningTree.NonTree T → FixedGen K T))).comp H₁
      erw [classicalRoseWordBoundary_map] at H
      have he : FreeGroup.mk (W.loopWord.map (fun p => ((Sum.inl p.1 : FixedGen K T), p.2))) =
          FreeGroup.mk (fixedCanonicalWords K T (Sum.inl j)) := by
        erw [fixedCanonicalWords_mk]
        change FreeGroup.map Sum.inl (FreeGroup.mk W.loopWord) = _
        solve_by_elim [BoundaryWords.eraseTree_mk]
      exact H.trans ((classicalRoseWordBoundary_homotopic_of_mk_eq he).trans
        (classicalPresWordAttaching_homotopic_read (fixedCanonicalWords K T) (Sum.inl j)
          (fixedCanonicalWords_ne_nil K T)).symm)
  | inr u =>
      have H := (ContinuousMap.Homotopic.refl (diskRoseMap
        (Sum.inr : PUnit → FixedGen K T))).comp dummyCircleBoundaryHomeomorph_homotopic_word; erw [classicalRoseWordBoundary_map] at H; have he :=
        (fixedCanonicalWords_mk K T (Sum.inr PUnit.unit)).symm; exact H.trans ((classicalRoseWordBoundary_homotopic_of_mk_eq he).trans
        (classicalPresWordAttaching_homotopic_read (fixedCanonicalWords K T) (Sum.inr PUnit.unit)
          (fixedCanonicalWords_ne_nil K T)).symm)

def fixedCanonicalAttachingHomotopy :
    (StabilizedDiskPresentation.attaching (fixedRoseAttaching K T)).Homotopy
      (classicalPresWordAttaching (fixedCanonicalWords K T) (fixedCanonicalWords_ne_nil K T)) := by
  let H j := Classical.choice (fixedStabilizedBoundary_homotopic K T j)
  exact FiniteChains.sigmaHomotopy H

def fixedClassicalPresWordDiskEquiv :=
  ((fixedRoseDiskEquiv K T).trans (StabilizedDiskPresentation.homotopyEquiv (fixedRoseAttaching K T))).trans
    (diskAttachingHomotopyEquiv _ _ (fixedCanonicalAttachingHomotopy K T))

def fixedCanonicalRealizationEquiv :=
  (fixedClassicalPresWordDiskEquiv K T).trans
    (presClassicalDiskComparison (fixedCanonicalWords K T) (fixedCanonicalWords_ne_nil K T)).symm

end FiniteChains.ClassicalCW
