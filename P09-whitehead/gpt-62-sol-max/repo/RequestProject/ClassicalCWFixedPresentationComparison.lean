module

public import RequestProject.StabilizedWordComparison
public import RequestProject.HomeomorphContinuousMap
public import RequestProject.ClassicalCWChainFixedInitial
public import RequestProject.PresClassicalDiskComparison

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

def fixedGraphAttaching :
    C(BoundaryFamily (RelCWComplex.cell (Set.univ : Set K) 2) (Fin 2 → ℝ),
      DiskAttachment (originalGraphAttaching K)) :=
  (skeletonAsDiskAttachment Set.univ 1).toContinuousMap.comp
    (skeletonAttachingMap Set.univ 2)

def fixedGraphWordAttaching :
    C(BoundaryFamily (RelCWComplex.cell (Set.univ : Set K) 2) (Fin 2 → ℝ),
      DiskAttachment (originalGraphAttaching K)) :=
  ⟨fun a => (fixedGraphWord K a.1).boundaryMap a.2,
    continuous_sigma (fun j => (fixedGraphWord K j).boundaryMap.continuous)⟩

def fixedGraphAttachingHomotopy : (fixedGraphAttaching K).Homotopy (fixedGraphWordAttaching K) :=
  .sigmaFamily fun j => Classical.choice (fixedGraphWord_spec K j)


def fixedGraphWordDiskEquiv : K ≃ₕ DiskAttachment (fixedGraphWordAttaching K) :=
  (((originalAsDiskAttachment K).toHomotopyEquiv.trans
    (diskAttachmentBaseChangeHomotopyEquiv (skeletonAttachingMap Set.univ 2)
      (skeletonAsDiskAttachment Set.univ 1).toHomotopyEquiv)).trans
        (diskAttachingHomotopyEquiv _ _ (fixedGraphAttachingHomotopy K)))

def fixedGraphCollapse : DiskAttachment (originalGraphAttaching K) ≃ₕ
    ClassicalGraphModel.Rose (Comb.SpanningTree.NonTree T) := by
  letI := zeroSkeleton_discrete (X := K)
  exact graphRoseHomotopyEquiv (originalGraphAttaching K) (originalGraphAttaching K).continuous T

def fixedRoseAttaching :
    C(BoundaryFamily (RelCWComplex.cell (Set.univ : Set K) 2) (Fin 2 → ℝ),
      ClassicalGraphModel.Rose (Comb.SpanningTree.NonTree T)) :=
  (fixedGraphCollapse K T).toFun.comp (fixedGraphWordAttaching K)

def fixedRoseDiskEquiv : K ≃ₕ DiskAttachment (fixedRoseAttaching K T) :=
  (fixedGraphWordDiskEquiv K).trans
    (diskAttachmentBaseChangeHomotopyEquiv (fixedGraphWordAttaching K) (fixedGraphCollapse K T))

def fixedCanonicalWords : FixedRel K → List (FixedGen K T × Bool) :=
  presCanonicalWords (fixedRelators K T) (Sum.inr PUnit.unit)

theorem fixedCanonicalWords_ne_nil (j : FixedRel K) : fixedCanonicalWords K T j ≠ [] :=
  presCanonicalWords_ne_nil _ _ _

theorem fixedCanonicalWords_mk (j : FixedRel K) :
    FreeGroup.mk (fixedCanonicalWords K T j) = fixedRelators K T j := mk_presCanonicalWords _ _ _

def fixedCanonicalAttachingHomotopy :
    (StabilizedDiskPresentation.attaching (fixedRoseAttaching K T)).Homotopy
      (classicalPresWordAttaching (fixedCanonicalWords K T) (fixedCanonicalWords_ne_nil K T)) := by
  letI := zeroSkeleton_discrete (X := K)
  let W j := (fixedGraphWord K j).eraseTree (originalGraphAttaching K) T
  apply stabilizedPresAttachingHomotopy (u := fun j => (W j).loopWord)
  · intro j
    exact ((fixedGraphWord K j).collapse_homotopic_eraseTree
      (originalGraphAttaching K) (originalGraphAttaching K).continuous T).trans
      (boundaryWords_homotopic_classicalWord (W j))
  · intro j
    erw [fixedCanonicalWords_mk, BoundaryWords.eraseTree_mk]
    rfl
  · exact (fixedCanonicalWords_mk K T (Sum.inr PUnit.unit)).symm

def fixedClassicalPresWordDiskEquiv : K ≃ₕ
    ClassicalPresWordDisks (fixedCanonicalWords K T) (fixedCanonicalWords_ne_nil K T) :=
  ((fixedRoseDiskEquiv K T).trans (StabilizedDiskPresentation.homotopyEquiv (fixedRoseAttaching K T))).trans
    (diskAttachingHomotopyEquiv _ _ (fixedCanonicalAttachingHomotopy K T))

def fixedCanonicalRealizationEquiv : K ≃ₕ Comb.orderNerveRealization (PresPos (fixedCanonicalWords K T)) :=
  (fixedClassicalPresWordDiskEquiv K T).trans
    (presClassicalDiskComparison (fixedCanonicalWords K T) (fixedCanonicalWords_ne_nil K T)).symm

end FiniteChains.ClassicalCW
