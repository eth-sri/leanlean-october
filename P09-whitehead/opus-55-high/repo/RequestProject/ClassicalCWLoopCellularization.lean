import RequestProject.Statement
import RequestProject.ClassicalCWVertexPaths
import RequestProject.ClassicalCWCompactSupport
import RequestProject.ClassicalCWSkeletonAttachment
import RequestProject.DiskAttachmentRadialCore


/-! Actual paths and loops in the given two-dimensional CW complex can be
moved, relative to endpoints already in its one-skeleton, into that original
one-skeleton. The conclusion retains the original space and cells.
Pending Lean verification. -/

noncomputable section
open scoped Classical
open Set Topology

namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment RelativeAttachment

def OneSkeleton (K : Whitehead.TwoComplex) := SkeletonCarrier (Set.univ : Set K) 2

instance (K : Whitehead.TwoComplex) : TopologicalSpace (OneSkeleton K) :=
  inferInstanceAs (TopologicalSpace (SkeletonCarrier (Set.univ : Set K) 2))

theorem twoComplex_mem_skeleton_three (K : Whitehead.TwoComplex) x :
    x ∈ CWComplex.skeletonLT (Set.univ : Set K) 3 := by
  have hx : x ∈ ⋃ n, ⋃ j : RelCWComplex.cell Set.univ n,
      CWComplex.closedCell n j := by rw [CWComplex.union]; trivial
  obtain ⟨n, j, hj⟩ := by simpa [Set.mem_iUnion] using hx
  have hn : n ≤ 2 := by
    by_contra h
    letI := K.dimension n (Nat.lt_of_not_ge h)
    exact isEmptyElim j
  exact CWComplex.skeletonLT_mono (C := Set.univ)
    (show (n : ℕ∞) + 1 ≤ 3 by exact_mod_cast by grind)
    (CWComplex.closedCell_subset_skeletonLT n j hj)

/-- Every path between original one-skeleton points is homotopic to a
path entirely in that original one-skeleton, fixing both endpoints. -/
theorem path_into_oneSkeleton K (x y : OneSkeleton K)
    p :
    ∃ q : Path x y, Path.Homotopic p (q.map continuous_subtype_val) := by
  let P : Path (skeletonInclusion _ 2 x)
      (skeletonInclusion _ 2 y) := {
    toFun := fun t => ⟨p t, twoComplex_mem_skeleton_three K _⟩
    continuous_toFun := p.continuous.subtype_mk _
    source' := Subtype.ext p.source
    target' := Subtype.ext p.target }
  let e := skeletonAsDiskAttachment (Set.univ : Set K) 2
  let r := skeletonAttachingMap (Set.univ : Set K) 2
  let P' := (P.map e.continuous).cast
    (skeletonAsDiskAttachment_inclusion _ 2 x).symm
    (skeletonAsDiskAttachment_inclusion _ 2 y).symm
  cases' twoCellAttachment_path_into_old r r.continuous x y P' with q hq
  have h := hq.map (skeletonAttachmentOrigin (Set.univ : Set K) 2)
  have hleft : P'.map (skeletonAttachmentOrigin _ 2).continuous = p := by
    apply Path.ext
    funext t
    change (skeletonAttachmentHomeomorph _ 2
      ((skeletonAttachmentHomeomorph _ 2).symm (P t))).val = p t
    aesop
  aesop
