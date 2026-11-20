module

public import RequestProject.Statement
public import RequestProject.ClassicalCWVertexPaths
public import RequestProject.ClassicalCWCompactSupport
public import RequestProject.ClassicalCWSkeletonAttachment
public import RequestProject.DiskAttachmentRadialCore

@[expose] public section

/-! Actual paths and loops in the given two-dimensional CW complex can be
moved, relative to endpoints already in its one-skeleton, into that original
one-skeleton. The conclusion retains the original space and cells.
Pending Lean verification. -/

noncomputable section
open scoped Classical
open Set Topology

namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment RelativeAttachment

variable (K : Whitehead.TwoComplex)

def OneSkeleton := SkeletonCarrier (Set.univ : Set K) 2

instance : TopologicalSpace (OneSkeleton K) :=
  inferInstanceAs (TopologicalSpace (SkeletonCarrier Set.univ 2))

theorem twoComplex_mem_skeleton_three (x : K) :
    x ∈ CWComplex.skeletonLT Set.univ 3 := by
  have hx : x ∈ ⋃ n, ⋃ j : RelCWComplex.cell Set.univ n,
      CWComplex.closedCell n j := by rw [CWComplex.union]; trivial
  obtain ⟨n, j, hj⟩ := by simpa only [Set.mem_iUnion] using hx
  have hn : n ≤ 2 := by
    by_contra h
    letI := K.dimension n (Nat.lt_of_not_ge h)
    exact isEmptyElim j
  exact CWComplex.skeletonLT_mono
    (show (n : ℕ∞) + 1 ≤ 3 by exact_mod_cast (by omega))
    (CWComplex.closedCell_subset_skeletonLT n j hj)

/-- Every path between original one-skeleton points is homotopic to a
path entirely in that original one-skeleton, fixing both endpoints. -/
theorem path_into_oneSkeleton (x y : OneSkeleton K)
    (p : Path x.val y.val) :
    ∃ q : Path x y, Path.Homotopic p (q.map continuous_subtype_val) := by
  let P : Path (skeletonInclusion Set.univ 2 x)
      (skeletonInclusion Set.univ 2 y) := {
    toFun := fun t => ⟨p t, twoComplex_mem_skeleton_three K _⟩
    continuous_toFun := p.continuous.subtype_mk _
    source' := Subtype.ext p.source
    target' := Subtype.ext p.target }
  let r := skeletonAttachingMap (Set.univ : Set K) 2
  let P' := (P.map (skeletonAsDiskAttachment Set.univ 2).continuous).cast
    (skeletonAsDiskAttachment_inclusion Set.univ 2 x).symm
    (skeletonAsDiskAttachment_inclusion Set.univ 2 y).symm
  obtain ⟨q, hq⟩ := twoCellAttachment_path_into_old r r.continuous x y P'
  refine ⟨q, ?_⟩
  have h := hq.map (skeletonAttachmentOrigin Set.univ 2)
  have hleft : P'.map (skeletonAttachmentOrigin Set.univ 2).continuous = p := by
    apply Path.ext
    funext t
    change (skeletonAttachmentHomeomorph Set.univ 2
      ((skeletonAttachmentHomeomorph Set.univ 2).symm _)).val = p t
    aesop
  have hright : (q.map (old_continuous r
      _)).map
        (skeletonAttachmentOrigin Set.univ 2).continuous =
      q.map continuous_subtype_val := rfl
  rwa [hleft, hright] at h

end FiniteChains.ClassicalCW
