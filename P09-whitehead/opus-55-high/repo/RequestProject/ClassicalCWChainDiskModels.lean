import RequestProject.ClassicalCWChainHomotopies


/-! Actual graph-and-word-disk models for all stages of an original CW
chain. These equivalences use the original characteristic disks and the
coherent birth-stage attaching homotopies. Unverified source. -/

noncomputable section
namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical ContinuousMap

variable (K : Whitehead.TwoComplex)

theorem subcomplex_mem_skeleton_three (C : CWComplex.Subcomplex (Set.univ : Set K))
    (x : (C : Set K)) : x.val ∈ CWComplex.skeletonLT C 3 := by
  have hx := x.property
  have hx' := (CWComplex.iUnion_openCell_eq_complex (C := (C : Set K))).symm
  have hmem := congrArg (x.val ∈ ·) hx'
  have hx := hmem.mp hx
  obtain ⟨n, j, hj⟩ := by simpa only [Set.mem_iUnion] using hx
  have hn : n < 3 := by
    by_contra h
    have hn2 : 2 < n := by omega
    letI := K.dimension n hn2
    exact isEmptyElim j.val
  change x.val ∈ (CWComplex.skeletonLT (C : Set K) (3 : ℕ∞) : Set K)
  rw [← CWComplex.iUnion_openCell_eq_skeletonLT]
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨by exact_mod_cast hn,
    Set.mem_iUnion.mpr ⟨j, hj⟩⟩⟩

def subcomplexTopSkeletonHomeomorph (C : CWComplex.Subcomplex (Set.univ : Set K)) :
    (C : Set K) ≃ₜ SkeletonCarrier (C : Set K) 3 where
  toFun x := ⟨x.val, subcomplex_mem_skeleton_three K C x⟩
  invFun x := ⟨x.val, (CWComplex.skeletonLT (C : Set K) (3 : ℕ∞)).subset_complex x.property⟩
  left_inv _x := Subtype.ext rfl
  right_inv _x := Subtype.ext rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def subcomplexAsDiskAttachment (C : CWComplex.Subcomplex (Set.univ : Set K)) :=
  (subcomplexTopSkeletonHomeomorph K C).trans (skeletonAsDiskAttachment _ 2)

namespace ChainWords
variable {n : ℕ} (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C)
  [Choices C]

def rawDiskEquiv i : (C i : Set K) ≃ₕ DiskAttachment (rawAttaching C i) :=
  (subcomplexAsDiskAttachment K _).toHomotopyEquiv.trans
    (diskAttachmentBaseChangeHomotopyEquiv (skeletonAttachingMap _ 2)
      (skeletonAsDiskAttachment _ 1).toHomotopyEquiv)

def wordDiskEquiv i :=
  (rawDiskEquiv K C i).trans (wordDiskChange C hC i)
