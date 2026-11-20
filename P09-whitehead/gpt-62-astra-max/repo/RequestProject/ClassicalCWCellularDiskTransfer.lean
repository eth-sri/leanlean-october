module

public import RequestProject.ClassicalCWBoundaryCellularization
public import RequestProject.ClassicalCWCellEmbedding
public import RequestProject.DiskFamilyHomotopyBaseChange

@[expose] public section

/-! Transfer a genuine one- or two-dimensional disk extension of a model
to an arbitrary original two-complex. The new attachment is cellularized
in the original CW structure and retains all of its literal old cells. -/

noncomputable section
namespace Whitehead
open scoped Topology Classical
open FiniteChains.RelativeAttachment

variable (K : TwoComplex) {P J : Type} [TopologicalSpace P]
  (e : ContinuousMap.HomotopyEquiv P K) (n : ℕ)
  (r : C(BoundaryFamily J (Fin n → ℝ), P))

/-- The actual result of transfer, including the commuting old-space
square and finite/properness consequences of the concrete added disks. -/
structure CellularDiskTransfer where
  target : TwoComplex
  oldEmbedding : CWCellEmbedding K target
  comparison : ContinuousMap.HomotopyEquiv (DiskAttachment r) target
  square : comparison.toFun.comp
      (⟨old r _, old_continuous _ _⟩) = oldEmbedding.map.comp e.toFun
  finite : FiniteCells K → Finite J → FiniteCells target
  proper : Nonempty J → ∃ z : target, z ∉ Set.range oldEmbedding.map

def cellularDiskTransferOfRepresentative (hn : 0 < n) (hn₂ : n ≤ 2)
    (q : C(BoundaryFamily J (Fin n → ℝ), K))
    (H : (e.toFun.comp r).Homotopy q) (hq : FiniteLowerBoundary n q) :
    CellularDiskTransfer K e n r := by
  let x₀ : K := Classical.choice inferInstance
  let D := (diskAttachmentBaseChangeHomotopyEquiv r e).trans
    (diskAttachingHomotopyEquiv (e.toFun.comp r) q H)
  refine {
    target := diskAttachmentTwoComplex K n hn hn₂ q x₀ hq
    oldEmbedding := diskAttachmentCellEmbedding K n hn hn₂ q x₀ hq
    comparison := D
    square := ?_
    finite := ?_
    proper := ?_ }
  · rfl
  · apply diskAttachment_finiteCells
  · intro hJ
    by_contra! hall
    exact diskAttachment_old_ne_univ K n hn hn₂ q x₀ hq (Set.eq_univ_of_forall hall)

/-- Every actual disk extension in one of the two permitted dimensions
has a transfer. All cellularity and finite boundary-support conditions
are supplied by the original-CW cellularization constructions. -/
def cellularDiskTransfer (hn : n = 1 ∨ n = 2) : CellularDiskTransfer K e n r := by
  by_cases h₁ : n = 1
  · subst n
    let a := e.toFun.comp r
    exact cellularDiskTransferOfRepresentative K e 1 r zero_lt_one (by omega)
      _ (vertexBoundaryHomotopy a)
      (vertexBoundaryMap_finiteLowerBoundary a)
  · have h₂ := hn.resolve_left h₁
    subst n
    let h := FiniteChains.ClassicalCW.boundaryFamily_into_oneSkeleton K (e.toFun.comp r)
    have hq := Classical.choose_spec h
    exact cellularDiskTransferOfRepresentative K e 2 r (by omega) le_rfl _
      (Classical.choice hq.1) hq.2

end Whitehead
