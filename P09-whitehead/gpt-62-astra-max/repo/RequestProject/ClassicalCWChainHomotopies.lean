module


public import RequestProject.ClassicalCWChainWords
public import RequestProject.NaturalDiskAttachingEquiv

@[expose] public section

/-! The actual attaching homotopies are chosen at birth as well. Their
naturality is a pointwise equality, not a fresh choice of homotopy at
each stage. Unverified source. -/

noncomputable section
namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical unitInterval ContinuousMap
variable {X : Type} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
  {n : ℕ} (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set X))
  (hC : Monotone C)
  [Choices C]

def birthHomotopy (j : TopCell C) := Classical.choice (birthWord_spec C j)

def wordHomotopy (i : Fin (n + 1)) (j : RelCWComplex.cell (C i : Set X) 2) :
    (subcomplexCellBoundary (C i) j).Homotopy (word C hC i j).boundaryMap where
  toContinuousMap := (subcomplexGraphDiskMap
    (hC (birth_le C (topCell C hC i j) i j.property))).comp
      (birthHomotopy C (topCell C hC i j)).toContinuousMap
  map_zero_left a := by
    change subcomplexGraphDiskMap _ (birthHomotopy C _ (0, a)) = _
    rw [(birthHomotopy C _).apply_zero]
    exact congrArg (fun f => f a) (subcomplexCellBoundary_natural
      (hC (birth_le C (topCell C hC i j) i j.property))
      (birthCell C (topCell C hC i j)))
  map_one_left a := by
    change subcomplexGraphDiskMap _ (birthHomotopy C _ (1, a)) = _
    rw [(birthHomotopy C _).apply_one]
    exact congrArg (fun f => f a) (subcomplexBoundaryWord_map
      (hC (birth_le C (topCell C hC i j) i j.property))
      (birthWord C (topCell C hC i j)))

theorem wordHomotopy_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set X) 2) (t : I) (a : UnitBoundary (Fin 2 → ℝ)) :
    wordHomotopy C hC k (subcomplexCellInclusion (hC hik) 2 j) (t, a) =
      subcomplexGraphDiskMap (hC hik) (wordHomotopy C hC i j (t, a)) := (congrArg (fun f => f (birthHomotopy C (topCell C hC i j) (t, a)))
    (subcomplexGraphDiskMap_comp
      (hC (birth_le C (topCell C hC i j) i j.property)) (hC hik))).symm

variable (i : Fin (n + 1))

def rawAttaching :
    C(BoundaryFamily (RelCWComplex.cell (C i : Set X) 2) (Fin 2 → ℝ),
      DiskAttachment (skeletonAttachingMap (C i : Set X) 1)) :=
  ⟨fun a => subcomplexCellBoundary (C i) a.1 a.2,
    continuous_sigma (fun j => (subcomplexCellBoundary (C i) j).continuous)⟩

def wordAttaching :
    C(BoundaryFamily (RelCWComplex.cell (C i : Set X) 2) (Fin 2 → ℝ),
      DiskAttachment (skeletonAttachingMap (C i : Set X) 1)) :=
  ⟨fun a => (word C hC i a.1).boundaryMap a.2,
    continuous_sigma (fun j => (word C hC i j).boundaryMap.continuous)⟩

def attachingHomotopy : (rawAttaching C i).Homotopy (wordAttaching C hC i) := by
  let H j := wordHomotopy C hC i j
  exact FiniteChains.sigmaHomotopy H

theorem attachingHomotopy_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set X) 2) (t : I) (a : UnitBoundary (Fin 2 → ℝ)) :
    attachingHomotopy C hC k (t, ⟨subcomplexCellInclusion (hC hik) 2 j, a⟩) =
      subcomplexGraphDiskMap (hC hik) (attachingHomotopy C hC i (t, ⟨j, a⟩)) :=
  wordHomotopy_natural C hC hik j t a

def wordDiskChange (i : Fin (n + 1)) :=
  naturalDiskAttachingEquiv (rawAttaching C i) (wordAttaching C hC i)
    (attachingHomotopy C hC i)

end FiniteChains.ClassicalCW.ChainWords
