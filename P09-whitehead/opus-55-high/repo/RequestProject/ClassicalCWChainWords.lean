import RequestProject.ClassicalSubcomplexBoundaryWords


/-! Simultaneous original-cell words for a finite filtration. Each actual
two-cell is straightened exactly once, at its first stage. The later
words, bases, and attaching homotopies are transported from this choice.
There is no finite-cell hypothesis. Unverified source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel
open Topology
open scoped Classical
variable {X : Type} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
  {n : ℕ} (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set X))
  (hC : Monotone C)

/-- Actual circle words and their homotopies. A seeded relative construction
may prescribe these on C0; the default is supplied by graph cellularization. -/
class Choices where
  cellWord : ∀ (i : Fin (n + 1)) (_j : RelCWComplex.cell (C i : Set X) 2),
    BoundaryWords (skeletonAttachingMap (C i : Set X) 1)
  cellWord_spec : ∀ i j,
    (subcomplexCellBoundary (C i) j).Homotopic (cellWord i j).boundaryMap


abbrev TopCell := RelCWComplex.cell (C (Fin.last n) : Set X) 2

def topCell (i : Fin (n + 1)) (j : RelCWComplex.cell (C i : Set X) 2) : TopCell C :=
  subcomplexCellInclusion (hC i.le_last) 2 j

def birthSet (j : TopCell C) :=
  Finset.univ.filter (fun i => j.val ∈ (C i).I 2)

theorem birthSet_nonempty j : (birthSet C j).Nonempty :=
  ⟨Fin.last n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.property⟩⟩

def birth (j : TopCell C) := (birthSet C j).min' (birthSet_nonempty C j)

theorem birth_mem j : j.val ∈ (C (birth C j)).I 2 :=
  (Finset.mem_filter.mp (Finset.min'_mem (birthSet C j) _)).2

theorem birth_le j i (hj : j.val ∈ (C i).I 2) :
    birth C j ≤ i :=
  Finset.min'_le _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)

def birthCell j : RelCWComplex.cell (C (birth C j) : Set X) 2 :=
  ⟨j.val, birth_mem C j⟩

variable [Choices C]

def birthWord (j : TopCell C) :=
  Choices.cellWord _ (birthCell C j)

theorem birthWord_spec j :
    (subcomplexCellBoundary (C (birth C j)) (birthCell C j)).Homotopic
      (birthWord C j).boundaryMap :=
  Choices.cellWord_spec _ _

def word (i : Fin (n + 1)) (j : RelCWComplex.cell (C i : Set X) 2) :=
  (birthWord C (topCell C hC i j)).map
    (subcomplexGraphInclusion (hC (birth_le C _ i j.property)))

theorem word_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    j :
    word C hC k (subcomplexCellInclusion (hC hik) 2 j) =
      (word C hC i j).map (subcomplexGraphInclusion (hC hik)) := by
  unfold word
  rw [BoundaryWords.map_comp, subcomplexGraphInclusion_comp]
  rfl
