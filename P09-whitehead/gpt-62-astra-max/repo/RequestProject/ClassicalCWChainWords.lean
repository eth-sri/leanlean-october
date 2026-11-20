module

public import RequestProject.ClassicalSubcomplexBoundaryWords

@[expose] public section

/-! Simultaneous original-cell words for a finite filtration. Each actual
two-cell is straightened exactly once, at its first stage. The later
words, bases, and attaching homotopies are transported from this choice.
There is no finite-cell hypothesis. Unverified source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical
variable {X : Type} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
  {n : ℕ} (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set X))
  (hC : Monotone C)

/-- Actual circle words and their homotopies. A seeded relative construction
may prescribe these on C0; the default is supplied by graph cellularization. -/
class Choices where
  cellWord : ∀ (i : Fin _) (_j : RelCWComplex.cell (C i : Set X) 2),
    BoundaryWords _
  cellWord_spec : ∀ i j,
    (subcomplexCellBoundary _ j).Homotopic (cellWord i j).boundaryMap

instance (priority := low) defaultChoices : Choices C where
  cellWord i j := Classical.choose _
  cellWord_spec i j := Classical.choose_spec (subcomplexCellBoundary_word_exists _ j)

abbrev TopCell := RelCWComplex.cell (C (Fin.last n) : Set X) 2

def topCell (i : Fin _) (j : RelCWComplex.cell (C i : Set X) 2) :=
  subcomplexCellInclusion (hC (Fin.le_last i)) 2 j

variable (j : TopCell C)

def birthSet :=
  Finset.univ.filter (fun i => j.val ∈ (C i).I 2)

theorem birthSet_nonempty : (birthSet C j).Nonempty :=
  ⟨Fin.last n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.property⟩⟩

def birth := (birthSet C j).min' (birthSet_nonempty C j)

theorem birth_mem : j.val ∈ (C (birth C j)).I 2 :=
  (Finset.mem_filter.mp (Finset.min'_mem _ (birthSet_nonempty C j))).2

theorem birth_le (i : Fin _) (hj : j.val ∈ (C i).I 2) :
    birth C j ≤ i :=
  Finset.min'_le _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)

def birthCell : RelCWComplex.cell (C (birth C j) : Set X) 2 :=
  ⟨j.val, birth_mem C j⟩

variable [Choices C]

variable (j : TopCell C)

def birthWord :=
  Choices.cellWord _ (birthCell C j)

theorem birthWord_spec :
    (subcomplexCellBoundary _ (birthCell C j)).Homotopic
      (birthWord C j).boundaryMap :=
  by apply Choices.cellWord_spec

def word (i : Fin _) (j : RelCWComplex.cell (C i : Set X) 2) :=
  (birthWord C _).map
    (subcomplexGraphInclusion (hC (birth_le C (topCell C hC i j) i j.property)))

theorem word_natural {i k : Fin _} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set X) 2) :
    word C hC k (subcomplexCellInclusion (hC hik) 2 j) =
      (word C hC i j).map (subcomplexGraphInclusion (hC hik)) := by
  unfold word
  rw [BoundaryWords.map_comp, subcomplexGraphInclusion_comp]
  rfl

variable {i k : Fin (n + 1)} (hik : i ≤ k)

end FiniteChains.ClassicalCW.ChainWords
