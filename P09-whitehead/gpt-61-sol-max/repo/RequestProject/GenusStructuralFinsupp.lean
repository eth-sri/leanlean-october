import Mathlib.Tactic

import RequestProject.GenerationStepFinsupp
import RequestProject.GenusActualSpineB2

/-! The actual genus-block operation as a supported structural map.

B1, B2, and injectivity are discharged by the constructed genus blocks.
The retained cells are fixed literally. The resulting preservation theorems
are the rule-3 input to the fixed-core replacement induction.
No Lean verification has been run on this source yet.
-/

noncomputable section
open scoped Classical

namespace FiniteChains.BlockFamily


variable {α Jr S : Type u} {Z M : S → Type u}
  [DecidableEq α] [DecidableEq S] [∀ s, DecidableEq (Z s)]
  (ρ : Jr ⊕ S → FreeGroup α) (b : ∀ s, M s → FreeGroup (α ⊕ Z s))
  (hfill : FilledF ρ b)
  (c : ∀ s, M s →₀ MonoidAlgebra ℤ (PresGroup (substPresF ρ b)))

variable (hc : IsFillingFS ρ b hfill c)
/-- The finite-support structural map of an arbitrary simultaneous block
replacement, with exactly the original coefficient map and surface fillings. -/
def substMorFS  : PresMorFS ρ (substPresF ρ b) where
  hom := substHomF ρ b hfill
  cells := fsCellsF ρ b hfill c
  cells_add := by
    intro y z
    ext k : 1
    exact congrFun (cellsF_add ρ b hfill (fun s => c s) y z) k
  cells_smul := by
    intro a y
    ext k : 1
    exact congrFun (cellsF_smul ρ b hfill (fun s => c s) a y) k
  cells_cycle := by
    intro y hy
    change coverSecondBoundary _ _ (fsCellsF ρ b hfill c y) = 0
    rw [fsCellsF_boundary ρ b hfill c hc y, hy]
    simp
  cells_aug := by
    intro y hy k
    change augPres (substPresF ρ b) (cellsF ρ b hfill (fun s => c s) y k) = 0
    exact augPres_cellsF_eq_zero hy k

/-- The structural map preserves the retained two-cells exactly, including
their actual coefficients in the new group ring. -/
theorem substMorFS_retained 
    (j : Jr) (a : MonoidAlgebra ℤ (PresGroup ρ)) :
    (substMorFS ρ b hfill c hc).cells (Finsupp.single (Sum.inl j) a) =
      Finsupp.single (Sum.inl j) (coeffF ρ b hfill a) := by
  ext k : 1
  cases k with
  | inl k =>
      change coeffF ρ b hfill (Finsupp.single (Sum.inl j) a (Sum.inl k)) = _
      by_cases h : k = j
      · subst k; simp
      · simp [h]
  | inr p =>
      change coeffF ρ b hfill (Finsupp.single (Sum.inl j) a (Sum.inr p.1)) *
        c p.1 p.2 = _
      simp

end FiniteChains.BlockFamily

namespace FiniteChains.Davis.Genus

open BlockFamily

variable {α Jr S : Type} (σ : Jr ⊕ S → FreeGroup α)
  (q : S → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup α)
  (hσ : ∀ s, σ (Sum.inr s) = commWord (u s) (finitePairs (q s)))

/-- Rule 3 with all its geometric inputs supplied, including for an
infinite family over an infinite fixed core. -/
def finiteSpineFamilyStructuralMap  :=
  substMorFS σ (familyFiniteSpineWordBlock q u)
    (familyFiniteSpineWordBlock_filled σ q u hσ)
    (finiteSpineFamilyFilling σ q u)
    (finiteSpineFamilyFilling_isFilling σ q u hσ)



/-- Actual equation (3.3) for the simultaneous genus replacement. -/
theorem finiteSpineFamilyStructuralMap_generates :
    FSGenerates (finiteSpineFamilyStructuralMap σ q u hσ) := by
  classical solve_by_elim (transparency := .default) [FiniteChains.Davis.Genus.finiteSpineFamily_fsGenerates_actual]

/-- On a retained core two-cell the structural map is literally the
labelled inclusion with its induced change of group-ring coefficients. -/
abbrev finiteSpineFamilyStructuralMap_core_cell
    (j : Jr) (a : MonoidAlgebra ℤ (PresGroup σ))  :=
  FiniteChains.BlockFamily.substMorFS_retained σ (FiniteChains.Davis.Genus.familyFiniteSpineWordBlock q u)
    (FiniteChains.Davis.Genus.familyFiniteSpineWordBlock_filled σ q u hσ)
    (FiniteChains.Davis.Genus.finiteSpineFamilyFilling σ q u)
    (FiniteChains.Davis.Genus.finiteSpineFamilyFilling_isFilling σ q u hσ) j a







end FiniteChains.Davis.Genus
