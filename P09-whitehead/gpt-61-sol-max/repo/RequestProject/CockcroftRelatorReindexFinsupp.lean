import Mathlib.Tactic

import RequestProject.CockcroftRelatorReindex
import RequestProject.GenerationStepFinsupp
import RequestProject.BlockFamilyBlockwiseFinsupp

/-! Relator reindexing for arbitrary presentations and finitely supported
chains. No finiteness of the generators or relators is imposed.
Pending Lean verification. -/

noncomputable section


set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelatorReindex
open BlockFamily

variable {A J K : Type u} [DecidableEq A]
  (ρ : J → FreeGroup A) (τ : K → FreeGroup A) (e : J ≃ K)
  (hrel : ∀ j, τ (e j) = ρ j)

variable (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ))
def cellsFS   :=
  Finsupp.mapDomain e (v.mapRange (coefficientMap ρ τ e hrel) (map_zero _))

section
omit [DecidableEq A]
variable (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ))
@[simp] theorem cellsFS_apply_image
     (j : J) :
    cellsFS ρ τ e hrel v (e j) = coefficientMap ρ τ e hrel (v j) := by simp_all [cellsFS]

theorem cellsFS_apply  (k : K) :
    cellsFS ρ τ e hrel v k = coefficientMap ρ τ e hrel (v (e.symm k)) := by
  grind [Equiv.apply_symm_apply, FiniteChains.RelatorReindex.cellsFS_apply_image]

@[simp] theorem cellsFS_single (j : J) (a : MonoidAlgebra ℤ (PresGroup ρ)) :
    cellsFS ρ τ e hrel (Finsupp.single j a) =
      Finsupp.single (e j) (coefficientMap ρ τ e hrel a) := by
  simp [cellsFS]

theorem cellsFS_add (v w : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    cellsFS ρ τ e hrel (v + w) = cellsFS ρ τ e hrel v + cellsFS ρ τ e hrel w := by
  ext k : 1
  simp only [cellsFS_apply, Finsupp.add_apply, map_add]
end

theorem cellsFS_boundary_apply  (a : A) :
    coverSecondBoundary (relSub τ) τ (cellsFS ρ τ e hrel v) a =
      coefficientMap ρ τ e hrel (coverSecondBoundary (relSub ρ) ρ v a) := by
  induction v using Finsupp.induction_linear with
  | zero => simp [cellsFS]
  | add v w hv hw =>
      simp_all [cellsFS_add]
  | single j c =>
      simp only [cellsFS_single, fsCoverSecondBoundary_apply, Finsupp.sum_single_index,
        zero_mul, map_mul, coefficientMap_matrix]

theorem cellsFS_cycle 
    (hv : FSIsFoxCycle ρ v) : FSIsFoxCycle τ (cellsFS ρ τ e hrel v) := by
  change coverSecondBoundary (relSub ρ) ρ v = 0 at hv
  apply Finsupp.ext
  intro a
  simp [cellsFS_boundary_apply, hv]

omit [DecidableEq A] in
theorem cellsFS_aug  (k : K) :
    augPres τ (cellsFS ρ τ e hrel v k) = augPres ρ (v (e.symm k)) := by
  rw [cellsFS_apply]
  exact augQ_mapDomain (groupMap ρ τ e hrel) (v (e.symm k))

include hrel in
theorem fsIsCockcroft_of (hτ : FSIsCockcroft τ) : FSIsCockcroft ρ := by
  intro v hv j
  have h := hτ (cellsFS ρ τ e hrel v) (cellsFS_cycle ρ τ e hrel v hv) (e j)
  simpa only [cellsFS_aug, Equiv.symm_apply_apply] using h

end FiniteChains.RelatorReindex
