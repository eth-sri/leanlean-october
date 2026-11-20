module

public import RequestProject.CockcroftRelatorReindex
public import RequestProject.GenerationStepFinsupp
public import RequestProject.BlockFamilyBlockwiseFinsupp

@[expose] public section

/-! Relator reindexing for arbitrary presentations and finitely supported
chains. No finiteness of the generators or relators is imposed.
Pending Lean verification. -/

noncomputable section
open scoped Classical

namespace FiniteChains.RelatorReindex
open BlockFamily

universe u
variable {A J K : Type u} [DecidableEq A]
  (ρ : J → FreeGroup A) (τ : K → FreeGroup A) (e : J ≃ K)
  (hrel : ∀ j, τ (e j) = ρ j)

variable (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ))

def cellsFS :=
  Finsupp.mapDomain e (v.mapRange (coefficientMap ρ τ e hrel) (map_zero _))

omit [DecidableEq A] in
@[simp] theorem cellsFS_apply_image (j : J) :
    cellsFS ρ τ e hrel v (e j) = coefficientMap ρ τ e hrel (v j) := by
  simp only [cellsFS, Finsupp.mapDomain_apply_of_injective e.injective, Finsupp.mapRange_apply]

omit [DecidableEq A] in
theorem cellsFS_apply (k : K) :
    cellsFS ρ τ e hrel v k = coefficientMap ρ τ e hrel (v (e.symm k)) := by
  simpa only [Equiv.apply_symm_apply] using cellsFS_apply_image ρ τ e hrel v (e.symm k)

omit [DecidableEq A] in
@[simp] theorem cellsFS_single (j : J) (a : MonoidAlgebra ℤ (PresGroup ρ)) :
    cellsFS ρ τ e hrel (Finsupp.single j a) =
      Finsupp.single (e j) (coefficientMap ρ τ e hrel a) := by
  simp only [cellsFS, Finsupp.mapRange_single, Finsupp.mapDomain_single]

omit [DecidableEq A] in
theorem cellsFS_add (v w : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    cellsFS ρ τ e hrel (v + w) = cellsFS ρ τ e hrel v + cellsFS ρ τ e hrel w := by
  ext k : 1
  simp only [cellsFS_apply, Finsupp.add_apply, map_add]

variable (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ))

theorem cellsFS_boundary_apply (a : A) :
    coverSecondBoundary (relSub τ) τ (cellsFS ρ τ e hrel v) a =
      coefficientMap ρ τ e hrel (coverSecondBoundary (relSub ρ) ρ v a) := by
  induction v using Finsupp.induction_linear with
  | zero => simp [cellsFS]
  | add v w hv hw =>
      simp only [cellsFS_add, map_add, Finsupp.add_apply, hv, hw]
  | single j c =>
      simp_all [cellsFS_single, fsCoverSecondBoundary_apply, coefficientMap_matrix]

theorem cellsFS_cycle
    (hv : FSIsFoxCycle ρ v) : FSIsFoxCycle τ (cellsFS ρ τ e hrel v) := by
  change coverSecondBoundary (relSub ρ) ρ v = 0 at hv
  ext <;> simp_all [cellsFS_boundary_apply, hv, Finsupp.zero_apply, map_zero]

omit [DecidableEq A] in
theorem cellsFS_aug (k : K) :
    augPres τ (cellsFS ρ τ e hrel v k) = augPres ρ (v (e.symm k)) := by
  rw [cellsFS_apply]
  apply augQ_mapDomain

include hrel in
theorem fsIsCockcroft_of (hτ : FSIsCockcroft τ) : FSIsCockcroft ρ := by
  intro v hv j
  have h := hτ (cellsFS ρ τ e hrel v) (cellsFS_cycle ρ τ e hrel v hv) (e j)
  grind [cellsFS_aug]

end FiniteChains.RelatorReindex
