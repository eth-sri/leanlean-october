module

public import RequestProject.CockcroftRelatorReindex
public import RequestProject.FinsuppBasis
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
variable {A J K : Type u}
  (ρ : J → FreeGroup A) (τ : K → FreeGroup A) (e : J ≃ K)
  (hrel : ∀ j, τ (e j) = ρ j)

def cellsFS (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    K →₀ MonoidAlgebra ℤ (PresGroup τ) :=
  Finsupp.mapDomain e (v.mapRange (coefficientMap ρ τ e hrel) (map_zero _))


@[simp] theorem cellsFS_apply_image
    (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (j : J) :
    cellsFS ρ τ e hrel v (e j) = coefficientMap ρ τ e hrel (v j) := by
  simp [cellsFS]


theorem cellsFS_apply (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (k : K) :
    cellsFS ρ τ e hrel v k = coefficientMap ρ τ e hrel (v (e.symm k)) := by
  simpa only [Equiv.apply_symm_apply] using cellsFS_apply_image ρ τ e hrel v (e.symm k)


@[simp] theorem cellsFS_single (j : J) (a : MonoidAlgebra ℤ (PresGroup ρ)) :
    cellsFS ρ τ e hrel (Finsupp.single j a) =
      Finsupp.single (e j) (coefficientMap ρ τ e hrel a) := by
  simp [cellsFS]


theorem cellsFS_add (v w : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    cellsFS ρ τ e hrel (v + w) = cellsFS ρ τ e hrel v + cellsFS ρ τ e hrel w := by
  ext k : 1
  simp only [cellsFS_apply, Finsupp.add_apply, map_add]

theorem cellsFS_boundary_apply (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (a : A) :
    coverSecondBoundary (relSub τ) τ (cellsFS ρ τ e hrel v) a =
      coefficientMap ρ τ e hrel (coverSecondBoundary (relSub ρ) ρ v a) := by
  finsupp_singles v [ cellsFS_add ]
  simp [cellsFS_single, fsCoverSecondBoundary_apply, Finsupp.sum_single_index, coefficientMap_matrix]

theorem cellsFS_cycle (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ))
    (hv : FSIsFoxCycle ρ v) : FSIsFoxCycle τ (cellsFS ρ τ e hrel v) := by
  change coverSecondBoundary (relSub ρ) ρ v = 0 at hv
  apply Finsupp.ext
  intro a
  simp only [cellsFS_boundary_apply, hv, Finsupp.zero_apply, map_zero]


theorem cellsFS_aug (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (k : K) :
    augPres τ (cellsFS ρ τ e hrel v k) = augPres ρ (v (e.symm k)) := by
  rw [cellsFS_apply]
  exact augQ_mapDomain (groupMap ρ τ e hrel) (v (e.symm k))

include hrel in
theorem fsIsCockcroft_of (hτ : FSIsCockcroft τ) : FSIsCockcroft ρ := by
  intro v hv j
  have h := hτ (cellsFS ρ τ e hrel v) (cellsFS_cycle ρ τ e hrel v hv) (e j)
  simpa only [cellsFS_aug, Equiv.symm_apply_apply] using h

end FiniteChains.RelatorReindex
