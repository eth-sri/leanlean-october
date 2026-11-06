module

public import PottsDiscontinuity.Torus.DiamondDisplacement
public import PottsDiscontinuity.Torus.RibbonIntersectionBoundary
public import PottsDiscontinuity.Torus.RibbonIntersectionLinear

/-!
# Displacement coordinates of full torus homology

Intersection with the two explicit conserved flows gives the two lifted displacement
coordinates. They descend through actual cellular boundaries and identify the full
capped first homology with the rational coordinate plane.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

open Module

variable {N M : ℕ}

section
variable (hN : Even N) (hM : Even M)
/-- The full-torus displacement map, expressed by its two intersection coordinates. -/
def fullDiamondDisplacementMap  :
    diamondCycleSpace hN hM (openRCConfig N M) →ₗ[ℚ] (ℚ × ℚ) where
  toFun f := (ribbonIntersection hN hM (openRCConfig N M) (verticalDiamondCycle hN hM) f,
    -ribbonIntersection hN hM (openRCConfig N M) (horizontalDiamondCycle hN hM) f)
  map_add' f g := by
    apply Prod.ext
    · exact ribbonIntersection_add_right hN hM _ _ f g
    · change -ribbonIntersection hN hM _ _ (f + g) =
        -ribbonIntersection hN hM _ _ f + -ribbonIntersection hN hM _ _ g
      rw [ribbonIntersection_add_right]
      ring
  map_smul' c f := by
    apply Prod.ext
    · exact ribbonIntersection_smul_right hN hM _ _ f c
    · change -ribbonIntersection hN hM _ _ (c • f) = c * -ribbonIntersection hN hM _ _ f
      rw [ribbonIntersection_smul_right]
      ring

theorem fullDiamondDisplacementMap_apply (f : diamondCycleSpace hN hM (openRCConfig N M)) :
    fullDiamondDisplacementMap hN hM f =
      (diamondHorizontalDisplacement (openRCConfig N M) f.val,
        diamondVerticalDisplacement (openRCConfig N M) f.val) := by
  apply Prod.ext
  · exact ribbonIntersection_vertical_eq_displacement hN hM f
  · change -ribbonIntersection hN hM _ _ f = _
    rw [ribbonIntersection_horizontal_eq_displacement, neg_neg]

theorem fullDiamondDisplacementMap_vertical  :
    fullDiamondDisplacementMap hN hM (verticalDiamondCycle hN hM) = (0, -(N * M : ℚ)) := by
  rw [fullDiamondDisplacementMap_apply, verticalDiamondCycle_displacement_x,
    verticalDiamondCycle_displacement_y]

theorem fullDiamondDisplacementMap_horizontal  :
    fullDiamondDisplacementMap hN hM (horizontalDiamondCycle hN hM) = (-(N * M : ℚ), 0) := by
  rw [fullDiamondDisplacementMap_apply, horizontalDiamondCycle_displacement_x,
    horizontalDiamondCycle_displacement_y]

theorem ribbonBoundarySpace_le_ker_displacement  :
    ribbonBoundarySpace hN hM (openRCConfig N M) ≤ LinearMap.ker (fullDiamondDisplacementMap hN hM) := by
  intro f hf
  apply Prod.ext
  · change ribbonIntersection hN hM _ _ f = 0
    rw [ribbonIntersection_antisymm,
      ribbonIntersection_zero_of_mem_boundary hN hM _ f _ hf, neg_zero]
  · change -ribbonIntersection hN hM _ _ f = 0
    rw [ribbonIntersection_antisymm,
      ribbonIntersection_zero_of_mem_boundary hN hM _ f _ hf, neg_zero, neg_zero]

/-- Actual displacement descends through the full torus cellular boundary subspace. -/
def fullHomologyDisplacementMap  :
    CappedRibbonHomology hN hM (openRCConfig N M) →ₗ[ℚ] (ℚ × ℚ) :=
  (ribbonBoundarySpace hN hM (openRCConfig N M)).liftQ (fullDiamondDisplacementMap hN hM)
    (ribbonBoundarySpace_le_ker_displacement hN hM)

@[simp] theorem fullHomologyDisplacementMap_mk (f : diamondCycleSpace hN hM (openRCConfig N M)) :
    fullHomologyDisplacementMap hN hM ((ribbonBoundarySpace hN hM (openRCConfig N M)).mkQ f) =
      fullDiamondDisplacementMap hN hM f := rfl

theorem fullHomologyDisplacementMap_surjective (hNp : 0 < N) (hMp : 0 < M) : Function.Surjective (fullHomologyDisplacementMap hN hM) := by
  have hn : (N * M : ℚ) ≠ 0 := by positivity
  rintro ⟨x, y⟩
  refine ⟨(ribbonBoundarySpace hN hM (openRCConfig N M)).mkQ
    ((-y / (N * M : ℚ)) • verticalDiamondCycle hN hM +
      (-x / (N * M : ℚ)) • horizontalDiamondCycle hN hM), ?_⟩
  rw [fullHomologyDisplacementMap_mk, map_add, map_smul, map_smul,
    fullDiamondDisplacementMap_vertical, fullDiamondDisplacementMap_horizontal]
  simp_all

theorem fullHomologyDisplacementMap_injective (hNp : 0 < N) (hMp : 0 < M) : Function.Injective (fullHomologyDisplacementMap hN hM) := by
  have hd : finrank ℚ (CappedRibbonHomology hN hM (openRCConfig N M)) = finrank ℚ (ℚ × ℚ) := by
    rw [finrank_cappedRibbonHomology_open hN hM hNp hMp, Module.finrank_prod, finrank_self]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr
    (fullHomologyDisplacementMap_surjective hN hM hNp hMp)
end

end PottsDiscontinuity.Torus
