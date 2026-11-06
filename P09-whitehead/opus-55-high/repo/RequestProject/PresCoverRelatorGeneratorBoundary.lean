import RequestProject.PresCylinderCollapsedRoseLinear
import RequestProject.PresCoverRelatorKernelEquiv
noncomputable section


namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

/-- Actual generator-incidence coefficients of the genuine collapsed attaching-boundary map. -/
def presCoverRelatorGeneratorBoundary :=
  (cylinderCoverCollapsedGeneratorCoordinates w _
    (coneAdjCoverBaseEnd_isPosetCover f hf)).comp
      (presCoverCylinderRelatorBoundaryChain w f hf)

/-- Vanishing of the genuine collapsed relator boundary is equivalent to its actual generator equation. -/
theorem presCoverCollapsedRelatorBoundary_eq_zero_iff_generator
    c :
    presCoverCollapsedRelatorBoundary w f hf c = 0 ↔
      presCoverRelatorGeneratorBoundary w f hf c = 0 :=
  cylinderCoverCollapsedChain_eq_zero_iff_coordinates w _
    _ _
      (presCoverCylinderRelatorBoundaryChain_cycle w f hf c)

/-- Equality of the two genuine kernels is proved from actual cycle-coordinate detection. -/
theorem presCoverCollapsedRelatorBoundary_ker_eq_generator :
    LinearMap.ker (presCoverCollapsedRelatorBoundary w f hf) =
      LinearMap.ker (presCoverRelatorGeneratorBoundary w f hf) := by
  ext c
  exact presCoverCollapsedRelatorBoundary_eq_zero_iff_generator w f hf c

/-- Genuine presentation-cover two-cycles are equivalent to the actual generator-boundary kernel. -/
def presCoverCycleRelatorGeneratorKernelEquiv (hpos : ∀ j, 0 < (w j).length) :
    LinearMap.ker (Comb.bdry2 (strictOrderCx P)) ≃ₗ[ℤ]
      LinearMap.ker (presCoverRelatorGeneratorBoundary w f hf) :=
  (presCoverCycleRelatorKernelEquiv w f hf hpos).trans
    (LinearEquiv.ofEq _ _ (presCoverCollapsedRelatorBoundary_ker_eq_generator w f hf))
