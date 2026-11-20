module

public import RequestProject.PresCylinderCollapsedRoseLinear
public import RequestProject.PresCoverRelatorKernelEquiv

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

/-- Actual generator-incidence coefficients of the genuine collapsed attaching-boundary map. -/
noncomputable def presCoverRelatorGeneratorBoundary :=
  (cylinderCoverCollapsedGeneratorCoordinates w _
    (coneAdjCoverBaseEnd_isPosetCover f hf)).comp
      (presCoverCylinderRelatorBoundaryChain w f hf)

/-- Vanishing of the genuine collapsed relator boundary is equivalent to its actual generator equation. -/
theorem presCoverCollapsedRelatorBoundary_eq_zero_iff_generator
    (c : PresCoverRelator w f →₀ ℤ) :
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
  apply presCoverCollapsedRelatorBoundary_eq_zero_iff_generator

/-- Genuine presentation-cover two-cycles are equivalent to the actual generator-boundary kernel. -/
noncomputable def presCoverCycleRelatorGeneratorKernelEquiv (hpos : ∀ j, 0 < (w j).length) :=
  (presCoverCycleRelatorKernelEquiv w f hf hpos).trans
    (LinearEquiv.ofEq _ _ (presCoverCollapsedRelatorBoundary_ker_eq_generator w f hf))

end FiniteChains.PresModel
