import RequestProject.PresCoverRelatorCycleRealization
noncomputable section


namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)

/-- The genuine collapsed attaching-boundary linear map on actual finite lifted relators. -/
def presCoverCollapsedRelatorBoundary :=
  (normalizedStrictChain1 _
    (presCoverCylinderCollapse_monotone w f hf)).comp
      (presCoverCylinderRelatorBoundaryChain w f hf)

/-- Actual genuine two-cycle coordinates take values in the proved collapsed-boundary kernel. -/
def presCoverCycleRelatorKernelMap :
    LinearMap.ker (Comb.bdry2 (strictOrderCx P)) →ₗ[ℤ]
      LinearMap.ker (presCoverCollapsedRelatorBoundary w f hf) :=
  (presCoverCycleRelatorLinear w f hf hpos).codRestrict
    _
    (fun c => LinearMap.mem_ker.mpr
      (presCover_cycle_collapsed_relator_boundary_zero w f hf hpos c.val
        (LinearMap.mem_ker.mp c.property)))

theorem presCoverCycleRelatorKernelMap_injective :
    Function.Injective (presCoverCycleRelatorKernelMap w f hf hpos) := by
  intro c d he
  apply presCoverCycleRelatorLinear_injective w f hf hpos
  exact congrArg Subtype.val he

theorem presCoverCycleRelatorKernelMap_surjective :
    Function.Surjective (presCoverCycleRelatorKernelMap w f hf hpos) := by
  intro c
  obtain ⟨z, hz, he⟩ := exists_presCover_cycle_of_collapsed_relator_boundary w f hf hpos c.val
    (LinearMap.mem_ker.mp c.property)
  aesop

/-- Genuine presentation-cover two-cycles are linearly equivalent to the kernel of
its actual collapsed attaching-boundary map, with no assumed comparison premise. -/
def presCoverCycleRelatorKernelEquiv :=
  LinearEquiv.ofBijective _
    ⟨presCoverCycleRelatorKernelMap_injective w f hf hpos,
      presCoverCycleRelatorKernelMap_surjective w f hf hpos⟩
