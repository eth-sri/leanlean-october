import RequestProject.NormalizedStrictBoundary
import RequestProject.PresCoverConeCylinderDecomposition
import RequestProject.Tac


bwd

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))

/-- The actual cylinder collapse kills the boundary of every genuine finite triangle chain. -/
theorem cylinderCover_collapse_boundary_zero
    (hf : IsPosetCover f) (c : StrictOrdTri P →₀ ℤ) :
    normalizedStrictChain1 (cylinderCoverCollapse w hf) (cylinderCoverCollapse_monotone w hf)
      (Comb.bdry2 (strictOrderCx P) c) = 0 := by
  simp [← bdry2_normalizedStrictChain2, cylinderCover_normalized_collapse_zero, map_zero]

variable (f : P → PresPos w) (hf : IsPosetCover f)

/-- The genuine collapse on the actual cylinder preimage in a presentation cover. -/
noncomputable def presCoverCylinderCollapse :
    {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →
      {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} :=
  cylinderCoverCollapse w (coneAdjCoverBaseEnd_isPosetCover f hf)

theorem presCoverCylinderCollapse_monotone : Monotone (presCoverCylinderCollapse w f hf) :=
  cylinderCoverCollapse_monotone w _

/-- The actual fan boundary of an actual cover two-cycle has a genuine cylinder
edge-chain lift whose actual collapsed chain is zero. -/
theorem exists_presCover_cycle_collapsed_fan_boundary
    hpos (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    ∃ b : StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ,
      chain1 (strictSubposetIncl {p | f p ∈ coneAdjBaseSet (S := circSet w)}) b =
        Comb.bdry2 (strictOrderCx P)
          (presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)) ∧
      normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
        (presCoverCylinderCollapse_monotone w f hf) b = 0 := by
  obtain ⟨d, _, hb⟩ := exists_presCover_cycle_cylinder_boundary w f hf hpos c hc
  refine ⟨-Comb.bdry2 (strictOrderCx {p : P // f p ∈ coneAdjBaseSet (S := circSet w)}) d,
    ?_, ?_⟩
  · simp_all
  · have hz := cylinderCover_collapse_boundary_zero w
      (coneAdjCoverBaseEnd_isPosetCover f hf) d
    aesop
