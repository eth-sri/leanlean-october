import Mathlib.Tactic

import RequestProject.PresCoverCollapsedFanBoundary

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

variable (p : PresCoverRelator w f)
/-- Each actual lifted attaching circle lies in the actual cylinder preimage. -/
noncomputable def presCoverCircleCylinderInclusion 
    (x : RelatorCircle w p.1.2) : {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} :=
  ⟨presCoverCircleInclusion w f hf p x,
    ⟨Sum.inr x.val, (presCoverConeCircleOrderIso_symm_projection w f hf p.1.1 p.1.2 p.2 x).symm⟩⟩

theorem presCoverCircleCylinderInclusion_strictMono  :
    StrictMono (presCoverCircleCylinderInclusion w f hf p) :=
  fun _ _ h => presCoverCircleInclusion_strictMono w f hf p h

/-- The actual attaching-circle boundary as a genuine chain in the cylinder preimage. -/
noncomputable def presCoverCylinderRelatorBoundary  :
    StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ :=
  chain1 (strictOrderCxMap (presCoverCircleCylinderInclusion w f hf p)
    (presCoverCircleCylinderInclusion_strictMono w f hf p)) (relatorCircleFundamentalChain w p.1.2)

theorem presCoverCylinderRelatorBoundary_inclusion  :
    chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)})
      (presCoverCylinderRelatorBoundary w f hf p) =
      Comb.bdry2 (strictOrderCx P) (presCoverRelatorFan w f hf p) := by
  rw  [presCoverRelatorFan_boundary]
  change Finsupp.mapDomain (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}).onE
    (Finsupp.mapDomain (strictOrderCxMap (presCoverCircleCylinderInclusion w f hf p)
      (presCoverCircleCylinderInclusion_strictMono w f hf p)).onE
      (relatorCircleFundamentalChain w p.1.2)) = _
  rw  [← Finsupp.mapDomain_comp]
  rfl

/-- The actual attaching-boundary map on genuine finite lifted-relator chains. -/
noncomputable def presCoverCylinderRelatorBoundaryChain :
    (PresCoverRelator w f →₀ ℤ) →ₗ[ℤ]
      (StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ) :=
  Finsupp.linearCombination ℤ (presCoverCylinderRelatorBoundary w f hf)

theorem presCoverCylinderRelatorBoundaryChain_inclusion (c : PresCoverRelator w f →₀ ℤ) :
    chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)})
      (presCoverCylinderRelatorBoundaryChain w f hf c) =
      Comb.bdry2 (strictOrderCx P) (presCoverRelatorFanChain w f hf c) := by
  induction c using Finsupp.induction_linear <;> simp_all [presCoverCylinderRelatorBoundaryChain, presCoverCylinderRelatorBoundary_inclusion, presCoverRelatorFanChain]

/-- Actual cover two-cycle coordinates satisfy the actual collapsed attaching-boundary equation. -/
theorem presCover_cycle_collapsed_relator_boundary_zero
    (hpos : ∀ j, 0 < (w j).length) (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
      (presCoverCylinderCollapse_monotone w f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf (presCoverRelatorChain w f hf hpos c)) = 0 := by
  obtain ⟨b, hb, hz⟩ := exists_presCover_cycle_collapsed_fan_boundary w f hf hpos c hc
  have he  :=
    Finsupp.mapDomain_injective
      (strictSubposetIncl_onE_injective {p : P | f p ∈ coneAdjBaseSet (S := circSet w)})
      ((presCoverCylinderRelatorBoundaryChain_inclusion w f hf _).trans hb.symm)
  rw  [he]
  exact hz

end FiniteChains.PresModel
