module

public import RequestProject.PresCoverCollapsedFanBoundary
public import RequestProject.FinsuppBasis

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

/-- Each actual lifted attaching circle lies in the actual cylinder preimage. -/
noncomputable def presCoverCircleCylinderInclusion (p : PresCoverRelator w f)
    (x : RelatorCircle w p.1.2) : {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} :=
  ⟨presCoverCircleInclusion w f hf p x,
    ⟨Sum.inr x.val, (presCoverConeCircleOrderIso_symm_projection w f hf p.1.1 p.1.2 p.2 x).symm⟩⟩

theorem presCoverCircleCylinderInclusion_strictMono (p : PresCoverRelator w f) :
    StrictMono (presCoverCircleCylinderInclusion w f hf p) :=
  fun _ _ h => presCoverCircleInclusion_strictMono w f hf p h

/-- The actual attaching-circle boundary as a genuine chain in the cylinder preimage. -/
noncomputable def presCoverCylinderRelatorBoundary (p : PresCoverRelator w f) :
    StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ :=
  chain1 (strictOrderCxMap (presCoverCircleCylinderInclusion w f hf p)
    (presCoverCircleCylinderInclusion_strictMono w f hf p)) (relatorCircleFundamentalChain w p.1.2)

theorem presCoverCylinderRelatorBoundary_inclusion (p : PresCoverRelator w f) :
    chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)})
      (presCoverCylinderRelatorBoundary w f hf p) =
      Comb.bdry2 (strictOrderCx P) (presCoverRelatorFan w f hf p) := by
  erw [presCoverRelatorFan_boundary]
  change Finsupp.mapDomain (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}).onE
    (Finsupp.mapDomain (strictOrderCxMap (presCoverCircleCylinderInclusion w f hf p)
      (presCoverCircleCylinderInclusion_strictMono w f hf p)).onE
      (relatorCircleFundamentalChain w p.1.2)) = _
  erw [← Finsupp.mapDomain_comp]
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
  finsupp_basis c
  simp [presCoverCylinderRelatorBoundaryChain, Finsupp.linearCombination_single, presCoverCylinderRelatorBoundary_inclusion, presCoverRelatorFanChain]

/-- Relative fillings recover exactly the collapsed attaching boundary of their
actual relator coefficients. -/
theorem presCover_relative_collapsed_boundary
    (hpos : ∀ j, 0 < (w j).length)
    (c : StrictOrdTri P →₀ ℤ)
    (b : StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ)
    (hb : Comb.bdry2 (strictOrderCx P) c =
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) b) :
    normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
      (presCoverCylinderCollapse_monotone w f hf) b =
    normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
      (presCoverCylinderCollapse_monotone w f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf (presCoverRelatorChain w f hf hpos c)) := by
  obtain ⟨d, hd⟩ := exists_presCover_relative_cone_cylinder_decomposition w f hf hpos c b hb
  have he : Comb.bdry2 (strictOrderCx _) d =
      b - presCoverCylinderRelatorBoundaryChain w f hf (presCoverRelatorChain w f hf hpos c) := by
    apply Finsupp.mapDomain_injective (strictSubposetIncl_onE_injective
      {p : P | f p ∈ coneAdjBaseSet (S := circSet w)})
    change chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)})
      (Comb.bdry2 (strictOrderCx _) d) =
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) _
    rw [← bdry2_chain2, hd, map_sub, hb, map_sub,
      presCoverCylinderRelatorBoundaryChain_inclusion]
  have hz := cylinderCover_collapse_boundary_zero w (coneAdjCoverBaseEnd_isPosetCover f hf) d
  rw [he, map_sub] at hz
  exact sub_eq_zero.mp hz

/-- Actual cover two-cycle coordinates satisfy the actual collapsed attaching-boundary equation. -/
theorem presCover_cycle_collapsed_relator_boundary_zero
    (hpos : ∀ j, 0 < (w j).length) (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
      (presCoverCylinderCollapse_monotone w f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf (presCoverRelatorChain w f hf hpos c)) = 0 := by
  simpa only [map_zero] using (presCover_relative_collapsed_boundary w f hf hpos c 0
    (by simpa only [map_zero] using hc)).symm

end FiniteChains.PresModel
