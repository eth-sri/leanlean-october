import RequestProject.PresCoverCollapsedFanBoundary
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

/-- Each actual lifted attaching circle lies in the actual cylinder preimage. -/
def presCoverCircleCylinderInclusion (p : PresCoverRelator w f)
    (x : RelatorCircle w p.1.2) : {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} :=
  ⟨presCoverCircleInclusion w f hf p x,
    ⟨Sum.inr x.val, (presCoverConeCircleOrderIso_symm_projection w f hf p.1.1 p.1.2 p.2 x).symm⟩⟩

theorem presCoverCircleCylinderInclusion_strictMono p :
    StrictMono (presCoverCircleCylinderInclusion w f hf p) :=
  fun _ _ h => presCoverCircleInclusion_strictMono w f hf p h

/-- The actual attaching-circle boundary as a genuine chain in the cylinder preimage. -/
def presCoverCylinderRelatorBoundary (p : PresCoverRelator w f) :
    StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ :=
  chain1 (strictOrderCxMap _
    (presCoverCircleCylinderInclusion_strictMono w f hf p)) (relatorCircleFundamentalChain w p.1.2)

theorem presCoverCylinderRelatorBoundary_inclusion p :
    chain1 (strictSubposetIncl {p | f p ∈ coneAdjBaseSet (S := circSet w)})
      (presCoverCylinderRelatorBoundary w f hf p) =
      Comb.bdry2 (strictOrderCx P) (presCoverRelatorFan w f hf p) := by
  rwd [presCoverRelatorFan_boundary]
  change Finsupp.mapDomain (strictSubposetIncl _).onE
    (Finsupp.mapDomain (strictOrderCxMap _
      (presCoverCircleCylinderInclusion_strictMono w f hf p)).onE
      (relatorCircleFundamentalChain w p.1.2)) = _
  rwd [← Finsupp.mapDomain_comp]
  rfl

/-- The actual attaching-boundary map on genuine finite lifted-relator chains. -/
def presCoverCylinderRelatorBoundaryChain :
    (PresCoverRelator w f →₀ ℤ) →ₗ[ℤ]
      (StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ) :=
  Finsupp.linearCombination ℤ (presCoverCylinderRelatorBoundary w f hf)

theorem presCoverCylinderRelatorBoundaryChain_inclusion c :
    chain1 (strictSubposetIncl {p | f p ∈ coneAdjBaseSet (S := circSet w)})
      (presCoverCylinderRelatorBoundaryChain w f hf c) =
      Comb.bdry2 (strictOrderCx P) (presCoverRelatorFanChain w f hf c) := by
  lin_ind c p n =>
    simp [presCoverCylinderRelatorBoundaryChain, Finsupp.linearCombination_single, map_smul, presCoverCylinderRelatorBoundary_inclusion, presCoverRelatorFanChain]

/-- Actual cover two-cycle coordinates satisfy the actual collapsed attaching-boundary equation. -/
theorem presCover_cycle_collapsed_relator_boundary_zero
    hpos (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
      (presCoverCylinderCollapse_monotone w f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf (presCoverRelatorChain w f hf hpos c)) = 0 := by
  obtain ⟨b, hb, hz⟩ := exists_presCover_cycle_collapsed_fan_boundary w f hf hpos c hc
  have he :=
    Finsupp.mapDomain_injective
      (strictSubposetIncl_onE_injective _)
      ((presCoverCylinderRelatorBoundaryChain_inclusion w f hf _).trans hb.symm)
  simp_all
