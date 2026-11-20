module

public import RequestProject.PresCoverCollapsedFanBoundary

@[expose] public section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

variable (p : PresCoverRelator w f)

/-- Each actual lifted attaching circle lies in the actual cylinder preimage. -/
def presCoverCircleCylinderInclusion
    (x : RelatorCircle w p.1.2) : {p : P // f p ∈ coneAdjBaseSet} :=
  ⟨presCoverCircleInclusion w f hf p x,
    ⟨Sum.inr x.val, (presCoverConeCircleOrderIso_symm_projection w f hf _ _ p.2 x).symm⟩⟩

theorem presCoverCircleCylinderInclusion_strictMono :
    StrictMono (presCoverCircleCylinderInclusion w f hf p) :=
  fun _ _ h => presCoverCircleInclusion_strictMono w f hf p h

/-- The actual attaching-circle boundary as a genuine chain in the cylinder preimage. -/
def presCoverCylinderRelatorBoundary :
    StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet} →₀ ℤ :=
  chain1 (strictOrderCxMap (presCoverCircleCylinderInclusion w f hf p)
    (presCoverCircleCylinderInclusion_strictMono w f hf p)) (relatorCircleFundamentalChain w p.1.2)

theorem presCoverCylinderRelatorBoundary_inclusion :
    chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)})
      (presCoverCylinderRelatorBoundary w f hf p) =
      Comb.bdry2 _ (presCoverRelatorFan w f hf p) := by
  erw [presCoverRelatorFan_boundary]
  change Finsupp.mapDomain _
    (Finsupp.mapDomain _
      _) = _
  erw [← Finsupp.mapDomain_comp]
  rfl

/-- The actual attaching-boundary map on genuine finite lifted-relator chains. -/
def presCoverCylinderRelatorBoundaryChain :=
  Finsupp.linearCombination ℤ (presCoverCylinderRelatorBoundary w f hf)

theorem presCoverCylinderRelatorBoundaryChain_inclusion (c : PresCoverRelator w f →₀ ℤ) :
    chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)})
      (presCoverCylinderRelatorBoundaryChain w f hf c) =
      Comb.bdry2 _ (presCoverRelatorFanChain w f hf c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single p n =>
    simp [presCoverCylinderRelatorBoundaryChain, Finsupp.linearCombination_single, map_smul, presCoverRelatorFanChain]
    exact congrArg (n • ·) (presCoverCylinderRelatorBoundary_inclusion w f hf p)

variable (hpos : ∀ j, 0 < (w j).length) (c : StrictOrdTri P →₀ ℤ)

/-- Relative fillings recover exactly the collapsed attaching boundary of their
actual relator coefficients. -/
theorem presCover_relative_collapsed_boundary
    (b : StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet} →₀ ℤ)
    (hb : Comb.bdry2 (strictOrderCx P) c =
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) b) :
    normalizedStrictChain1 _
      (presCoverCylinderCollapse_monotone w f hf) b =
    normalizedStrictChain1 _
      (presCoverCylinderCollapse_monotone w f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf (presCoverRelatorChain w f hf hpos c)) := by
  obtain ⟨d, hd⟩ := exists_presCover_relative_cone_cylinder_decomposition w f hf hpos c b hb
  have he : Comb.bdry2 (strictOrderCx _) d =
      b - presCoverCylinderRelatorBoundaryChain w f hf (presCoverRelatorChain w f hf hpos c) := by
    apply Finsupp.mapDomain_injective (strictSubposetIncl_onE_injective
      _)
    change chain1 _
      _ =
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) _
    calc
      _ = Comb.bdry2 _
          _ :=
        (bdry2_chain2 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) d).symm
      _ = _ := by
        rw [hd, map_sub, map_sub]
        exact congrArg₂ (· - ·) hb (presCoverCylinderRelatorBoundaryChain_inclusion w f hf _).symm
  have hz := cylinderCover_collapse_boundary_zero w (coneAdjCoverBaseEnd_isPosetCover f hf) d
  rw [he, map_sub] at hz
  exact sub_eq_zero.mp hz


theorem presCover_cycle_collapsed_relator_boundary_zero
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    normalizedStrictChain1 _
      (presCoverCylinderCollapse_monotone w f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf (presCoverRelatorChain w f hf hpos c)) = 0 := by
  simpa using (presCover_relative_collapsed_boundary w f hf hpos c 0 (by simpa using hc)).symm

end FiniteChains.PresModel
