import RequestProject.PresCylinderRoseCover
import RequestProject.RoseCoverCycleReconstruction
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

/-- Actual collapse normalization commutes with the edge boundary. -/
theorem bdry1_normalizedStrictChain1 g hg
    c :
    Comb.bdry1 (strictOrderCx P) (normalizedStrictChain1 g hg c) =
      Finsupp.mapDomain g (Comb.bdry1 (strictOrderCx P) c) := by
  rwd [bdry1_normalizeOrdChain1, bdry1_chain1, bdry1_chain1]
  change Finsupp.mapDomain g (Finsupp.mapDomain id _) = _
  simp

end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → CylBase w) (hf : IsPosetCover f)

/-- The actual collapsed finite edge chain, linearly pulled back to the actual rose preimage. -/
def cylinderCoverCollapsedRoseChain :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (cylinderCoverRoseSet w f) →₀ ℤ) :=
  (Finsupp.lcomapDomain _
    (strictSubposetIncl_onE_injective _)).comp
      (normalizedStrictChain1 _ (cylinderCoverCollapse_monotone w hf))

/-- Including the actual rose chain recovers exactly the genuine normalized collapsed chain. -/
theorem cylinderCoverCollapsedRoseChain_inclusion c :
    chain1 (strictSubposetIncl (cylinderCoverRoseSet w f))
      (cylinderCoverCollapsedRoseChain w f hf c) =
        normalizedStrictChain1 (cylinderCoverCollapse w hf) (cylinderCoverCollapse_monotone w hf) c := by
  apply Finsupp.mapDomain_comapDomain _ (strictSubposetIncl_onE_injective _)
  intro e he
  have hs := cylinderCoverCollapsedChain_support_rose w f hf c e he
  exact ⟨⟨(⟨e.val.1, hs.1⟩, ⟨e.val.2, hs.2⟩), e.property⟩, Subtype.ext rfl⟩

/-- An actual collapsed one-cycle is a genuine one-cycle on the actual rose preimage. -/
theorem cylinderCoverCollapsedRoseChain_cycle (c : StrictOrdEdge P →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx P) c = 0) :
    Comb.bdry1 (strictOrderCx (cylinderCoverRoseSet w f))
      (cylinderCoverCollapsedRoseChain w f hf c) = 0 := by
  apply Finsupp.mapDomain_injective (f := Subtype.val) Subtype.val_injective
  change chain0 (strictSubposetIncl _)
    (Comb.bdry1 _
      (cylinderCoverCollapsedRoseChain w f hf c)) = _
  simp [← bdry1_chain1, cylinderCoverCollapsedRoseChain_inclusion, bdry1_normalizedStrictChain1, hc, Finsupp.mapDomain_zero]

/-- The actual surviving generator-incidence coordinates of a collapsed cylinder chain. -/
def cylinderCoverCollapsedGeneratorCoordinates :=
  (roseCoverGeneratorCoordinates _
    (cylinderCoverRoseEnd_isPosetCover w f hf)).comp
      (cylinderCoverCollapsedRoseChain w f hf)

/-- For genuine one-cycles the collapsed chain vanishes exactly when its actual generator coordinates vanish. -/
theorem cylinderCoverCollapsedChain_eq_zero_iff_coordinates (c : StrictOrdEdge P →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx P) c = 0) :
    normalizedStrictChain1 (cylinderCoverCollapse w hf) (cylinderCoverCollapse_monotone w hf) c = 0 ↔
      cylinderCoverCollapsedGeneratorCoordinates w f hf c = 0 := by
  have hi := cylinderCoverCollapsedRoseChain_inclusion w f hf c
  have he : normalizedStrictChain1 _
      (cylinderCoverCollapse_monotone w hf) c = 0 ↔ cylinderCoverCollapsedRoseChain w f hf c = 0 := by
    constructor
    · intro h
      apply Finsupp.mapDomain_injective (strictSubposetIncl_onE_injective _)
      aesop
    aesop
  exact he.trans (roseCover_cycle_eq_zero_iff_coordinates _
    _ _
      (cylinderCoverCollapsedRoseChain_cycle w f hf c hc))
