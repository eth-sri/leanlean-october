module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.FirstSectorEnergy
public import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalFamily

@[expose] public section

namespace OAI


open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSectorTransform
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve HeckeFamily CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentSupportedCorrelation IdealMobiusDivisorSum


theorem residualPool_supported (C : Ideal ActualEisensteinCubic.O) (hC : C≠0) (S : Finset (Ideal ActualEisensteinCubic.O))
    (a : residualPool C hC (supportedColumns S)) : Supported (a:Ideal ActualEisensteinCubic.O) := ((OAI.CanonicalQuadraticSieve.supported_mul_iff C ↑a).mp (Finset.mem_filter.mp ((OAI.SevenEighths.CenteredMomentFirstSectors.mem_residualPool C hC (OAI.SevenEighths.CenteredMomentSourceRow.supportedColumns S) ↑a).mp a.property)).right).right

theorem commonLabels_supported (S : Finset (Ideal ActualEisensteinCubic.O))
    (p : commonLabels (supportedColumns S) (supportedColumns S)) :
    Supported p.val.1 ∧ Supported p.val.2 := by
  obtain ⟨q,hq,he⟩ := Finset.mem_image.mp p.property
  have hq₁ := (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).2
  have hq₂ := (Finset.mem_filter.mp (Finset.mem_product.mp hq).2).2
  rw [← he]
  exact ⟨commonPart_supported _ _ hq₁,commonPart_supported _ _ hq₂⟩

end SevenEighths.CenteredMomentFirstSectorTransform



end OAI
