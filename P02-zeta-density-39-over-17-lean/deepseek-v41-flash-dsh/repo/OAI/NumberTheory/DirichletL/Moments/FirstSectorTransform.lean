module
public import OAI.NumberTheory.DirichletL.Moments.FirstSectorEnergy
public import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalFamily

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSectorTransform
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve HeckeFamily CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily CenteredMomentSupportedCorrelation IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem residualPool_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : residualPool C hC (supportedColumns S)) : Supported (a:Ideal O) := by
  have ha := (Finset.mem_filter.mp ((mem_residualPool C hC (supportedColumns S) a).mp a.property)).2
  exact ((supported_mul_iff C a).mp ha).2

theorem commonLabels_supported (S : Finset (Ideal O))
    (p : commonLabels (supportedColumns S) (supportedColumns S)) :
    Supported p.val.1 ∧ Supported p.val.2 := by
  obtain ⟨q,hq,he⟩ := Finset.mem_image.mp p.property
  have hq₁ := (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).2
  have hq₂ := (Finset.mem_filter.mp (Finset.mem_product.mp hq).2).2
  rw [← he]
  exact ⟨commonPart_supported _ _ hq₁,commonPart_supported _ _ hq₂⟩

end SevenEighths.CenteredMomentFirstSectorTransform

end

end OAI
