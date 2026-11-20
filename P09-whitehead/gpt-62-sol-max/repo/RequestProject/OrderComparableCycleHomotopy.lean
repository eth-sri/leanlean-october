module

public import RequestProject.OrderNormalizationNaturality
public import RequestProject.OrderTwoMapPrism

@[expose] public section

/-! Finite strict three-chains witnessing a pointwise order homotopy. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

theorem strict_cycle_comparable_boundary (g h : P → P)
    (hg : Monotone g) (hh : Monotone h) (hgh : ∀ x, g x ≤ h x)
    (c : StrictOrdTri P →₀ ℤ) (hc : bdry2 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTet P →₀ ℤ,
      strictOrdBoundary3 y = normalizedStrictChain2 h hh c -
        normalizedStrictChain2 g hg c := by
  let w := chain2 (strictOrderIncl P) c
  have hw : bdry2 (orderCx P) w = 0 := by
    exact chain2_cycle _ hc
  refine ⟨normalizeOrdChain3 (ordMapPrism2 g h hg hh hgh w), ?_⟩
  rw [← normalizeOrdChain2_ordBoundary3, ordMapPrism_cycle g h hg hh hgh w hw, map_sub]
  rfl

theorem normalizedStrictChain2_id (c : StrictOrdTri P →₀ ℤ) :
    normalizedStrictChain2 id monotone_id c = c := by
  change normalizeOrdChain2 (Finsupp.mapDomain id (Finsupp.mapDomain (strictOrderIncl P).onF c)) = c
  rw [Finsupp.mapDomain_id, normalizeOrdChain2_inclusion]

end FiniteChains.Comb
