module

public import RequestProject.OrderNerveReturnHomotopy

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
variable {P : Type} [PartialOrder P]

/-- A genuine singular filling of a realized simplicial cycle produces an
actual simplicial filling, in every positive dimension. -/
theorem orderNerveExplicitSingular_reflects_boundaries (n : ℕ)
    (c : ComposableArrows P _ →₀ ℤ) (hc : orderSimplicialBoundary P n c = 0)
    (b : Chain (orderNerveRealization P) _)
    (hb : boundary _ b = (orderNerveExplicitSingularMap P).f _ c) :
    ∃ a : ComposableArrows P _ →₀ ℤ, orderSimplicialBoundary P _ a = c := by
  let w := orderSingularToNerve P _ b + orderReturnHomotopy P _ c
  have hw : w ∈ Nerve.Inc P := AddSubgroup.add_mem _
    (orderSingularToNerve_mem_inc _ _) (orderReturnHomotopy_mem_inc _ _)
  have hd : Nerve.bdry w = orderNerveGradedEncode _ c := by
    erw [map_add, orderSingularToNerve_boundary, hb, orderReturnHomotopy_identity,
      hc, map_zero, sub_zero]
    change orderNerveRoundTrip P _ c +
      (orderNerveGradedEncode _ c - orderNerveRoundTrip P _ c) = _
    abel
  refine ⟨orderNerveGradedDecode _ w, ?_⟩
  apply orderNerveGradedEncode_injective (n + 1)
  erw [orderNerveGradedEncode_boundary, orderNerveGradedEncode_decode _ hw,
    ← Nerve.lengthProjection_bdry, hd, orderNerveGradedEncode_length]

end FiniteChains.Comb
