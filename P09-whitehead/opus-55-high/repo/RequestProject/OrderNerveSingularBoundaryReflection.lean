import RequestProject.OrderNerveReturnHomotopy
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
variable {P : Type} [PartialOrder P]

/-- A genuine singular filling of a realized simplicial cycle produces an
actual simplicial filling, in every positive dimension. -/
theorem orderNerveExplicitSingular_reflects_boundaries n
    (c : ComposableArrows P (n + 1) →₀ ℤ) (hc : orderSimplicialBoundary P n c = 0)
    (b : Chain (orderNerveRealization P) (n + 2))
    (hb : boundary (n + 1) b = (orderNerveExplicitSingularMap P).f (n + 1) c) :
    ∃ a : ComposableArrows P (n + 2) →₀ ℤ, orderSimplicialBoundary P (n + 1) a = c := by
  let w := orderSingularToNerve P _ b + orderReturnHomotopy P _ c
  have hw : w ∈ Nerve.Inc P := AddSubgroup.add_mem _
    (orderSingularToNerve_mem_inc _ _) (orderReturnHomotopy_mem_inc _ _)
  have hd : Nerve.bdry w = orderNerveGradedEncode _ c := by
    rwd [map_add, orderSingularToNerve_boundary, hb, orderReturnHomotopy_identity,
      hc, map_zero, sub_zero]
    change orderNerveRoundTrip P _ c +
      (orderNerveGradedEncode _ c - orderNerveRoundTrip P _ c) = _
    abel
  refine ⟨orderNerveGradedDecode _ w, ?_⟩
  apply orderNerveGradedEncode_injective _
  simp [orderNerveGradedEncode_boundary, orderNerveGradedEncode_decode _ hw, ← Nerve.lengthProjection_bdry, hd, orderNerveGradedEncode_length]
