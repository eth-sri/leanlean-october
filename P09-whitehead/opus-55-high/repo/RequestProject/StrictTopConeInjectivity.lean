import RequestProject.StrictTopConeThreeChains
import RequestProject.Tac


/-! The genuine strict cone maps preserve all finite-chain coefficients. -/
namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
  (f : P → Q) (hf : StrictMono f) (c : Q) (hc : ∀ x, f x < c) (hfi : Function.Injective f)

include hfi in
theorem strictTopConeEdgeTriangle_injective :
    Function.Injective (strictTopConeEdgeTriangle f hf c hc) := by
  intro e d h
  apply Subtype.ext
  apply Prod.ext
  · exact hfi (congrArg (·.1.1) h)
  · exact hfi (congrArg (·.1.2.1) h)

theorem strictTopConeEdgeChain_eq_mapDomain z :
    strictTopConeEdgeChain f hf c hc z =
      Finsupp.mapDomain (strictTopConeEdgeTriangle f hf c hc) z := by
  lin_ind z with z w hz hw => rw [map_add, Finsupp.mapDomain_add, hz, hw]
  | e n => simp [strictTopConeEdgeChain]

include hfi in
theorem strictTopConeEdgeChain_injective :
    Function.Injective (strictTopConeEdgeChain f hf c hc) := by
  intro z w h
  rw [strictTopConeEdgeChain_eq_mapDomain, strictTopConeEdgeChain_eq_mapDomain] at h
  exact Finsupp.mapDomain_injective (strictTopConeEdgeTriangle_injective f hf c hc hfi) h

include hfi in
theorem strictTopConeTriangleTetrahedron_injective :
    Function.Injective (strictTopConeTriangleTetrahedron f hf c hc) := by
  intro s t h
  apply Subtype.ext
  apply Prod.ext
  · exact hfi (congrArg (·.1.1) h)
  · apply Prod.ext
    · exact hfi (congrArg (·.1.2.1) h)
    · exact hfi (congrArg (·.1.2.2.1) h)
