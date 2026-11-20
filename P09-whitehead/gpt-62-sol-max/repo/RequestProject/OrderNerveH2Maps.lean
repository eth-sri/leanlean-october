module

public import RequestProject.OrderNerveH2
public import RequestProject.OrderNerveCellMaps

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- The actual map on two-cycles induced by a monotone map. -/
noncomputable def orderNerveCycleMap (f : P → Q) (hf : Monotone f) :
    LinearMap.ker (bdry2 (orderCx P)) →ₗ[ℤ] LinearMap.ker (bdry2 (orderCx Q)) where
  toFun c := ⟨chain2 (orderCxMap f hf) c.val, by
    change bdry2 (orderCx Q) (chain2 (orderCxMap f hf) c.val) = 0
    rw [bdry2_chain2, c.property]; exact map_zero _⟩
  map_add' c d := Subtype.ext (map_add _ _ _)
  map_smul' n c := Subtype.ext (map_smul _ _ _)

/-- The actual induced map on second integral order-nerve homology. -/
noncomputable def orderNerveH2Map (f : P → Q) (hf : Monotone f) :
    OrderNerveH2 P →ₗ[ℤ] OrderNerveH2 Q :=
  (LinearMap.range (ordBoundary3Cycles P)).mapQ
    (LinearMap.range (ordBoundary3Cycles Q)) (orderNerveCycleMap f hf) (by
      intro c hc
      obtain ⟨y, rfl⟩ := hc
      exact ⟨Finsupp.mapDomain (ordTetMap f hf) y,
        Subtype.ext (chain2_ordBoundary3 f hf y).symm⟩)

/-- The induced homology map sends a cycle class to the class of its actual pushforward. -/
theorem orderNerveH2Map_class (f : P → Q) (hf : Monotone f)
    (c : OrdTri P →₀ ℤ) (hc : bdry2 (orderCx P) c = 0) :
    orderNerveH2Map f hf (orderNerveH2Class P c hc) =
      orderNerveH2Class Q (chain2 (orderCxMap f hf) c)
        (by rw [bdry2_chain2, hc]; exact map_zero _) := rfl

end FiniteChains.Comb
