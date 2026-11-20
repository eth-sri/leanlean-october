module

public import RequestProject.OrderNerveH2
public import RequestProject.OrderNerveCellMaps

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

variable (f : P → Q) (hf : Monotone f)

/-- The actual map on two-cycles induced by a monotone map. -/
noncomputable def orderNerveCycleMap :
    LinearMap.ker (bdry2 (orderCx P)) →ₗ[ℤ] LinearMap.ker (bdry2 (orderCx Q)) where
  toFun c := ⟨chain2 (orderCxMap f hf) c.val, by
    change bdry2 _ _ = 0
    rw [bdry2_chain2, c.property]; exact map_zero _⟩
  map_add' c d := Subtype.ext (map_add _ _ _)
  map_smul' n c := Subtype.ext (map_smul _ _ _)

/-- The actual induced map on second integral order-nerve homology. -/
noncomputable def orderNerveH2Map :=
  (LinearMap.range (ordBoundary3Cycles P)).mapQ
    (LinearMap.range (ordBoundary3Cycles Q)) (orderNerveCycleMap f hf) (by
      intro c hc
      obtain ⟨y, rfl⟩ := hc
      exact ⟨Finsupp.mapDomain (ordTetMap f hf) y,
        Subtype.ext (chain2_ordBoundary3 f hf y).symm⟩)

end FiniteChains.Comb
