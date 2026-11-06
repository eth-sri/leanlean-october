import RequestProject.OrderNerveH2
import RequestProject.OrderNerveCellMaps
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- The actual map on two-cycles induced by a monotone map. -/
def orderNerveCycleMap (f : P → Q) (hf : Monotone f) :
    LinearMap.ker (bdry2 (orderCx P)) →ₗ[ℤ] LinearMap.ker (bdry2 (orderCx Q)) where
  toFun c := ⟨chain2 (orderCxMap f hf) c.val, by
    change bdry2 (orderCx Q) (chain2 (orderCxMap f hf) c.val) = 0
    rw [bdry2_chain2, c.property]; rfl⟩
  map_add' c d := Subtype.ext (map_add _ _ _)
  map_smul' n c := Subtype.ext (map_smul _ _ _)

/-- The actual induced map on second integral order-nerve homology. -/
def orderNerveH2Map (f : P → Q) (hf : Monotone f) :
    OrderNerveH2 P →ₗ[ℤ] OrderNerveH2 Q :=
  (LinearMap.range (ordBoundary3Cycles P)).mapQ
    (LinearMap.range (ordBoundary3Cycles Q)) (orderNerveCycleMap f hf) (by
      intro c hc
      obtain ⟨y, rfl⟩ := hc
      exact ⟨Finsupp.mapDomain (ordTetMap f hf) y,
        Subtype.ext (chain2_ordBoundary3 f hf y).symm⟩)

