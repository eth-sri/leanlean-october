import Mathlib.Tactic

import RequestProject.OrderUniversalPoset

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P : Type u} [PartialOrder P] {a : P}

variable (g : Pi1 (orderCx P) a)
variable (v : UOrder P a)
/-- Actual deck transformations commute with actual lifted order steps. -/
theorem uOrderStep_deckV   (q : P)
    (h : uOrderEnd v ≤ q) :
    uOrderStep (deckV g v) q (by simpa [uOrderEnd, endV_deckV] using h) =
      deckV g (uOrderStep v q h) := by
  grind [uOrderEnd, endV_deckV, uOrderStep, extend_deckV]

/-- The actual deck action preserves the genuine lifted partial order. -/
theorem uOrder_deckV_monotone  :
    @Monotone (UOrder P a) (UOrder P a)
      (uOrderPartialOrder (P := P) (a := a)).toPreorder
      (uOrderPartialOrder (P := P) (a := a)).toPreorder (deckV g) := by
  intro v z hvz
  obtain ⟨h, he⟩ := hvz
  refine ⟨by simpa [uOrderEnd, endV_deckV] using h, ?_⟩
  have hs := uOrderStep_deckV g v (uOrderEnd z) h
  simpa [uOrderEnd, endV_deckV] using hs.trans (congrArg (deckV g) he)

/-- Deck transformations are actual order isomorphisms of the path-class cover. -/
def uOrderDeckOrderIso  : UOrder P a ≃o UOrder P a where
  toFun := deckV g
  invFun := deckV g⁻¹
  left_inv v := by rw [← deckV_mul, inv_mul_cancel, deckV_one]
  right_inv v := by rw [← deckV_mul, mul_inv_cancel, deckV_one]
  map_rel_iff' {v z} := by
    
    constructor
    · intro h
      have hi := uOrder_deckV_monotone g⁻¹ h
      
      simpa [← deckV_mul, inv_mul_cancel, deckV_one] using hi
    · exact fun h => uOrder_deckV_monotone g h

/-- The deck action on the actual lifted-order type. -/
def uOrderDeck   : UOrder P a := deckV g v

theorem uOrderDeck_end   :
    uOrderEnd (uOrderDeck g v) = uOrderEnd v := endV_deckV g v

end FiniteChains.Comb
