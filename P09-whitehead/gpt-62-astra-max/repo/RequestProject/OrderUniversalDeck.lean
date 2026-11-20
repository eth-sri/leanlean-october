module

public import RequestProject.OrderUniversalPoset

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

variable (g : Pi1 (orderCx P) a)

/-- Actual deck transformations commute with actual lifted order steps. -/
theorem uOrderStep_deckV (v : UOrder P a) (q : P)
    (h : uOrderEnd v ≤ q) :
    uOrderStep (deckV g v) q (by simp_all [uOrderEnd, endV_deckV]) =
      deckV g (uOrderStep v q h) := by
  have he : ordPos (by simp_all [uOrderEnd, endV_deckV] :
      uOrderEnd (deckV g v) ≤ q) = ordPos h := by
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (endV_deckV g v) rfl
    · rfl
  unfold uOrderStep
  rw [he, extend_deckV]

/-- The actual deck action preserves the genuine lifted partial order. -/
theorem uOrder_deckV_monotone :
    @Monotone _ _
      (uOrderPartialOrder (a := a)).toPreorder
      (uOrderPartialOrder (a := a)).toPreorder (deckV g) := by
  intro v z hvz
  obtain ⟨h, he⟩ := hvz
  refine ⟨by grind [uOrderEnd, endV_deckV], ?_⟩
  have hs := uOrderStep_deckV g v _ h
  simp_all [uOrderEnd, endV_deckV]

/-- Deck transformations are actual order isomorphisms of the path-class cover. -/
def uOrderDeckOrderIso : UOrder P a ≃o UOrder P a where
  toFun := deckV g
  invFun := deckV g⁻¹
  left_inv v := by rw [← deckV_mul, inv_mul_cancel, deckV_one]
  right_inv v := by rw [← deckV_mul, mul_inv_cancel, deckV_one]
  map_rel_iff' {v z} := by
    change UOrderLe _ (deckV g z) ↔ UOrderLe v z
    constructor
    · intro h
      have hi := uOrder_deckV_monotone g⁻¹ h
      change UOrderLe (deckV g⁻¹ (deckV g v)) (deckV g⁻¹ _) at hi
      simpa only [← deckV_mul, inv_mul_cancel, deckV_one] using hi
    · solve_by_elim [uOrder_deckV_monotone]

variable (v : UOrder P a)

/-- The deck action on the actual lifted-order type. -/
def uOrderDeck : UOrder P a := deckV g v

theorem uOrderDeck_end :
    uOrderEnd (uOrderDeck g v) = uOrderEnd v := endV_deckV g v

end FiniteChains.Comb
