import Mathlib.Tactic

import RequestProject.OrderCocycleCover
import RequestProject.OrderUniversalPosetConnected
import RequestProject.PosetCoverStrictEdgeLift

namespace FiniteChains.Comb.OrdCocycle
variable {P G : Type u} [PartialOrder P] [Group G] (c : OrdCocycle P G)

/-- Sheet coordinates on an actual fibre of the cocycle covering. -/
def coverFibreEquiv (p : P) : {x : c.Cover // x.point = p} ≃ G where
  toFun x := x.val.sheet
  invFun g := ⟨⟨p, g⟩, rfl⟩
  left_inv x := by
    aesop
  right_inv _ := rfl

variable (a : P)
/-- The genuine universal-cover path class maps to its endpoint and reading. -/
def universalReading  (v : UOrder P a) : c.Cover :=
  ⟨uOrderEnd v, c.readVertex a v⟩

theorem universalReading_monotone  : Monotone (c.universalReading a) := by
  intro v w h
  obtain ⟨h, hw⟩ := h
  refine ⟨h, ?_⟩
  
  have he := c.readVertex_extend a (ordPos h) v rfl
  change c.readVertex a (uOrderStep v (uOrderEnd w) h) =
    c.readVertex a v * c.val (uOrderEnd v) (uOrderEnd w) at he
  rw [hw] at he
  exact he.symm

variable (hP : IsConnected (orderCx P))
include hP in
theorem universalReading_surjective  
    (hm : Function.Surjective (c.monodromy a)) :
    Function.Surjective (c.universalReading a) := by
  rintro ⟨p, g⟩
  obtain ⟨v, hv⟩ := (uOrderEnd_isPosetCover (a := a) hP).surj p
  obtain ⟨z, hz, hg⟩ := c.readVertex_fibre_surjective a hm v g
  refine ⟨z, ?_⟩
  change Cover.mk (uOrderEnd z) (c.readVertex a z) = Cover.mk p g
  rw [hg, show uOrderEnd z = p from hz.trans hv]

include hP in
/-- Surjective monodromy, rather than faithful monodromy, gives a connected cover. -/
theorem cover_isConnected  
    (hm : Function.Surjective (c.monodromy a)) : IsConnected (orderCx c.Cover) := by
  intro v w
  obtain ⟨v', rfl⟩ := c.universalReading_surjective a hP hm v
  obtain ⟨w', rfl⟩ := c.universalReading_surjective a hP hm w
  obtain ⟨p, hp⟩ := uOrder_complex_isConnected (P := P) (a := a) v' w'
  exact ⟨mapPath (orderCxMap (c.universalReading a) (c.universalReading_monotone a)) p,
    isPath_mapPath _ hp⟩

theorem cover_deck_transitive (v w : c.Cover) (h : v.point = w.point) :
    ∃ e : c.Cover ≃o c.Cover,
      (∀ p, (e p).point = p.point) ∧ e v = w := by
  refine ⟨c.coverDeck (w.sheet * v.sheet⁻¹), fun _ => rfl, ?_⟩
  cases v with
  | mk vp vg =>
    simp_all [coverDeck]

end FiniteChains.Comb.OrdCocycle
