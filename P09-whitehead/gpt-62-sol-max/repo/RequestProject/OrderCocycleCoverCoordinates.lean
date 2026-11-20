module

public import RequestProject.OrderCocycleCover
public import RequestProject.OrderUniversalPosetConnected
public import RequestProject.PosetCoverStrictEdgeLift

@[expose] public section

namespace FiniteChains.Comb.OrdCocycle
universe u
variable {P G : Type u} [PartialOrder P] [Group G] (c : OrdCocycle P G)

/-- Sheet coordinates on an actual fibre of the cocycle covering. -/
def coverFibreEquiv (p : P) : {x : c.Cover // x.1 = p} ≃ G where
  toFun x := x.val.2
  invFun g := ⟨⟨p, g⟩, rfl⟩
  left_inv x := Subtype.ext (Sigma.ext x.2.symm HEq.rfl)
  right_inv _ := rfl

/-- The genuine universal-cover path class maps to its endpoint and reading. -/
def universalReading (a : P) (v : UOrder P a) : c.Cover :=
  ⟨uOrderEnd v, c.readVertex a v⟩

theorem universalReading_monotone (a : P) : Monotone (c.universalReading a) := by
  intro v w h
  obtain ⟨h, hw⟩ := h
  refine ⟨h, ?_⟩
  change c.readVertex a v * c.val (uOrderEnd v) (uOrderEnd w) = c.readVertex a w
  have he := c.readVertex_extend a (ordPos h) v rfl
  change c.readVertex a (uOrderStep v (uOrderEnd w) h) =
    c.readVertex a v * c.val (uOrderEnd v) (uOrderEnd w) at he
  simp_all

theorem universalReading_surjective (a : P) (hP : IsConnected (orderCx P))
    (hm : Function.Surjective (c.monodromy a)) :
    Function.Surjective (c.universalReading a) := by
  rintro ⟨p, g⟩
  obtain ⟨z, hz, hg⟩ := c.exists_point_reading a hP hm p g
  exact ⟨z, Sigma.ext hz (heq_of_eq hg)⟩

/-- Surjective monodromy, rather than faithful monodromy, gives a connected cover. -/
theorem cover_isConnected (a : P) (hP : IsConnected (orderCx P))
    (hm : Function.Surjective (c.monodromy a)) : IsConnected (orderCx c.Cover) := by
  intro v w
  obtain ⟨v', rfl⟩ := c.universalReading_surjective a hP hm v
  obtain ⟨w', rfl⟩ := c.universalReading_surjective a hP hm w
  obtain ⟨p, hp⟩ := uOrder_complex_isConnected (P := P) (a := a) v' w'
  exact ⟨mapPath (orderCxMap (c.universalReading a) (c.universalReading_monotone a)) p,
    isPath_mapPath _ hp⟩

theorem cover_deck_transitive (v w : c.Cover) (h : v.1 = w.1) :
    ∃ e : c.Cover ≃o c.Cover,
      (∀ p, (e p).1 = p.1) ∧ e v = w := by
  refine ⟨c.coverDeck (w.2 * v.2⁻¹), fun _ => rfl, ?_⟩
  exact Sigma.ext h (heq_of_eq (by change (w.2 * v.2⁻¹) * v.2 = w.2; simp [mul_assoc]))

end FiniteChains.Comb.OrdCocycle
