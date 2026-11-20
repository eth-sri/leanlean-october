module

public import RequestProject.OrderConstructionConnected
public import RequestProject.PresPosetNonemptyWords

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u}

theorem rose_isConnected : IsConnected (orderCx (Rose α)) := by
  have h : ∀ x : Rose α, orderComponentLabel _ x = orderComponentLabel _ Rose.base := by
    intro x
    cases x with
    | base => rfl
    | mid i =>
        exact (orderComponentLabel_eq_of_le (Rose.mid_le_edg i false)).trans
          (orderComponentLabel_eq_of_le (Rose.base_le_edg i false)).symm
    | edg i b => grind [orderComponentLabel_eq_of_le, Rose.base_le_edg]
  intro x y
  exact (orderComponentLabel_eq_iff _ _).mp ((h x).trans (h y).symm)

/-- Nonempty attaching words give connected genuine presentation poset models. -/
theorem presPos_isConnected (w : J → List (α × Bool)) (hw : ∀ j, w j ≠ []) :
    IsConnected (orderCx (PresPos w)) := by
  apply coneAdj_isConnected _
    (cylP_isConnected _ rose_isConnected)
  intro j
  exact ⟨cylOuter _ _,
    0, CPos.cor, List.length_pos_iff.mpr (hw j), rfl⟩

end FiniteChains.PresModel
