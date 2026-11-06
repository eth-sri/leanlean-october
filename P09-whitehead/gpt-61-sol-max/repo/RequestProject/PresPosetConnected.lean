import Mathlib.Tactic

import RequestProject.OrderConstructionConnected
import RequestProject.PresPosetNonemptyWords

namespace FiniteChains.PresModel
open Comb
variable {α J : Type u}

theorem rose_isConnected : IsConnected (orderCx (Rose α)) := by
  have h : ∀ x : Rose α, orderComponentLabel _ x = orderComponentLabel _ Rose.base := by
    intro x
    cases x with
    | base => rfl
    | mid i =>
        exact (orderComponentLabel_eq_of_le (Rose.mid_le_edg i false)).trans
          (orderComponentLabel_eq_of_le (Rose.base_le_edg i false)).symm
    | edg i b => exact (orderComponentLabel_eq_of_le (Rose.base_le_edg i b)).symm
  intro x y
  exact (orderComponentLabel_eq_iff _ _).mp ((h x).trans (h y).symm)

/-- Nonempty attaching words give connected genuine presentation poset models. -/
abbrev presPos_isConnected (w : J → List (α × Bool)) (hw : ∀ j, w j ≠ [])  :=
  FiniteChains.Comb.coneAdj_isConnected (FiniteChains.PresModel.circSet w)
    (FiniteChains.Comb.cylP_isConnected (FiniteChains.PresModel.aHom w) FiniteChains.PresModel.rose_isConnected)
    fun (j : J) =>
    Exists.intro
      (FiniteChains.Comb.cylOuter (FiniteChains.PresModel.aHom w)
        (FiniteChains.PresModel.TCirc.pt w j 0 FiniteChains.PresModel.CPos.cor))
      (Exists.intro 0 (Exists.intro FiniteChains.PresModel.CPos.cor ⟨List.length_pos_iff.mpr (hw j), rfl⟩))

end FiniteChains.PresModel
