import Mathlib.Tactic

import RequestProject.OrderRoseWedgeTopology

/-! The concrete cyclic order of the four vertices in one rose circle.
This fixes the positive generator orientation before passing to realization. -/

noncomputable section
namespace FiniteChains.PresModel


def roseFourVertex : Fin 4 → Rose PUnit :=
  ![.base, .edg PUnit.unit false, .mid PUnit.unit, .edg PUnit.unit true]

theorem roseFourVertex_injective : Function.Injective roseFourVertex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [roseFourVertex]

theorem roseFourVertex_surjective : Function.Surjective roseFourVertex := by
  intro p
  cases p with
  | base => exact ⟨0, rfl⟩
  | mid a => cases a; exact ⟨2, rfl⟩
  | edg a b =>
      cases a
      cases b
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩

def roseFourVertexEquiv : Fin 4 ≃ Rose PUnit :=
  Equiv.ofBijective roseFourVertex ⟨roseFourVertex_injective, roseFourVertex_surjective⟩



end FiniteChains.PresModel
