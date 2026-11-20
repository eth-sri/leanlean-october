module

public import RequestProject.SubstOneWay
public import RequestProject.ChamberQuotientCover
public import RequestProject.PresPosetAlphaW

@[expose] public section

/-!
# The one-way comparison over a model built on prescribed relator words

This is `RequestProject/SubstOneWayQuotient.lean` with the base of the chamber construction taken
to be the poset model `PresPos w` of the presentation complex of `ρ` built on a **prescribed**
family `w` of relator words, `FreeGroup.mk (w j) = ρ j`.  Nothing changes in the argument: the
marked comparison of `ρ` with the fundamental group of the model is injective
(`FiniteChains.PresModel.alphaHomW_injective`) and the inclusion of the base copy in the
quotient `Q = Z/Γ` is injective on fundamental groups
(`FiniteChains.Davis.pi1Map_qNew_injective`).
-/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

variable {α J : Type u}
    (ρ : J → FreeGroup α)
    (w : J → List (α × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = ρ j)
    (att : NeSpx A →o PresPos w)
include α J

/-- **The comparison of the source presentation with the quotient**, over the model built on the
prescribed relator words. -/
noncomputable def baseToQuotientW :
    PresGroup ρ →*
      Comb.Pi1 (orderCx (Qpos A (PresPos w) att)) (qNew (A := A) (att := att) (ptBase w)) :=
  (Comb.pi1Map (orderCxMap (qNew (A := A) (X := PresPos w) (att := att)) qNew_monotone)
      (ptBase w)).comp (alphaHomW ρ w hw)

/-- **The comparison is injective.** -/
theorem baseToQuotientW_injective :
    Function.Injective (baseToQuotientW (A := A) ρ w hw att) := by
  intro x y h
  solve_by_elim [alphaHomW_injective, pi1Map_qNew_injective]

end Davis
end FiniteChains
