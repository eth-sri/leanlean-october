import Mathlib.Tactic

import RequestProject.SubstOneWayQuotient
import RequestProject.PresPosetAlphaW

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

namespace FiniteChains.Davis


open RACG Mirror Comb PresModel


variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- **The comparison of the source presentation with the quotient**, over the model built on the
prescribed relator words. -/
noncomputable def baseToQuotientW {α J : Type u} (ρ : J → FreeGroup α)
    (w : J → List (α × Bool)) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)
    (att : NeSpx A →o PresPos w)  :=
  (Comb.pi1Map (orderCxMap (qNew (A := A) (X := PresPos w) (att := att)) qNew_monotone)
      (ptBase w)).comp (alphaHomW ρ w hw)

/-- **The comparison is injective.** -/
theorem baseToQuotientW_injective {α J : Type u} (ρ : J → FreeGroup α)
    (w : J → List (α × Bool)) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)
    (att : NeSpx A →o PresPos w) :
    Function.Injective (baseToQuotientW (A := A) ρ w hw att) := by
  classical solve_by_elim (transparency := .default) (maxDepth := 10) [FiniteChains.relSub_normal, FiniteChains.PresModel.alphaHomW_injective, FiniteChains.Davis.pi1Map_qNew_injective, ptBase]

end FiniteChains.Davis

