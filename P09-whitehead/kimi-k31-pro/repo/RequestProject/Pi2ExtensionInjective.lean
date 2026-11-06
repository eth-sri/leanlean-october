module

public import RequestProject.Pi2Generation
public import RequestProject.HNNEmbedding

@[expose] public section

/-!
# The two extension steps of rule 1 really do contain the old group

`RequestProject/Pi2Generation.lean` proves the generation statement (3.3) for a
one-generator, one-relator extension from two hypotheses: right-regularity of the Fox
derivative of the new relator, and injectivity of the induced map of fundamental groups.
This file discharges the second hypothesis for the two extensions used in rule 1 of
Section 3.4.

* `FiniteChains.extHom_tietze_injective` — for the defining relator `z = s` the map of
  fundamental groups is injective (it is in fact an isomorphism, with the explicit retraction
  `FiniteChains.tietzeRetract`);
* `FiniteChains.extHom_hnn_injective` — for the stable-letter relator `z u z^{-1} = v` the map
  is injective whenever the images of `u` and `v` have infinite order, because the enlarged
  presentation maps onto the HNN extension identifying the two infinite cyclic subgroups,
  and the base group of an HNN extension embeds into it (Serre's normal form theorem, see
  `RequestProject/HNNEmbedding.lean`).

Consequently the two generation statements
`FiniteChains.extCycle_tietze_span_of` and `FiniteChains.extCycle_hnn_span_of` hold with no
hypothesis on the fundamental groups at all.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α)

/-! ### The Tietze step -/

section Tietze

variable (s : FreeGroup α)

/-- The retraction of free groups sending the new generator to the word `s`. -/
def tietzeLift : FreeGroup (Option α) →* FreeGroup α :=
  FreeGroup.lift (fun o => o.elim s FreeGroup.of)

omit [Fintype α] [DecidableEq α] in
@[simp] theorem tietzeLift_of_none : tietzeLift s (FreeGroup.of none) = s := by
  simp [tietzeLift]

omit [Fintype α] [DecidableEq α] in
@[simp] theorem tietzeLift_map_some (w : FreeGroup α) :
    tietzeLift s (FreeGroup.map Option.some w) = w := by
  have h : (tietzeLift s).comp (FreeGroup.map Option.some) = MonoidHom.id _ :=
    FreeGroup.ext_hom _ _ fun a => by simp [tietzeLift]
  exact congrArg (fun f : FreeGroup α →* FreeGroup α => f w) h

end Tietze

/-! ### The stable-letter step -/

section HNN

variable (u v : FreeGroup α)
  (hu : ¬ IsOfFinOrder (QuotientGroup.mk u : PresGroup ρ))
  (hv : ¬ IsOfFinOrder (QuotientGroup.mk v : PresGroup ρ))

end HNN

/-! ### The generation statements without hypotheses on the fundamental groups -/

end FiniteChains
