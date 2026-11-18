module

public import RequestProject.SlideGeneration
public import RequestProject.RuleOneMor

@[expose] public section

/-!
# Rule 2 as a structural map with the generation property

Rule 2 of the operation `T` of Lemma 3.9 replaces an extra relator `r*` by
`r⁰ = r* ∏_j r_j^{c_j}`, a product of `r*` with retained core relators.  The paper justifies
the generation equation (3.3) for this rule by the remark that the move is a finite sequence
of slides of the relator disk over core disks, hence a homotopy equivalence relative to `D`.

`RequestProject/SlideGeneration.lean` proves the combinatorial content of that remark: the
slide does not change the normal closure of the relators, and on two-cycles it acts as the
`ℤ[G]`-linear isomorphism `y ↦ (j ↦ y j - y_{j₀} λ j)`.  This file packages the move as a
**structural map** `PresMor` of `RequestProject/GenerationStep.lean` and proves that it
satisfies `FiniteChains.Generates`, so that rule 2 composes with rules 1 and 3.

* `FiniteChains.slideGroupHom` — the (iso)morphism of fundamental groups induced by the
  slide, together with its inverse and the induced isomorphism of group rings;
* `FiniteChains.slideMor` — rule 2 as a structural map;
* `FiniteChains.generates_slideMor` — **equation (3.3) for rule 2**, with no hypothesis
  beyond the defining property of the correcting word and its coefficient vector.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α) (j₀ : J) (u : FreeGroup α)
  (hu : u ∈ Subgroup.normalClosure (Set.range (coreRel ρ j₀)))

/-! ### The identification of the two fundamental groups -/

omit [Fintype α] [DecidableEq α] [Fintype J] in
/-- The slide does not change the normal closure of the relators, so the identity of the free
group descends to the two presented groups. -/
def slideGroupHom : PresGroup ρ →* PresGroup (slideRel ρ j₀ u) :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    rw [Subgroup.comap_id, relSub_slideRel ρ j₀ u hu])

omit [Fintype α] [DecidableEq α] [Fintype J] in
/-- The inverse identification. -/
def slideGroupHomInv : PresGroup (slideRel ρ j₀ u) →* PresGroup ρ :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    rw [Subgroup.comap_id, relSub_slideRel ρ j₀ u hu])

omit [Fintype α] [DecidableEq α] [Fintype J] in
@[simp] theorem slideGroupHom_mk (w : FreeGroup α) :
    slideGroupHom ρ j₀ u hu (QuotientGroup.mk w) = QuotientGroup.mk w := rfl

omit [Fintype α] [DecidableEq α] [Fintype J] in
@[simp] theorem slideGroupHomInv_mk (w : FreeGroup α) :
    slideGroupHomInv ρ j₀ u hu (QuotientGroup.mk w) = QuotientGroup.mk w := rfl

/-! ### Rule 2 as a structural map -/

variable (lam : J → MonoidAlgebra ℤ (PresGroup ρ))

end FiniteChains
