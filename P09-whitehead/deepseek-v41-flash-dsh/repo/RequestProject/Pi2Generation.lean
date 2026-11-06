module

public import RequestProject.Pi2Extension
public import RequestProject.BaseChangeCycles

@[expose] public section

/-!
# Generation of `π₂` over the enlarged group ring (equation (3.3) for one extension step)

Lemma 3.9 of the paper rests on the generation statement

  `π₂(T(P)) = ℤ[G(T(P))] · η_{P*} π₂(P)`,                                        (3.3)

and Proposition 3.11 repeats the same argument downstairs.  In the combinatorial model `π₂`
is the module of Fox cycles, and this file proves (3.3) for one step of the construction —
adjoining a single generator together with a single relator — from the two ingredients
established separately:

* `RequestProject/Pi2Extension.lean`: a Fox cycle of the enlarged presentation is zero on the
  new two-cell and is a Fox cycle of the *old* Fox matrix, read in the enlarged group ring;
* `RequestProject/BaseChangeCycles.lean`: cycles of a matrix with entries in the group ring of
  a subgroup are generated, over the big group ring, by cycles over the subgroup ring.

The subgroup in question is the image of the old fundamental group, so the second ingredient
applies as soon as that image is a faithful copy of the old group — exactly the HNN normal
form statement quoted in the paper (`RequestProject/HNNEmbedding.lean`) in the case of the
stable-letter extension, and a triviality for the Tietze step.

The main results are `FiniteChains.extCycle_mem_span` (the general step) and its two
instances `FiniteChains.extCycle_tietze_span`, `FiniteChains.extCycle_hnn_span`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α) (w₀ : FreeGroup (Option α))

/-- The image of a Fox cycle of the old presentation among the two-cells of the enlarged
presentation: the structural map `η_P` in coordinates. -/
noncomputable def extCycleImage (y : J → MonoidAlgebra ℤ (PresGroup ρ)) :
    Option J → MonoidAlgebra ℤ (PresGroup (extRel ρ w₀))
  | none => 0
  | some j => extRingHom ρ w₀ (y j)

/-- Padding a vector of coefficients on the old two-cells with `0` on the new two-cell. -/
def padCells (R : Type*) [Ring R] (J : Type*) : (J → R) →ₗ[R] (Option J → R) :=
  LinearMap.pi (fun jo => match jo with | none => 0 | some j => LinearMap.proj j)

@[simp] theorem padCells_none {R : Type*} [Ring R] {J : Type*} (u : J → R) :
    padCells R J u none = 0 := rfl

@[simp] theorem padCells_some {R : Type*} [Ring R] {J : Type*} (u : J → R) (j : J) :
    padCells R J u (some j) = u j := rfl

end FiniteChains
