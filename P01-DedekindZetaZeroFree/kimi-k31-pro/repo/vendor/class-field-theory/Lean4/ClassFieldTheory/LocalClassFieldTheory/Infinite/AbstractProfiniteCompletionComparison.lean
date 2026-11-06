module

public import ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletion

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Comparison with the abstract profinite completion

The abstract profinite completion of a group is the completion formed from all
finite-index normal subgroups, without reference to a topology.  We realize it
by applying the open-quotient construction to a discrete copy of the group.

When every finite-index normal subgroup is open in the given topology, the
open-quotient completion and the abstract completion are canonically
isomorphic as topological groups.
-/

noncomputable section

open scoped Pointwise

namespace LocalClassFieldTheory

universe u v

/-- A copy of a group equipped with the discrete topology. -/
@[ext]
structure AbstractProfiniteSource (G : Type u) where
  /-- The underlying group element. -/
  val : G

namespace AbstractProfiniteSource

variable (G : Type u)

/-- The tautological equivalence between the discrete copy and the underlying type. -/
def equiv : AbstractProfiniteSource G ≃ G where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- The discrete source copy inherits the group structure of `G`. -/
instance [Group G] : Group (AbstractProfiniteSource G) := (equiv G).group

/-- The abstract profinite source carries the discrete topology. -/
instance : TopologicalSpace (AbstractProfiniteSource G) := ⊥

/-- The topology on the abstract profinite source is discrete. -/
instance : DiscreteTopology (AbstractProfiniteSource G) := ⟨rfl⟩

/-- The discrete source copy of a group is a topological group. -/
instance [Group G] : IsTopologicalGroup (AbstractProfiniteSource G) := inferInstance

/-- The tautological multiplicative equivalence from the discrete copy. -/
def mulEquiv [Group G] : AbstractProfiniteSource G ≃* G where
  toEquiv := equiv G
  map_mul' _ _ := rfl

end AbstractProfiniteSource

/-- The abstract profinite completion formed from all finite-index normal
subgroups.  This is a stable, non-`abbrev` public object; its inverse-limit
realization is available through `abstractProfiniteCompletionEquivModel`. -/
noncomputable def AbstractProfiniteCompletion
    (G : Type u) [Group G] : ProfiniteGrp :=
  TopologicalProfiniteCompletion (AbstractProfiniteSource G)

/-- Canonical comparison with the concrete open-finite-quotient model used
to construct the abstract profinite completion. -/
noncomputable def abstractProfiniteCompletionEquivModel
    (G : Type u) [Group G] :
    AbstractProfiniteCompletion G ≃ₜ*
      TopologicalProfiniteCompletion (AbstractProfiniteSource G) := by
  change TopologicalProfiniteCompletion (AbstractProfiniteSource G) ≃ₜ*
    TopologicalProfiniteCompletion (AbstractProfiniteSource G)
  exact ContinuousMulEquiv.refl _

/-- The canonical dense class map from the discrete source into the stable
abstract completion. -/
noncomputable def abstractProfiniteCompletionClass
    (G : Type u) [Group G] :
    AbstractProfiniteSource G →ₜ* AbstractProfiniteCompletion G :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (abstractProfiniteCompletionEquivModel G).symm).comp
    (topologicalProfiniteCompletionMap (AbstractProfiniteSource G))

/-- The model equivalence sends an abstract completion class to the canonical topological class. -/
@[simp] theorem abstractProfiniteCompletionEquivModel_class
    (G : Type u) [Group G] (g : AbstractProfiniteSource G) :
    abstractProfiniteCompletionEquivModel G
        (abstractProfiniteCompletionClass G g) =
      topologicalProfiniteCompletionMap (AbstractProfiniteSource G) g :=
  (abstractProfiniteCompletionEquivModel G).apply_symm_apply _



/-- Extend a continuous homomorphism from the discrete source across the
stable abstract profinite completion.  This is the representation-independent
universal-property entry point for `AbstractProfiniteCompletion`. -/
noncomputable def abstractProfiniteCompletionLift
    (G : Type u) [Group G]
    (P : ProfiniteGrp.{v})
    (f : AbstractProfiniteSource G →ₜ* P) :
    AbstractProfiniteCompletion G →ₜ* P :=
  (topologicalProfiniteCompletionLift P f).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (abstractProfiniteCompletionEquivModel G))

/-- The universal lift agrees with the original map on abstract completion classes. -/
@[simp] theorem abstractProfiniteCompletionLift_class
    (G : Type u) [Group G]
    (P : ProfiniteGrp.{v})
    (f : AbstractProfiniteSource G →ₜ* P)
    (g : AbstractProfiniteSource G) :
    abstractProfiniteCompletionLift G P f
        (abstractProfiniteCompletionClass G g) = f g := by
  unfold abstractProfiniteCompletionLift
  change topologicalProfiniteCompletionLift P f
      (abstractProfiniteCompletionEquivModel G
        (abstractProfiniteCompletionClass G g)) = f g
  rw [abstractProfiniteCompletionEquivModel_class,
    topologicalProfiniteCompletionLift_map]

/-- Composing the universal lift with the class map recovers the source homomorphism. -/
@[simp] theorem abstractProfiniteCompletionLift_comp_class
    (G : Type u) [Group G]
    (P : ProfiniteGrp.{v})
    (f : AbstractProfiniteSource G →ₜ* P) :
    (abstractProfiniteCompletionLift G P f).comp
        (abstractProfiniteCompletionClass G) = f := by
  ext g
  exact abstractProfiniteCompletionLift_class G P f g



section Comparison

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The model-valued completion map used internally to establish continuity. -/
 def abstractProfiniteCompletionModelMapMonoidHom :
    G →* TopologicalProfiniteCompletion (AbstractProfiniteSource G) :=
  (topologicalProfiniteCompletionMap (AbstractProfiniteSource G)).toMonoidHom.comp
    (AbstractProfiniteSource.mulEquiv G).symm.toMonoidHom

/-- The abstract completion map, viewed as a homomorphism from the original group. -/
def abstractProfiniteCompletionMapMonoidHom : G →* AbstractProfiniteCompletion G :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (abstractProfiniteCompletionEquivModel G).symm).toMonoidHom.comp
    (abstractProfiniteCompletionModelMapMonoidHom G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The completion map sends `g` to the class of its discrete source copy. -/
@[simp] theorem abstractProfiniteCompletionMapMonoidHom_apply (g : G) :
    abstractProfiniteCompletionMapMonoidHom G g =
      abstractProfiniteCompletionClass G
        ((AbstractProfiniteSource.mulEquiv G).symm g) :=
  by
    change (abstractProfiniteCompletionEquivModel G).symm
        (topologicalProfiniteCompletionMap (AbstractProfiniteSource G)
          ((AbstractProfiniteSource.mulEquiv G).symm g)) =
      (abstractProfiniteCompletionEquivModel G).symm
        (topologicalProfiniteCompletionMap (AbstractProfiniteSource G)
          ((AbstractProfiniteSource.mulEquiv G).symm g))
    rfl















end Comparison

end LocalClassFieldTheory

end
