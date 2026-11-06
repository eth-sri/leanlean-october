module

public import Mathlib

public import ClassFieldTheory.Definitions.LocalClassFieldTheory.TopologicalProfiniteCompletion
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Completion by open finite quotients

This module constructs the topological profinite completion of a topological
group from its open finite-index normal subgroups.  Unlike the abstract
completion by all finite quotients, the indexing category records the topology
on the source group.  This is the completion needed for infinite local
reciprocity.

The construction uses Mathlib's category of profinite groups, products, and
closed subgroups; it does not depend on a separate copied inverse-system implementation.
-/

noncomputable section

open CategoryTheory
open scoped Pointwise

namespace LocalClassFieldTheory

universe u v w

section Completion

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The canonical map has dense image in the open-quotient completion. -/
theorem topologicalProfiniteCompletionMap_denseRange :
    DenseRange (topologicalProfiniteCompletionMap G) := by
  let S  :=
    MonoidHom.range (openFiniteQuotientProductMapMonoidHom G)
  let incl : S → S.topologicalClosure :=
    Set.inclusion (Subgroup.le_topologicalClosure S)
  have hincl : DenseRange incl :=
    (denseRange_inclusion_iff
      (Subgroup.le_topologicalClosure S :
        (S : Set (openFiniteQuotientProduct G)) ⊆
          (S.topologicalClosure : Set (openFiniteQuotientProduct G)))).2 <| by
      simp [Subgroup.topologicalClosure_coe]
  have hrange :
      Set.range (topologicalProfiniteCompletionMap G) = Set.range incl := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨(openFiniteQuotientProductMapMonoidHom G).rangeRestrict g, rfl⟩
    · rintro ⟨y, rfl⟩
      rcases y.2 with ⟨g, hg⟩
      refine ⟨g, ?_⟩
      apply Subtype.ext
      change (openFiniteQuotientProductMapMonoidHom G) g = y
      exact hg
  intro x
  rw [hrange]
  exact hincl x

/-- Projection of the completion to one of its defining finite quotients. -/
def topologicalProfiniteCompletionProjection
    (H : OpenFiniteIndexNormalSubgroup G) :
    TopologicalProfiniteCompletion G →ₜ* openFiniteQuotient G H where
  toFun x := x.1 H
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_apply H).comp continuous_subtype_val

/-- Projecting the canonical completion image of `g` gives its quotient class. -/
@[simp]
theorem topologicalProfiniteCompletionProjection_map
    (H : OpenFiniteIndexNormalSubgroup G) (g : G) :
    topologicalProfiniteCompletionProjection G H
        (topologicalProfiniteCompletionMap G g) =
      QuotientGroup.mk g :=
  rfl



















































/-- The finite quotient projections commute with every transition map in the
open finite-quotient diagram. -/
theorem topologicalProfiniteCompletionProjection_transition
    {H K : OpenFiniteIndexNormalSubgroup G} (f : H ⟶ K)
    (x : TopologicalProfiniteCompletion G) :
    (openFiniteQuotientDiagram G).map f
        (topologicalProfiniteCompletionProjection G H x) =
      topologicalProfiniteCompletionProjection G K x := by
  let lhs : TopologicalProfiniteCompletion G → openFiniteQuotient G K :=
    fun y =>
      (openFiniteQuotientDiagram G).map f
        (topologicalProfiniteCompletionProjection G H y)
  let rhs  :=
    fun y => topologicalProfiniteCompletionProjection G K y
  have hlhs : Continuous lhs :=
    ((openFiniteQuotientDiagram G).map f).hom.continuous_toFun.comp
      (topologicalProfiniteCompletionProjection G H).continuous_toFun
  have hrhs : Continuous rhs :=
    (topologicalProfiniteCompletionProjection G K).continuous_toFun
  have heq  :=
    (topologicalProfiniteCompletionMap_denseRange G).equalizer hlhs hrhs <| by
      funext g
      rfl
  exact congrFun heq x

end Completion

/-! ### Universal property -/

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section
variable (P : ProfiniteGrp.{v}) (f : G →ₜ* P) (N : OpenNormalSubgroup P)
include P f N
/-- The open finite-index normal subgroup obtained by pulling an open normal
subgroup of a profinite target back along a continuous homomorphism. -/
def topologicalProfiniteCompletionPreimageIndex
      :
    OpenFiniteIndexNormalSubgroup G :=
  ⟨
    { toOpenSubgroup := N.toOpenSubgroup.comap f.toMonoidHom f.continuous_toFun
      isNormal' := by
        change ((N : Subgroup P).comap f.toMonoidHom).Normal
        infer_instance },
    by
    let q  :=
      (QuotientGroup.mk' (N : Subgroup P)).comp f.toMonoidHom
    let  := Subgroup.finiteIndex_ker q
    apply Subgroup.finiteIndex_of_le (H := q.ker)
    intro g hg
    change f g ∈ N
    exact (QuotientGroup.eq_one_iff (f g)).mp hg⟩

/-- The finite-stage map induced by a continuous homomorphism to a profinite
group, after quotienting by the pulled-back open normal subgroup. -/
def topologicalProfiniteCompletionFiniteQuotientMap
      :
    G ⧸ (topologicalProfiniteCompletionPreimageIndex P f N).toOpenNormalSubgroup.toSubgroup →*
      P ⧸ (N : Subgroup P) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (N : Subgroup P)).comp f.toMonoidHom) <| by
      intro g hg
      exact (QuotientGroup.eq_one_iff (f g)).mpr hg

/-- The finite-stage map as a continuous homomorphism between the corresponding
finite profinite quotients.

This is deliberately a `ContinuousMonoidHom`, rather than a categorical
`ProfiniteGrp` morphism: the latter forces source and target into the same
universe even though the universal property has no such mathematical
restriction. -/
def topologicalProfiniteCompletionFiniteQuotientMorphism
      :
    openFiniteQuotient G (topologicalProfiniteCompletionPreimageIndex P f N) →ₜ*
      (P.toFiniteQuotientFunctor ⋙ forget₂ FiniteGrp ProfiniteGrp).obj N where
  toMonoidHom := topologicalProfiniteCompletionFiniteQuotientMap P f N
  continuous_toFun := by
    let : DiscreteTopology
        (openFiniteQuotient G
          (topologicalProfiniteCompletionPreimageIndex P f N)) :=
      ⟨rfl⟩
    exact continuous_of_discreteTopology

/-- The continuous projection from the open-quotient completion to an open
finite quotient of a profinite target. -/
def topologicalProfiniteCompletionFiniteProjection
       :=
  (topologicalProfiniteCompletionFiniteQuotientMorphism P f N).comp
    (topologicalProfiniteCompletionProjection G
      (topologicalProfiniteCompletionPreimageIndex P f N))

/-- The induced finite projection sends the completion image of `g` to the class of `f g`. -/
@[simp]
theorem topologicalProfiniteCompletionFiniteProjection_map
      (g : G) :
    topologicalProfiniteCompletionFiniteProjection P f N
        (topologicalProfiniteCompletionMap G g) =
      QuotientGroup.mk' (N : Subgroup P) (f g) :=
  rfl
end


section
variable (P : ProfiniteGrp.{v}) (f : G →ₜ* P)
include P f
/-- The finite projections induced by a map to a profinite group commute with
the transition maps between the target's open finite quotients. -/
theorem topologicalProfiniteCompletionFiniteProjection_transition
     
    {N M : OpenNormalSubgroup P} (i : N ⟶ M)
    (x : TopologicalProfiniteCompletion G) :
    (P.toFiniteQuotientFunctor ⋙ forget₂ FiniteGrp ProfiniteGrp).map i
        (topologicalProfiniteCompletionFiniteProjection P f N x) =
      topologicalProfiniteCompletionFiniteProjection P f M x := by
  let lhs :=
    fun y =>
      (P.toFiniteQuotientFunctor ⋙ forget₂ FiniteGrp ProfiniteGrp).map i
        (topologicalProfiniteCompletionFiniteProjection P f N y)
  let rhs :=
    fun y => topologicalProfiniteCompletionFiniteProjection P f M y
  have hlhs : Continuous lhs :=
    ((P.toFiniteQuotientFunctor ⋙ forget₂ FiniteGrp ProfiniteGrp).map i).hom.continuous_toFun.comp
      (topologicalProfiniteCompletionFiniteProjection P f N).continuous_toFun
  have hrhs : Continuous rhs :=
    (topologicalProfiniteCompletionFiniteProjection P f M).continuous_toFun
  have heq  :=
    (topologicalProfiniteCompletionMap_denseRange G).equalizer hlhs hrhs <| by
      funext g
      rfl
  exact congrFun heq x

/-- The map from the open-quotient completion to the inverse limit of all
finite quotients of a profinite target. -/
noncomputable def topologicalProfiniteCompletionToFiniteQuotientLimit
      :
    TopologicalProfiniteCompletion G →ₜ*
      ProfiniteGrp.limit (ProfiniteGrp.diagram P) where
  toFun x :=
    ⟨fun N => topologicalProfiniteCompletionFiniteProjection P f N x,
      by
        intro N M i
        apply topologicalProfiniteCompletionFiniteProjection_transition⟩
  map_one' := by
    apply Subtype.ext
    funext N
    exact (topologicalProfiniteCompletionFiniteProjection P f N).map_one
  map_mul' x y := by
    apply Subtype.ext
    funext N
    exact (topologicalProfiniteCompletionFiniteProjection P f N).map_mul x y
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro N
    exact (topologicalProfiniteCompletionFiniteProjection P f N).continuous_toFun

/-- A continuous homomorphism from `G` to a profinite group extends canonically
to the completion of `G` by its open finite quotients. -/
noncomputable def topologicalProfiniteCompletionLift
      :
    TopologicalProfiniteCompletion G →ₜ* P :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P).symm).comp
    (topologicalProfiniteCompletionToFiniteQuotientLimit P f)

/-- The canonical lift agrees with the original homomorphism on the dense image of `G`. -/
@[simp]
theorem topologicalProfiniteCompletionLift_map
      (g : G) :
    topologicalProfiniteCompletionLift P f
        (topologicalProfiniteCompletionMap G g) =
      f g := by
  let e := ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P
  apply e.injective
  change e (e.symm (topologicalProfiniteCompletionToFiniteQuotientLimit P f
    (topologicalProfiniteCompletionMap G g))) = e (f g)
  rw [e.apply_symm_apply]
  apply Subtype.ext
  funext N
  rfl











/-- The canonical lift is the unique continuous homomorphism extending the
given map on the dense image of `G`. -/
theorem topologicalProfiniteCompletionLift_unique
     
    (h : TopologicalProfiniteCompletion G →ₜ* P)
    (hh : h.comp (topologicalProfiniteCompletionMap G) = f) :
    h = topologicalProfiniteCompletionLift P f := by
  let lhs  := fun x => h x
  let rhs  :=
    fun x => topologicalProfiniteCompletionLift P f x
  have heq : lhs = rhs :=
    (topologicalProfiniteCompletionMap_denseRange G).equalizer
      h.continuous_toFun
      (topologicalProfiniteCompletionLift P f).continuous_toFun <| by
        funext g
        change h (topologicalProfiniteCompletionMap G g) =
          topologicalProfiniteCompletionLift P f
            (topologicalProfiniteCompletionMap G g)
        rw [topologicalProfiniteCompletionLift_map]
        exact DFunLike.congr_fun hh g
  apply ContinuousMonoidHom.ext
  intro x
  exact congrFun heq x
end


/-! ### Functorial action -/

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]















































variable {J : Type w} [Group J] [TopologicalSpace J] [IsTopologicalGroup J]






























































end LocalClassFieldTheory

end
