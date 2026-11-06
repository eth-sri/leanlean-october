module

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.DoubleCosetOrbitGeometry

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Transfer--norm Frobenius geometry

For a finite Galois extension and an intermediate field, this module builds the
Frobenius-side subgroup and orbit equivalences used in transfer--norm
naturality.  The reusable orbit and double-coset constructions are isolated in
`DoubleCosetOrbitGeometry`.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology
open CategoryTheory

noncomputable section

open scoped BigOperators
open MulAction

section transferFrobeniusGeometry

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The absolute group of an intermediate field, identified with its
literal copy inside the absolute group of the base field. -/
noncomputable def transferNormNaturalityIntermediateAbsoluteEquiv
    (K K' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup) :
    K'.toSubgroup ≃* extensionSubgroup K K' hK'K :=
  MulEquiv.ofBijective
    ((Subgroup.inclusion hK'K).codRestrict
      (extensionSubgroup K K' hK'K) (fun k' => k'.2))
    ⟨fun _ _ h => Subtype.ext (congrArg (fun z => z.1.1) h), by
      rintro ⟨k, hk'⟩
      let k' : K'.toSubgroup := ⟨k.1, hk'⟩
      exact ⟨k', Subtype.ext rfl⟩⟩

/-- The absolute intermediate-field equivalence evaluates by the underlying transfer map. -/
@[simp]
theorem transferNormNaturalityIntermediateAbsoluteEquiv_apply
    (K K' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (k' : K'.toSubgroup) :
    ((transferNormNaturalityIntermediateAbsoluteEquiv K K' hK'K k').1 : G) = k'.1 :=
  rfl

/-- Normality of `L | K` restricts to every intermediate field `K'`. -/
theorem transferNormNaturality_intermediateExtension_normal
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal] :
    (extensionSubgroup K' L hLK').Normal := by
  have hcomap : extensionSubgroup K' L hLK' =
      (extensionSubgroup K L (hLK'.trans hK'K)).comap
        (Subgroup.inclusion hK'K) := by
    ext k'
    rw [Subgroup.mem_comap, mem_extensionSubgroup_iff,
      mem_extensionSubgroup_iff]
    rfl
  rw [hcomap]
  exact hLnormal.comap (Subgroup.inclusion hK'K)

namespace DegreeData

section
variable (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
include D E L hL hLnormal hL'normal
/-- The restriction map on the infinite Frobenius quotients is injective
when the top field is unchanged. -/
theorem transferNormNaturalityFrobeniusTowerMap_injective
      :
    Function.Injective
      (D.finiteReciprocityNaturalityFrobeniusTowerMap
        E.base.field E.field.field L L
        (hL.trans E.below) hL E.below le_rfl) := by
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro k'
  refine QuotientGroup.induction_on y ?_
  intro l' h
  apply QuotientGroup.eq.mpr
  have hmem :
      (Subgroup.inclusion E.below k')⁻¹ * Subgroup.inclusion E.below l' ∈
        D.extensionInertiaWithin E.base.field L (hL.trans E.below) :=
    QuotientGroup.eq.mp h
  constructor
  · apply (mem_extensionSubgroup_iff E.field.field L hL (k'⁻¹ * l')).2
    have hG := (mem_extensionSubgroup_iff E.base.field L
      (hL.trans E.below)
      ((Subgroup.inclusion E.below k')⁻¹ *
        Subgroup.inclusion E.below l')).1 hmem.1
    simpa using hG
  · have hI := hmem.2
    change D.degree (((Subgroup.inclusion E.below k')⁻¹ *
      Subgroup.inclusion E.below l' : E.base.field.toSubgroup) : G) = 1 at hI
    change D.degree ((k'⁻¹ * l' : E.field.field.toSubgroup) : G) = 1
    exact hI

/-- The copy of `G(\widetilde L/K')` inside
`G(\widetilde L/K)`.  This is the subgroup `H` used in the classical
double-coset proof of transfer--norm naturality. -/
def transferNormNaturalityFrobeniusIntermediateSubgroup
      :
    Subgroup (E.base.field.toSubgroup ⧸
      D.extensionInertiaWithin E.base.field L (hL.trans E.below)) :=
  (D.finiteReciprocityNaturalityFrobeniusTowerMap
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl).range

/-- The subgroup above is also the image of `G_K'` under the quotient
projection `G_K → G(\widetilde L/K)`. -/
theorem transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
      :
    D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL =
      (extensionSubgroup E.base.field E.field.field E.below).map
        (QuotientGroup.mk'
          (D.extensionInertiaWithin E.base.field L
            (hL.trans E.below))) := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    refine QuotientGroup.induction_on x ?_
    intro k'
    refine ⟨Subgroup.inclusion E.below k', ?_, rfl⟩
    exact k'.2
  · rintro ⟨k, hk', rfl⟩
    let k' : E.field.field.toSubgroup := ⟨k.1, hk'⟩
    refine ⟨QuotientGroup.mk k', ?_⟩
    change QuotientGroup.mk (Subgroup.inclusion E.below k') =
      QuotientGroup.mk k
    rfl

/-- Quotient projection maps the literal absolute subgroup belonging to
`K'` onto its copy `H` inside `G(\widetilde L/K)`. -/
noncomputable def transferNormNaturalityIntermediateToFrobeniusSubgroup
      :
    extensionSubgroup E.base.field E.field.field E.below →*
      D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL := by
  refine ((QuotientGroup.mk'
    (D.extensionInertiaWithin E.base.field L (hL.trans E.below))).comp
      (extensionSubgroup E.base.field E.field.field E.below).subtype).codRestrict
        (D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL) ?_
  intro m
  change QuotientGroup.mk m.1 ∈
    D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  rw [D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    E L hL]
  exact ⟨m.1, m.2, rfl⟩



























/-- The intermediate-to-Frobenius map has the stated value on each representative. -/
@[simp]
theorem transferNormNaturalityIntermediateToFrobeniusSubgroup_apply
     
    (m : extensionSubgroup E.base.field E.field.field E.below) :
    (D.transferNormNaturalityIntermediateToFrobeniusSubgroup
      E L hL m).1 =
        (QuotientGroup.mk m.1 : E.base.field.toSubgroup ⧸
          D.extensionInertiaWithin E.base.field L (hL.trans E.below)) := by
  rfl
end










































































/-- `H` has finite index in `G(\widetilde L/K)`, with no normality
assumption on the intermediate extension `K'/K`. -/
theorem transferNormNaturalityFrobeniusIntermediateFiniteIndex
    (D : DegreeData G) [IsTopologicalGroup G]
    (R : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ R.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup R.base.field L (hL.trans R.below)).Normal]
    [hL'normal : (extensionSubgroup R.field.field L hL).Normal] :
    (D.transferNormNaturalityFrobeniusIntermediateSubgroup R L hL).FiniteIndex := by
  rw [D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    R L hL]
  let I := D.extensionInertiaWithin R.base.field L (hL.trans R.below)
  let M := extensionSubgroup R.base.field R.field.field R.below
  have hIM : I ≤ M := by
    intro k hk
    apply (mem_extensionSubgroup_iff
      R.base.field R.field.field R.below k).2
    exact hL ((mem_extensionSubgroup_iff R.base.field L
      (hL.trans R.below) k).1 hk.1)
  let p := QuotientGroup.mk' I
  have hker : p.ker ≤ M := by
    simpa [p] using hIM
  let : M.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  rw [Subgroup.finiteIndex_iff,
    M.index_map_eq (QuotientGroup.mk'_surjective I) hker]
  exact Subgroup.FiniteIndex.index_ne_zero







































































































































































end DegreeData

end transferFrobeniusGeometry
end

end ClassFormation
