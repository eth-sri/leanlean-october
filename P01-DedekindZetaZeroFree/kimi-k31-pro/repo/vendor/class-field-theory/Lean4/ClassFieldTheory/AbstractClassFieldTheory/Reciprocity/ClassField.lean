module

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# The abstract class-field correspondence

This file gives the inverse direction of the finite abelian classification:
a norm-open subgroup produces its class field.  The construction is the
inverse of the order isomorphism proved by abstract class field theory, so
the defining norm-subgroup equality and the two lattice formulas are
consequences rather than extra assumptions.
-/

noncomputable section

namespace ClassFormation

open CyclicCohomology KummerTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The class field belonging to a norm-open subgroup. -/
noncomputable def classField
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (N : NormOpenAddSubgroup A K.field) :
    FiniteAbelianSubextension K.field :=
  (normSubgroupOrderIso v hcf K).symm (OrderDual.toDual N)

/-- The norm subgroup of the class field of `N` is `N`. -/
@[simp]
theorem classField_normSubgroup
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (N : NormOpenAddSubgroup A K.field) :
    (classField v hcf K N).normSubgroup A = N.1 := by
  calc
    (classField v hcf K N).normSubgroup A =
        (OrderDual.ofDual
          (normSubgroupOrderIso v hcf K (classField v hcf K N))).1 := by
            exact (normSubgroupOrderIso_apply
              v hcf K (classField v hcf K N)).symm
    _ = N.1 := by
      simp [classField]

/-- Taking the class field is inverse to taking the norm subgroup. -/
@[simp]
theorem classField_normSubgroupMap
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (L : FiniteAbelianSubextension K.field) :
    classField v hcf K (normSubgroupMap A L) = L := by
  change (normSubgroupOrderIso v hcf K).symm
      (normSubgroupOrderIso v hcf K L) = L
  exact (normSubgroupOrderIso v hcf K).symm_apply_apply L









/-- Intersection of two norm-open subgroups, with its openness produced
from finite Galois norm neighbourhoods. -/
def normOpenInf
    (K : FiniteAbstractField G)
    (N₁ N₂ : NormOpenAddSubgroup A K.field) :
    NormOpenAddSubgroup A K.field := by
  refine ⟨N₁.1 ⊓ N₂.1, ?_⟩
  rw [normTopology_addSubgroup_isOpen_iff]
  obtain ⟨E₁, hE₁⟩ :=
    (normTopology_addSubgroup_isOpen_iff A K.field N₁.1).1 N₁.2
  obtain ⟨E₂, hE₂⟩ :=
    (normTopology_addSubgroup_isOpen_iff A K.field N₂.1).1 N₂.2
  refine ⟨E₁.compositum E₂, le_inf ?_ ?_⟩
  · exact (FiniteGaloisSubextension.normSubgroup_compositum_le_left
      A E₁ E₂).trans hE₁
  · exact (FiniteGaloisSubextension.normSubgroup_compositum_le_right
      A E₁ E₂).trans hE₂

/-- Product of two norm-open subgroups, with openness produced by either
of its open factors. -/
def normOpenSup
    (K : FiniteAbstractField G)
    (N₁ N₂ : NormOpenAddSubgroup A K.field) :
    NormOpenAddSubgroup A K.field := by
  refine ⟨N₁.1 ⊔ N₂.1, ?_⟩
  rw [normTopology_addSubgroup_isOpen_iff]
  obtain ⟨E₁, hE₁⟩ :=
    (normTopology_addSubgroup_isOpen_iff A K.field N₁.1).1 N₁.2
  exact ⟨E₁, hE₁.trans le_sup_left⟩

@[simp]
theorem normOpenInf_val
    (K : FiniteAbstractField G)
    (N₁ N₂ : NormOpenAddSubgroup A K.field) :
    (normOpenInf K N₁ N₂).1 = N₁.1 ⊓ N₂.1 :=
  rfl

@[simp]
theorem normOpenSup_val
    (K : FiniteAbstractField G)
    (N₁ N₂ : NormOpenAddSubgroup A K.field) :
    (normOpenSup K N₁ N₂).1 = N₁.1 ⊔ N₂.1 :=
  rfl





end FiniteAbelianSubextension
end ClassFormation

end
