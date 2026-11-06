module

public import Mathlib

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Topology.Algebra.Group.Pointwise

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Finite abelian extensions in abstract reciprocity

the finite abelian class-field classification classifies finite abelian extensions `L | K` by
their norm subgroups.  This file builds the extension side of that
correspondence independently of the reciprocity isomorphism:

* a finite Galois extension whose actual quotient is commutative;
* the field-inclusion order (opposite to inclusion of closed subgroups);
* compositum and intersection operations;
* the actual assignment `L ↦ N_{L/K} A_L` and its unconditional order
  relations.

The reverse inclusions in the two norm formulas, and hence the classification
bijection itself, require the abstract reciprocity theorem and are deliberately not postulated.
-/

noncomputable section

namespace ClassFormation

open CyclicCohomology KummerTheory

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A finite abelian extension `L | K`: a finite Galois extension together
with commutativity of its actual quotient `G_K/G_L`. -/
structure FiniteAbelianSubextension (K : ClosedSubgroup G) where
  /-- The underlying finite Galois subextension. -/
  toFiniteGaloisExtension : FiniteGaloisSubextension K
  /-- Commutativity of the relative Galois quotient. -/
  commutative : IsMulCommutative toFiniteGaloisExtension.extensionQuotient

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

section
variable (L : FiniteAbelianSubextension K)
include L
/-- Introduces the abbreviation `field`. -/
abbrev field    :=
  L.toFiniteGaloisExtension.field

/-- Introduces the abbreviation `below`. -/
abbrev below   :
    L.field.toSubgroup ≤ K.toSubgroup :=
  L.toFiniteGaloisExtension.below

/-- Introduces the abbreviation `normal`. -/
abbrev normal   :
    (extensionSubgroup K L.field L.below).Normal :=
  L.toFiniteGaloisExtension.normal

/-- Introduces the abbreviation `finite`. -/
abbrev finite   :
    Finite (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  L.toFiniteGaloisExtension.finite

/-- The finite abelian quotient carried by the extension.  Its representation
is inherited through the finite Galois extension boundary rather than exposed
as a transparent quotient abbreviation. -/
@[implicit_reducible]
def extensionQuotient    :=
  L.toFiniteGaloisExtension.extensionQuotient
end


/-- The quotient attached to a finite abelian subextension is a commutative group. -/
@[implicit_reducible]
instance extensionQuotient_commGroup (L : FiniteAbelianSubextension K) :
    CommGroup L.extensionQuotient := by
  unfold extensionQuotient
  letI  := L.commutative
  exact
    { (inferInstance :
        Group L.toFiniteGaloisExtension.extensionQuotient) with
      mul_comm := L.commutative.is_comm.comm }

/-- The quotient attached to a finite abelian subextension is finite. -/
instance extensionQuotient_finite (L : FiniteAbelianSubextension K) :
    Finite L.extensionQuotient := by
  unfold extensionQuotient
  infer_instance

/-- Comparison with the quotient presentation used by the underlying group
library. -/
def extensionQuotientMulEquiv (L : FiniteAbelianSubextension K) :
    L.extensionQuotient ≃*
      (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  L.toFiniteGaloisExtension.extensionQuotientMulEquiv

/-- The canonical quotient projection for a finite abelian extension. -/
def extensionQuotientMk (L : FiniteAbelianSubextension K) :
    K.toSubgroup →* L.extensionQuotient :=
  L.toFiniteGaloisExtension.extensionQuotientMk

/-- The named abelian quotient projection agrees with the underlying quotient map. -/
@[simp]
theorem extensionQuotientMk_apply (L : FiniteAbelianSubextension K)
    (k : K.toSubgroup) :
    L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
      (QuotientGroup.mk k :
        K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  L.toFiniteGaloisExtension.extensionQuotientMk_apply k









/-- Two packages with the same closed subgroup represent the same finite
abelian extension. -/
@[ext]
theorem ext {L₁ L₂ : FiniteAbelianSubextension K}
    (h : L₁.field = L₂.field) : L₁ = L₂ := by
  cases L₁ with
  | mk L₁ h₁ =>
      cases L₂ with
      | mk L₂ h₂ =>
          cases L₁ with
          | mk F₁ b₁ n₁ f₁ =>
              cases L₂ with
              | mk F₂ b₂ n₂ f₂ =>
                  dsimp only [field] at h
                  cases h
                  rfl

/-- The order is field inclusion.  Since fields are represented by their
absolute Galois subgroups, it is the opposite subgroup order. -/
instance : PartialOrder (FiniteAbelianSubextension K) where
  le L₁ L₂ := L₂.field.toSubgroup ≤ L₁.field.toSubgroup
  le_refl _ := le_rfl
  le_trans _ _ _ h₁₂ h₂₃ := h₂₃.trans h₁₂
  le_antisymm L₁ L₂ h₁₂ h₂₁ := by
    apply ext
    apply ClosedSubgroup.ext
    have hs  :=
      le_antisymm h₂₁ h₁₂
    apply congrArg <;> aesop






/-- Base change of a finite abelian extension to an arbitrary
intermediate abstract field.  Contravariantly the new top subgroup is
the intersection with the new base subgroup. -/
def baseChange (M : FiniteAbelianSubextension K)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    FiniteAbelianSubextension L where
  toFiniteGaloisExtension :=
    M.toFiniteGaloisExtension.baseChange L hLK
  commutative := by
    let P :=
      M.toFiniteGaloisExtension.baseChange L hLK
    let  :=
      M.normal
    let  :=
      P.normal
    refine ⟨⟨?_⟩⟩
    intro x y
    refine P.extensionQuotient_inductionOn
      (motive := fun x => x * y = y * x) x ?_
    intro a
    refine P.extensionQuotient_inductionOn
      (motive := fun y =>
        P.extensionQuotientMk a * y =
          y * P.extensionQuotientMk a) y ?_
    intro b
    apply P.extensionQuotientMulEquiv.injective
    simp only [map_mul, P.extensionQuotientMk_apply]
    apply QuotientGroup.eq.mpr
    apply (mem_extensionSubgroup_iff L P.field P.below _).2
    constructor
    · exact ((a * b)⁻¹ * (b * a)).property
    · let aK  :=
        Subgroup.inclusion hLK a
      let bK  :=
        Subgroup.inclusion hLK b
      have hcomm :=
        M.commutative.is_comm.comm
          (M.extensionQuotientMk aK)
          (M.extensionQuotientMk bK)
      have hcommRaw :=
        congrArg M.extensionQuotientMulEquiv hcomm
      simp only [map_mul, M.extensionQuotientMk_apply] at hcommRaw
      exact
        (mem_extensionSubgroup_iff
          K M.field M.below _).1
          (QuotientGroup.eq.mp hcommRaw)

/-- The compositum `L₁L₂`, contravariantly represented by
`G_{L₁} ∩ G_{L₂}`. -/
def compositum (L₁ L₂ : FiniteAbelianSubextension K) :
    FiniteAbelianSubextension K where
  toFiniteGaloisExtension :=
    L₁.toFiniteGaloisExtension.compositum L₂.toFiniteGaloisExtension
  commutative := by
    let P := L₁.toFiniteGaloisExtension.compositum
      L₂.toFiniteGaloisExtension
    let  := L₁.normal
    let  := L₂.normal
    let  := P.normal
    refine ⟨⟨?_⟩⟩
    intro x y
    refine P.extensionQuotient_inductionOn
      (motive := fun x => x * y = y * x) x ?_
    intro a
    refine P.extensionQuotient_inductionOn
      (motive := fun y => P.extensionQuotientMk a * y =
        y * P.extensionQuotientMk a) y ?_
    intro b
    apply P.extensionQuotientMulEquiv.injective
    simp only [map_mul, P.extensionQuotientMk_apply]
    apply QuotientGroup.eq.mpr
    apply (mem_extensionSubgroup_iff K P.field P.below _).2
    constructor
    · have hcomm := L₁.commutative.is_comm.comm
          (L₁.extensionQuotientMk a) (L₁.extensionQuotientMk b)
      have hcommRaw := congrArg L₁.extensionQuotientMulEquiv hcomm
      simp only [map_mul, L₁.extensionQuotientMk_apply] at hcommRaw
      exact (mem_extensionSubgroup_iff K L₁.field L₁.below _).1
        (QuotientGroup.eq.mp hcommRaw)
    · have hcomm := L₂.commutative.is_comm.comm
          (L₂.extensionQuotientMk a) (L₂.extensionQuotientMk b)
      have hcommRaw := congrArg L₂.extensionQuotientMulEquiv hcomm
      simp only [map_mul, L₂.extensionQuotientMk_apply] at hcommRaw
      exact (mem_extensionSubgroup_iff K L₂.field L₂.below _).1
        (QuotientGroup.eq.mp hcommRaw)

/-- The left subextension embeds into the compositum. -/
theorem le_compositum_left (L₁ L₂ : FiniteAbelianSubextension K) :
    L₁ ≤ L₁.compositum L₂ :=
  by
    change (L₁.field.toSubgroup ⊓ L₂.field.toSubgroup) ≤
      L₁.field.toSubgroup
    exact inf_le_left

/-- The right subextension embeds into the compositum. -/
theorem le_compositum_right (L₁ L₂ : FiniteAbelianSubextension K) :
    L₂ ≤ L₁.compositum L₂ :=
  by
    change (L₁.field.toSubgroup ⊓ L₂.field.toSubgroup) ≤
      L₂.field.toSubgroup
    exact inf_le_right







section Intersection

variable [IsTopologicalGroup G] [CompactSpace G]


























































































































end Intersection

end FiniteAbelianSubextension

end GroupOnly

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- The norm subgroup assigned to a finite abelian extension,
`N_L = N_{L/K} A_L` in the finite abelian class-field classification. -/
def normSubgroup (A : Rep ℤ G) (L : FiniteAbelianSubextension K) :
    AddSubgroup (ambientFixedAddSubgroup A K) := by
  letI  := L.finite
  exact finiteNormSubgroup A K L.field L.below

/-- The source-level implication in the order formula:
an inclusion of fields gives the reverse inclusion of norm subgroups. -/
theorem normSubgroup_antitone (A : Rep ℤ G)
    {L₁ L₂ : FiniteAbelianSubextension K} (h : L₁ ≤ L₂) :
    normSubgroup A L₂ ≤ normSubgroup A L₁ := by
  let  := L₂.finite
  let  := L₁.finite
  let hL₂L₁finite  :=
    FiniteGaloisSubextension.finite_extension_over_intermediate
      L₂.below L₁.below h
  let T : DegreeData.FiniteTower G := {
    top := L₂.field
    middle := L₁.field
    base := K
    top_le_middle := h
    middle_le_base := L₁.below
    finiteTopQuotient := by
      change Finite (L₁.field.toSubgroup ⧸
        extensionSubgroup L₁.field L₂.field h)
      exact hL₂L₁finite
    finiteBaseQuotient := L₁.finite }
  change finiteNormSubgroup A K L₂.field L₂.below ≤
    finiteNormSubgroup A K L₁.field L₁.below
  rintro _ ⟨a, rfl⟩
  refine ⟨relativeNorm A L₁.field L₂.field h a, ?_⟩
  exact T.norm_trans_apply A a

/-- The unconditional half of
`N_{L₁L₂} = N_{L₁} ∩ N_{L₂}` in the finite abelian class-field classification. -/
theorem normSubgroup_compositum_le_inf (A : Rep ℤ G)
    (L₁ L₂ : FiniteAbelianSubextension K) :
    normSubgroup A (L₁.compositum L₂) ≤
      normSubgroup A L₁ ⊓ normSubgroup A L₂ := by
  intro x hx
  exact ⟨normSubgroup_antitone A (le_compositum_left L₁ L₂) hx,
    normSubgroup_antitone A (le_compositum_right L₁ L₂) hx⟩













end FiniteAbelianSubextension

end Representation

end ClassFormation

end
