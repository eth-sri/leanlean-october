module

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory KummerTheory CyclicCohomology

open ClassFormation

/-!
# Finite local reciprocity: finite abstract fields inside a separable closure

The abstract fields to which the class field axiom is applied are the open
closed subgroups of the absolute Galois group.  This file turns the explicit
finite-index witness from the abstract class-formation data into the corresponding finite fixed
field.  It is the field-theoretic input needed before the local class-field-axiom theorem can be
applied.
-/

noncomputable section

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

section

variable (H : ClosedSubgroup (Gal(Ω / k)))

/-- The concrete fixed field represented by an abstract closed subgroup. -/
abbrev abstractFixedField :
    IntermediateField k Ω :=
  IntermediateField.fixedField H.toSubgroup

/-- Passing from an abstract field to its concrete fixed field
and back recovers the original closed subgroup. -/
theorem closedFixingSubgroup_abstractFixedField_eq :
    closedFixingSubgroup k Ω (abstractFixedField k Ω H) = H := by
  ext σ
  change σ ∈ (abstractFixedField k Ω H).fixingSubgroup ↔ σ ∈ H
  rw [InfiniteGalois.fixingSubgroup_fixedField H]
  rfl

end

omit [IsGalois k Ω] in
/-- Absolute finiteness in the abstract class-formation quotient presentation gives a
finite quotient of the ambient absolute Galois group by the same subgroup. -/
theorem ambientQuotientFiniteOfAbstractFinite
    (H : ClosedSubgroup (Gal(Ω / k)))
    (hfinite : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / k))) H (le_baseField H))) :
    Finite (Gal(Ω / k) ⧸ H.toSubgroup) := by
  apply Nat.finite_of_card_ne_zero
  change H.toSubgroup.index ≠ 0
  rw [← Subgroup.relIndex_top_right]
  exact @Subgroup.index_ne_zero_of_finite
    (baseField (Gal(Ω / k))).toSubgroup _
    (extensionSubgroup (baseField (Gal(Ω / k))) H (le_baseField H))
    hfinite

omit [IsGalois k Ω] in
/-- An abstract field finite over the distinguished base is represented by
an open subgroup of the absolute Galois group. -/
theorem abstractFiniteClosedSubgroup_isOpen
    (H : ClosedSubgroup (Gal(Ω / k)))
    (hfinite : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / k))) H (le_baseField H))) :
    IsOpen H.carrier := by
  let :=
    ambientQuotientFiniteOfAbstractFinite k Ω H hfinite
  let :=
    H.toSubgroup.finiteIndex_of_finite_quotient
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex H.toSubgroup H.isClosed'

/-- The fixed field of an abstract field finite over the distinguished base
is an actual finite field extension. -/
theorem abstractFixedField_finiteDimensional
    (H : ClosedSubgroup (Gal(Ω / k)))
    (hfinite : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / k))) H (le_baseField H))) :
    FiniteDimensional k (abstractFixedField k Ω H) := by
  apply (InfiniteGalois.isOpen_iff_finite
     (abstractFixedField k Ω H)).1
  rw [InfiniteGalois.fixingSubgroup_fixedField H]
  grind [abstractFiniteClosedSubgroup_isOpen]

omit [IsGalois k Ω] in
/-- Inclusion of abstract subgroups reverses to inclusion of their concrete
fixed fields. -/
theorem abstractFixedField_le {K L : ClosedSubgroup (Gal(Ω / k))}
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    abstractFixedField k Ω K ≤ abstractFixedField k Ω L :=
  IntermediateField.fixedField_le hLK

section

variable (H : ClosedSubgroup (Gal(Ω / k)))

/-- The abstract subgroup representing a fixed field is canonically the
absolute Galois group of the ambient extension over that fixed field. -/
def abstractSubgroupEquivGaloisGroup :
    H.toSubgroup ≃* Gal(Ω / abstractFixedField k Ω H) :=
  (MulEquiv.subgroupCongr
      (InfiniteGalois.fixingSubgroup_fixedField H).symm).trans
    (IntermediateField.fixingSubgroupEquiv (abstractFixedField k Ω H))

/-- States the theorem `abstractSubgroupEquivGaloisGroup_apply`. -/
@[simp]
theorem abstractSubgroupEquivGaloisGroup_apply (σ : H.toSubgroup) (x : Ω) :
    abstractSubgroupEquivGaloisGroup k Ω H σ x = σ.1 x :=
  rfl

end

/-- The upper fixed field, regarded as an intermediate field over the lower
fixed field in a relative abstract extension. -/
abbrev abstractRelativeFixedField
    {K L : ClosedSubgroup (Gal(Ω / k))}
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    IntermediateField (abstractFixedField k Ω K) Ω :=
  IntermediateField.extendScalars (abstractFixedField_le k Ω hLK)

/-- Under the preceding Galois-group equivalence, the relative class-formation
subgroup is exactly the subgroup fixing the upper concrete field. -/
theorem map_extensionSubgroup_abstractSubgroupEquiv
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (extensionSubgroup K L hLK).map
        (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom =
      (abstractRelativeFixedField k Ω hLK).fixingSubgroup := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hfix : ∀ y ∈ abstractFixedField k Ω L, σ.1 y = y := by
      refine (IntermediateField.mem_fixingSubgroup_iff
        (abstractFixedField k Ω L) σ.1).1 ?_
      rw [InfiniteGalois.fixingSubgroup_fixedField L]
      exact ((mem_extensionSubgroup_iff K L hLK σ).1 hσ)
    exact hfix x hx
  · intro hτ
    let σ :=
      (abstractSubgroupEquivGaloisGroup k Ω K).symm τ
    refine ⟨σ, ?_, (abstractSubgroupEquivGaloisGroup k Ω K).apply_symm_apply τ⟩
    apply (mem_extensionSubgroup_iff K L hLK σ).2
    have hσfix : σ.1 ∈
        (abstractFixedField k Ω L).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      calc
        σ.1 x = abstractSubgroupEquivGaloisGroup k Ω K σ x :=
          (abstractSubgroupEquivGaloisGroup_apply k Ω K σ x).symm
        _ = τ x := by
          rfl
        _ = x := ((IntermediateField.mem_fixingSubgroup_iff
          (abstractRelativeFixedField k Ω hLK) τ).1 hτ x hx)
    rw [InfiniteGalois.fixingSubgroup_fixedField L] at hσfix
    exact hσfix

/-- Relative normality in the abstract class-formation framework is the actual normality of the subgroup
fixing the upper field inside the lower field's absolute Galois group. -/
theorem abstractRelativeFixingSubgroup_normal
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal := by
  have hmap :=
    hnormal.map (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom
      (abstractSubgroupEquivGaloisGroup k Ω K).surjective
  rw [map_extensionSubgroup_abstractSubgroupEquiv k Ω K L hLK] at hmap
  exact hmap

/-- The concrete relative fixed field is Galois precisely from the normality
witness occurring in the abstract cyclic extension. -/
theorem abstractRelativeFixedField_isGalois
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    IsGalois (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) := by
  apply (InfiniteGalois.normal_iff_isGalois
    (abstractRelativeFixedField k Ω hLK)).1
  exact abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal

section

variable (K L : ClosedSubgroup (Gal(Ω / k))) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)

/-- Restriction through the lower fixed field, followed by quotienting by
the upper fixing subgroup. -/
def abstractRelativeToAmbientQuotient :
    letI := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    K.toSubgroup →*
      Gal(Ω / abstractFixedField k Ω K) ⧸
        (abstractRelativeFixedField k Ω hLK).fixingSubgroup := by
  letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  exact (QuotientGroup.mk'
    (abstractRelativeFixedField k Ω hLK).fixingSubgroup).comp
      (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom

/-- The kernel of the preceding quotient map is the exact abstract class-formation
relative subgroup. -/
theorem abstractRelativeToAmbientQuotient_ker :
    letI := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    (abstractRelativeToAmbientQuotient k Ω K L hLK hnormal).ker =
      extensionSubgroup K L hLK := by
  let :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  ext σ
  change
    QuotientGroup.mk' (abstractRelativeFixedField k Ω hLK).fixingSubgroup
        (abstractSubgroupEquivGaloisGroup k Ω K σ) = 1 ↔
      σ ∈ extensionSubgroup K L hLK
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [← map_extensionSubgroup_abstractSubgroupEquiv k Ω K L hLK]
  constructor
  · simpa [this] using hτ
  · simp

/-- The quotient map from the abstract lower subgroup is surjective. -/
theorem abstractRelativeToAmbientQuotient_surjective :
    letI := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    Function.Surjective
      (abstractRelativeToAmbientQuotient k Ω K L hLK hnormal) := by
  let :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  intro q
  refine Quotient.inductionOn' q ?_
  intro τ
  refine ⟨(abstractSubgroupEquivGaloisGroup k Ω K).symm τ, ?_⟩
  rfl

/-- The exact abstract class-formation quotient of a relative normal extension is the
ordinary quotient of the lower absolute Galois group by the upper fixing
subgroup. -/
def abstractExtensionQuotientEquivAmbient :
    letI := hnormal
    letI := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    K.toSubgroup ⧸ extensionSubgroup K L hLK ≃*
      Gal(Ω / abstractFixedField k Ω K) ⧸
        (abstractRelativeFixedField k Ω hLK).fixingSubgroup := by
  letI := hnormal
  letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  exact (QuotientGroup.quotientMulEquivOfEq
      (abstractRelativeToAmbientQuotient_ker
        k Ω K L hLK hnormal).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (abstractRelativeToAmbientQuotient k Ω K L hLK hnormal)
      (abstractRelativeToAmbientQuotient_surjective
        k Ω K L hLK hnormal))

end

/-- The quotient group appearing in the abstract class-field-axiom predicate is
canonically the actual Galois group of the two concrete fixed fields. -/
def abstractExtensionQuotientEquivGaloisGroup
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    letI := hnormal
    K.toSubgroup ⧸ extensionSubgroup K L hLK ≃*
      Gal(abstractRelativeFixedField k Ω hLK / abstractFixedField k Ω K) := by
  letI := hnormal
  letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  let H :=
    closedFixingSubgroup (abstractFixedField k Ω K) Ω
      (abstractRelativeFixedField k Ω hLK)
  letI : H.toSubgroup.Normal := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  exact (abstractExtensionQuotientEquivAmbient
      k Ω K L hLK hnormal).trans
    ((InfiniteGalois.normalAutEquivQuotient H).trans
      (AlgEquiv.autCongr
        (IntermediateField.equivOfEq
          (InfiniteGalois.fixedField_fixingSubgroup
            (abstractRelativeFixedField k Ω hLK)))))

/-- In a finite abstract tower `L / K / k`, the concrete upper fixed field is
finite over the concrete lower fixed field. -/
theorem abstractFixedField_relativeFiniteDimensional
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hKfinite : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / k))) K (le_baseField K)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)) :
    letI : Algebra (abstractFixedField k Ω K) (abstractFixedField k Ω L) :=
      RingHom.toAlgebra
        (IntermediateField.inclusion (abstractFixedField_le k Ω hLK))
    FiniteDimensional (abstractFixedField k Ω K)
      (abstractFixedField k Ω L) := by
  let : Algebra (abstractFixedField k Ω K) (abstractFixedField k Ω L) :=
    RingHom.toAlgebra
      (IntermediateField.inclusion (abstractFixedField_le k Ω hLK))
  let : IsScalarTower k (abstractFixedField k Ω K)
      (abstractFixedField k Ω L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let :=
    hKfinite
  let := hLKfinite
  let :=
    FiniteGaloisSubextension.finite_extension_trans hLK (le_baseField K)
  let :=
    abstractFixedField_finiteDimensional k Ω L inferInstance
  exact FiniteDimensional.right k
    (abstractFixedField k Ω K) (abstractFixedField k Ω L)

/-- The same relative finiteness statement in the scalar-extended
intermediate-field presentation used by infinite Galois theory. -/
theorem abstractRelativeFixedField_finiteDimensional
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hKfinite : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / k))) K (le_baseField K)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)) :
    FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) := by
  exact abstractFixedField_relativeFiniteDimensional k Ω K L hLK hKfinite hLKfinite

/-- The abstract extension degree is the ordinary degree of the concrete
finite Galois extension represented by the same pair of fixed fields. -/
theorem finiteAbstractExtension_degree_eq_finrank
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hKfinite : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / k))) K (le_baseField K)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)) :
    ((DegreeData.FiniteAbstractExtension.ofInclusion L K hLK).degree : ℕ) =
      Module.finrank (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) := by
  let := hnormal
  let := hLKfinite
  let :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKfinite hLKfinite
  let :=
    abstractRelativeFixedField_isGalois k Ω K L hLK hnormal
  calc
    _ =
        (extensionSubgroup K L hLK).index :=
      (DegreeData.FiniteAbstractExtension.ofInclusion L K hLK).extensionSubgroup_index_eq_degree.symm
    _ = Nat.card
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      Subgroup.index_eq_card (extensionSubgroup K L hLK)
    _ = Nat.card (Gal(abstractRelativeFixedField k Ω hLK / abstractFixedField k Ω K)) :=
      Nat.card_congr
        (abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal).toEquiv
    _ = Module.finrank (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) :=
      IsGalois.card_aut_eq_finrank
        (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK)

end
end LocalClassFieldTheory
