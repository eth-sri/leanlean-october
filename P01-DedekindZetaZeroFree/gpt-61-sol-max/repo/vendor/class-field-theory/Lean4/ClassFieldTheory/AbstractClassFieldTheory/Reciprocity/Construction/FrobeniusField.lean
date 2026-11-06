module

public import Mathlib

public import ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

namespace ClassFormation

open CyclicCohomology

/-!
# The abstract reciprocity construction: the field fixed by a Frobenius lift

This file passes from the group-dual `Γ` of the Frobenius fixed-field theorem to the actual
abstract field `Σ`.  Thus `G_Σ` is the inverse image of `Γ` under
`G_K → G_K / I_L`, embedded back into the ambient profinite group.
-/

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

section
variable (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
include D K L hLK hLnormal σ
/-- The subgroup `G_Σ ≤ G_K`: the inverse image of
`Γ = closure ⟨σ⟩` under `G_K → G_K / I_L`. -/
def frobeniusFixedSubgroupWithin    :=
  (D.frobeniusClosure K L hLK σ).toSubgroup.comap
    (QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK))

/-- Membership in the internal Frobenius-fixed subgroup is characterized by
fixedness under Frobenius. -/
@[simp]
theorem mem_frobeniusFixedSubgroupWithin_iff   (k : K.field.toSubgroup) :
    k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ ↔
      QuotientGroup.mk k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup :=
  Iff.rfl

/-- The Frobenius-fixed subgroup inside the extension subgroup is closed. -/
theorem frobeniusFixedSubgroupWithin_isClosed   :
    IsClosed
      (D.frobeniusFixedSubgroupWithin K L hLK σ : Set K.field.toSubgroup) := by
  change IsClosed
    ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) ⁻¹'
      ((D.frobeniusClosure K L hLK σ).toSubgroup : Set
        (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)))
  exact (D.frobeniusClosure K L hLK σ).isClosed'.preimage
    continuous_quotient_mk'

/-- The actual abstract field `Σ` fixed by the chosen Frobenius lift.
Its absolute Galois subgroup is the inverse image of `Γ`, now regarded as
a closed subgroup of the ambient group `G`. -/
def frobeniusFixedField   : ClosedSubgroup G where
  toSubgroup :=
    (D.frobeniusFixedSubgroupWithin K L hLK σ).map
      K.field.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      (Subtype.val ''
        (D.frobeniusFixedSubgroupWithin K L hLK σ : Set K.field.toSubgroup))
    exact K.field.isClosed'.isClosedEmbedding_subtypeVal.isClosedMap _
      (D.frobeniusFixedSubgroupWithin_isClosed K L hLK σ)

/-- An element lies in the Frobenius fixed field exactly when Frobenius fixes its restriction. -/
@[simp]
theorem mem_frobeniusFixedField_iff   (g : G) :
    g ∈ D.frobeniusFixedField K L hLK σ ↔
      ∃ k : K.field.toSubgroup,
        k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ ∧ k.1 = g := by
  rfl

/-- The field `Σ` extends `K`, i.e. `G_Σ ≤ G_K`. -/
theorem frobeniusFixedField_le   :
    (D.frobeniusFixedField K L hLK σ).toSubgroup ≤ K.field.toSubgroup := by
  rintro g ⟨k, _, rfl⟩
  exact k.2

/-- Inside `G_K`, the subgroup attached to the actual field `Σ` is
literally the quotient-projection inverse image used in its definition. -/
theorem extensionSubgroup_frobeniusFixedField   :
    extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField_le K L hLK σ) =
      D.frobeniusFixedSubgroupWithin K L hLK σ := by
  ext k
  change
    (k.1 ∈ D.frobeniusFixedField K L hLK σ) ↔
      k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ
  rw [D.mem_frobeniusFixedField_iff K L hLK σ]
  constructor
  · rintro ⟨t, ht, htk⟩
    have : t = k := by
      apply Subtype.ext
      exact htk
    simpa [this] using ht
  · intro hk
    exact ⟨k, hk, rfl⟩

/-- The subgroup `I_L = G_{\widetilde L}` lies in `G_Σ`. -/
theorem extensionInertiaWithin_le_frobeniusFixedSubgroupWithin
      :
    D.extensionInertiaWithin K.field L hLK ≤
      D.frobeniusFixedSubgroupWithin K L hLK σ := by
  intro k hk
  change QuotientGroup.mk k ∈
    (D.frobeniusClosure K L hLK σ).toSubgroup
  rw [(QuotientGroup.eq_one_iff k).2 hk]
  exact Subgroup.one_mem _

/-- Ambient form of `I_L ≤ G_Σ`. -/
theorem fieldInertia_le_frobeniusFixedField   :
    (D.fieldInertia L).toSubgroup ≤
      (D.frobeniusFixedField K L hLK σ).toSubgroup := by
  intro g hg
  let k : K.field.toSubgroup := ⟨g, hLK hg.1⟩
  have hkE : k ∈ extensionSubgroup K.field L hLK := hg.1
  have hkI : k ∈ D.fieldInertiaWithin K.field := hg.2
  exact ⟨k,
    D.extensionInertiaWithin_le_frobeniusFixedSubgroupWithin
      K L hLK σ ⟨hkE, hkI⟩,
    rfl⟩
end


section
variable (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements K L hLK)
include D K L hLK hLnormal hLfinite σ
/-- finiteness of the Frobenius fixed field on the actual field side: `Σ | K` is finite. -/
theorem frobeniusFixedField_finite   :
    Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ)) := by
  let N := D.extensionInertiaWithin K.field L hLK
  let Q := K.field.toSubgroup ⧸ N
  let Γ : Subgroup Q :=
    (D.frobeniusClosure K L hLK σ).toSubgroup
  let S : Subgroup K.field.toSubgroup :=
    D.frobeniusFixedSubgroupWithin K L hLK σ
  let : Finite (Q ⧸ Γ) := by
    apply D.frobeniusFixedField_finiteIndex
  have hΓ  := Γ.index_ne_zero_of_finite
  have hS : S.index ≠ 0 := by
    rw [show S = Γ.comap (QuotientGroup.mk' N) by rfl]
    rw [Subgroup.index_comap_of_surjective Γ
      (QuotientGroup.mk'_surjective N)]
    exact hΓ
  apply Nat.finite_of_card_ne_zero
  change
    (extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField_le K L hLK σ)).index ≠ 0
  rw [D.extensionSubgroup_frobeniusFixedField K L hLK σ]
  exact hS

/-- The Frobenius fixed field bundled with its finite extension data. -/
def frobeniusFixedFiniteExtension   :
    FiniteAbstractExtension G where
  field := D.frobeniusFixedField K L hLK σ
  base := K.field
  below := D.frobeniusFixedField_le K L hLK σ
  finiteQuotient := D.frobeniusFixedField_finite K L hLK σ
end































section
variable (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
include D K L hLK hLnormal σ
/-- The procyclic degree isomorphism, faithfully pulled back along
`G_K → G_K / I_L`: `G_Σ ∩ I_K = I_L`.  This is the subgroup form of
the equality `\widetilde Σ = \widetilde L`. -/
theorem frobeniusFixedSubgroupWithin_inf_fieldInertiaWithin
      :
    D.frobeniusFixedSubgroupWithin K L hLK σ ⊓
        D.fieldInertiaWithin K.field =
      D.extensionInertiaWithin K.field L hLK := by
  apply le_antisymm
  · intro k hk
    let a : D.frobeniusClosure K L hLK σ :=
      ⟨QuotientGroup.mk k, hk.1⟩
    have hda : D.fixedFieldNormalizedDegree K L hLK σ a = 1 := by
      apply Multiplicative.ext
      apply zHatMulNat_injective
        (D.frobeniusExponent_pos K L hLK σ)
      change D.frobeniusExponent K L hLK σ •
          (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd =
        D.frobeniusExponent K L hLK σ • (1 : ZHatMul).toAdd
      rw [D.frobeniusExponent_nsmul_fixedFieldNormalizedDegree]
      change (D.normalizedDegree K k).toAdd =
        D.frobeniusExponent K L hLK σ • (1 : ZHatMul).toAdd
      have hdk : D.normalizedDegree K k = 1 := by
        change k ∈ (D.normalizedDegree K).toMonoidHom.ker
        rw [D.normalizedDegree_ker K]
        exact hk.2
      rw [hdk]
      simp
    have ha : a = 1 := by
      apply D.frobeniusFixedField_normalizedDegree_injective K L hLK σ
      simpa using hda
    apply (QuotientGroup.eq_one_iff k).mp
    exact congrArg Subtype.val ha
  · intro k hk
    exact
      ⟨D.extensionInertiaWithin_le_frobeniusFixedSubgroupWithin
          K L hLK σ hk,
        hk.2⟩

/-- Ambient version of the procyclic degree isomorphism: the maximal unramified
extensions of `Σ` and `L` have the same absolute Galois subgroup. -/
theorem frobeniusFixedField_fieldInertia   :
    D.fieldInertia (D.frobeniusFixedField K L hLK σ) =
      D.fieldInertia L := by
  ext g
  constructor
  · intro hg
    obtain ⟨k, hkS, hkg⟩ := hg.1
    have hgdeg : D.degree g = 1 := hg.2
    have hkI : k ∈ D.fieldInertiaWithin K.field := by
      change D.degree k.1 = 1
      exact (congrArg D.degree hkg).trans hgdeg
    have hkN : k ∈ D.extensionInertiaWithin K.field L hLK := by
      rw [← D.frobeniusFixedSubgroupWithin_inf_fieldInertiaWithin
        K L hLK σ]
      exact ⟨hkS, hkI⟩
    exact ⟨hkg ▸ hkN.1, hg.2⟩
  · intro hg
    let k : K.field.toSubgroup := ⟨g, hLK hg.1⟩
    have hgdeg : D.degree g = 1 := hg.2
    have hkE : k ∈ extensionSubgroup K.field L hLK := hg.1
    have hkI : k ∈ D.fieldInertiaWithin K.field := hgdeg
    have hkS  :=
      D.extensionInertiaWithin_le_frobeniusFixedSubgroupWithin
        K L hLK σ ⟨hkE, hkI⟩
    exact ⟨⟨k, hkS, rfl⟩, hg.2⟩
end


/-- The normalized-degree image of the actual subgroup `G_Σ ≤ G_K` is
the image already computed on the group-dual `Γ`. -/
theorem frobeniusFixedSubgroupWithin_normalizedDegree_image
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusFixedSubgroupWithin K L hLK σ).map
        (D.normalizedDegree K).toMonoidHom =
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range := by
  ext z
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨QuotientGroup.mk k, hk⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
      (D.extensionInertiaWithin K.field L hLK) a.1
    have hkS : k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
      simp_all
    refine ⟨k, hkS, ?_⟩
    calc
      D.normalizedDegree K k =
          D.extensionNormalizedDegree K L hLK
            ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) k) :=
        (D.extensionNormalizedDegree_mk K L hLK k).symm
      _ = D.extensionNormalizedDegree K L hLK a.1 :=
        congrArg (D.extensionNormalizedDegree K L hLK) hk

section
variable (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
include D K L hLK hLnormal
private theorem frobeniusFixedField_mappedRelIndex  
    (σ : D.FrobeniusElements K L hLK) :
    ((D.frobeniusFixedField K L hLK σ).toSubgroup.map
        D.degree.toMonoidHom).relIndex
      (K.field.toSubgroup.map D.degree.toMonoidHom) =
      D.frobeniusExponent K L hLK σ := by
  let S  :=
    D.frobeniusFixedSubgroupWithin K L hLK σ
  let dK : K.field.toSubgroup →* ZHatMul :=
    (D.normalizedDegree K).toMonoidHom
  let scale : ZHatMul →* ZHatMul :=
    (zHatPowNat (K.residueDegree : ℕ)).toMonoidHom
  have hraw : (D.restrictedDegree K.field).toMonoidHom = scale.comp dK := by
    apply MonoidHom.ext
    intro k
    apply Multiplicative.ext
    exact (D.residueDegree_nsmul_normalizedDegree K k).symm
  have hSigmaImage :
      (D.frobeniusFixedField K L hLK σ).toSubgroup.map
          D.degree.toMonoidHom =
        S.map (D.restrictedDegree K.field).toMonoidHom := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨k, hk, hkg⟩ := hg
      refine ⟨k, hk, ?_⟩
      exact congrArg D.degree hkg
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.1, ⟨k, hk, rfl⟩, rfl⟩
  have hKimage :
      K.field.toSubgroup.map D.degree.toMonoidHom =
        (⊤ : Subgroup K.field.toSubgroup).map
          (D.restrictedDegree K.field).toMonoidHom := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, trivial, rfl⟩
    · rintro ⟨k, _, rfl⟩
      exact ⟨k.1, k.2, rfl⟩
  have hscale : Function.Injective scale := by
    intro x y hxy
    apply Multiplicative.ext
    apply zHatMulNat_injective K.residueDegree.property
    exact congrArg Multiplicative.toAdd hxy
  have htop : (⊤ : Subgroup K.field.toSubgroup).map dK = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨k, hk⟩ := D.normalizedDegree_surjective K z
    exact ⟨k, trivial, hk⟩
  rw [hSigmaImage, hKimage, hraw]
  rw [← Subgroup.map_map, ← Subgroup.map_map]
  rw [Subgroup.relIndex_map_map_of_injective _ _ hscale]
  rw [show S.map dK =
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range by
        apply D.frobeniusFixedSubgroupWithin_normalizedDegree_image]
  rw [htop, Subgroup.relIndex_top_right,
    D.frobeniusClosureDegree_range K L hLK σ,
    AddSubgroup.index_toSubgroup,
    zHatMulNat_range_index _
      (D.frobeniusExponent_pos K L hLK σ)]

/-- The Frobenius fixed-field residue-degree formula on the finite extension
object: `f_{Σ|K} = d_K(σ)`. -/
theorem frobeniusFixedField_residueDegreeOverBase  
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements K L hLK) :
    ((D.frobeniusFixedFiniteExtension K L hLK σ).residueDegree D : ℕ) =
      D.frobeniusExponent K L hLK σ := by
  let E := D.frobeniusFixedFiniteExtension K L hLK σ
  rw [← E.mapped_relIndex_eq_residueDegree D]
  apply D.frobeniusFixedField_mappedRelIndex

/-- The actual relative residue quotient of the Frobenius fixed field over
`K` is finite.  Positivity of the computed mapped relative index gives an
honest finite-index witness before any natural-valued cardinality is formed. -/
theorem frobeniusFixedField_relativeResidueQuotientFinite
     
    (σ : D.FrobeniusElements K L hLK) :
    Finite
      (↥(K.field.toSubgroup.map D.degree.toMonoidHom) ⧸
        ((D.frobeniusFixedField K L hLK σ).toSubgroup.map
            D.degree.toMonoidHom).subgroupOf
          (K.field.toSubgroup.map D.degree.toMonoidHom)) := by
  apply (Subgroup.index_ne_zero_iff_finite).mp
  change ((D.frobeniusFixedField K L hLK σ).toSubgroup.map
      D.degree.toMonoidHom).relIndex
        (K.field.toSubgroup.map D.degree.toMonoidHom) ≠ 0
  rw [D.frobeniusFixedField_mappedRelIndex K L hLK σ]
  exact (D.frobeniusExponent_pos K L hLK σ).ne'

/-- The Frobenius fixed field equipped with its actual finite absolute
residue quotient. -/
noncomputable def frobeniusFixedResidueField  
    (σ : D.FrobeniusElements K L hLK) :
    FiniteResidueAbstractField D := by
  letI := D.frobeniusFixedField_relativeResidueQuotientFinite K L hLK σ
  exact FiniteResidueAbstractField.ofRelativeInclusion D
    (D.frobeniusFixedField K L hLK σ) K
    (D.frobeniusFixedField_le K L hLK σ)

/-- Absolute residue-degree formula, now stated only through positive
natural invariants of honest finite quotient bundles. -/
theorem frobeniusFixedResidueField_residueDegree  
    (σ : D.FrobeniusElements K L hLK) :
    ((D.frobeniusFixedResidueField K L hLK σ).residueDegree : ℕ) =
      D.frobeniusExponent K L hLK σ * (K.residueDegree : ℕ) := by
  let Sigma := D.frobeniusFixedResidueField K L hLK σ
  let E : AbstractExtension G := {
    field := D.frobeniusFixedField K L hLK σ
    base := K.field
    below := D.frobeniusFixedField_le K L hLK σ
  }
  let := D.frobeniusFixedField_relativeResidueQuotientFinite K L hLK σ
  have hrelative :
      E.relativeResidueDegreeCardinal D =
        (D.frobeniusExponent K L hLK σ : Cardinal) := by
    rw [AbstractExtension.relativeResidueDegreeCardinal]
    change Cardinal.mk
        (↥(K.field.toSubgroup.map D.degree.toMonoidHom) ⧸
          ((D.frobeniusFixedField K L hLK σ).toSubgroup.map
              D.degree.toMonoidHom).subgroupOf
            (K.field.toSubgroup.map D.degree.toMonoidHom)) = _
    rw [← Nat.cast_card]
    exact_mod_cast D.frobeniusFixedField_mappedRelIndex K L hLK σ
  have hcard :=
    E.relativeResidueDegreeCardinal_mul_residueDegreeCardinal D
  change E.relativeResidueDegreeCardinal D *
      D.residueDegreeCardinal K.field =
    D.residueDegreeCardinal Sigma.field at hcard
  rw [hrelative, K.residueDegreeCardinal_eq_coe,
    Sigma.residueDegreeCardinal_eq_coe] at hcard
  exact_mod_cast hcard.symm
end


section
variable (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
include D K L hLK hLnormal σ
/-- Restriction from the actual group `G_Σ` to the group-dual `Γ`. -/
def frobeniusFixedFieldToClosure   :
    (D.frobeniusFixedField K L hLK σ).toSubgroup →*
      D.frobeniusClosure K L hLK σ where
  toFun s := by
    let k  :=
      Subgroup.inclusion (D.frobeniusFixedField_le K L hLK σ) s
    refine ⟨QuotientGroup.mk k, ?_⟩
    have hk : k ∈
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ) := s.2
    rw [D.extensionSubgroup_frobeniusFixedField K L hLK σ] at hk
    exact hk
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' := by
    intro a b
    apply Subtype.ext
    rfl

/-- The map from the Frobenius fixed field to the closure evaluates by the underlying inclusion. -/
@[simp]
theorem frobeniusFixedFieldToClosure_apply  
    (s : (D.frobeniusFixedField K L hLK σ).toSubgroup) :
    (D.frobeniusFixedFieldToClosure K L hLK σ s).1 =
      QuotientGroup.mk
        (Subgroup.inclusion
          (D.frobeniusFixedField_le K L hLK σ) s) :=
  rfl

/-- Every element of the Frobenius closure lifts from the Frobenius fixed field. -/
theorem frobeniusFixedFieldToClosure_surjective   :
    Function.Surjective (D.frobeniusFixedFieldToClosure K L hLK σ) := by
  intro a
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
    (D.extensionInertiaWithin K.field L hLK) a.1
  have hkS : k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
    simp_all
  let s : (D.frobeniusFixedField K L hLK σ).toSubgroup :=
    ⟨k.1, ⟨k, hkS, rfl⟩⟩
  refine ⟨s, ?_⟩
  apply Subtype.ext
  exact hk
end


section
variable (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
include D K L hLK hLnormal σ
/-- The kernel of restriction `G_Σ → Γ` is precisely `I_Σ`; by
the procyclic degree isomorphism, this is also `I_L`. -/
theorem frobeniusFixedFieldToClosure_ker   :
    (D.frobeniusFixedFieldToClosure K L hLK σ).ker =
      D.fieldInertiaWithin (D.frobeniusFixedField K L hLK σ) := by
  ext s
  let k  :=
    Subgroup.inclusion (D.frobeniusFixedField_le K L hLK σ) s
  have hkS : k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
    have hk : k ∈
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ) := s.2
    rw [D.extensionSubgroup_frobeniusFixedField K L hLK σ] at hk
    exact hk
  constructor
  · intro hs
    have hq : QuotientGroup.mk k = 1 :=
      congrArg Subtype.val hs
    have hkN  :=
      (QuotientGroup.eq_one_iff k).mp hq
    exact hkN.2
  · intro hs
    have hkI : k ∈ D.fieldInertiaWithin K.field := hs
    have hkN : k ∈ D.extensionInertiaWithin K.field L hLK := by
      rw [← D.frobeniusFixedSubgroupWithin_inf_fieldInertiaWithin
        K L hLK σ]
      exact ⟨hkS, hkI⟩
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff k).mpr hkN

/-- The canonical identification
`G_Σ / I_Σ ≃ Γ = Gal(\widetilde L / Σ)`. -/
def frobeniusFixedFieldQuotientEquiv   :
    ((D.frobeniusFixedField K L hLK σ).toSubgroup ⧸
        D.fieldInertiaWithin (D.frobeniusFixedField K L hLK σ)) ≃*
      D.frobeniusClosure K L hLK σ :=
  (QuotientGroup.quotientMulEquivOfEq
      (D.frobeniusFixedFieldToClosure_ker K L hLK σ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (D.frobeniusFixedFieldToClosure K L hLK σ)
      (D.frobeniusFixedFieldToClosure_surjective K L hLK σ))

/-- The Frobenius fixed-field quotient equivalence has the expected value on representatives. -/
@[simp]
theorem frobeniusFixedFieldQuotientEquiv_mk  
    (s : (D.frobeniusFixedField K L hLK σ).toSubgroup) :
    D.frobeniusFixedFieldQuotientEquiv K L hLK σ
        (QuotientGroup.mk s) =
      D.frobeniusFixedFieldToClosure K L hLK σ s := rfl
end


/-- The normalized degree constructed on `Γ` in the Frobenius fixed-field theorem is exactly
the intrinsic normalized degree of the actual field `Σ`. -/
theorem frobeniusFixedField_normalizedDegree_compatibility (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (s : (D.frobeniusFixedField K L hLK σ).toSubgroup) :
    D.fixedFieldNormalizedDegree K L hLK σ
        (D.frobeniusFixedFieldToClosure K L hLK σ s) =
      D.normalizedDegree (D.frobeniusFixedResidueField K L hLK σ) s := by
  let Sigma := D.frobeniusFixedResidueField K L hLK σ
  let a : D.frobeniusClosure K L hLK σ :=
    D.frobeniusFixedFieldToClosure K L hLK σ s
  let k : K.field.toSubgroup :=
    Subgroup.inclusion (D.frobeniusFixedField_le K L hLK σ) s
  let n := D.frobeniusExponent K L hLK σ
  apply Multiplicative.ext
  apply zHatMulNat_injective Sigma.residueDegree.property
  change (Sigma.residueDegree : ℕ) •
      (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd =
    (Sigma.residueDegree : ℕ) • (D.normalizedDegree Sigma s).toAdd
  calc
    (Sigma.residueDegree : ℕ) •
        (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd =
      (K.residueDegree : ℕ) •
        (n • (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd) := by
          rw [show (Sigma.residueDegree : ℕ) =
              n * (K.residueDegree : ℕ) by
            apply D.frobeniusFixedResidueField_residueDegree]
          rw [smul_smul, Nat.mul_comm]
    _ = (K.residueDegree : ℕ) •
        (D.frobeniusClosureDegree K L hLK σ a).toAdd := by
          rw [D.frobeniusExponent_nsmul_fixedFieldNormalizedDegree]
    _ = (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd := rfl
    _ = (D.degree s.1).toAdd := D.residueDegree_nsmul_normalizedDegree K k
    _ = (Sigma.residueDegree : ℕ) •
        (D.normalizedDegree Sigma s).toAdd := by
          exact (D.residueDegree_nsmul_normalizedDegree Sigma s).symm







































end DegreeData

end
end ClassFormation
