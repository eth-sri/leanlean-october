module
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityDefinition

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction: independence of the prime element

This file supplies the finite-Galois cofinality and compositum argument used to prove that the reciprocity construction is independent of its prime element.
-/

noncomputable section

section groupTheoreticRefinements

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

section

variable [IsTopologicalGroup G] {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)

/-- The normal core of a finite intermediate field, embedded back into the
ambient absolute Galois group. -/
def normalCoreField :
    ClosedSubgroup G where
  toSubgroup :=
    (extensionSubgroup K M.field M.below).normalCore.map
      K.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      (Subtype.val ''
        ((extensionSubgroup K M.field M.below).normalCore : Set K.toSubgroup))
    exact K.isClosed'.isClosedEmbedding_subtypeVal.isClosedMap _
      ((extensionSubgroup K M.field M.below).normalCore_isClosed
        (extensionSubgroup_isClosed K M.field M.below))

/-- The normal core field lies below the field from which it is constructed. -/
theorem normalCoreField_le :
    (M.normalCoreField).toSubgroup ≤ K.toSubgroup := by
  rintro g ⟨k, _, rfl⟩
  exact k.2

end

/-- The normal core is contained in the specified refinement field. -/
theorem normalCoreField_le_field [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) :
    (M.normalCoreField).toSubgroup ≤ M.field.toSubgroup := by
  rintro g ⟨k, hk, rfl⟩
  exact (mem_extensionSubgroup_iff K M.field M.below k).1
    ((extensionSubgroup K M.field M.below).normalCore_le hk)

section

variable [IsTopologicalGroup G] {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)

/-- The subgroup representing the normal core field is the corresponding normal core. -/
theorem extensionSubgroup_normalCoreField :
    extensionSubgroup K M.normalCoreField M.normalCoreField_le =
      (extensionSubgroup K M.field M.below).normalCore := by
  ext k
  constructor
  · intro hk
    obtain ⟨k', hk', hk'n⟩ := hk
    have hk'eq : k' = k := by
      apply Subtype.ext
      exact hk'n
    simpa [hk'eq] using hk'
  · intro hk
    exact ⟨k, hk, rfl⟩

/-- Every finite intermediate field admits a finite Galois refinement once
the bottom extension is normal. -/
def galoisRefinement
    [hEnormal :
      (extensionSubgroup K E (M.above.trans M.below)).Normal] :
    FiniteIntermediateField E K where
  field := M.normalCoreField
  above := by
    intro e he
    let eK : K.toSubgroup := ⟨e, M.below (M.above he)⟩
    have hle : extensionSubgroup K E (M.above.trans M.below) ≤
        extensionSubgroup K M.field M.below := by
      intro x hx
      apply (mem_extensionSubgroup_iff K M.field M.below x).2
      exact M.above
        ((mem_extensionSubgroup_iff K E (M.above.trans M.below) x).1 hx)
    exact ⟨eK, ((Subgroup.normal_le_normalCore.mpr hle) ((mem_extensionSubgroup_iff K E (M.above.trans M.below) eK).2 he)), rfl⟩
  below := M.normalCoreField_le
  finite := by
    let H := extensionSubgroup K M.field M.below
    let :=
      @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _ H M.finite
    let : H.normalCore.FiniteIndex := inferInstance
    rw [M.extensionSubgroup_normalCoreField]
    infer_instance

/-- A Galois refinement lies below the original finite field. -/
theorem galoisRefinement_le_field
    [_hEnormal :
      (extensionSubgroup K E (M.above.trans M.below)).Normal] :
    (M.galoisRefinement).field.toSubgroup ≤ M.field.toSubgroup :=
  M.normalCoreField_le_field

end

/-- The subgroup representing a Galois refinement is normal. -/
instance galoisRefinement_normal [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    [hEnormal :
      (extensionSubgroup K E (M.above.trans M.below)).Normal] :
    (extensionSubgroup K (M.galoisRefinement).field
      (M.galoisRefinement).below).Normal := by
  change (extensionSubgroup K M.normalCoreField M.normalCoreField_le).Normal
  rw [M.extensionSubgroup_normalCoreField]
  infer_instance

section

variable {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) (S : ClosedSubgroup G)

/-- The field compositum `MΣ`, contravariantly represented by
`G_M ∩ G_Σ`. -/
def compositumWith : ClosedSubgroup G :=
  M.field ⊓ S

/-- The common compositum refinement maps below its left input field. -/
theorem compositumWith_le_left :
    (M.compositumWith S).toSubgroup ≤ M.field.toSubgroup :=
  inf_le_left

/-- The common compositum refinement maps below its right input field. -/
theorem compositumWith_le_right :
    (M.compositumWith S).toSubgroup ≤ S.toSubgroup :=
  inf_le_right

/-- The compositum of the two finite refinements has finite relative quotient. -/
theorem compositumWith_finite (hSK : S.toSubgroup ≤ K.toSubgroup) :
    Finite (S.toSubgroup ⧸
      extensionSubgroup S (M.compositumWith S) (M.compositumWith_le_right S)) := by
  let := M.finite
  have hMK : M.field.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hinter := Subgroup.relIndex_inter_ne_zero hMK S.toSubgroup
  rw [(inf_eq_right.mpr hSK)] at hinter
  apply Nat.finite_of_card_ne_zero
  change (extensionSubgroup S (M.compositumWith S)
      (M.compositumWith_le_right S)).index ≠ 0
  have hsub : extensionSubgroup S (M.compositumWith S)
      (M.compositumWith_le_right S) =
      M.field.toSubgroup.subgroupOf S.toSubgroup := by
    ext x
    rw [mem_extensionSubgroup_iff, Subgroup.mem_subgroupOf]
    change (x.1 ∈ M.field.toSubgroup ∧ x.1 ∈ S.toSubgroup) ↔
      x.1 ∈ M.field.toSubgroup
    exact and_iff_left x.2
  rw [hsub]
  simpa [Subgroup.relIndex] using hinter

/-- The compositum of normal refinements is again normal. -/
theorem compositumWith_normal (hSK : S.toSubgroup ≤ K.toSubgroup)
    [hMnormal : (extensionSubgroup K M.field M.below).Normal] :
    (extensionSubgroup S (M.compositumWith S)
      (M.compositumWith_le_right S)).Normal := by
  constructor
  intro p hp s
  let pK : K.toSubgroup := ⟨p.1, hSK p.2⟩
  let sK : K.toSubgroup := ⟨s.1, hSK s.2⟩
  have hconjM' : s.1 * p.1 * s.1⁻¹ ∈ M.field.toSubgroup := by
    have := (mem_extensionSubgroup_iff K M.field M.below _).1 (hMnormal.conj_mem pK ((mem_extensionSubgroup_iff K M.field M.below pK).2 ((mem_extensionSubgroup_iff S (M.compositumWith S)
      (M.compositumWith_le_right S) p).1 hp).1) sK)
    exact this
  apply (mem_extensionSubgroup_iff S (M.compositumWith S)
    (M.compositumWith_le_right S) _).2
  refine ⟨hconjM', ?_⟩
  exact S.toSubgroup.mul_mem
      (S.toSubgroup.mul_mem s.2 p.2) (S.toSubgroup.inv_mem s.2)

/-- The compositum of two finite extensions of `K` is finite over `K`.
Contravariantly this is the finite-index theorem for an intersection. -/
theorem compositumWith_finite_over_base (hSK : S.toSubgroup ≤ K.toSubgroup)
    [hSfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K S hSK)] :
    Finite (K.toSubgroup ⧸ extensionSubgroup K (M.compositumWith S)
      ((M.compositumWith_le_right S).trans hSK)) := by
  have hMindex : M.field.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
      (extensionSubgroup K M.field M.below) M.finite
  have hSindex : S.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
      (extensionSubgroup K S hSK) hSfinite
  apply Nat.finite_of_card_ne_zero
  change (extensionSubgroup K (M.compositumWith S)
      ((M.compositumWith_le_right S).trans hSK)).index ≠ 0
  have hsub : extensionSubgroup K (M.compositumWith S)
      ((M.compositumWith_le_right S).trans hSK) =
      (M.field.toSubgroup ⊓ S.toSubgroup).subgroupOf K.toSubgroup := by
    ext x
    rw [mem_extensionSubgroup_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rfl
  rw [hsub]
  simpa [Subgroup.relIndex] using
    Subgroup.relIndex_inf_ne_zero hMindex hSindex

end

/-- If `P | K` is finite and `P` contains the intermediate field `M`, then
`P | M` is finite. -/
alias finite_extension_of_le := ClassFormation.FiniteGaloisSubextension.finite_extension_over_intermediate

end FiniteIntermediateField

namespace DegreeData

/-- In a finite unramified Galois extension, the restriction of any
degree-one lift is a generator.  This common form is used both in the universal norm-descent lemma
and in the explicit unramified norm-quotient calculation. -/
theorem quotient_generator_of_unramified_degree_one (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [hfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (φ : K.field.toSubgroup)
    (hφ : D.normalizedDegree K φ =
      Multiplicative.ofAdd (1 : ZHat)) :
    ∀ x : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK,
      x ∈ Subgroup.zpowers (QuotientGroup.mk φ) := by
  intro x
  obtain ⟨q, hqx⟩ := D.frobeniusRestriction_surjective K L hLK x
  obtain ⟨n, _hn, hdegree⟩ := q.2
  let t := Quotient.out q.1
  have htq :=
    Quotient.out_eq' q.1
  have hdt : D.normalizedDegree K t =
      (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
    calc
      D.normalizedDegree K t =
          D.extensionNormalizedDegree K L hLK
            (QuotientGroup.mk t) := rfl
      _ = D.extensionNormalizedDegree K L hLK q.1 :=
        congrArg (D.extensionNormalizedDegree K L hLK) htq
      _ = _ := hdegree
  let z := t⁻¹ * φ ^ n
  have hzI : z ∈ D.fieldInertiaWithin K.field := by
    rw [← D.normalizedDegree_ker K]
    calc
      D.normalizedDegree K z =
          (D.normalizedDegree K t)⁻¹ *
            (D.normalizedDegree K φ) ^ n := by
        simp [z, map_mul, map_inv, map_pow]
      _ = ((Multiplicative.ofAdd (1 : ZHat)) ^ n)⁻¹ *
            (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
        rw [hdt, hφ]
      _ = 1 := by simp
  have htgen :
      (QuotientGroup.mk t : K.field.toSubgroup ⧸
        extensionSubgroup K.field L hLK) = (QuotientGroup.mk φ) ^ n := by
    apply QuotientGroup.eq.mpr
    simpa [z] using ((mem_extensionSubgroup_iff K.field L hLK z).2 (((DegreeData.AbstractExtension.mk L K.field hLK).isUnramified_iff_inertia_le D).1
      hUnramified ⟨z.2, hzI⟩))
  have htx :
      (QuotientGroup.mk t : K.field.toSubgroup ⧸
        extensionSubgroup K.field L hLK) = x := by
    calc
      QuotientGroup.mk t = D.extensionRestriction K.field L hLK
          (QuotientGroup.mk t) := rfl
      _ = D.extensionRestriction K.field L hLK q.1 :=
        congrArg (D.extensionRestriction K.field L hLK) htq
      _ = x := hqx
  have hxpow : x = (QuotientGroup.mk φ) ^ n := htx.symm.trans htgen
  rw [hxpow]
  simp

/-- A finite unramified Galois quotient is generated by the restriction of
an element of normalized degree `1`.  This is the cyclicity input needed to
use the finite-cyclic Tate complexes in the unit-cohomology axiom. -/
theorem exists_quotient_generator_of_unramified
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [hfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    ∃ g : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK,
      ∀ x, x ∈ Subgroup.zpowers g := by
  exact Exists.casesOn (normalizedDegree_surjective D K (Multiplicative.ofAdd 1)) fun φ hφ ↦ Exists.intro (↑φ) (quotient_generator_of_unramified_degree_one D K L hLK hUnramified φ hφ)

end DegreeData

end groupTheoreticRefinements

section reciprocityIndependence

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **Independence of the prime element.**
Assuming the unit-cohomology axiom, replacing the chosen prime of the Frobenius fixed field
by any other prime does not change the reciprocity class. -/
theorem reciprocityValueOfPrime_eq_reciprocityMap
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
      (hLnormal := by
        assumption))
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (hLnormal := by
          assumption) σ))
    (hπ :
      let Sigma : FiniteAbstractField G :=
        { field := D.frobeniusFixedField
            (K.toFiniteResidueAbstractField D) L hLK
            (hLnormal := by
              assumption) σ
          finite := D.frobeniusFixedField_absoluteFinite K L hLK σ }
      v.IsPrimeElement Sigma π) :
    D.reciprocityValueOfPrime A (K.toFiniteResidueAbstractField D)
        L hLK
        (hLnormal := by
          assumption)
        (hLfinite := by
          assumption) σ π =
      D.reciprocityMap A v K L hLK σ := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    assumption
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    assumption
  let S := D.frobeniusFixedField KR L hLK σ
  let E := D.maximalUnramifiedField L
  have hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let hSfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  have hπSigma : v.IsPrimeElement Sigma π := by
    simpa [Sigma, S, KR] using hπ
  let π₀ : ambientFixedAddSubgroup A S := v.chosenPrimeElement Sigma
  let u : v.unitAddSubgroup Sigma :=
    ⟨π - π₀, v.sub_chosenPrimeElement_mem_unitAddSubgroup Sigma hπSigma⟩
  rw [D.reciprocityMap_eq_chosenPrime A v K L hLK σ]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change relativeNorm A K.field S hSK π -
      relativeNorm A K.field S hSK π₀ ∈ infiniteNormSubgroup A E K.field
  rw [← map_sub]
  change relativeNorm A K.field S hSK u.1 ∈
    infiniteNormSubgroup A E K.field
  simp
  intro M
  let hEnormal :
      (extensionSubgroup K.field E
        (D.maximalUnramifiedField_le_of_le hLK)).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L hLK
  let R := M.galoisRefinement
  let P := R.compositumWith S
  have hES : E.toSubgroup ≤ S.toSubgroup :=
    D.fieldInertia_le_frobeniusFixedField KR L hLK σ
  have hPS : P.toSubgroup ≤ S.toSubgroup :=
    R.compositumWith_le_right S
  have hPK : P.toSubgroup ≤ K.field.toSubgroup := hPS.trans hSK
  have hPM : P.toSubgroup ≤ M.field.toSubgroup :=
    (R.compositumWith_le_left S).trans M.galoisRefinement_le_field
  let hRnormal :
      (extensionSubgroup K.field R.field R.below).Normal := inferInstance
  let hPSnormal :
      (extensionSubgroup S P hPS).Normal :=
    FiniteIntermediateField.compositumWith_normal R S hSK
  let hPSfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S P hPS) :=
    R.compositumWith_finite S hSK
  let hPKfinite :=
    R.compositumWith_finite_over_base S hSK
  have hSinertia : D.fieldInertia S = E := by
    dsimp [S, E]
    exact D.frobeniusFixedField_fieldInertia KR L hLK σ
  have hPSunramified :
      (DegreeData.AbstractExtension.mk P S hPS).IsUnramified D := by
    rw [(DegreeData.AbstractExtension.mk P S hPS).isUnramified_iff_inertia_le D]
    intro x hx
    change x ∈ R.field.toSubgroup ∧ x ∈ S.toSubgroup
    refine ⟨R.above ?_, hx.1⟩
    have hxI : x ∈ D.fieldInertia S := ⟨hx.1, hx.2⟩
    rw [hSinertia] at hxI
    exact hxI
  let Sresidue := Sigma.toFiniteResidueAbstractField D
  let hPSnormalResidue :
      (extensionSubgroup Sresidue.field P hPS).Normal := by
    assumption
  let hPSfiniteResidue : Finite
      (Sresidue.field.toSubgroup ⧸
        extensionSubgroup Sresidue.field P hPS) := by
    assumption
  obtain ⟨g, hg⟩ :=
    D.exists_quotient_generator_of_unramified
      Sresidue P hPS (by
        assumption)
  let hPabsolute :=
    relativeTowerQuotientFinite (baseField G) S P hPS (le_baseField S)
  let : Fintype (S.toSubgroup ⧸ extensionSubgroup S P hPS) :=
    Fintype.ofFinite _
  let Kuc : FiniteAbstractField G := Sigma
  let Euc : FiniteUnramifiedCyclicExtension D Kuc :=
    { field := P
      below := hPS
      normal := hPSnormal
      finite := hPSfinite
      generator := g
      generates := hg
      unramified := hPSunramified }
  have hzero :=
    hAxiom Kuc Euc
  obtain ⟨ε, hε⟩ :=
    v.exists_unit_relativeNorm_eq_of_tateHZero_isZero
      Euc.toFiniteAbstractFieldExtension Euc.normal
        Euc.toFiniteAbstractFieldExtension_isUnramified
        g hg hzero.1 u
  let hMfinite := M.finite
  let hPMfinite :=
    FiniteIntermediateField.finite_extension_of_le hPK M.below hPM
  change relativeNorm A K.field S hSK u.1 ∈
    (relativeNorm A K.field M.field M.below).range
  refine ⟨relativeNorm A M.field P hPM ε.1, ?_⟩
  let TMP : DegreeData.FiniteTower G :=
    { top := P
      middle := M.field
      base := K.field
      top_le_middle := hPM
      middle_le_base := M.below
      finiteTopQuotient := hPMfinite
      finiteBaseQuotient := hMfinite }
  let TSP : DegreeData.FiniteTower G :=
    { top := P
      middle := S
      base := K.field
      top_le_middle := hPS
      middle_le_base := hSK
      finiteTopQuotient := hPSfinite
      finiteBaseQuotient := hSfinite }
  calc
    relativeNorm A K.field M.field M.below
        (relativeNorm A M.field P hPM ε.1) =
        relativeNorm A K.field P hPK ε.1 :=
      TMP.norm_trans_apply A ε.1
    _ = relativeNorm A K.field S hSK
        (relativeNorm A S P hPS ε.1) :=
      (TSP.norm_trans_apply A ε.1).symm
    _ = relativeNorm A K.field S hSK u.1 := congrArg _ hε

end DegreeData

end reciprocityIndependence

end
end ClassFormation
