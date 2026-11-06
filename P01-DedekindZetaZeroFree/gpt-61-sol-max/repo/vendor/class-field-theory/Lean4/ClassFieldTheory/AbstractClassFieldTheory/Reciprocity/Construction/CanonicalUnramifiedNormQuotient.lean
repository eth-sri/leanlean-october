module

public import Mathlib

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnramifiedNormQuotient
public import GaloisCohomology.Cyclic.IntegralRepUniverse

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction: the canonical unramified valuation quotient

the valuation-quotient axiom supplies the order of `Z / nZ`.  The construction then uses the
canonical reduction inherited from `Z ⊆ ℤ̂`, rather than an arbitrary
isomorphism with `ℤ / nℤ`.  This file constructs that canonical map and
proves directly that it induces the unramified norm-quotient isomorphism
used in the unramified norm-quotient equivalence.
-/

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- Reduction modulo `n` restricted to the actual value subgroup
`Z ⊆ ℤ̂`. -/
alias canonicalValueReduction := _root_.ClassFormation.ValuationData.valueModulo

/-- The canonical value reduction sends the unit element to zero. -/
@[simp]
theorem canonicalValueReduction_one
    (v : ValuationData D A) (n : ℕ) (hn : 0 < n) :
    v.canonicalValueReduction n hn v.oneValue = 1 := by
  change zHatReduction n hn (1 : ZHat) = 1
  rfl







/-- Canonical reduction descended to `Z / nZ`. -/
alias canonicalValueQuotientHom := _root_.ClassFormation.ValuationData.canonicalQuotientMap

/-- The quotient homomorphism evaluates on a coset through canonical value reduction. -/
@[simp]
theorem canonicalValueQuotientHom_mk
    (v : ValuationData D A) (n : ℕ) (hn : 0 < n)
    (z : v.valueGroup) :
    v.canonicalValueQuotientHom n hn
      (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n) z) =
        v.canonicalValueReduction n hn z := rfl







/-- The canonical isomorphism `Z / nZ ≃ ℤ / nℤ` from the valuation-quotient axiom. -/
alias canonicalValueQuotientEquiv := _root_.ClassFormation.ValuationData.cyclic_value_quotients

section
variable (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
include v E
/-- Canonical valuation modulo `[L : K]` on `A_K`. -/
def canonicalUnramifiedValuationHom
      :
    ambientFixedAddSubgroup A E.base.field →+ ZMod (E.degree : ℕ) :=
  (v.canonicalValueReduction (E.degree : ℕ) E.degree.property).comp
    (v.valuationAt E.base)

theorem finiteNormSubgroup_le_canonicalUnramifiedValuationHom_ker
     
    (hUnramified : E.IsUnramified D) :
    finiteNormSubgroup A E.base.field E.field.field E.below ≤
      (v.canonicalUnramifiedValuationHom E).ker := by
  rintro _ ⟨a, rfl⟩
  let n := (E.degree : ℕ)
  let hn : 0 < n := E.degree.property
  have htower := v.normalizedValuation_tower E a
  have hresidueDegree :
      ((E.toFiniteResidueAbstractExtension D).residueDegree : ℕ) =
        (E.degree : ℕ) := E.residueDegree_eq_degree_of_isUnramified D hUnramified
  dsimp only at htower
  rw [hresidueDegree] at htower
  have htower' :
      n • ((v.valuationAt E.field a) : ZHat) =
        ((v.valuationAt E.base
          (relativeNorm A E.base.field E.field.field E.below a)) : ZHat) := htower
  change zHatReduction n hn
      (v.valuationAt E.base
        (relativeNorm A E.base.field E.field.field E.below a) : ZHat) = 0
  rw [← htower', map_nsmul]
  simp [n]

/-- The canonical valuation induced on the finite unramified norm
quotient. -/
def canonicalUnramifiedNormQuotientValuation
     
    (hUnramified : E.IsUnramified D) :
    FiniteNormQuotient A E.base.field E.field.field E.below →+
      ZMod (E.degree : ℕ) :=
  finiteNormQuotientLift A E.base.field E.field.field E.below
    (v.canonicalUnramifiedValuationHom E)
    (v.finiteNormSubgroup_le_canonicalUnramifiedValuationHom_ker
      E hUnramified)

/-- Valuation sends a finite norm class to its canonical unramified quotient value. -/
@[simp]
theorem canonicalUnramifiedNormQuotientValuation_finiteNormClass
     
    (hUnramified : E.IsUnramified D)
    (a : ambientFixedAddSubgroup A E.base.field) :
    v.canonicalUnramifiedNormQuotientValuation E hUnramified
      (finiteNormClass A E.base.field E.field.field E.below a) =
        v.canonicalUnramifiedValuationHom E a := rfl
end



















/-- The valuation map separates classes in the unramified norm quotient. -/
theorem canonicalUnramifiedNormQuotientValuation_injective
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup
      E.base.field E.field.field E.below).Normal)
    (hUnramified : E.IsUnramified D) :
    Function.Injective
      (v.canonicalUnramifiedNormQuotientValuation E hUnramified) := by
  let := hnormal
  let n := (E.degree : ℕ)
  let hn : 0 < n := E.degree.property
  have hkernel : ∀ q : FiniteNormQuotient A E.base.field
      E.field.field E.below,
      v.canonicalUnramifiedNormQuotientValuation E hUnramified q = 0 →
        q = 0 := by
    intro q
    refine FiniteNormQuotient.induction_on A E.base.field E.field.field
      E.below q ?_
    intro a ha
    change v.canonicalValueReduction n hn (v.valuationAt E.base a) = 0 at ha
    have hqValue :
        (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)
          (v.valuationAt E.base a)) = 0 := by
      apply (v.canonicalValueQuotientEquiv n hn).injective
      change v.canonicalValueQuotientHom n hn
          (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)
            (v.valuationAt E.base a)) =
        v.canonicalValueQuotientHom n hn 0
      rw [v.canonicalValueQuotientHom_mk, ha, map_zero]
    obtain ⟨z, haz⟩ :=
      (QuotientAddGroup.eq_zero_iff (v.valuationAt E.base a)).1 hqValue
    have haz' : v.valuationAt E.base a = n • z := haz.symm
    obtain ⟨b, hb⟩ := v.normalizedValuation_surjective E.field z
    let normb  :=
      relativeNorm A E.base.field E.field.field E.below b
    have htower := v.normalizedValuation_tower E b
    have hresidueDegree :
        ((E.toFiniteResidueAbstractExtension D).residueDegree : ℕ) =
          (E.degree : ℕ) := E.residueDegree_eq_degree_of_isUnramified D hUnramified
    dsimp only at htower
    rw [hresidueDegree] at htower
    have hnormb : v.valuationAt E.base normb = n • z := by
      apply Subtype.ext
      calc
        ((v.valuationAt E.base normb) : ZHat) =
            n • ((v.valuationAt E.field b) : ZHat) := htower.symm
        _ = n • (z : ZHat) := by rw [hb]
        _ = (((n • z)) : ZHat) := rfl
    let u : v.unitAddSubgroup E.base :=
      ⟨a - normb, by
        rw [v.mem_unitAddSubgroup_iff, map_sub, haz', hnormb, sub_self]⟩
    let KR := E.base.toFiniteResidueAbstractField D
    let hnormalKR :
        (extensionSubgroup KR.field E.field.field E.below).Normal := by
      change (extensionSubgroup E.base.field E.field.field E.below).Normal
      exact hnormal
    let hfiniteKR : Finite
        (KR.field.toSubgroup ⧸
          extensionSubgroup KR.field E.field.field E.below) := by
      change Finite (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below)
      exact E.finiteQuotient
    obtain ⟨g, hg⟩ :=
      D.exists_quotient_generator_of_unramified
        KR E.field.field E.below hUnramified
    let : Fintype (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below) :=
      Fintype.ofFinite _
    let Euc : FiniteUnramifiedCyclicExtension D E.base :=
      { field := E.field.field
        below := E.below
        normal := hnormal
        finite := E.finiteQuotient
        generator := g
        generates := hg
        unramified := by
          change E.IsUnramified D
          exact hUnramified }
    have hzero :
        CategoryTheory.Limits.IsZero
            (tateCohomology (Euc.unitRepresentation v) 0) ∧
          CategoryTheory.Limits.IsZero
            (tateCohomology (Euc.unitRepresentation v) (-1)) :=
      hAxiom E.base Euc
    obtain ⟨ε, hε⟩ :=
      v.exists_unit_relativeNorm_eq_of_tateHZero_isZero
        Euc.toFiniteAbstractFieldExtension Euc.normal
          Euc.toFiniteAbstractFieldExtension_isUnramified
          g hg hzero.1 u
    change v.unitAddSubgroup E.field at ε
    change relativeNorm A E.base.field E.field.field E.below ε.1 = u.1 at hε
    apply (finiteNormClass_eq_zero_iff A E.base.field E.field.field
      E.below a).2
    refine ⟨b + ε.1, ?_⟩
    rw [map_add, hε]
    change normb + (a - normb) = a
    abel
  intro x y hxy
  apply sub_eq_zero.mp
  apply hkernel
  rw [map_sub, hxy, sub_self]

















end ValuationData

end
end ClassFormation
