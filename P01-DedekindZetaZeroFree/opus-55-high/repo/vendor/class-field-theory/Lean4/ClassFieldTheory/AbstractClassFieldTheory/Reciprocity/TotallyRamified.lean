module

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity theorem: the totally ramified calculation

This file isolates the calculation.  The input from the finite reciprocity equivalence is an equality in an actual finite norm quotient.  Such an equality is
first turned into an equality of actual norms.  For the cyclic totally
ramified extension `M / M⁰`, the class-field axiom then supplies the element `a` with
`aᵒ-a = v-u`.  The element written in this construction as
`π_L^k v a^(1-σ̃)` is descended from `A_M` to the actual fixed group
`A_{M⁰}`, and its valuation is computed to be `k`.  The final invocation of
the valuation endpoint in the reciprocity reduction exact row therefore gives `k = 0`.

The only comparison not made in this file is the finite reciprocity equivalence
identification of a reciprocity value with the prime-norm class.  No
compatibility record or theorem-shaped certificate is introduced for that
comparison.
-/


open CategoryTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-! ## The linear calculation behind the fixed element -/

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The representative extracted from a zero prime-norm class can be
written as `π_L^k v` with an actual unit `v ∈ U_L`.  This is the
prime/valuation calculation: both
`L / K` and the Frobenius fixed field `Σ / K` have relative residue
degree one. -/
theorem primeNormClass_eq_zero_exists_unit_norm_eq
    (v : ValuationData D A)
    (K L S : FiniteAbstractField G)
    (hLK : L.field.toSubgroup ≤ K.field.toSubgroup)
    (hSK : S.field.toSubgroup ≤ K.field.toSubgroup)
    (hTot : (DegreeData.AbstractExtension.mk
      L.field K.field hLK).IsTotallyRamified D)
    [hLKfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field hLK)]
    [hSKfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S.field hSK)]
    (hSigmaResidue :
      ((DegreeData.FiniteAbstractExtension.ofInclusion
        S.field K.field hSK).residueDegree D : ℕ) = 1)
    (k : ℕ)
    (piS : ambientFixedAddSubgroup A S.field)
    (piL : ambientFixedAddSubgroup A L.field)
    (hpiS : v.IsPrimeElement S piS)
    (hpiL : v.IsPrimeElement L piL)
    (hclass :
      finiteNormClass A K.field L.field hLK
          (relativeNorm A K.field S.field hSK (k • piS)) = 0) :
    ∃ w : v.unitAddSubgroup L,
      relativeNorm A K.field L.field hLK (k • piL + w.1) =
        relativeNorm A K.field S.field hSK (k • piS) := by
  obtain ⟨b, hb⟩ :=
    (finiteNormClass_eq_zero_iff
      A K.field L.field hLK _).1 hclass
  let EL : FiniteAbstractFieldExtension G :=
    { field := L
      base := K
      below := hLK
      finiteQuotient := hLKfinite }
  let ES : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion S.field K hSK
  have hvalB : v.valuationAt L b = k • v.oneValue := by
    apply Subtype.ext
    have hL := v.normalizedValuation_tower EL b
    have hS := v.normalizedValuation_tower ES (k • piS)
    have hTotEL : EL.IsTotallyRamified D := by
      simpa [EL, FiniteAbstractFieldExtension.IsTotallyRamified,
        FiniteAbstractFieldExtension.toFiniteAbstractExtension] using hTot
    have hresidue : (EL.residueDegree D : ℕ) = 1 :=
      EL.toFiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified
        D hTotEL
    change (EL.residueDegree D : ℕ) •
        ((v.valuationAt L b : v.valueGroup) : ZHat) =
      ((v.valuationAt K (relativeNorm A K.field L.field hLK b) :
        v.valueGroup) : ZHat) at hL
    rw [hresidue, one_nsmul] at hL
    have hSigmaResidue' : (ES.residueDegree D : ℕ) = 1 := by
      let ES₀ :=
        DegreeData.FiniteAbstractExtension.ofInclusion S.field K.field hSK
      have hSigmaCard :
          ES₀.toAbstractExtension.relativeResidueDegreeCardinal D = 1 := by
        calc
          ES₀.toAbstractExtension.relativeResidueDegreeCardinal D =
              ((ES₀.residueDegree D : ℕ) : Cardinal) :=
            ES₀.relativeResidueDegreeCardinal_eq_coe D
          _ = 1 := by rw [hSigmaResidue]; simp
      apply Nat.cast_injective (R := Cardinal)
      unfold FiniteAbstractFieldExtension.residueDegree
      rw [← ES.toFiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe D]
      simpa [ES, ES₀, FiniteAbstractFieldExtension.toFiniteAbstractExtension,
        FiniteAbstractFieldExtension.ofInclusion,
        DegreeData.FiniteAbstractExtension.toAbstractExtension,
        DegreeData.FiniteAbstractExtension.ofInclusion] using hSigmaCard
    change (ES.residueDegree D : ℕ) •
        ((v.valuationAt S (k • piS) : v.valueGroup) : ZHat) =
      ((v.valuationAt K
        (relativeNorm A K.field S.field hSK (k • piS)) :
          v.valueGroup) : ZHat) at hS
    rw [hSigmaResidue', one_nsmul] at hS
    calc
      ((v.valuationAt L b : v.valueGroup) : ZHat) =
          ((v.valuationAt K (relativeNorm A K.field L.field hLK b) :
            v.valueGroup) : ZHat) := hL
      _ = ((v.valuationAt K
          (relativeNorm A K.field S.field hSK (k • piS)) :
            v.valueGroup) : ZHat) := by rw [hb]
      _ = ((v.valuationAt S (k • piS) : v.valueGroup) : ZHat) := hS.symm
      _ = ((k • v.oneValue : v.valueGroup) : ZHat) := by
        congr 1
        rw [map_nsmul, hpiS]
  let wL : ambientFixedAddSubgroup A L.field := b - k • piL
  have hw : v.valuationAt L wL = 0 := by
    change v.valuationAt L (b - k • piL) = 0
    rw [map_sub, map_nsmul, hvalB, hpiL, sub_self]
  let w : v.unitAddSubgroup L :=
    ⟨wL, (v.mem_unitAddSubgroup_iff L wL).2 hw⟩
  refine ⟨w, ?_⟩
  calc
    relativeNorm A K.field L.field hLK (k • piL + w.1) =
        relativeNorm A K.field L.field hLK b := by
      congr 1
      apply Subtype.ext
      dsimp [w, wL]
      abel
    _ = relativeNorm A K.field S.field hSK (k • piS) := hb

/-- Normalized valuation is invariant under the actual quotient action.
This is the quotient-representation form of the unit-cohomology axiom's
`valuationAt_normalExtensionAction`. -/
theorem valuationAt_extensionFixedRepresentation_action
    (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup
      E.base.field E.field.field E.below).Normal)
    (q : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (a : (extensionFixedRepresentation A E.base.field E.field.field
      E.below hnormal).V) :
    v.valuationAt E.field
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal
          ((extensionFixedRepresentation A E.base.field E.field.field
            E.below hnormal).ρ q a)) =
      v.valuationAt E.field
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal a) := by
  let := hnormal
  refine Quotient.inductionOn' q ?_
  intro r
  let aL : ambientFixedAddSubgroup A E.field.field :=
    extensionFixedRepresentationEquiv A E.base.field E.field.field
      E.below hnormal a
  have heq :
      extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal
          ((extensionFixedRepresentation A E.base.field E.field.field
            E.below hnormal).ρ
            (QuotientGroup.mk r) a) =
        normalExtensionAction A E.base.field E.field.field E.below
          hnormal r aL := by
    rfl
  rw [heq]
  exact v.valuationAt_normalExtensionAction E hnormal r aL

/-- The class-field axiom, in representative form: equality of two actual relative
norms yields the element `a` for which `a^σ-a = v-u`. -/
theorem abstractReciprocity_exists_hMinusOne_primitive
    (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup
      E.base.field E.field.field E.below).Normal)
    (g : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (u w : ambientFixedAddSubgroup A E.field.field)
    (hnorm : relativeNorm A E.base.field E.field.field E.below w =
      relativeNorm A E.base.field E.field.field E.below u) :
    let M := extensionFixedRepresentation A E.base.field E.field.field
      E.below hnormal
    ∃ a : M.V,
      M.ρ g a - a =
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal).symm
          (w - u) := by
  let := hnormal
  let := E.finiteQuotient
  let := Fintype.ofFinite
    (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
  let M := extensionFixedRepresentation A E.base.field E.field.field
    E.below hnormal
  let z : M.V :=
    (extensionFixedRepresentationEquiv A E.base.field E.field.field
      E.below hnormal).symm (w - u)
  have hzNorm : M.norm.hom z = 0 := by
    apply Subtype.ext
    calc
      (M.norm.hom z).1 =
          ((relativeNorm A E.base.field E.field.field E.below (w - u) :
            ambientFixedAddSubgroup A E.base.field) : A.V) :=
        extensionFixedRepresentation_norm_coe A E.base.field E.field.field
          E.below hnormal z
      _ = ((relativeNorm A E.base.field E.field.field E.below w -
          relativeNorm A E.base.field E.field.field E.below u :
            ambientFixedAddSubgroup A E.base.field) : A.V) := by
        rw [map_sub]
      _ = 0 := by simp_all
  let Ecf : FiniteCyclicSubextension E.base :=
    { field := E.field.field
      below := E.below
      normal := hnormal
      finite := E.finiteQuotient
      generator := g
      generates := hg }
  have hzero : Limits.IsZero (tateCohomology M (-1)) := by
    simpa [Ecf,
      FiniteCyclicSubextension.fixedRepresentation] using
        hcf.tateHMinusOne_isZero E.base Ecf
  obtain ⟨a, ha⟩ :=
    CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero
      M g hg hzero z hzNorm
  exact ⟨a, ha⟩
