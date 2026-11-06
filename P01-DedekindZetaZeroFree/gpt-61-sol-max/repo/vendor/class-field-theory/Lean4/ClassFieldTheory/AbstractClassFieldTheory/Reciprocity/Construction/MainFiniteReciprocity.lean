module

public import Mathlib

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusActionRemainder
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.ConjugatePrimeNorm
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.CorrectionSum
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusPowerSumRelation
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.NormClassRelation
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.PrimeUnitDifferences
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FiniteStageCorrections
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.ReciprocityMapMul

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

open CategoryTheory
open scoped BigOperators


/-!
# The abstract reciprocity construction, the finite reciprocity equivalence

This file carries out the descent preparation.  The reciprocity
value on the Frobenius semigroup is first mapped to the finite norm quotient.
We then compare two lifts by their positive Frobenius exponents, construct
the degree-zero quotient between unequal lifts, and prove that this quotient
has zero finite reciprocity value.  Finally reciprocity multiplicativity supplies
additivity on the Frobenius semigroup, so the lift supplied by the finite degree-quotient decomposition descends to the additive reciprocity homomorphism of the finite reciprocity equivalence.
-/

noncomputable section

section finiteReciprocityValues

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The reciprocity value of a Frobenius element after passage from the
universal norm quotient to the finite quotient by `N_{L/K} A_L`. -/
def finiteReciprocityValue (D : DegreeData G) (A : Rep ℤ G)
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK) :
    FiniteNormQuotient A K.field L hLK :=
  D.maximalUnramifiedToFiniteNormQuotient A K.field L hLK
    (D.reciprocityMap A v K L hLK σ)

section
variable (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
include D A v hAxiom K L hLK hLnormal hLfinite
/-- reciprocity multiplicativity remains additive after passage from the universal norm
quotient to the finite quotient by `N_{L/K} A_L`. -/
theorem finiteReciprocityValue_mul
     
    (α β : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK) :
    D.finiteReciprocityValue A v K L hLK (α * β) =
      D.finiteReciprocityValue A v K L hLK α +
        D.finiteReciprocityValue A v K L hLK β := by
  unfold finiteReciprocityValue
  rw [D.reciprocityMap_mul A v hAxiom K L hLK α β]
  exact map_add
    (D.maximalUnramifiedToFiniteNormQuotient A K.field L hLK) _ _































/-- The same formula for any prime element of the fixed field.  Prime-choice
independence is exactly the reciprocity construction's consequence of the unit-cohomology axiom. -/
theorem finiteReciprocityValue_eq_primeNormClass_of_isPrime
     
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (hπ :
      let Sigma : FiniteAbstractField G :=
        { field := D.frobeniusFixedField
            (K.toFiniteResidueAbstractField D) L hLK σ
          finite := D.frobeniusFixedField_absoluteFinite K L hLK σ }
      v.IsPrimeElement Sigma π) :
    let KR := K.toFiniteResidueAbstractField D
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
      D.frobeniusFixedField_finite KR L hLK σ
    D.finiteReciprocityValue A v K L hLK σ =
      finiteNormClass A K.field L hLK
        (relativeNorm A K.field S hSK π) := by
  dsimp only
  rw [finiteReciprocityValue,
    ← D.reciprocityValueOfPrime_eq_reciprocityMap
      A v hAxiom K L hLK σ π hπ]
  exact D.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass
    A K.field L hLK _
end


end DegreeData

end finiteReciprocityValues

section frobeniusLiftAlgebra

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

section
variable (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ τ : D.FrobeniusElements K L hLK)
include D K L hLK hLnormal σ τ
section
variable (hdegree : D.frobeniusExponent K L hLK σ <
      D.frobeniusExponent K L hLK τ)
include hdegree
/-- The quotient between two Frobenius lifts when the exponent of the first
is strictly smaller.  Its exponent is the positive difference. -/
def frobeniusLiftDifference  
      :
    D.FrobeniusElements K L hLK := by
  let nσ := D.frobeniusExponent K L hLK σ
  let nτ := D.frobeniusExponent K L hLK τ
  let m := nτ - nσ
  have hm : 0 < m := Nat.sub_pos_of_lt hdegree
  refine ⟨σ.1⁻¹ * τ.1, m, hm, ?_⟩
  rw [map_mul, map_inv,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK τ]
  have hle : nσ ≤ nτ := Nat.le_of_lt hdegree
  change ((Multiplicative.ofAdd (1) : ZHatMul) ^ nσ)⁻¹ *
      (Multiplicative.ofAdd (1) : ZHatMul) ^ nτ =
    (Multiplicative.ofAdd (1) : ZHatMul) ^ m
  rw [← Nat.add_sub_of_le hle, pow_add]
  simp [m]

/-- The difference of two Frobenius lifts coerces to their ambient quotient difference. -/
@[simp]
theorem frobeniusLiftDifference_coe  
      :
    (D.frobeniusLiftDifference K L hLK σ τ hdegree).1 =
      σ.1⁻¹ * τ.1 :=
  rfl

/-- Multiplying the smaller lift by its quotient recovers the larger lift. -/
theorem mul_frobeniusLiftDifference  
      :
    σ * D.frobeniusLiftDifference K L hLK σ τ hdegree = τ := by
  apply Subtype.ext
  rw [frobeniusMul_coe, frobeniusLiftDifference_coe]
  simp
end


/-- If the two lifts have the same restriction, their quotient restricts
trivially. -/
theorem frobeniusRestriction_frobeniusLiftDifference  
    (hRestriction : D.frobeniusRestriction K L hLK σ =
      D.frobeniusRestriction K L hLK τ)
    (hdegree : D.frobeniusExponent K L hLK σ <
      D.frobeniusExponent K L hLK τ) :
    D.frobeniusRestriction K L hLK
      (D.frobeniusLiftDifference K L hLK σ τ hdegree) = 1 := by
  change D.extensionRestriction K.field L hLK
    (D.frobeniusLiftDifference K L hLK σ τ hdegree).1 = 1
  rw [D.frobeniusLiftDifference_coe K L hLK σ τ hdegree]
  rw [map_mul, map_inv]
  change (D.frobeniusRestriction K L hLK σ)⁻¹ *
      D.frobeniusRestriction K L hLK τ = 1
  rw [hRestriction, inv_mul_cancel]
end


end DegreeData

end frobeniusLiftAlgebra

section trivialRestrictionValues

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- A Frobenius lift restricting trivially to `L` has zero value in the
finite norm quotient. Its fixed field contains `L`, so its norm to `K` factors through
`N_{L/K}`. -/
theorem finiteReciprocityValue_eq_zero_of_restriction_eq_one
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hσ : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ = 1) :
    D.finiteReciprocityValue A v K L hLK σ = 0 := by
  let KR := K.toFiniteResidueAbstractField D
  
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let hSL : S.toSubgroup ≤ L.toSubgroup :=
    D.frobeniusFixedField_le_of_restriction_eq_one
      KR L hLK σ hσ
  let hSfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let hSLfinite  :=
    FiniteIntermediateField.finite_extension_of_le hSK hLK hSL
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  rw [finiteReciprocityValue,
    D.reciprocityMap_eq_chosenPrime A v K L hLK σ]
  change D.maximalUnramifiedToFiniteNormQuotient A K.field L hLK
      (D.maximalUnramifiedNormClass A K.field L
        (relativeNorm A K.field S hSK (v.chosenPrimeElement Sigma))) = 0
  rw [D.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass]
  apply (finiteNormClass_eq_zero_iff A K.field L hLK _).2
  change relativeNorm A K.field S hSK (v.chosenPrimeElement Sigma) ∈
    (relativeNorm A K.field L hLK).range
  refine ⟨relativeNorm A L S hSL (v.chosenPrimeElement Sigma), ?_⟩
  let T : DegreeData.FiniteTower G :=
    { top := S
      middle := L
      base := K.field
      top_le_middle := hSL
      middle_le_base := hLK
      finiteTopQuotient := hSLfinite
      finiteBaseQuotient := hLfinite }
  apply T.norm_trans_apply

end DegreeData

end trivialRestrictionValues

section equalFrobeniusLifts

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Equal restrictions and equal positive degrees give equal Frobenius
lifts.  This is the first case in the lift-independence proof. -/
theorem frobenius_eq_of_restriction_eq_of_exponent_eq (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    {σ τ : D.FrobeniusElements K L hLK}
    (hRestriction : D.frobeniusRestriction K L hLK σ =
      D.frobeniusRestriction K L hLK τ)
    (hExponent : D.frobeniusExponent K L hLK σ =
      D.frobeniusExponent K L hLK τ) :
    σ = τ := by
  apply D.frobenius_eq_of_restriction_eq_of_degree_eq
    K L hLK hRestriction
  rw [D.extensionNormalizedDegree_frobenius_eq_pow,
    D.extensionNormalizedDegree_frobenius_eq_pow, hExponent]

end DegreeData

end equalFrobeniusLifts

section liftComparison

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The complete degree comparison. Two lifts of the same
finite automorphism are either equal, or the larger-degree lift is the
smaller one times a positive Frobenius lift which restricts trivially and
therefore has zero value in the finite norm quotient. -/
theorem finiteReciprocityHom_lift_comparison
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ τ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hRestriction : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ =
      D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK τ) :
    σ = τ ∨
      (∃ ι : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK,
        τ = σ * ι ∧
        D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK ι = 1 ∧
        D.finiteReciprocityValue A v K L hLK ι = 0) ∨
      (∃ ι : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK,
        σ = τ * ι ∧
        D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK ι = 1 ∧
        D.finiteReciprocityValue A v K L hLK ι = 0) := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := hLnormal
  rcases lt_trichotomy
      (D.frobeniusExponent KR L hLK σ)
      (D.frobeniusExponent KR L hLK τ) with hlt | heq | hgt
  · right
    left
    let ι := D.frobeniusLiftDifference KR L hLK σ τ hlt
    refine ⟨ι, ?_, ?_, ?_⟩
    · exact (D.mul_frobeniusLiftDifference KR L hLK σ τ hlt).symm
    · apply D.frobeniusRestriction_frobeniusLiftDifference <;> assumption
    · exact D.finiteReciprocityValue_eq_zero_of_restriction_eq_one
        A v K L hLK ι
        (D.frobeniusRestriction_frobeniusLiftDifference
          KR L hLK σ τ hRestriction hlt)
  · left
    apply D.frobenius_eq_of_restriction_eq_of_exponent_eq <;> assumption
  · right
    right
    let ι := D.frobeniusLiftDifference KR L hLK τ σ hgt
    refine ⟨ι, ?_, ?_, ?_⟩
    · exact (D.mul_frobeniusLiftDifference KR L hLK τ σ hgt).symm
    · apply D.frobeniusRestriction_frobeniusLiftDifference <;> aesop
    · exact D.finiteReciprocityValue_eq_zero_of_restriction_eq_one
        A v K L hLK ι
        (D.frobeniusRestriction_frobeniusLiftDifference
          KR L hLK τ σ hRestriction.symm hgt)

end DegreeData

end liftComparison

section chosenFrobeniusLifts

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

section
variable (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (q : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)
include D K L hLK hLnormal hLfinite q
/-- A specified Frobenius lift of a finite Galois automorphism, chosen from
the surjectivity in the finite degree-quotient decomposition. -/
def chosenFiniteReciprocityFrobeniusLift    :=
  Classical.choose (D.frobeniusRestriction_surjective K L hLK q)

/-- The chosen finite-reciprocity Frobenius lift restricts to the prescribed Frobenius element. -/
@[simp]
theorem frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift   :
    D.frobeniusRestriction K L hLK
      (D.chosenFiniteReciprocityFrobeniusLift K L hLK q) = q :=
  Classical.choose_spec (D.frobeniusRestriction_surjective K L hLK q)
end


end DegreeData

end chosenFrobeniusLifts

section finiteReciprocityHom

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

section
variable (D : DegreeData G) (A : Rep ℤ G)
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
include D A v K L hLK hLnormal hLfinite
/-- The canonical candidate underlying the finite reciprocity equivalence, obtained by
choosing the finite degree-quotient decomposition lift and evaluating in the finite norm
quotient.  Lift-independence and additivity are reduced to the concrete
steps above and reciprocity multiplicativity, respectively. -/
def finiteReciprocityCandidate   :
    Additive (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) →
      FiniteNormQuotient A K.field L hLK :=
  fun q => D.finiteReciprocityValue A v K L hLK
    (D.chosenFiniteReciprocityFrobeniusLift
      (K.toFiniteResidueAbstractField D) L hLK q.toMul)

/-- The finite reciprocity candidate evaluates a norm class through its chosen Frobenius lift. -/
@[simp]
theorem finiteReciprocityCandidate_apply  
    (q : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)) :
    D.finiteReciprocityCandidate A v K L hLK q =
      D.finiteReciprocityValue A v K L hLK
        (D.chosenFiniteReciprocityFrobeniusLift
          (K.toFiniteResidueAbstractField D) L hLK q.toMul) :=
  rfl



































/-- The finite reciprocity candidate sends the zero norm class to the identity. -/
@[simp]
theorem finiteReciprocityCandidate_zero   :
    D.finiteReciprocityCandidate A v K L hLK 0 = 0 := by
  apply D.finiteReciprocityValue_eq_zero_of_restriction_eq_one
  apply D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift
end







































section
variable (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hmul : ∀ α β : D.FrobeniusElements
        (K.toFiniteResidueAbstractField D) L hLK,
      D.finiteReciprocityValue A v K L hLK (α * β) =
        D.finiteReciprocityValue A v K L hLK α +
          D.finiteReciprocityValue A v K L hLK β)
include D A v K L hLK hLnormal hLfinite hmul
/-- Once reciprocity multiplicativity supplies additivity on the Frobenius semigroup,
the degree comparison proves that the finite reciprocity value is
independent of the chosen lift.  This is the full three-case argument. -/
private theorem finiteReciprocityValue_eq_of_same_restriction_of_mul
     
    (σ τ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hRestriction : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ =
      D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK τ) :
    D.finiteReciprocityValue A v K L hLK σ =
      D.finiteReciprocityValue A v K L hLK τ := by
  rcases D.finiteReciprocityHom_lift_comparison A v K L hLK
      σ τ hRestriction with h | h | h
  · rw [h]
  · rcases h with ⟨ι, hτ, _, hι⟩
    rw [hτ, hmul, hι, add_zero]
  · rcases h with ⟨ι, hσ, _, hι⟩
    rw [hσ, hmul, hι, add_zero]

/-- The finite degree-quotient decomposition candidate is additive as soon as reciprocity multiplicativity
is available.  Lift-independence is invoked for the chosen lift of a
product and the product of the two chosen lifts. -/
theorem finiteReciprocityCandidate_add_of_mul
     
    (q r : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)) :
    D.finiteReciprocityCandidate A v K L hLK (q + r) =
      D.finiteReciprocityCandidate A v K L hLK q +
        D.finiteReciprocityCandidate A v K L hLK r := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := hLnormal
  let σ₁ := D.chosenFiniteReciprocityFrobeniusLift KR L hLK q.toMul
  let σ₂ := D.chosenFiniteReciprocityFrobeniusLift KR L hLK r.toMul
  let σ₃ := D.chosenFiniteReciprocityFrobeniusLift KR L hLK (q + r).toMul
  change D.finiteReciprocityValue A v K L hLK σ₃ =
    D.finiteReciprocityValue A v K L hLK σ₁ +
      D.finiteReciprocityValue A v K L hLK σ₂
  have hRestriction :
      D.frobeniusRestriction KR L hLK σ₃ =
        D.frobeniusRestriction KR L hLK (σ₁ * σ₂) := by
    dsimp [σ₁, σ₂, σ₃]
    rw [D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift,
      D.frobeniusRestriction_mul,
      D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift,
      D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift]
  calc
    D.finiteReciprocityValue A v K L hLK σ₃ =
        D.finiteReciprocityValue A v K L hLK (σ₁ * σ₂) :=
      D.finiteReciprocityValue_eq_of_same_restriction_of_mul
        A v K L hLK hmul σ₃ (σ₁ * σ₂) hRestriction
    _ = D.finiteReciprocityValue A v K L hLK σ₁ +
        D.finiteReciprocityValue A v K L hLK σ₂ := hmul σ₁ σ₂

/-- The finite reciprocity equivalence with the semigroup-additivity input isolated.  The
final theorem discharges this input directly from reciprocity multiplicativity. -/
 def finiteReciprocityHom_of_mul
      :
    Additive (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) →+
      FiniteNormQuotient A K.field L hLK where
  toFun := D.finiteReciprocityCandidate A v K L hLK
  map_zero' := D.finiteReciprocityCandidate_zero A v K L hLK
  map_add' := D.finiteReciprocityCandidate_add_of_mul
    A v K L hLK hmul

/-- Evaluation of the conditional finite reciprocity homomorphism using any
Frobenius lift of the specified finite automorphism. -/
private theorem finiteReciprocityHom_of_mul_apply_of_frobeniusLift
     
    (q : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK))
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hσ : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ = q.toMul) :
    D.finiteReciprocityHom_of_mul A v K L hLK hmul q =
      D.finiteReciprocityValue A v K L hLK σ := by
  change D.finiteReciprocityValue A v K L hLK
      (D.chosenFiniteReciprocityFrobeniusLift
        (K.toFiniteResidueAbstractField D) L hLK q.toMul) =
    D.finiteReciprocityValue A v K L hLK σ
  apply D.finiteReciprocityValue_eq_of_same_restriction_of_mul
    A v K L hLK hmul
  rw [D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift, hσ]
end


section
variable (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
include D A v hAxiom K L hLK hLnormal hLfinite
/-- Prime-norm formula for the conditional finite reciprocity equivalence map, using
an arbitrary Frobenius lift and an arbitrary prime of its fixed field. -/
private theorem finiteReciprocityHom_of_mul_apply_eq_primeNormClass
     
    (hmul : ∀ α β : D.FrobeniusElements
        (K.toFiniteResidueAbstractField D) L hLK,
      D.finiteReciprocityValue A v K L hLK (α * β) =
        D.finiteReciprocityValue A v K L hLK α +
          D.finiteReciprocityValue A v K L hLK β)
    (q : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK))
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hσ : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ = q.toMul)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (hπ :
      let Sigma : FiniteAbstractField G :=
        { field := D.frobeniusFixedField
            (K.toFiniteResidueAbstractField D) L hLK σ
          finite := D.frobeniusFixedField_absoluteFinite K L hLK σ }
      v.IsPrimeElement Sigma π) :
    let KR := K.toFiniteResidueAbstractField D
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
      D.frobeniusFixedField_finite KR L hLK σ
    D.finiteReciprocityHom_of_mul A v K L hLK hmul q =
      finiteNormClass A K.field L hLK
        (relativeNorm A K.field S hSK π) := by
  dsimp only
  rw [D.finiteReciprocityHom_of_mul_apply_of_frobeniusLift
    A v K L hLK hmul q σ hσ]
  apply D.finiteReciprocityValue_eq_primeNormClass_of_isPrime <;> assumption

/-- **the finite reciprocity equivalence.** The prime-norm construction descends from positive
Frobenius lifts to an additive reciprocity homomorphism on the finite Galois
group. -/
def finiteReciprocityHom
       :=
  D.finiteReciprocityHom_of_mul A v K L hLK
    (D.finiteReciprocityValue_mul A v hAxiom K L hLK)

/-- Prime-norm evaluation formula for the finite reciprocity equivalence, using any prime
element in the fixed field of a chosen Frobenius lift. -/
theorem finiteReciprocityHom_apply_eq_primeNormClass
     
    (q : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK))
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hσ : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ = q.toMul)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (hπ :
      let Sigma : FiniteAbstractField G :=
        { field := D.frobeniusFixedField
            (K.toFiniteResidueAbstractField D) L hLK σ
          finite := D.frobeniusFixedField_absoluteFinite K L hLK σ }
      v.IsPrimeElement Sigma π) :
    let KR := K.toFiniteResidueAbstractField D
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
      D.frobeniusFixedField_finite KR L hLK σ
    D.finiteReciprocityHom A v hAxiom K L hLK q =
      finiteNormClass A K.field L hLK
        (relativeNorm A K.field S hSK π) := by
  apply D.finiteReciprocityHom_of_mul_apply_eq_primeNormClass <;> assumption
end


end DegreeData

end finiteReciprocityHom

/-!
# The abstract reciprocity construction, the unramified norm-quotient equivalence

This file proves the generator calculation in the unramified case: the finite reciprocity equivalence sends arithmetic Frobenius to the prime
class.  That class generates the finite norm quotient, so the resulting
reciprocity homomorphism is promoted to an additive equivalence.
-/

noncomputable section

section unramifiedFixedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

section
variable (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
include D K L hLK hnormal
/-- For an unramified `L / K`, the fixed field of the degree-one
Frobenius lift is itself unramified over `K`. -/
theorem unramifiedFrobenius_fixedField_isUnramified
     
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    (DegreeData.AbstractExtension.mk
      (D.frobeniusFixedField K L hLK
        (D.chosenUnramifiedFrobeniusLift K L hLK)) K.field
      (D.frobeniusFixedField_le K L hLK
        (D.chosenUnramifiedFrobeniusLift K L hLK))).IsUnramified D := by
  let σ := D.chosenUnramifiedFrobeniusLift K L hLK
  let S := D.frobeniusFixedField K L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le K L hLK σ
  rw [(DegreeData.AbstractExtension.mk S K.field hSK).isUnramified_iff_inertia_le D]
  intro g hg
  have hgL : g ∈ L.toSubgroup :=
    ((DegreeData.AbstractExtension.mk L K.field hLK).isUnramified_iff_inertia_le D).1
      hUnramified hg
  exact D.fieldInertia_le_frobeniusFixedField K L hLK σ
    ⟨hgL, hg.2⟩

/-- The fixed field of the degree-one lift has degree one over `K` in the
unramified case.  This is `f_{Σ/K}=d_K(φ_K)=1` together with
`[Σ:K]=f_{Σ/K}`. -/
theorem unramifiedFrobenius_fixedField_degree
     
    [hfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    let σ := D.chosenUnramifiedFrobeniusLift K L hLK
    let S := D.frobeniusFixedField K L hLK σ
    let hSK := D.frobeniusFixedField_le K L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
      D.frobeniusFixedField_finite K L hLK σ
    ((DegreeData.FiniteAbstractExtension.ofInclusion S K.field hSK).degree : ℕ) = 1 := by
  let σ := D.chosenUnramifiedFrobeniusLift K L hLK
  let S := D.frobeniusFixedField K L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le K L hLK σ
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
    D.frobeniusFixedField_finite K L hLK σ
  let E  :=
    DegreeData.FiniteAbstractExtension.ofInclusion S K.field hSK
  have hSUnramified :
      (DegreeData.AbstractExtension.mk S K.field hSK).IsUnramified D :=
    D.unramifiedFrobenius_fixedField_isUnramified
      K L hLK hUnramified
  calc
    (E.degree : ℕ) = (E.residueDegree D : ℕ) := by
      symm
      apply E.residueDegree_eq_degree_of_isUnramified <;> assumption
    _ = D.frobeniusExponent K L hLK σ :=
      D.frobeniusFixedField_residueDegreeOverBase K L hLK σ
    _ = 1 := D.chosenUnramifiedFrobeniusLift_exponent K L hLK
end


end DegreeData

end unramifiedFixedFields

section unramifiedReciprocity

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

section
variable (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
include v K L hLK hnormal hUnramified
/-- The prime-norm calculation in the unramified norm-quotient equivalence: the prime element of
`K`, included into the fixed field of the degree-one lift, has norm equal
to the original prime element. -/
theorem unramifiedFrobenius_primeNorm
      :
    let KR := K.toFiniteResidueAbstractField D
    letI hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := hnormal
    let σ := D.chosenUnramifiedFrobeniusLift KR L hLK
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
      D.frobeniusFixedField_finite KR L hLK σ
    relativeNorm A K.field S hSK
        (fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)) =
      v.chosenPrimeElement K := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := hnormal
  let σ := D.chosenUnramifiedFrobeniusLift KR L hLK
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field
        (D.frobeniusFixedField KR L hLK σ)
        (D.frobeniusFixedField_le KR L hLK σ)) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let E  :=
    DegreeData.FiniteAbstractExtension.ofInclusion S K.field hSK
  change relativeNorm A K.field S hSK
      (fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)) =
    v.chosenPrimeElement K
  calc
    relativeNorm A K.field S hSK
        (fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)) =
        (E.degree : ℕ) • v.chosenPrimeElement K := by
      have hnorm :=
        relativeNorm_fixedFieldInclusion A E (v.chosenPrimeElement K)
      change relativeNorm A K.field S hSK
          (fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)) =
        (E.degree : ℕ) • v.chosenPrimeElement K at hnorm
      exact hnorm
    _ = 1 • v.chosenPrimeElement K := by
      rw [show (E.degree : ℕ) = 1 by
        have hdegree :=
          D.unramifiedFrobenius_fixedField_degree
            KR L hLK hUnramified
        change (E.degree : ℕ) = 1 at hdegree
        exact hdegree]
    _ = v.chosenPrimeElement K := one_nsmul _

/-- The included prime element is a prime element in the fixed field used
for the degree-one Frobenius lift. -/
theorem unramifiedFrobenius_includedPrime_isPrime
      :
    let KR := K.toFiniteResidueAbstractField D
    letI hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := hnormal
    let σ := D.chosenUnramifiedFrobeniusLift KR L hLK
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
      D.frobeniusFixedField_finite KR L hLK σ
    letI : Finite ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) S (le_baseField S)) :=
      D.frobeniusFixedField_absoluteFinite K L hLK σ
    let Sigma : FiniteAbstractField G := ⟨S, inferInstance⟩
    v.IsPrimeElement Sigma
      (fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)) := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := hnormal
  let σ := D.chosenUnramifiedFrobeniusLift KR L hLK
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let hSfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  let ES : FiniteAbstractFieldExtension G :=
    { field := Sigma
      base := K
      below := hSK
      finiteQuotient := hSfinite }
  have hES : ES.IsUnramified D := by
    have hunramified :=
      D.unramifiedFrobenius_fixedField_isUnramified KR L hLK hUnramified
    change ES.IsUnramified D at hunramified
    exact hunramified
  exact v.prime_of_unramified ES hES
    (v.chosenPrimeElement K) (v.chosenPrimeElement_isPrime K)
end


section
variable (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (f : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) →+
      FiniteNormQuotient A K.field L hLK)
    (hf : f (Additive.ofMul (D.unramifiedFrobenius
        (K.toFiniteResidueAbstractField D) L hLK)) =
      finiteNormClass A K.field L hLK (v.chosenPrimeElement K))
include v hAxiom K L hLK hnormal hUnramified f hf
/-- The last generator-and-order argument in the unramified norm-quotient equivalence.  Any
homomorphism which sends the arithmetic Frobenius generator to the prime
class is bijective: the prime class generates the norm quotient, and both
finite groups have order `[L : K]`. -/
theorem unramifiedReciprocity_bijective_of_generator
      :
    Function.Bijective f := by
  let e := v.unramifiedReciprocity_valuationEquiv
    hAxiom K L hLK hUnramified
  let E  :=
    FiniteAbstractFieldExtension.ofInclusion L K hLK
  let : NeZero (E.degree : ℕ) := ⟨E.degree.property.ne'⟩
  let : Finite (FiniteNormQuotient A K.field L hLK) :=
    Finite.of_equiv (ZMod E.degree) e.symm
  have hsurj : Function.Surjective f := by
    rw [← AddMonoidHom.range_eq_top]
    apply top_unique
    rw [← v.primeClass_zmultiples_eq_top hAxiom K L hLK
      hUnramified (v.chosenPrimeElement K) (v.chosenPrimeElement_isPrime K)]
    rw [AddSubgroup.zmultiples_le]
    exact ⟨Additive.ofMul (D.unramifiedFrobenius
      (K.toFiniteResidueAbstractField D) L hLK), hf⟩
  apply (Nat.bijective_iff_surjective_and_card f).2
  refine ⟨hsurj, ?_⟩
  calc
    Nat.card (Additive
        (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)) =
        Nat.card
          (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) :=
      Nat.card_congr Additive.toMul
    _ = (extensionSubgroup K.field L hLK).index :=
      (Subgroup.index_eq_card _).symm
    _ = (E.degree : ℕ) := E.toFiniteAbstractExtension.extensionSubgroup_index_eq_degree
    _ = Nat.card (ZMod E.degree) :=
      (Nat.card_zmod _).symm
    _ = Nat.card (FiniteNormQuotient A K.field L hLK) :=
      (Nat.card_congr e.toEquiv).symm

/-- Additive-equivalence form of the generator criterion for the unramified norm-quotient equivalence.  This is useful independently of the particular construction of the
reciprocity homomorphism: a homomorphism with the required Frobenius value
is canonically promoted to an equivalence. -/
noncomputable def unramifiedReciprocity_equiv_of_generator
       :=
  AddEquiv.ofBijective f
    (v.unramifiedReciprocity_bijective_of_generator hAxiom
      K L hLK hUnramified f hf)

/-- The generator-dependent unramified reciprocity equivalence has the expected
value on each class. -/
@[simp]
theorem unramifiedReciprocity_equiv_of_generator_apply
     
    (q : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)) :
    v.unramifiedReciprocity_equiv_of_generator hAxiom K L hLK
      hUnramified f hf q = f q :=
  rfl
end


section
variable (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
include v hAxiom K L hLK hnormal hUnramified
/-- The finite reciprocity equivalence sends arithmetic Frobenius to the class of a prime
element when `L / K` is unramified.  This is the generator calculation. -/
theorem unramifiedReciprocity_frobenius_image
      :
    D.finiteReciprocityHom A v hAxiom K L hLK
        (Additive.ofMul (D.unramifiedFrobenius
          (K.toFiniteResidueAbstractField D) L hLK)) =
      finiteNormClass A K.field L hLK (v.chosenPrimeElement K) := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := hnormal
  let σ := D.chosenUnramifiedFrobeniusLift KR L hLK
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK := D.frobeniusFixedField_le KR L hLK σ
  let hSfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  let π  :=
    fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)
  have hπ : v.IsPrimeElement Sigma π := by
    apply v.unramifiedFrobenius_includedPrime_isPrime <;> assumption
  rw [D.finiteReciprocityHom_apply_eq_primeNormClass
    A v hAxiom K L hLK
      (Additive.ofMul (D.unramifiedFrobenius KR L hLK)) σ
      (rfl) π hπ]
  rw [show relativeNorm A K.field S hSK π = v.chosenPrimeElement K by
    apply v.unramifiedFrobenius_primeNorm <;> assumption]

/-- **the unramified norm-quotient equivalence.** For a finite unramified Galois extension, the
reciprocity homomorphism of the finite reciprocity equivalence is an additive equivalence. -/
noncomputable def unramifiedReciprocityEquiv
       :=
  v.unramifiedReciprocity_equiv_of_generator hAxiom K L hLK hUnramified
    (D.finiteReciprocityHom A v hAxiom K L hLK)
    (v.unramifiedReciprocity_frobenius_image hAxiom
      K L hLK hUnramified)

/-- The canonical unramified reciprocity equivalence evaluates by the normalized valuation class. -/
@[simp]
theorem unramifiedReciprocityEquiv_apply
     
    (q : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)) :
    v.unramifiedReciprocityEquiv hAxiom K L hLK hUnramified q =
      D.finiteReciprocityHom A v hAxiom K L hLK q :=
  rfl
end


end ValuationData
end unramifiedReciprocity
end
end

end ClassFormation
