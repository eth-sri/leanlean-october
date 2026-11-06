module

public import GaloisCohomology.GroupTheory.Augmentation
public import GaloisCohomology.GroupTheory.Transfer.RelativeAugmentation
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Torsion
public import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/













set_option autoImplicit false

/-!
# Witt's transfer theorem

For a finitely generated group `G` with finite abelianization, the transfer
from `G / G'` to `G' / G''` is trivial.

The proof follows Witt's group-ring argument. This file first
constructs the required right Fox coefficients directly from free words; no
presentation relations are assumed as extra input.
-/

open scoped BigOperators Pointwise

noncomputable section

namespace GroupTheory
namespace Transfer
namespace Witt

open GroupTheory.Augmentation
open Subgroup
open GroupTheory.Transfer.RelativeAugmentation

variable {G : Type*} [Group G]

/-- Finite index of the commutator gives finiteness of the
abelianization. -/
noncomputable instance finiteAbelianizationOfFiniteIndex
    [FiniteIndex (commutator G)] :
    Finite (Abelianization G) := by
  let : Fintype (Abelianization G) :=
    (commutator G).fintypeQuotientOfFiniteIndex
  exact Finite.of_fintype _

/-- The transfer between the successive commutator abelianizations
`G / G'` and `G' / G''`. -/
noncomputable def commutatorTransfer
    [FiniteIndex (commutator G)] :
    Abelianization G →* Abelianization (commutator G) :=
  Abelianization.lift
    (MonoidHom.transfer
      (Abelianization.of :
        commutator G →* Abelianization (commutator G)))

@[simp]
theorem commutatorTransfer_of
    [FiniteIndex (commutator G)] (g : G) :
    commutatorTransfer (G := G) (Abelianization.of g) =
      MonoidHom.transfer
        (Abelianization.of :
          commutator G →* Abelianization (commutator G)) g :=
  rfl

/-- The integral group-ring element `[g] - 1`. -/
def groupRingDelta (g : G) : IntegralGroupRing G :=
  MonoidAlgebra.single g 1 -
    MonoidAlgebra.single (1 : G) 1

@[simp]
theorem groupRingDelta_one :
    groupRingDelta (1 : G) = 0 := by
  simp [groupRingDelta]

theorem groupRingDelta_mul (g h : G) :
    groupRingDelta (g * h) =
      groupRingDelta g * MonoidAlgebra.single h 1 +
        groupRingDelta h := by
  have hs :
      MonoidAlgebra.single (g * h) (1 : ℤ) =
        MonoidAlgebra.single g 1 *
          MonoidAlgebra.single h 1 := by
    simp
  rw [groupRingDelta, groupRingDelta, groupRingDelta, hs,
    ← MonoidAlgebra.one_def]
  noncomm_ring



theorem groupRingDelta_inv (g : G) :
    groupRingDelta g⁻¹ =
      groupRingDelta g *
        (-MonoidAlgebra.single g⁻¹ 1) := by
  let x : IntegralGroupRing G :=
    MonoidAlgebra.single g 1
  let y : IntegralGroupRing G :=
    MonoidAlgebra.single g⁻¹ 1
  have hs :
      x * y =
        (1 : IntegralGroupRing G) := by
    simp [x, y, ← MonoidAlgebra.one_def]
  calc
    groupRingDelta g⁻¹ = y - 1 := rfl
    _ = y - x * y := by rw [hs]
    _ = (x - 1) * (-y) := by noncomm_ring
    _ = groupRingDelta g *
        (-MonoidAlgebra.single g⁻¹ 1) := rfl



@[simp]
theorem augmentation_groupRingDelta (g : G) :
    augmentation G (groupRingDelta g) = 0 := by
  simp [groupRingDelta]

/-- The exponent-sum vector of a free word. -/
def wordExponent {X : Type*} (w : FreeGroup X) : X →₀ ℤ :=
  FreeAbelianGroup.toFinsupp
    (Additive.ofMul (Abelianization.of w))

@[simp]
theorem wordExponent_one {X : Type*} :
    wordExponent (1 : FreeGroup X) = 0 := by
  exact map_zero FreeAbelianGroup.toFinsupp

@[simp]
theorem wordExponent_of {X : Type*} (x : X) :
    wordExponent (FreeGroup.of x) =
      Finsupp.single x 1 := by
  exact FreeAbelianGroup.toFinsupp_of x

@[simp]
theorem wordExponent_inv {X : Type*} (w : FreeGroup X) :
    wordExponent w⁻¹ = -wordExponent w := by
  show
    FreeAbelianGroup.toFinsupp
        (-Additive.ofMul (Abelianization.of w)) =
      -FreeAbelianGroup.toFinsupp
        (Additive.ofMul (Abelianization.of w))
  exact map_neg FreeAbelianGroup.toFinsupp _

@[simp]
theorem wordExponent_mul {X : Type*} (u v : FreeGroup X) :
    wordExponent (u * v) =
      wordExponent u + wordExponent v := by
  show
    FreeAbelianGroup.toFinsupp
        (Additive.ofMul (Abelianization.of u) +
          Additive.ofMul (Abelianization.of v)) =
      FreeAbelianGroup.toFinsupp
          (Additive.ofMul (Abelianization.of u)) +
        FreeAbelianGroup.toFinsupp
          (Additive.ofMul (Abelianization.of v))
  exact map_add FreeAbelianGroup.toFinsupp _ _

/-- A right Fox expansion of a free word, together with the fact that the
augmentation of each coefficient is the corresponding exponent sum.

This is the source-producing form needed for Witt's relation matrix. -/
theorem exists_rightFoxExpansion
    {X : Type*} [Fintype X] [DecidableEq X]
    (φ : FreeGroup X →* G) (w : FreeGroup X) :
    ∃ μ : X → IntegralGroupRing G,
      groupRingDelta (φ w) =
          ∑ i : X,
            groupRingDelta (φ (FreeGroup.of i)) * μ i ∧
      ∀ i : X,
        augmentation G (μ i) =
          wordExponent w i := by
  induction w using FreeGroup.induction_on with
  | one =>
      refine ⟨0, ?_, ?_⟩
      · simp
      · intro i
        rw [wordExponent_one]
        rfl
  | of x =>
      refine
        ⟨Pi.single x 1, ?_, ?_⟩
      · rw [Finset.sum_eq_single x]
        · simp
        · intro y _ hy
          simp [Pi.single_eq_of_ne hy]
        · simp
      · intro i
        by_cases hxi : x = i
        · subst i
          simp
        · rw [Pi.single_eq_of_ne (Ne.symm hxi), map_zero,
            wordExponent_of,
            Finsupp.single_eq_of_ne (Ne.symm hxi)]
  | inv_of x hx =>
      refine
        ⟨Pi.single x
            (-MonoidAlgebra.single
              (φ (FreeGroup.of x))⁻¹ 1),
          ?_, ?_⟩
      · rw [Finset.sum_eq_single x]
        · simpa using
            groupRingDelta_inv
              (φ (FreeGroup.of x))
        · intro y _ hy
          simp [Pi.single_eq_of_ne hy]
        · simp
      · intro i
        by_cases hxi : x = i
        · subst i
          simp
        · rw [Pi.single_eq_of_ne (Ne.symm hxi), map_zero,
            wordExponent_inv]
          change 0 = -(wordExponent (FreeGroup.of x) i)
          rw [wordExponent_of,
            Finsupp.single_eq_of_ne (Ne.symm hxi), neg_zero]
  | mul u v hu hv =>
      obtain ⟨μ, hμ, haugμ⟩ := hu
      obtain ⟨ν, hν, haugν⟩ := hv
      refine
        ⟨fun i =>
            μ i * MonoidAlgebra.single (φ v) 1 + ν i,
          ?_, ?_⟩
      · rw [map_mul, groupRingDelta_mul, hμ, hν,
          Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_add, mul_assoc]
      · intro i
        rw [map_add, map_mul, haugμ, haugν]
        simp only [augmentation_single, mul_one]
        rw [wordExponent_mul]
        rfl

/-- The map on free abelianizations induced by a free presentation. -/
def presentationMap
    {X : Type*} (φ : FreeGroup X →* G) :
    FreeAbelianGroup X →+
      Additive (Abelianization G) :=
  (Abelianization.map φ).toAdditive

@[simp]
theorem presentationMap_of
    {X : Type*} (φ : FreeGroup X →* G) (x : X) :
    presentationMap φ (FreeAbelianGroup.of x) =
      Additive.ofMul
        (Abelianization.of (φ (FreeGroup.of x))) :=
  rfl



/-- The same presentation map, regarded as a `ℤ`-linear map. -/
def presentationLinearMap
    {X : Type*} (φ : FreeGroup X →* G) :
    FreeAbelianGroup X →ₗ[ℤ]
      Additive (Abelianization G) :=
  (presentationMap φ).toIntLinearMap

@[simp]
theorem presentationLinearMap_apply
    {X : Type*} (φ : FreeGroup X →* G)
    (a : FreeAbelianGroup X) :
    presentationLinearMap φ a =
      presentationMap φ a :=
  rfl

/-- Finite abelianization makes the relation lattice of a finite free
presentation have full rank. -/
theorem presentationKernel_finrank_eq
    {X : Type*} [Fintype X]
    (φ : FreeGroup X →* G)
    [FiniteIndex (commutator G)] :
    Module.finrank ℤ (presentationLinearMap φ).ker =
      Module.finrank ℤ (FreeAbelianGroup X) := by
  let : Fintype (Abelianization G) :=
    (commutator G).fintypeQuotientOfFiniteIndex
  let f := presentationLinearMap φ
  let e := f.quotKerEquivRange
  let : Finite f.range :=
    Finite.of_injective
      ((↑) : f.range →
        Additive (Abelianization G))
      Subtype.coe_injective
  have ht :
      Module.IsTorsion ℤ f.range :=
    isAddTorsion_iff_isTorsion_int.mp
      isAddTorsion_of_finite
  have hrange :
      Module.finrank ℤ f.range = 0 :=
    Module.finrank_eq_zero_iff_isTorsion.mpr ht
  have hzero :
      Module.finrank ℤ
          ((FreeAbelianGroup X) ⧸ f.ker) = 0 :=
    e.finrank_eq.trans hrange
  change
    Module.finrank ℤ f.ker =
      Module.finrank ℤ (FreeAbelianGroup X)
  have hrank := f.ker.finrank_quotient_add_finrank
  calc
    Module.finrank ℤ f.ker =
        0 + Module.finrank ℤ f.ker := by
          rw [zero_add]
    _ = Module.finrank ℤ
          ((FreeAbelianGroup X) ⧸ f.ker) +
        Module.finrank ℤ f.ker := by
          rw [hzero]
    _ = Module.finrank ℤ (FreeAbelianGroup X) :=
      hrank

/-- A basis of the relation lattice, indexed by the generators. -/
noncomputable def relationBasis
    {X : Type*} [Fintype X]
    (φ : FreeGroup X →* G)
    [FiniteIndex (commutator G)] :
    Module.Basis X ℤ (presentationLinearMap φ).ker :=
  Submodule.smithNormalFormBotBasis
    (FreeAbelianGroup.basis X)
    (presentationKernel_finrank_eq φ)

/-- Every vector in the relation lattice is represented by an actual
relation word.  The correction from a lift to a relation is made inside
the commutator subgroup of the free group, so it does not change the
free abelianization. -/
theorem exists_relationWord
    {X : Type*}
    (φ : FreeGroup X →* G)
    (hφ : Function.Surjective φ)
    (m : (presentationLinearMap φ).ker) :
    ∃ r : FreeGroup X,
      φ r = 1 ∧
      Additive.ofMul (Abelianization.of r) =
        (m : FreeAbelianGroup X) := by
  obtain ⟨w, hw⟩ :=
    QuotientGroup.mk'_surjective
      (commutator (FreeGroup X))
      (Additive.toMul (m : FreeAbelianGroup X))
  have hw' :
      Additive.ofMul (Abelianization.of w) =
        (m : FreeAbelianGroup X) :=
    congrArg Additive.ofMul hw
  have habAdd :
      Additive.ofMul
          (Abelianization.of (φ w)) = 0 := by
    calc
      Additive.ofMul
          (Abelianization.of (φ w)) =
          presentationLinearMap φ
            (Additive.ofMul
              (Abelianization.of w)) := rfl
      _ = presentationLinearMap φ
            (m : FreeAbelianGroup X) := by
              rw [hw']
      _ = 0 := m.property
  have hab :
      Abelianization.of (φ w) = 1 := by
    exact congrArg Additive.toMul habAdd
  have hφw :
      φ w ∈ commutator G :=
    (QuotientGroup.eq_one_iff (φ w)).mp hab
  have hmap :
      (commutator (FreeGroup X)).map φ =
        commutator G := by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr hφ]
    rfl
  have hinv :
      (φ w)⁻¹ ∈
        (commutator (FreeGroup X)).map φ := by
    rw [hmap]
    exact (commutator G).inv_mem hφw
  obtain ⟨c, hc, hcφ⟩ := hinv
  have hcAb :
      Abelianization.of c = 1 :=
    (QuotientGroup.eq_one_iff c).mpr hc
  refine ⟨w * c, ?_, ?_⟩
  · rw [map_mul, hcφ]
    exact mul_inv_cancel _
  · rw [map_mul, ofMul_mul, hw', hcAb, ofMul_one]
    exact add_zero _

/-- The group-ring map induced by abelianization. -/
def abelianizationRingMap :
    IntegralGroupRing G →+*
      IntegralGroupRing (Abelianization G) :=
  MonoidAlgebra.mapDomainRingHom ℤ Abelianization.of

@[simp]
theorem abelianizationRingMap_single
    (g : G) (n : ℤ) :
    abelianizationRingMap
        (MonoidAlgebra.single g n) =
      MonoidAlgebra.single (Abelianization.of g) n := by
  simp [abelianizationRingMap]

@[simp]
theorem abelianizationRingMap_groupRingDelta
    (g : G) :
    abelianizationRingMap (groupRingDelta g) =
      groupRingDelta (Abelianization.of g) := by
  simp [groupRingDelta]

@[simp]
theorem augmentation_abelianizationRingMap
    (x : IntegralGroupRing G) :
    augmentation (Abelianization G)
        (abelianizationRingMap x) =
      augmentation G x := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
      simp [MonoidAlgebra.of]
  | add x y hx hy =>
      simp [hx, hy]
  | smul n x hx =>
      simp [hx]

/-- An additive section of the group-ring abelianization map, obtained
by choosing the quotient representative of every abelianization class. -/
def abelianizationRingSection :
    IntegralGroupRing (Abelianization G) →+
      IntegralGroupRing G where
  toFun :=
    MonoidAlgebra.mapDomain
      (fun a : Abelianization G => a.out)
  map_zero' := MonoidAlgebra.mapDomain_zero _
  map_add' := MonoidAlgebra.mapDomain_add _

@[simp]
theorem abelianizationRingSection_single
    (a : Abelianization G) (n : ℤ) :
    abelianizationRingSection
        (MonoidAlgebra.single a n) =
      MonoidAlgebra.single a.out n := by
  simp [abelianizationRingSection]

@[simp]
theorem abelianizationRingMap_section
    (z : IntegralGroupRing (Abelianization G)) :
    abelianizationRingMap
        (abelianizationRingSection z) = z := by
  induction z using MonoidAlgebra.induction_on with
  | of a =>
      simp only [MonoidAlgebra.of_apply,
        abelianizationRingSection_single,
        abelianizationRingMap_single]
      congr 1
      exact Quotient.out_eq a
  | add x y hx hy =>
      simp [hx, hy]
  | smul n x hx =>
      simp only [map_zsmul, hx]







section Presentation

variable {X : Type*} [Fintype X] [DecidableEq X]
variable (φ : FreeGroup X →* G)
variable (hφ : Function.Surjective φ)
variable [FiniteIndex (commutator G)]

/-- The chosen relation word representing the corresponding relation
basis vector. -/
noncomputable def relationWord (j : X) :
    FreeGroup X :=
  (exists_relationWord φ hφ (relationBasis φ j)).choose

omit [DecidableEq X] in
@[simp]
theorem relationWord_map (j : X) :
    φ (relationWord φ hφ j) = 1 :=
  (exists_relationWord φ hφ
    (relationBasis φ j)).choose_spec.1



/-- The chosen right Fox coefficient of the `j`-th relation at the
`i`-th generator. -/
noncomputable def foxCoefficient (i j : X) :
    IntegralGroupRing G :=
  ((exists_rightFoxExpansion φ
    (relationWord φ hφ j)).choose i)







/-- Witt's relation matrix, with entries reduced to the group ring of
the finite abelianization. -/
noncomputable def foxMatrix :
    Matrix X X
      (IntegralGroupRing (Abelianization G)) :=
  fun i j =>
    abelianizationRingMap
      (foxCoefficient φ hφ i j)

/-- A chosen lift of an adjugate-matrix entry back to `ℤ[G]`. -/
noncomputable def adjugateCoefficientLift (j k : X) :
    IntegralGroupRing G :=
  abelianizationRingSection
    ((foxMatrix φ hφ).adjugate j k)

@[simp]
theorem abelianizationRingMap_adjugateCoefficientLift
    (j k : X) :
    abelianizationRingMap
        (adjugateCoefficientLift φ hφ j k) =
      (foxMatrix φ hφ).adjugate j k :=
  abelianizationRingMap_section _

/-- A chosen lift of the determinant. -/
noncomputable def foxDeterminantLift :
    IntegralGroupRing G :=
  abelianizationRingSection (foxMatrix φ hφ).det

@[simp]
theorem abelianizationRingMap_foxDeterminantLift :
    abelianizationRingMap
        (foxDeterminantLift φ hφ) =
      (foxMatrix φ hφ).det :=
  abelianizationRingMap_section _























end Presentation

/-- The norm element of a finite group. -/
def groupNormElement
    (Q : Type*) [Group Q] [Finite Q] :
    IntegralGroupRing Q :=
  letI := Fintype.ofFinite Q
  ∑ q : Q, MonoidAlgebra.single q 1

@[simp]
theorem augmentation_groupNormElement
    (Q : Type*) [Group Q] [Finite Q] :
    augmentation Q (groupNormElement Q) =
      Nat.card Q := by
  let := Fintype.ofFinite Q
  simp [groupNormElement, Nat.card_eq_fintype_card]





section PresentationNorm

variable {X : Type*} [Fintype X] [DecidableEq X]
variable (φ : FreeGroup X →* G)
variable (hφ : Function.Surjective φ)
variable [FiniteIndex (commutator G)]













end PresentationNorm



end Witt
end Transfer
end GroupTheory

end
