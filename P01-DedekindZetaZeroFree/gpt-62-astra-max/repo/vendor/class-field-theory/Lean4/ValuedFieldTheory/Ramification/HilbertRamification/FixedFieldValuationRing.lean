module

public import ValuedFieldTheory.Ramification.HilbertRamification.UniqueExtensionIntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Restricted valuation rings on actual fixed fields

For a normal subgroup of a finite Galois group, this file uses the literal
fixed field and the restriction of the chosen top valuation ring.  Unique
extension identifies that restricted ring with the integral closure of the
base valuation ring.  It is consequently a DVR, without a completeness or
Henselian assumption.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher

open RamificationTheory.DiscreteValuationField.DVF

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

section

variable (H : Subgroup Gal(L/K))

/-- The actual fixed field of a subgroup. -/
abbrev fixedFieldDVF :=
  IntermediateField.fixedField H

/-- Restriction of the chosen top valuation ring to the actual fixed field. -/
def fixedFieldValuationSubringDVF :
    ValuationSubring (fixedFieldDVF (K := K) H) :=
  target.valuation.valuationSubring.comap
    (algebraMap (fixedFieldDVF (K := K) H) L)

/-- States the theorem `mem_fixedFieldValuationSubringDVF_iff`. -/
@[simp] theorem mem_fixedFieldValuationSubringDVF_iff (a : fixedFieldDVF (K := K) H) :
    a ∈ fixedFieldValuationSubringDVF (K := K) (target := target) H ↔
      algebraMap (fixedFieldDVF (K := K) H) L a ∈
        target.valuation.valuationSubring :=
  Iff.rfl

/-- Inclusion of the restricted fixed-field valuation ring into the top
valuation ring. -/
def fixedFieldValuationSubringDVFToTarget :
    fixedFieldValuationSubringDVF (K := K) (target := target) H →+*
      target.valuationSubring :=
  (algebraMap (fixedFieldDVF (K := K) H) L).restrict
    (fixedFieldValuationSubringDVF (K := K) (target := target) H)
    target.valuation.valuationSubring (fun _ ha => ha)

/-- States the theorem `fixedFieldValuationSubringDVFToTarget_apply_coe`. -/
@[simp] theorem fixedFieldValuationSubringDVFToTarget_apply_coe
    (a : fixedFieldValuationSubringDVF (K := K) (target := target) H) :
    ((fixedFieldValuationSubringDVFToTarget
      (K := K) (target := target) H a : target.valuationSubring) : L) =
      algebraMap (fixedFieldDVF (K := K) H) L (a : fixedFieldDVF (K := K) H) :=
  rfl

/-- The base valuation-ring map into the restricted valuation ring of the
fixed field. -/
def baseToFixedFieldValuationSubringDVF :
    base.valuationSubring →+*
      fixedFieldValuationSubringDVF (K := K) (target := target) H :=
  (algebraMap K (fixedFieldDVF (K := K) H)).restrict
    base.valuation.valuationSubring
    (fixedFieldValuationSubringDVF (K := K) (target := target) H)
    (fun a _ha => by
      change target.valuation (algebraMap K L (a : K)) ≤ 1
      exact (_root_.Valuation.HasExtension.val_map_le_one_iff
        (vR := base.valuation) (vA := target.valuation) (a : K)).2 _ha)

end

/-- Provides the instance `instAlgebraBaseFixedFieldValuationSubringDVF`. -/
noncomputable instance instAlgebraBaseFixedFieldValuationSubringDVF
    (H : Subgroup Gal(L/K)) :
    Algebra base.valuationSubring
      (fixedFieldValuationSubringDVF (K := K) (target := target) H) :=
  (baseToFixedFieldValuationSubringDVF
    (base := base) (target := target) H).toAlgebra

/-- The restricted valuation on the fixed field extends the base valuation. -/
theorem base_hasExtension_fixedFieldValuationSubringDVF
    (H : Subgroup Gal(L/K)) :
    base.valuation.HasExtension
      (fixedFieldValuationSubringDVF
        (K := K) (target := target) H).valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext a
  simp [ValuationSubring.integer_valuation, _root_.Valuation.mem_integer_iff]
  apply Valuation.HasExtension.val_map_le_one_iff

/-- Provides the instance `instBaseHasExtensionFixedFieldValuationSubringDVF`. -/
instance instBaseHasExtensionFixedFieldValuationSubringDVF
    (H : Subgroup Gal(L/K)) :
    base.valuation.HasExtension
      (fixedFieldValuationSubringDVF
        (K := K) (target := target) H).valuation :=
  base_hasExtension_fixedFieldValuationSubringDVF
    (base := base) (target := target) H

variable [FiniteDimensional K L]
variable [IsGalois K L]

/-- The quotient automorphism on the fixed field commutes with inclusion into
the top field. -/
theorem algebraMap_normalAutEquivQuotient_apply_dvf
    (H : Subgroup Gal(L/K)) [H.Normal]
    (sigma : Gal(L/K)) (a : fixedFieldDVF (K := K) H) :
    algebraMap (fixedFieldDVF (K := K) H) L
        (IsGalois.normalAutEquivQuotient H sigma a) =
      sigma (algebraMap (fixedFieldDVF (K := K) H) L a) := by
  apply AlgEquiv.restrictNormal_commutes

/-- Every automorphism of the fixed field preserves its restricted
valuation ring.  Surjectivity in the finite Galois correspondence is used
only to prove preservation; the automorphism appearing in the statement is
an automorphism of `L ^ H` itself. -/
theorem fixedFieldDVF_aut_mem_valuationSubring_iff
    (huniq :
      HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal]
    (q : Gal((fixedFieldDVF (K := K) H)/K))
    (a : fixedFieldDVF (K := K) H) :
    a ∈ fixedFieldValuationSubringDVF (K := K) (target := target) H ↔
      q a ∈ fixedFieldValuationSubringDVF (K := K) (target := target) H := by
  obtain ⟨sigma, hsigma⟩ := QuotientGroup.mk'_surjective H ((IsGalois.normalAutEquivQuotient H).symm q)
  have hq : IsGalois.normalAutEquivQuotient H sigma = q := by
    change (IsGalois.normalAutEquivQuotient H)
      ((QuotientGroup.mk' H) sigma) = q
    rw [hsigma]
    exact (IsGalois.normalAutEquivQuotient H).apply_symm_apply q
  rw [mem_fixedFieldValuationSubringDVF_iff,
    mem_fixedFieldValuationSubringDVF_iff]
  rw [← hq, algebraMap_normalAutEquivQuotient_apply_dvf]
  exact
    mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension
        huniq sigma _

variable (huniq : HasUniqueValuationExtension.{u, v, w, x, x} base target) (H : Subgroup Gal(L/K))
    [H.Normal]

/-- The canonical action of the fixed-field Galois group on its restricted
valuation ring. -/
def fixedFieldValuationSubringAutDVF
    (q : Gal((fixedFieldDVF (K := K) H)/K)) :
    fixedFieldValuationSubringDVF (K := K) (target := target) H ≃+*
      fixedFieldValuationSubringDVF (K := K) (target := target) H where
  toFun a := ⟨q (a : fixedFieldDVF (K := K) H),
    (fixedFieldDVF_aut_mem_valuationSubring_iff
      (base := base) (target := target) huniq H q _).1 a.property⟩
  invFun a := ⟨q⁻¹ (a : fixedFieldDVF (K := K) H),
    (fixedFieldDVF_aut_mem_valuationSubring_iff
      (base := base) (target := target) huniq H q⁻¹ _).1 a.property⟩
  left_inv a := by ext; simp
  right_inv a := by ext; simp
  map_mul' a b := by ext; simp
  map_add' a b := by ext; simp

/-- States the theorem `fixedFieldValuationSubringAutDVF_apply_coe`. -/
@[simp] theorem fixedFieldValuationSubringAutDVF_apply_coe
    (q : Gal((fixedFieldDVF (K := K) H)/K))
    (a : fixedFieldValuationSubringDVF (K := K) (target := target) H) :
    ((fixedFieldValuationSubringAutDVF
      (base := base) (target := target) huniq H q a :
        fixedFieldValuationSubringDVF (K := K) (target := target) H) :
      fixedFieldDVF (K := K) H) = q (a : fixedFieldDVF (K := K) H) :=
  rfl

/-- States the theorem `fixedFieldValuationSubringAutDVF_mul_apply`. -/
@[simp] theorem fixedFieldValuationSubringAutDVF_mul_apply
    (q r : Gal((fixedFieldDVF (K := K) H)/K))
    (a : fixedFieldValuationSubringDVF (K := K) (target := target) H) :
    fixedFieldValuationSubringAutDVF
        (base := base) (target := target) huniq H (q * r) a =
      fixedFieldValuationSubringAutDVF
        (base := base) (target := target) huniq H q
        (fixedFieldValuationSubringAutDVF
          (base := base) (target := target) huniq H r a) := by
  rfl

end Higher
end RamificationTheory.HilbertRamification

end
