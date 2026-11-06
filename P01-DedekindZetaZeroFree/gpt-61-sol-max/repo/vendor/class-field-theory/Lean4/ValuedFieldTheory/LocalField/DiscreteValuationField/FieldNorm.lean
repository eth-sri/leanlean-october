module

public import Mathlib

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.LocalField.NormUnits
public import ValuedFieldTheory.LocalField.DiscreteValuationField.NormFiltration
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValueGroup

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Field norm on unit groups

This file connects mathlib's `Algebra.norm` with the unit-group and valued-norm
APIs used by local CFT.
-/

noncomputable section

universe u v w

namespace DiscreteValuationField

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]

/-- The norm subgroup of `Kˣ` attached to `L/K`. -/
noncomputable def fieldNormSubgroup  :=
  (normUnits K L).range



































/-- First-isomorphism-theorem form for the field norm on unit groups:
`Lˣ / ker(N)` is the norm subgroup of `Kˣ`. -/
noncomputable def fieldNormUnitsQuotientKerEquivFieldNormSubgroup  :=
  QuotientGroup.quotientKerEquivRange (normUnits K L)

/--
Establishes the identity `fieldNormUnitsQuotientKerEquivFieldNormSubgroup K L (QuotientGroup.mk'
(MonoidHom.ker (normUnits K L)) z) = (normUnits K L).rangeRestrict z`.
-/
@[simp] theorem fieldNormUnitsQuotientKerEquivFieldNormSubgroup_mk
    (z : Lˣ) :
    fieldNormUnitsQuotientKerEquivFieldNormSubgroup K L
        (QuotientGroup.mk'
          (MonoidHom.ker (normUnits K L)) z) =
      (normUnits K L).rangeRestrict z :=
  rfl

/--
Establishes the identity `((fieldNormUnitsQuotientKerEquivFieldNormSubgroup K L (QuotientGroup.mk'
(MonoidHom.ker (normUnits K L)) z) : fieldNormSubgroup K L) : Kˣ) = normUnits K L z`.
-/
@[simp] theorem coe_fieldNormUnitsQuotientKerEquivFieldNormSubgroup_mk
    (z : Lˣ) :
    ((fieldNormUnitsQuotientKerEquivFieldNormSubgroup K L
        (QuotientGroup.mk'
          (MonoidHom.ker (normUnits K L)) z) :
        fieldNormSubgroup K L) : Kˣ) =
      normUnits K L z :=
  rfl

/-- The quotient map `Kˣ → Kˣ / N_{L/K}(Lˣ)` attached to the field norm. -/
noncomputable def fieldNormQuotientMap  :=
  QuotientGroup.mk' (fieldNormSubgroup K L)

/--
The defining evaluation formula for `fieldNormQuotientMap` is `fieldNormQuotientMap K L x =
QuotientGroup.mk' (fieldNormSubgroup K L) x`.
-/
@[simp] theorem fieldNormQuotientMap_apply (x : Kˣ) :
    fieldNormQuotientMap K L x =
      QuotientGroup.mk' (fieldNormSubgroup K L) x :=
  rfl




















































































































































































































































































































































































































































section
variable (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
include vK vL residueDegree hformula
/-- Package a field norm as a `ValuedNorm` once the valuation formula has been
proved for the concrete extension.  The natural-number argument is not a
second source of extension-invariant data: `hformula` certifies it as the
valuation multiplier (and a source uniformizer makes that multiplier unique). -/
@[reducible] noncomputable def valuedFieldNorm
      :
    ValuedNorm vK vL where
  toHom := normUnits K L
  residueDegree := residueDegree
  valuation_formula := hformula

/--
Establishes the identity `(valuedFieldNorm K L vK vL residueDegree hformula).toHom =
normUnits K L`.
-/
@[simp] theorem valuedFieldNorm_toHom
      :
    (valuedFieldNorm K L vK vL residueDegree hformula).toHom =
      normUnits K L :=
  rfl

/--
Establishes the identity `(valuedFieldNorm K L vK vL residueDegree hformula).normSubgroup =
fieldNormSubgroup K L`.
-/
theorem valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
      :
    (valuedFieldNorm K L vK vL residueDegree hformula).normSubgroup =
      fieldNormSubgroup K L := by
  ext x
  rfl

/-- Concrete cyclic description of the field-norm quotient.  The assumptions
are the valuation formula for the field norm and the assertion that every
target valuation-zero element is already a field norm. -/
noncomputable def fieldNormQuotientEquivZMod
     
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L) :
    Kˣ ⧸ fieldNormSubgroup K L ≃* Multiplicative (ZMod residueDegree) :=
  let N := valuedFieldNorm K L vK vL residueDegree hformula
  have hnorm : N.normSubgroup = fieldNormSubgroup K L := by
    apply valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
  have hzero' : vK.zeroSubgroup ≤ N.normSubgroup := by
    rw [hnorm]
    exact hzero
  (QuotientGroup.quotientMulEquivOfEq hnorm.symm).trans
    (N.normQuotientEquivZMod hϖK hϖL hzero')
end




































































































































































































































































































































































































































































































































































































































































































































































































































/-- Concrete compatibility condition saying that the field norm maps the
`n`-th source principal-unit subgroup into the requested target level. -/
abbrev fieldNormMapsFiltrationLevels
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)  :=
  ∀ n {x : Lˣ}, x ∈ UL.principalUnitSubgroup n →
    normUnits K L x ∈ UK.principalUnitSubgroup (targetLevel n)
































section
variable (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
include UK UL targetLevel hN n
/-- The field norm restricted to a principal-unit filtration level. -/
def fieldNormMapLevelOfMapsFiltrationLevels
      :
    UL.principalUnitSubgroup n →*
      UK.principalUnitSubgroup (targetLevel n) where
  toFun x := ⟨normUnits K L x.1, hN n x.2⟩
  map_one' := by
    apply Subtype.ext
    exact (normUnits K L).map_one
  map_mul' x y := by
    apply Subtype.ext
    exact (normUnits K L).map_mul x.1 y.1

/--
The defining evaluation formula for `fieldNormMapLevelOfMapsFiltrationLevels` is
`(fieldNormMapLevelOfMapsFiltrationLevels K L UK UL targetLevel hN n x : Kˣ) = normUnits K L
x.1`.
-/
@[simp] theorem fieldNormMapLevelOfMapsFiltrationLevels_apply
     
    (x : UL.principalUnitSubgroup n) :
    (fieldNormMapLevelOfMapsFiltrationLevels K L UK UL targetLevel hN n x :
        Kˣ) =
      normUnits K L x.1 :=
  rfl

/-- The field norm descended to quotients by compatible principal-unit
filtration levels. -/
def fieldNormFiltrationQuotientMap
     
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    Lˣ ⧸ UL.principalUnitSubgroup n →*
      Kˣ ⧸ UK.principalUnitSubgroup (targetLevel n) :=
  QuotientGroup.map (UL.principalUnitSubgroup n)
    (UK.principalUnitSubgroup (targetLevel n)) (normUnits K L) (by
      intro x hx
      exact hN n hx)

/--
The defining evaluation formula for `fieldNormFiltrationQuotientMap` is
`fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n (QuotientGroup.mk x) = QuotientGroup.mk
(normUnits K L x)`.
-/
@[simp] theorem fieldNormFiltrationQuotientMap_apply_mk
     
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] (x : Lˣ) :
    fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
        (QuotientGroup.mk x) =
      QuotientGroup.mk (normUnits K L x) :=
  rfl

/--
Establishes the identity `fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
(QuotientGroup.mk' (UL.principalUnitSubgroup n) x) = QuotientGroup.mk' (UK.principalUnitSubgroup
(targetLevel n)) (normUnits K L x)`.
-/
@[simp] theorem fieldNormFiltrationQuotientMap_apply_mk'
     
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] (x : Lˣ) :
    fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
        (QuotientGroup.mk' (UL.principalUnitSubgroup n) x) =
      QuotientGroup.mk' (UK.principalUnitSubgroup (targetLevel n))
        (normUnits K L x) :=
  rfl
end































































































































/-- The preimage of a target principal-unit filtration subgroup under the
field norm. -/
def fieldNormFiltrationPreimageSubgroup
    (UK : AntitoneSubgroupFiltration Kˣ) (targetLevel : ℕ → ℕ) (n : ℕ)  :=
  (UK.principalUnitSubgroup (targetLevel n)).comap (normUnits K L)


























/--
The subgroup appearing in `(fieldNormFiltrationPreimageSubgroup K L UK targetLevel n).Normal` is
normal.
-/
instance fieldNormFiltrationPreimageSubgroup_normal
    (UK : AntitoneSubgroupFiltration Kˣ) (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    (fieldNormFiltrationPreimageSubgroup K L UK targetLevel n).Normal := by
  dsimp [fieldNormFiltrationPreimageSubgroup]
  infer_instance

/-- The class of the field-norm preimage of the target filtration subgroup
inside the source filtration quotient. -/
def fieldNormFiltrationPreimageClassInQuotient
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]  :=
  Subgroup.map (QuotientGroup.mk' (UL.principalUnitSubgroup n))
    (fieldNormFiltrationPreimageSubgroup K L UK targetLevel n)

/--
The subgroup appearing in `(fieldNormFiltrationPreimageClassInQuotient K L UK UL targetLevel
n).Normal` is normal.
-/
instance fieldNormFiltrationPreimageClassInQuotient_normal
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    (fieldNormFiltrationPreimageClassInQuotient
      K L UK UL targetLevel n).Normal := by
  dsimp [fieldNormFiltrationPreimageClassInQuotient]
  infer_instance



















































section
variable (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal]
include UK UL targetLevel hN n
/-- The kernel of the concrete field-norm filtration quotient map is the class
of the norm-preimage of the target filtration subgroup. -/
theorem fieldNormFiltrationQuotientMap_ker_eq_preimageClass
      :
    (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n).ker =
      fieldNormFiltrationPreimageClassInQuotient
        K L UK UL targetLevel n := by
  apply QuotientGroup.ker_map



















/-- First-isomorphism form of the concrete field-norm filtration quotient map,
with codomain the actual range when no surjectivity hypothesis is available. -/
noncomputable def fieldNormFiltrationQuotientModuloPreimageClassEquivRange
       :=
  (QuotientGroup.quotientMulEquivOfEq
      (fieldNormFiltrationQuotientMap_ker_eq_preimageClass
        K L UK UL targetLevel hN n).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n))

/--
Establishes the identity `fieldNormFiltrationQuotientModuloPreimageClassEquivRange K L UK UL
targetLevel hN n (QuotientGroup.mk' (fieldNormFiltrationPreimageClassInQuotient K L UK UL
targetLevel n) q) = (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n).rangeRestrict q`.
-/
@[simp] theorem fieldNormFiltrationQuotientModuloPreimageClassEquivRange_mk
     
    (q : Lˣ ⧸ UL.principalUnitSubgroup n) :
    fieldNormFiltrationQuotientModuloPreimageClassEquivRange
        K L UK UL targetLevel hN n
        (QuotientGroup.mk'
          (fieldNormFiltrationPreimageClassInQuotient
            K L UK UL targetLevel n) q) =
      (fieldNormFiltrationQuotientMap
        K L UK UL targetLevel hN n).rangeRestrict q :=
  rfl
end












































































end DiscreteValuationField

end

end LocalFieldTheory
