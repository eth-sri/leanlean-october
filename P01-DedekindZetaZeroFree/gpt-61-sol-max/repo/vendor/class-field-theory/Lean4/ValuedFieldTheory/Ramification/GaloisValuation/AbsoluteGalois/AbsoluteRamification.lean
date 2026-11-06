module

public import Mathlib

public import ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

namespace RamificationTheory

open ValuationTheory

/-!
# Absolute Galois ramification

This file develops the decomposition and inertia subgroups of an absolute
Galois group after the finite-level valuation-restriction layer.
-/

noncomputable section

universe u v w z

namespace Field
namespace absoluteGaloisGroup

open scoped Topology Pointwise
open CategoryTheory

section AbsoluteRamification

variable (K : Type u) [Field K]

















/-- The absolute decomposition subgroup attached to a chosen valuation subring
of the algebraic closure. -/
abbrev decompositionSubgroup
    (A : ValuationSubring (AlgebraicClosure K)) :
    Subgroup (Field.absoluteGaloisGroup K) :=
  A.decompositionSubgroup K

/-- Provides the instance `decompositionSubgroupMulSemiringAction`. -/
instance decompositionSubgroupMulSemiringAction
    (A : ValuationSubring (AlgebraicClosure K)) :
    MulSemiringAction (decompositionSubgroup K A) A := by
  change MulSemiringAction (A.decompositionSubgroup K) A
  infer_instance










































































































































































































































































































































































































section
variable (A : ValuationSubring (AlgebraicClosure K))
include A
/-- The absolute inertia subgroup attached to a chosen valuation subring of the
algebraic closure. -/
noncomputable abbrev inertiaSubgroup
      :
    Subgroup (decompositionSubgroup K A) :=
  A.inertiaSubgroup K

/-- The absolute decomposition-group action on the residue field of the chosen
valuation subring. -/
noncomputable def decompositionResidueAction
      :
    decompositionSubgroup K A →*
      (IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A) :=
  MulSemiringAction.toRingAut
    (decompositionSubgroup K A) (IsLocalRing.ResidueField A)

/-- Absolute inertia is the kernel of the decomposition action on the residue
field of the chosen valuation subring. -/
theorem inertiaSubgroup_eq_ker
      :
    inertiaSubgroup K A =
      MonoidHom.ker (decompositionResidueAction K A) :=
  rfl

/-- States the theorem `decompositionResidueAction_ker`. -/
theorem decompositionResidueAction_ker
      :
    MonoidHom.ker (decompositionResidueAction K A) =
      inertiaSubgroup K A :=
  rfl
end


/-- Provides the instance `inertiaSubgroup_normal`. -/
instance inertiaSubgroup_normal
    (A : ValuationSubring (AlgebraicClosure K)) :
    (inertiaSubgroup K A).Normal := by
  rw [inertiaSubgroup_eq_ker]
  infer_instance




































































































































section
variable (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤)
include A hA
/-- If the absolute decomposition subgroup is all of `G_K`, every absolute
automorphism can be viewed as a decomposition element. -/
def toDecompositionSubgroupOfEqTop
      :
    Field.absoluteGaloisGroup K →*
      decompositionSubgroup K A where
  toFun σ := ⟨σ, by rw [hA]; exact Subgroup.mem_top σ⟩
  map_one' := by
    ext
    rfl
  map_mul' _ _ := by
    ext
    rfl

/-- States the theorem `toDecompositionSubgroupOfEqTop_coe`. -/
@[simp] theorem toDecompositionSubgroupOfEqTop_coe
     
    (σ : Field.absoluteGaloisGroup K) :
    (toDecompositionSubgroupOfEqTop K A hA σ :
      Field.absoluteGaloisGroup K) = σ :=
  rfl

/-- When `D_A = G_K`, the decomposition residue action becomes an ambient
absolute Galois action on the residue field. -/
noncomputable def absoluteResidueActionOfDecompositionSubgroupEqTop
      :
    Field.absoluteGaloisGroup K →*
      (IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A) :=
  (decompositionResidueAction K A).comp
    (toDecompositionSubgroupOfEqTop K A hA)

/-- States the theorem `absoluteResidueActionOfDecompositionSubgroupEqTop_apply`. -/
@[simp] theorem absoluteResidueActionOfDecompositionSubgroupEqTop_apply
     
    (σ : Field.absoluteGaloisGroup K) :
    absoluteResidueActionOfDecompositionSubgroupEqTop K A hA σ =
      decompositionResidueAction K A
        (toDecompositionSubgroupOfEqTop K A hA σ) :=
  rfl
end

























































/-- Proof-dependent Henselian-DVF-facing absolute residue action.  The
Henselian top theorem is kept as an explicit argument; once
`decompositionSubgroup_eq_top_of_henselianDVF` is available, this is the stable
name used downstream without changing the residue-action target. -/
noncomputable def absoluteResidueActionOfHenselianDVF
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (hA : decompositionSubgroup K A = ⊤)  :=
  absoluteResidueActionOfDecompositionSubgroupEqTop K A hA

/-- States the theorem `absoluteResidueActionOfHenselianDVF_apply`. -/
@[simp] theorem absoluteResidueActionOfHenselianDVF_apply
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (hA : decompositionSubgroup K A = ⊤)
    (sigma : Field.absoluteGaloisGroup K) :
    absoluteResidueActionOfHenselianDVF K F A hA sigma =
      absoluteResidueActionOfDecompositionSubgroupEqTop K A hA sigma :=
  rfl


















































































section
variable (A : ValuationSubring (AlgebraicClosure K))
include A
/-- Under `D_A = G_K`, quotienting the absolute Galois group by the kernel of
the ambient residue action gives the range of that action.  The kernel is
identified with ambient inertia by
`absoluteResidueActionOfDecompositionSubgroupEqTop_ker`. -/
noncomputable def absoluteQuotientKernelEquivResidueActionRangeOfDecompositionSubgroupEqTop
     
    (hA : decompositionSubgroup K A = ⊤)  :=
  QuotientGroup.quotientKerEquivRange
    (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA)

/-- States the theorem `absoluteQuotientKernelEquivResidueActionRangeOfDecompositionSubgroupEqTop_mk`. -/
@[simp] theorem absoluteQuotientKernelEquivResidueActionRangeOfDecompositionSubgroupEqTop_mk
     
    (hA : decompositionSubgroup K A = ⊤)
    (σ : Field.absoluteGaloisGroup K) :
    absoluteQuotientKernelEquivResidueActionRangeOfDecompositionSubgroupEqTop
        K A hA
        (QuotientGroup.mk'
          (MonoidHom.ker
            (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA)) σ) =
      (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA).rangeRestrict
        σ :=
  rfl






























































/-- Absolute decomposition modulo inertia is the range of the residue-field
action. -/
noncomputable def decompositionQuotientInertiaEquivResidueActionRange
       :=
  (QuotientGroup.quotientMulEquivOfEq
      (decompositionResidueAction_ker K A).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (decompositionResidueAction K A))

/-- States the theorem `decompositionQuotientInertiaEquivResidueActionRange_mk`. -/
@[simp] theorem decompositionQuotientInertiaEquivResidueActionRange_mk
     
    (σ : decompositionSubgroup K A) :
    decompositionQuotientInertiaEquivResidueActionRange K A
        (QuotientGroup.mk' (inertiaSubgroup K A) σ) =
      (decompositionResidueAction K A).rangeRestrict σ :=
  rfl
end














end AbsoluteRamification

end absoluteGaloisGroup
end Field

end

end RamificationTheory
