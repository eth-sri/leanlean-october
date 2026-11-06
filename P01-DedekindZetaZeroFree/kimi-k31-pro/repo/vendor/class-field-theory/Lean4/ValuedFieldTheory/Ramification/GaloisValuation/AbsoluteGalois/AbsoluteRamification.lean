module

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



/-- Provides the instance `absoluteGaloisGroupMulSemiringActionAlgebraicClosure`. -/
noncomputable instance absoluteGaloisGroupMulSemiringActionAlgebraicClosure :
    MulSemiringAction
      (Field.absoluteGaloisGroup K) (AlgebraicClosure K) := by
  change MulSemiringAction
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (AlgebraicClosure K)
  infer_instance

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

/-- The absolute decomposition subgroup is the stabilizer of the chosen
valuation subring. -/
theorem decompositionSubgroup_eq_stabilizer
    (A : ValuationSubring (AlgebraicClosure K)) :
    decompositionSubgroup K A =
      MulAction.stabilizer (Field.absoluteGaloisGroup K) A :=
  rfl

/-- Membership in the absolute decomposition subgroup is stabilization of the
chosen valuation subring. -/
@[simp] theorem mem_decompositionSubgroup_iff
    (A : ValuationSubring (AlgebraicClosure K))
    (σ : Field.absoluteGaloisGroup K) :
    σ ∈ decompositionSubgroup K A ↔ σ • A = A := by
  rw [decompositionSubgroup_eq_stabilizer, MulAction.mem_stabilizer_iff]



























/-- The absolute inertia subgroup attached to a chosen valuation subring of the
algebraic closure. -/
noncomputable abbrev inertiaSubgroup
    (A : ValuationSubring (AlgebraicClosure K)) :
    Subgroup (decompositionSubgroup K A) :=
  A.inertiaSubgroup K

/-- The absolute decomposition-group action on the residue field of the chosen
valuation subring. -/
noncomputable def decompositionResidueAction
    (A : ValuationSubring (AlgebraicClosure K)) :
    decompositionSubgroup K A →*
      (IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A) :=
  MulSemiringAction.toRingAut
    (decompositionSubgroup K A) (IsLocalRing.ResidueField A)

/-- Absolute inertia is the kernel of the decomposition action on the residue
field of the chosen valuation subring. -/
theorem inertiaSubgroup_eq_ker
    (A : ValuationSubring (AlgebraicClosure K)) :
    inertiaSubgroup K A =
      MonoidHom.ker (decompositionResidueAction K A) :=
  rfl

/-- States the theorem `decompositionResidueAction_ker`. -/
theorem decompositionResidueAction_ker
    (A : ValuationSubring (AlgebraicClosure K)) :
    MonoidHom.ker (decompositionResidueAction K A) =
      inertiaSubgroup K A :=
  rfl

/-- Provides the instance `inertiaSubgroup_normal`. -/
instance inertiaSubgroup_normal
    (A : ValuationSubring (AlgebraicClosure K)) :
    (inertiaSubgroup K A).Normal := by
  rw [inertiaSubgroup_eq_ker]
  infer_instance

/-- Membership in absolute inertia is triviality of the induced residue-field
automorphism. -/
@[simp] theorem mem_inertiaSubgroup_iff
    (A : ValuationSubring (AlgebraicClosure K))
    (σ : decompositionSubgroup K A) :
    σ ∈ inertiaSubgroup K A ↔
      decompositionResidueAction K A σ = 1 := by
  rw [inertiaSubgroup_eq_ker, MonoidHom.mem_ker]



/-- Absolute inertia as a subgroup of the ambient absolute Galois group. -/
noncomputable abbrev inertiaSubgroupInAbsolute
    (A : ValuationSubring (AlgebraicClosure K)) :
    Subgroup (Field.absoluteGaloisGroup K) :=
  Subgroup.map (decompositionSubgroup K A).subtype (inertiaSubgroup K A)



/-- Ambient absolute inertia membership is decomposition membership plus
triviality of the induced residue-field automorphism. -/
theorem mem_inertiaSubgroupInAbsolute_iff
    (A : ValuationSubring (AlgebraicClosure K))
    (σ : Field.absoluteGaloisGroup K) :
    σ ∈ inertiaSubgroupInAbsolute K A ↔
      ∃ hσ : σ ∈ decompositionSubgroup K A,
        decompositionResidueAction K A ⟨σ, hσ⟩ = 1 := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨τ.property, (mem_inertiaSubgroup_iff K A τ).1 hτ⟩
  · rintro ⟨hσ, hres⟩
    refine ⟨⟨σ, hσ⟩, ?_, rfl⟩
    exact (mem_inertiaSubgroup_iff K A ⟨σ, hσ⟩).2 hres







/-- If the absolute decomposition subgroup is all of `G_K`, every absolute
automorphism can be viewed as a decomposition element. -/
def toDecompositionSubgroupOfEqTop
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
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
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤)
    (σ : Field.absoluteGaloisGroup K) :
    (toDecompositionSubgroupOfEqTop K A hA σ :
      Field.absoluteGaloisGroup K) = σ :=
  rfl

/-- When `D_A = G_K`, the decomposition residue action becomes an ambient
absolute Galois action on the residue field. -/
noncomputable def absoluteResidueActionOfDecompositionSubgroupEqTop
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
    Field.absoluteGaloisGroup K →*
      (IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A) :=
  (decompositionResidueAction K A).comp
    (toDecompositionSubgroupOfEqTop K A hA)

/-- States the theorem `absoluteResidueActionOfDecompositionSubgroupEqTop_apply`. -/
@[simp] theorem absoluteResidueActionOfDecompositionSubgroupEqTop_apply
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤)
    (σ : Field.absoluteGaloisGroup K) :
    absoluteResidueActionOfDecompositionSubgroupEqTop K A hA σ =
      decompositionResidueAction K A
        (toDecompositionSubgroupOfEqTop K A hA σ) :=
  rfl



/-- The ambient residue action attached to `D_A = G_K` has kernel equal to
ambient absolute inertia. -/
theorem absoluteResidueActionOfDecompositionSubgroupEqTop_ker
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
    MonoidHom.ker
      (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA) =
        inertiaSubgroupInAbsolute K A := by
  ext σ
  rw [MonoidHom.mem_ker, mem_inertiaSubgroupInAbsolute_iff]
  constructor
  · intro hσ
    refine ⟨by rw [hA]; exact Subgroup.mem_top σ, ?_⟩
    simpa [absoluteResidueActionOfDecompositionSubgroupEqTop,
      toDecompositionSubgroupOfEqTop] using hσ
  · rintro ⟨hσD, hres⟩
    have hσeq :
        (toDecompositionSubgroupOfEqTop K A hA σ :
          decompositionSubgroup K A) = ⟨σ, hσD⟩ := by
      ext
      rfl
    simpa [absoluteResidueActionOfDecompositionSubgroupEqTop, hσeq] using hres



/-- Proof-dependent Henselian-DVF-facing absolute residue action.  The
Henselian top theorem is kept as an explicit argument; once
`decompositionSubgroup_eq_top_of_henselianDVF` is available, this is the stable
name used downstream without changing the residue-action target. -/
noncomputable def absoluteResidueActionOfHenselianDVF
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (hA : decompositionSubgroup K A = ⊤) :
    MonoidHom (Field.absoluteGaloisGroup K)
      (RingEquiv (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A)) :=
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









/-- Under `D_A = G_K`, ambient absolute inertia is normal in `G_K`. -/
theorem inertiaSubgroupInAbsolute_normal_of_decompositionSubgroup_eq_top
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
    (inertiaSubgroupInAbsolute K A).Normal := by
  rw [← absoluteResidueActionOfDecompositionSubgroupEqTop_ker K A hA]
  infer_instance





/-- Under `D_A = G_K`, quotienting the absolute Galois group by the kernel of
the ambient residue action gives the range of that action.  The kernel is
identified with ambient inertia by
`absoluteResidueActionOfDecompositionSubgroupEqTop_ker`. -/
noncomputable def absoluteQuotientKernelEquivResidueActionRangeOfDecompositionSubgroupEqTop
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
    Field.absoluteGaloisGroup K ⧸
        MonoidHom.ker
          (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA) ≃*
      (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA).range :=
  QuotientGroup.quotientKerEquivRange
    (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA)

/-- States the theorem `absoluteQuotientKernelEquivResidueActionRangeOfDecompositionSubgroupEqTop_mk`. -/
@[simp] theorem absoluteQuotientKernelEquivResidueActionRangeOfDecompositionSubgroupEqTop_mk
    (A : ValuationSubring (AlgebraicClosure K))
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

/-- Under `D_A = G_K`, quotienting the absolute Galois group by ambient
inertia gives the range of the ambient residue action. -/
noncomputable def absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
    letI : (inertiaSubgroupInAbsolute K A).Normal :=
      inertiaSubgroupInAbsolute_normal_of_decompositionSubgroup_eq_top K A hA
    Field.absoluteGaloisGroup K ⧸ inertiaSubgroupInAbsolute K A ≃*
      (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA).range := by
  letI : (inertiaSubgroupInAbsolute K A).Normal :=
    inertiaSubgroupInAbsolute_normal_of_decompositionSubgroup_eq_top K A hA
  exact (QuotientGroup.quotientMulEquivOfEq
      (absoluteResidueActionOfDecompositionSubgroupEqTop_ker K A hA).symm).trans
    (absoluteQuotientKernelEquivResidueActionRangeOfDecompositionSubgroupEqTop K A hA)

/-- States the theorem `absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop_mk`. -/
@[simp] theorem absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop_mk
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤)
    (σ : Field.absoluteGaloisGroup K) :
    letI : (inertiaSubgroupInAbsolute K A).Normal :=
      inertiaSubgroupInAbsolute_normal_of_decompositionSubgroup_eq_top K A hA
    absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop
        K A hA
        (QuotientGroup.mk' (inertiaSubgroupInAbsolute K A) σ) =
      (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA).rangeRestrict
        σ := by
  let : (inertiaSubgroupInAbsolute K A).Normal :=
    inertiaSubgroupInAbsolute_normal_of_decompositionSubgroup_eq_top K A hA
  change
    absoluteQuotientKernelEquivResidueActionRangeOfDecompositionSubgroupEqTop
        K A hA
        (QuotientGroup.mk'
          (MonoidHom.ker
            (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA)) σ) =
      (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA).rangeRestrict σ
  rfl

/-- States the theorem `absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop_symm_rangeRestrict`. -/
@[simp] theorem absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop_symm_rangeRestrict
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤)
    (σ : Field.absoluteGaloisGroup K) :
    letI : (inertiaSubgroupInAbsolute K A).Normal :=
      inertiaSubgroupInAbsolute_normal_of_decompositionSubgroup_eq_top K A hA
    (absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop
        K A hA).symm
        ((absoluteResidueActionOfDecompositionSubgroupEqTop K A hA).rangeRestrict
          σ) =
      QuotientGroup.mk' (inertiaSubgroupInAbsolute K A) σ := by
  let : (inertiaSubgroupInAbsolute K A).Normal :=
    inertiaSubgroupInAbsolute_normal_of_decompositionSubgroup_eq_top K A hA
  apply
    (absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop
      K A hA).injective
  rw [absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop_mk]
  exact
    (absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop
      K A hA).apply_symm_apply
      ((absoluteResidueActionOfDecompositionSubgroupEqTop K A hA).rangeRestrict σ)

/-- Absolute decomposition modulo inertia is the range of the residue-field
action. -/
noncomputable def decompositionQuotientInertiaEquivResidueActionRange
    (A : ValuationSubring (AlgebraicClosure K)) :
    decompositionSubgroup K A ⧸ inertiaSubgroup K A ≃*
      (decompositionResidueAction K A).range :=
  (QuotientGroup.quotientMulEquivOfEq
      (decompositionResidueAction_ker K A).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (decompositionResidueAction K A))

/-- States the theorem `decompositionQuotientInertiaEquivResidueActionRange_mk`. -/
@[simp] theorem decompositionQuotientInertiaEquivResidueActionRange_mk
    (A : ValuationSubring (AlgebraicClosure K))
    (σ : decompositionSubgroup K A) :
    decompositionQuotientInertiaEquivResidueActionRange K A
        (QuotientGroup.mk' (inertiaSubgroup K A) σ) =
      (decompositionResidueAction K A).rangeRestrict σ :=
  rfl

/-- States the theorem `decompositionQuotientInertiaEquivResidueActionRange_symm_rangeRestrict`. -/
@[simp] theorem decompositionQuotientInertiaEquivResidueActionRange_symm_rangeRestrict
    (A : ValuationSubring (AlgebraicClosure K))
    (σ : decompositionSubgroup K A) :
    (decompositionQuotientInertiaEquivResidueActionRange K A).symm
        ((decompositionResidueAction K A).rangeRestrict σ) =
      QuotientGroup.mk' (inertiaSubgroup K A) σ := by
  apply (decompositionQuotientInertiaEquivResidueActionRange K A).injective
  rw [decompositionQuotientInertiaEquivResidueActionRange_mk]
  exact (decompositionQuotientInertiaEquivResidueActionRange K A).apply_symm_apply
    ((decompositionResidueAction K A).rangeRestrict σ)

end AbsoluteRamification

end absoluteGaloisGroup
end Field

end

end RamificationTheory
