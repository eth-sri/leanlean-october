module

public import ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveUniformizer
public import ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusEvaluation

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Residue Frobenius on completed p-adic Lubin--Tate levels

The completed multiplicative Lubin--Tate level is totally ramified over its
completed-unramified coefficient field.  Hence the canonical residue map is
an isomorphism.  Under this identification, every unit-indexed completed
Frobenius lift induces the arithmetic Frobenius `x ↦ x ^ p` on the residue
field.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ResidueField
open ValuationTheory.DiscreteValuationField.ValuedExtension

section

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- The completed multiplicative level has residue degree one over the
completed-unramified coefficient field. -/
theorem padicCompletedLevel_residueDegree_eq_one :
    residueDegree
        (padicCompletedUnramifiedCompleteDVF p).toDVF
        (padicCompletedLevelCompleteDVF p n).toDVF = 1 := by
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let : IsScalarTower base.valuationSubring
      target.valuationSubring (padicCompletedLevelField p n) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact
    (residueDegree_eq_one_iff_ramificationIndex_eq_degree_of_finite_separable
      base target).2
      (by
        apply padicCompletedLevel_ramificationIndex_eq_degree)

/-- The target residue field has linear rank one over the
completed-unramified residue field. -/
theorem padicCompletedLevel_residueField_finrank_eq_one :
    Module.finrank
        (padicCompletedUnramifiedCompleteDVF p).residueField
        (padicCompletedLevelCompleteDVF p n).residueField = 1 := by
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let : IsScalarTower base.valuationSubring
      target.valuationSubring (padicCompletedLevelField p n) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let :=
    maximalIdeal_liesOver base target
  have hfinrank :
      residueDegree base.toDVF target.toDVF =
        Module.finrank base.residueField target.residueField := by
    rw [residueDegree_eq_finrank_quotient base target]
    rfl
  calc
    Module.finrank base.residueField target.residueField =
        residueDegree base.toDVF target.toDVF :=
      hfinrank.symm
    _ = 1 := by
      exact padicCompletedLevel_residueDegree_eq_one p n

/-- The canonical residue map from the completed-unramified coefficient
field onto the completed level is surjective. -/
theorem padicCompletedLevel_residueMap_surjective :
    Function.Surjective
      (residueMap
        (padicCompletedUnramifiedCompleteDVF p).toDVF
        (padicCompletedLevelCompleteDVF p n).toDVF) := by
  exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp (padicCompletedLevel_residueField_finrank_eq_one p n)).right

/-- The canonical residue-field equivalence from the completed-unramified
coefficient field to a completed multiplicative level. -/
noncomputable def padicCompletedLevelResidueFieldEquiv :
    (padicCompletedUnramifiedCompleteDVF p).residueField ≃+*
      (padicCompletedLevelCompleteDVF p n).residueField :=
  residueFieldEquivOfSurjective
    (padicCompletedUnramifiedCompleteDVF p).toDVF
    (padicCompletedLevelCompleteDVF p n).toDVF
    (padicCompletedLevel_residueMap_surjective p n)

/-- The completed-level residue equivalence evaluates by the canonical
residue map. -/
@[simp]
theorem padicCompletedLevelResidueFieldEquiv_apply
    (x : (padicCompletedUnramifiedCompleteDVF p).residueField) :
    padicCompletedLevelResidueFieldEquiv p n x =
      residueMap
        (padicCompletedUnramifiedCompleteDVF p).toDVF
        (padicCompletedLevelCompleteDVF p n).toDVF x :=
  rfl

end

private theorem
    padicCompletedUnramifiedWitt_residue_frobenius_eq_pow
    (p : ℕ) [Fact p.Prime]
    (a : padicCompletedUnramifiedWittRing p) :
    IsLocalRing.residue (padicCompletedUnramifiedWittRing p)
        (WittVector.frobenius a) =
      IsLocalRing.residue (padicCompletedUnramifiedWittRing p) a ^ p := by
  calc
    _ =
        IsLocalRing.residue (padicCompletedUnramifiedWittRing p)
          (a ^ p) := by
      rw [residue_eq_residue_iff_sub_mem_maximalIdeal,
        padicCompletedUnramifiedWittRing_maximalIdeal,
        ← WittVector.ker_constantCoeff]
      simp [map_sub, map_pow, WittVector.constantCoeff_apply]
    _ =
        IsLocalRing.residue (padicCompletedUnramifiedWittRing p) a ^ p := by
      rw [map_pow]

/-- The actual residue action induced by every unit-indexed completed
Frobenius lift is the arithmetic Frobenius `x ↦ x ^ p`. -/
theorem
    padicCompletedUnitFrobeniusIntegerEquiv_residue_apply_eq_pow
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicLocalField
      p).valuationSubringˣ)
    (x : (padicCompletedLevelCompleteDVF p n).residueField) :
    IsLocalRing.ResidueField.mapEquiv
        (padicCompletedUnitFrobeniusIntegerEquiv p n u) x =
      x ^ p := by
  let W := padicCompletedUnramifiedWittRing p
  let target := padicCompletedLevelCompleteDVF p n
  let coefficientResidueEquiv :=
    (IsLocalRing.ResidueField.mapEquiv (padicCompletedUnramifiedWittRingEquivValuationSubring p)).trans
      (padicCompletedLevelResidueFieldEquiv p n)
  have hcoefficient (a : W) :
      coefficientResidueEquiv (IsLocalRing.residue W a) =
        target.residueMap
          (padicCompletedLevelWittCoefficientHom p n a) := by
    simp only [coefficientResidueEquiv, RingEquiv.trans_apply,
      IsLocalRing.ResidueField.mapEquiv_apply]
    rfl
  obtain ⟨z, rfl⟩ := coefficientResidueEquiv.surjective x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
  calc
    _ =
        target.residueMap
          (padicCompletedUnitFrobeniusIntegerEquiv p n u
            (padicCompletedLevelWittCoefficientHom p n a)) := by
      rfl
    _ =
        target.residueMap
          (padicCompletedLevelWittCoefficientHom p n
            (WittVector.frobenius a)) := by
      rw [padicCompletedUnitFrobeniusIntegerEquiv_wittCoefficientHom]
    _ =
        coefficientResidueEquiv
          (IsLocalRing.residue W (WittVector.frobenius a)) :=
      (hcoefficient (WittVector.frobenius a)).symm
    _ =
        coefficientResidueEquiv
          (IsLocalRing.residue W a ^ p) := by
      rw [padicCompletedUnramifiedWitt_residue_frobenius_eq_pow]
    _ = coefficientResidueEquiv (IsLocalRing.residue W a) ^ p := by
      rw [map_pow]

end LubinTate

end
