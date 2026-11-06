module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueRoots
public import Mathlib.Algebra.CharP.Lemmas

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


namespace LocalFieldTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField

/-!
# Teichmuller lifts

Constructs multiplicative Teichmuller representatives, and in equal characteristic the
coefficient-field section of the residue map.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- The Teichmuller representative lift from the finite residue field to the
valuation ring: `0` lifts to `0`, and nonzero residue classes lift through the
root-of-unity splitting of `κˣ`. -/
def residueTeichmullerLift [Finite F.residueField] :
    F.residueField → F.valuationSubring :=
  fun y =>
    letI := Classical.decEq F.residueField
    if hy : y = 0 then
      0
    else
      (((higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F).symm
          (Units.mk0 y hy) :
        higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
        F.valuationSubringˣ)

/-- The Teichmuller lift reduces to the residue class it lifts. -/
theorem residueMap_residueTeichmullerLift [Finite F.residueField]
    (y : F.residueField) :
    F.residueMap (higherPrincipalUnitGroup.residueTeichmullerLift F y) = y := by
  classical
  by_cases hy : y = 0
  · simp [higherPrincipalUnitGroup.residueTeichmullerLift, hy]
  · let e :=
      higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F
    have hroot :
        higherPrincipalUnitGroup.residueUnitHom F
            (((e.symm (Units.mk0 y hy) :
              higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
              F.valuationSubringˣ)) =
          Units.mk0 y hy := by
      change e (e.symm (Units.mk0 y hy)) = Units.mk0 y hy
      simp
    have hval :=
      congrArg (fun u : F.residueFieldˣ => (u : F.residueField)) hroot
    simpa [higherPrincipalUnitGroup.residueTeichmullerLift, hy, e,
      higherPrincipalUnitGroup.residueUnitHom] using hval
