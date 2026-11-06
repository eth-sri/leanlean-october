module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorLocalComparison
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.OnePlaceNormKernel
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.LocalNorm
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
public import ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlace

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/









set_option autoImplicit false

/-!
# Support of the narrow finite conductor

There are two source statements in the ramification criterion:

* a prime belongs to the support of the narrow finite conductor exactly
  when its one-place finite local conductor exponent is nonzero;
* a finite abelian local extension is ramified exactly when its concrete
  local conductor exponent is nonzero.

The local conductor criterion itself is public in
`LocalClassFieldTheory.Finite.UnramifiedConductor`.  The global
reciprocity identity `N(C_L) ∩ K_vˣ = N(L_vˣ)` identifies the two
exponents for a global extension, yielding the global conductor-support
corollary.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

namespace ConductorialSubgroup
























end ConductorialSubgroup

/-- At an unramified chosen completion, the zeroth local higher-unit
class subgroup consists of global idele-class norms. -/
theorem localHigherUnitClassSubgroup_zero_le_ideleClassNorm_range_of_chosenUnramified
    {L : Type}
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    RayClass.localHigherUnitClassSubgroup v 0 ≤
      (_root_.ideleClassNorm K L).range := by
  rintro _ ⟨x, hx, rfl⟩
  apply
    Reciprocity.finitePlaceIdeleClass_mem_ideleClassNorm_range_of_mem_chosenLocalNorm
      (K := K) (L := L) v x
  apply
    _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v hunram
  rw [← RayClass.localHigherUnitGroup_zero]
  exact hx

/-- Algebraic unramifiedness at a finite prime forces the zeroth local
higher-unit class subgroup into the global norm subgroup. -/
theorem localHigherUnitClassSubgroup_zero_le_ideleClassNorm_range_of_isUnramifiedAt
    {L : Type}
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      Algebra.IsUnramifiedAt (𝓞 K)
        (_root_.finitePlaceExtensionCentre
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v)).asIdeal) :
    RayClass.localHigherUnitClassSubgroup v 0 ≤
      (_root_.ideleClassNorm K L).range :=
  localHigherUnitClassSubgroup_zero_le_ideleClassNorm_range_of_chosenUnramified
    (K := K) (L := L) v
    (_root_.chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      (K := K) (L := L) v hunram)






















end GlobalClassFields
end GlobalClassFieldTheory

end
