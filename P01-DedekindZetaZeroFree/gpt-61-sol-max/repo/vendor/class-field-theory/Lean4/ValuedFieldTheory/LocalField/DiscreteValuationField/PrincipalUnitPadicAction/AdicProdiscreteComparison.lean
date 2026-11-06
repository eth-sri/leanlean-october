module

public import Mathlib

public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.InverseLimitTopology

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Adic and prodiscrete principal-unit models

The adic topology on first principal units agrees with the prodiscrete topology carried
by the inverse limit of finite quotient coordinates.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

namespace Internal

section
variable (F : CompleteDVF.{u, v} K)
include F
/-- Internal comparison from the type-level adic model to the raw
instance-parametric carrier. -/
noncomputable def adicPrincipalUnitsHomeomorphUnderlying
      :
    letI : TopologicalSpace F.valuationSubring :=
      (uniformizerPowerIdeal
        (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
    AdicPrincipalUnits F ≃ₜ
      Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) := by
  letI  :=
    (uniformizerPowerIdeal
      (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
  exact (AdicPrincipalUnits.homeomorph F).trans
    (WithTopology.homeomorph
      (α := Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1))
      (topology := principalUnitAdicTopology F))















/-- Internal comparison from the type-level prodiscrete model to the raw
instance-parametric inverse-limit carrier. -/
noncomputable def principalUnitProdiscreteLimitHomeomorphUnderlying
      :
    letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
      fun _ => ⊥
    PrincipalUnitProdiscreteLimit F ≃ₜ
      Additive (Internal.principalUnitInverseLimitCarrier F) := by
  letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⊥
  exact (PrincipalUnitProdiscreteLimit.homeomorph F).trans
    (WithTopology.homeomorph
      (α := Additive (Internal.principalUnitInverseLimitCarrier F))
      (topology := principalUnitProdiscreteTopology F))













end


end Internal

/-- The only bridge where the raw instance-parametric presentations are
installed.  Public topology APIs use `AdicPrincipalUnits` and
`PrincipalUnitProdiscreteLimit` instead. -/
noncomputable def adicPrincipalUnitsHomeomorphProdiscreteLimit
    (F : CompleteDVF.{u, v} K) :
    AdicPrincipalUnits F ≃ₜ PrincipalUnitProdiscreteLimit F := by
  letI  :=
    (uniformizerPowerIdeal
      (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
  letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⊥
  let source := Internal.adicPrincipalUnitsHomeomorphUnderlying F
  let target := Internal.principalUnitProdiscreteLimitHomeomorphUnderlying F
  exact source.trans
    ((Internal.principalUnitAddHomeomorphInverseLimitCarrier F).trans target.symm)















/-- The prodiscrete principal-unit limit is Hausdorff. -/
noncomputable instance principalUnitProdiscreteLimitT2Space
    (F : CompleteDVF.{u, v} K) :
    T2Space (PrincipalUnitProdiscreteLimit F) := by
  let : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⊥
  let : (n : ℕ) → DiscreteTopology (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⟨rfl⟩
  let : (n : ℕ) → T2Space (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => DiscreteTopology.toT2Space
  let : T2Space (Internal.principalUnitInverseLimitCarrier F) := by
    infer_instance
  let : T2Space (Additive (Internal.principalUnitInverseLimitCarrier F)) := by
    change T2Space (Internal.principalUnitInverseLimitCarrier F)
    infer_instance
  exact T2Space.of_injective_continuous
    (Internal.principalUnitProdiscreteLimitHomeomorphUnderlying F).injective
    (Internal.principalUnitProdiscreteLimitHomeomorphUnderlying F).continuous

section
variable (F : CompleteDVF.{u, v} K)
include F
/-- Algebraic form of the canonical identification between adic principal
units and their prodiscrete limit. -/
noncomputable def adicPrincipalUnitsAddEquivProdiscreteLimit
       :=
  (AdicPrincipalUnits.addEquiv F).trans
    ((principalUnitAddEquivInverseLimitCarrier F).trans
      (PrincipalUnitProdiscreteLimit.addEquiv F).symm)













/-- Additive topological form of
`adicPrincipalUnitsHomeomorphProdiscreteLimit`. -/
noncomputable def adicPrincipalUnitsContinuousAddEquivProdiscreteLimit
      :
    AdicPrincipalUnits F ≃ₜ+ PrincipalUnitProdiscreteLimit F :=
  ContinuousAddEquiv.mk'
    (adicPrincipalUnitsHomeomorphProdiscreteLimit F)
    (fun x y => (adicPrincipalUnitsAddEquivProdiscreteLimit F).map_add x y)
end







end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
