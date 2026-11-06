module

public import Mathlib

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.LocalField.Analytic.ContinuousFieldUnitLog
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Topology.Instances.ZMod

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Finite and uniformizer factors of the field-unit group

This file isolates the two factors of the field-unit structure theorem which do not depend on
the structure theorem for first principal units.  The Teichmuller factor is
the cyclic group of order `q - 1`, with its (necessarily discrete) topology.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

variable {K : Type u} [Field K]

/-- A continuous algebraic equivalence from a compact group to a Hausdorff
group is automatically a topological group equivalence. -/
noncomputable def continuousMulEquivOfCompactToT2
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [Mul A] [Mul B] [CompactSpace A] [T2Space B]
    (e : A ≃* B) (he : Continuous e)  :=
  ContinuousMulEquiv.mk'
    (he.homeoOfEquivCompactToT2 (f := e.toEquiv)) e.map_mul

/-- Additive version of `continuousMulEquivOfCompactToT2`. -/
noncomputable def continuousAddEquivOfCompactToT2
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [Add A] [Add B] [CompactSpace A] [T2Space B]
    (e : A ≃+ B) (he : Continuous e)  :=
  ContinuousAddEquiv.mk'
    (he.homeoOfEquivCompactToT2 (f := e.toEquiv)) e.map_add




























/-- The Teichmuller roots form, algebraically and topologically, the cyclic
group of order `q - 1`, where `q` is the residue-field cardinality. -/
noncomputable def residueRootsOfUnityContinuousMulEquivZMod
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField] :
    letI : Valued K (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F
    Multiplicative (ZMod (Nat.card F.residueField - 1)) ≃ₜ*
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F := by
  letI  :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F
  rw [← Nat.card_units F.residueField]
  let e  :=
    (zmodCyclicMulEquiv
      (G := F.residueFieldˣ) inferInstance).trans
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F).symm
  haveI  :=
    Finite.of_equiv F.residueFieldˣ
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F).symm.toEquiv
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

































































































































































































































end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
