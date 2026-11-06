module

public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Degree
public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Canonical ramification invariants

The ramification index and residue degree are the ideal-theoretic invariants of
the chosen valuation rings.  Every theorem below is stated directly in the
ambient valued-extension context; there are no compatibility aliases or
extension-marker arguments.
-/


universe u v w x

namespace LocalFieldTheory.DiscreteValuationField

open ValuationTheory.DiscreteValuationField

namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The local fundamental identity for a finite extension of valuation rings. -/
theorem degree_eq_ramificationIndex_mul_residueDegree
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.degree
        base.toDVF target.toDVF =
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
          base.toDVF target.toDVF *
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF :=
  (ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_mul_residueDegree_eq_degree
    base target).symm

/--
Establishes the inequality
`ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF target.toDVF
≠ 0`.
-/
theorem ramificationIndex_ne_zero
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
      base.toDVF target.toDVF ≠ 0 :=
  ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_ne_zero
    base target

/--
Establishes the strict bound `0 <
ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF target.toDVF`.
-/
theorem ramificationIndex_pos
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] :
    0 < ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
      base.toDVF target.toDVF :=
  Nat.pos_of_ne_zero (ramificationIndex_ne_zero base target)

/--
Establishes the strict bound `0 <
ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree base.toDVF target.toDVF`.
-/
theorem residueDegree_pos
    [Module.Finite base.valuationSubring target.valuationSubring] :
    0 < ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
      base.toDVF target.toDVF :=
  ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree_pos
    base target

/--
Establishes the identity `ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
base.toDVF target.toDVF = ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF
target.toDVF`.
-/
theorem ramificationIndex_eq_degree_of_residueDegree_eq_one
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    (h :
      ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
        base.toDVF target.toDVF = 1) :
    ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        base.toDVF target.toDVF =
      ValuationTheory.DiscreteValuationField.ValuedExtension.degree
        base.toDVF target.toDVF := by
  rw [degree_eq_ramificationIndex_mul_residueDegree base target, h, mul_one]

variable [FiniteDimensional K L]

/--
Establishes the identity `ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF
target.toDVF = ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF
target.toDVF * ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree base.toDVF
target.toDVF`.
-/
theorem degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.degree
        base.toDVF target.toDVF =
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
          base.toDVF target.toDVF *
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF :=
  (ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_mul_residueDegree_eq_degree_of_finite_separable
      base target).symm

/--
Characterizes `ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree base.toDVF
target.toDVF = 1` by the equivalent condition
`ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF target.toDVF
= ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF target.toDVF`.
-/
theorem residueDegree_eq_one_iff_ramificationIndex_eq_degree_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF = 1 ↔
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
          base.toDVF target.toDVF =
        ValuationTheory.DiscreteValuationField.ValuedExtension.degree
          base.toDVF target.toDVF := by
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.moduleFinite_target_valuationSubring_of_finite_separable
      base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      base target
  constructor
  · exact ramificationIndex_eq_degree_of_residueDegree_eq_one base target
  · intro he
    have hdegree :=
      degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable
        base target
    have hpos := ramificationIndex_pos base target
    apply Nat.eq_of_mul_eq_mul_left hpos
    omega
