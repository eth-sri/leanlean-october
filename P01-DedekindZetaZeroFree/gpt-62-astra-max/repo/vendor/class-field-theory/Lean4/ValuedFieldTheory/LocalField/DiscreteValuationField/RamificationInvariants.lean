module

public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Canonical ramification invariants

The ramification index and residue degree are the ideal-theoretic invariants of
the chosen valuation rings.  Every theorem below is stated directly in the
ambient valued-extension context; there are no compatibility aliases or
extension-marker arguments.
-/

noncomputable section

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
alias ramificationIndex_ne_zero := ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_ne_zero

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

/--
Characterizes `ValuationTheory.DiscreteValuationField.ValuedExtension.IsUnramified base.toDVF
target.toDVF` by the equivalent condition
`ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF target.toDVF
= 1`.
-/
@[simp] theorem isUnramified_iff_ramificationIndex_eq_one :
    ValuationTheory.DiscreteValuationField.ValuedExtension.IsUnramified
          base.toDVF target.toDVF ↔
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        base.toDVF target.toDVF = 1 :=
  Iff.rfl

/--
Characterizes `ValuationTheory.DiscreteValuationField.ValuedExtension.IsTotallyRamified base.toDVF
target.toDVF` by the equivalent condition
`ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree base.toDVF target.toDVF =
1`.
-/
@[simp] theorem isTotallyRamified_iff_residueDegree_eq_one :
    ValuationTheory.DiscreteValuationField.ValuedExtension.IsTotallyRamified
          base.toDVF target.toDVF ↔
      ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
        base.toDVF target.toDVF = 1 :=
  Iff.rfl

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
  let :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.moduleFinite_target_valuationSubring_of_finite_separable
      base target
  let :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      base target
  constructor
  · apply ramificationIndex_eq_degree_of_residueDegree_eq_one
  · intro he
    apply Nat.eq_of_mul_eq_mul_left (ramificationIndex_pos base target)
    grind [degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable]

end ValuedExtension
end LocalFieldTheory.DiscreteValuationField

end
