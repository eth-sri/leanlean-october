module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.RingTheory.Invariant.Basic
public import ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring
public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Degree
public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Decomposition and inertia for finite extensions of complete DVFs

For a finite separable extension of complete discretely valued fields, the
extension of the base valuation is unique.  Consequently every
base-field automorphism stabilizes the chosen target valuation ring and the
full Galois group is the decomposition group.  Reduction then gives the
finite Galois exact sequence

`1 -> I(L/K) -> Gal(L/K) -> Gal(k_L/k_K) -> 1`.

The valuation-subring definitions and their ordinary exactness are reused
from `HilbertRamification.ValuationSubring`; this file only supplies the
complete-DVF specialization and the finite-Galois surjectivity theorem.
-/

noncomputable section

open scoped Pointwise

universe u v w x

namespace RamificationTheory.HilbertRamification.CompleteDVF

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

 instance decompositionGroupMulSemiringAction :
    MulSemiringAction
      (ValuationSubring.decompositionGroup K
        target.valuation.valuationSubring)
      target.valuationSubring := by
  change MulSemiringAction
    (target.valuation.valuationSubring.decompositionSubgroup K)
    target.valuation.valuationSubring
  infer_instance

 instance decompositionGroupResidueFieldMulSemiringAction :
    MulSemiringAction
      (ValuationSubring.decompositionGroup K
        target.valuation.valuationSubring)
      target.residueField := by
  change MulSemiringAction
    (target.valuation.valuationSubring.decompositionSubgroup K)
    (IsLocalRing.ResidueField target.valuation.valuationSubring)
  infer_instance

section ValuationUniqueness

variable [FiniteDimensional K L]

include base target

end ValuationUniqueness

section FullGaloisGroup

variable [FiniteDimensional K L]

include base target
