module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Relrank
public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Field-theoretic composita for finite valued extensions

The actual common-top part of Abhyankar's lemma needs valuation data on the
compositum `L ⊔ K'` inside a common ambient field.  This file records the
purely field-theoretic source facts before any valuation extension is added:
finite-dimensionality over either branch, degree bounds and equalities, the
intersection degree square, and separability of the common top.
-/

noncomputable section

universe u v

namespace DiscreteValuationField
namespace FieldCompositum

open scoped TensorProduct

variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]

instance supRightAlgebra (L K' : IntermediateField K Ω) :
    Algebra K' (L ⊔ K' : IntermediateField K Ω) :=
  (IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right)).toAlgebra

instance supLeftAlgebra (L K' : IntermediateField K Ω) :
    Algebra L (L ⊔ K' : IntermediateField K Ω) :=
  (IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left)).toAlgebra

instance supRightIsScalarTower (L K' : IntermediateField K Ω) :
    IsScalarTower K K' (L ⊔ K' : IntermediateField K Ω) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  ext
  rfl

instance supLeftIsScalarTower (L K' : IntermediateField K Ω) :
    IsScalarTower K L (L ⊔ K' : IntermediateField K Ω) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  ext
  rfl
