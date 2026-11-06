module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldMaximality
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldComparison
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertSplitting

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Prime splitting for a maximal everywhere-unramified cyclic norm quotient

Suppose a cyclic extension is unramified at every finite and infinite
place and its degree is the ordinary class number.  Its actual
idèle-class norm quotient is then the small-Hilbert reciprocity quotient.
This file transports prime Frobenius classes across that identification
and proves that trivial Frobenius is equivalent to principality of the
prime ideal.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

/-- The canonical idèle-class multiplication makes every subgroup normal. -/
theorem hilbertPrimeSplittingClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] hilbertPrimeSplittingClassGroupIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    [IsUnramifiedAtInfinitePlaces K L]









 













































end GlobalClassFields
end GlobalClassFieldTheory

end
