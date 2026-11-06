module

public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.OrdinaryClassGroupComparison
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.SmallOriginal
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldComparison
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/










set_option autoImplicit false

/-!
# Arithmetic Artin reciprocity for any small Hilbert class field

The intrinsic small Hilbert class field is unique up to a base-field
equivalence.  Therefore its actual idèle-class norm subgroup is the same as
that of the selected class field.  Arithmetic global reciprocity then gives
the Artin map, with its prime normalization obtained from the prime idèle.
-/

open scoped Classical NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory.SmallHilbertClassFieldComparison

variable {K : Type} [Field K] [NumberField K]

local instance smallHilbertArtinIdeleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩



 







end ClassFieldTheory.SmallHilbertClassFieldComparison

end
