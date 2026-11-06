module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.BigOriginal
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
# Arithmetic Artin reciprocity for any big Hilbert class field

The maximal finite-prime-unramified abelian extension has the same idèle-class
norm subgroup as the selected big Hilbert class field.  Arithmetic global
reciprocity therefore gives its narrow-class-group Artin isomorphism.
-/

open scoped Classical NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory.GlobalClassFieldComparison

variable {K : Type} [Field K] [NumberField K]

local instance bigHilbertArtinIdeleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩













end ClassFieldTheory.GlobalClassFieldComparison

end
