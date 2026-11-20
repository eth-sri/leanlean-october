module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowClassGroup
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# The narrow ray class group and the narrow ideal class group

At the modulus with no finite part and every real place selected, the
ideal-theoretic ray class group is the narrow class group.  The comparison
preserves the class of each finite prime.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

variable {K : Type u} [Field K] [NumberField K]

end ClassFieldTheory

end
