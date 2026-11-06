module

public import Mathlib

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.OrdinaryRayClassModulus
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Prime classes in ray class groups
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

 section
variable {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support)
include K m v hv
lemma finitePrimeFractionalIdeal_mem_primeTo
      :
    finitePrimeFractionalIdeal v ∈ rayClassPrimeToIdeals m := by
  intro w hw
  apply FractionalIdeal.count_maximal_coprime <;> aesop

/-- The class in the ray class group represented by a finite prime away from
the modulus. -/
def rayClassOfFinitePrime
       :=
  QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)
    ⟨finitePrimeFractionalIdeal v, finitePrimeFractionalIdeal_mem_primeTo m v hv⟩
end


















end ClassFieldTheory

end
