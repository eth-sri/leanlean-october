module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassPrimeIdele
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.UnramifiedPrimeArtin
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldUnramifiedMaximality
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinCompatibility
public import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# The ideal-theoretic unramified decomposition law

This file identifies the ideal Artin symbol of a prime with the genuine
global and local Frobenius automorphism.  For an unramified prime it then
combines this identification with the Dedekind-domain fundamental identity
to give the complete decomposition law:

* the order of the prime class modulo the defining ideal group;
* the order of the actual Frobenius automorphism;
* the common inertia degree of the primes above it; and
* the number of primes above it

are related by the global ideal decomposition law.
-/

open scoped NumberField Classical BigOperators

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField IsDedekindDomain
open HilbertRamification

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

attribute [local instance] idealArtinKernelNormal



























section SmallHilbertPrimeSplitting

variable {K : Type} [Field K] [NumberField K]







end SmallHilbertPrimeSplitting

end IdealClassFieldTheory
end GlobalClassFieldTheory

end
