module

public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealArtinQuotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Ideal Frobenius classes and the decomposition law

This file records the ideal-class-field ingredient of the decomposition
law.  A prime outside a defining modulus gives an element of the ideal
Artin quotient, and the first isomorphism theorem preserves its order.
The general unramified Galois identity `r * f = n` belongs to
`RamificationTheory.HilbertRamification.Dedekind.Basic`.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  ideleClassSubgroupNormal idealArtinKernelNormal

/-- The ideal-theoretic Frobenius class attached to a prime outside the
defining modulus.  Under global reciprocity this is the usual Frobenius
automorphism. -/
def idealFrobeniusClass
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    IdeleClassGroup K ⧸ N :=
  idealArtinMap m N hm
    (RayClass.primeToModulusIdeal m v hv)





end IdealClassFieldTheory
end GlobalClassFieldTheory

end
