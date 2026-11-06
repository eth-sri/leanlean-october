module
public import GuthMaynard.NativeSource.GuthMaynard.QuadraticDivisor
public import Mathlib.Data.Int.GCD

@[expose] public section

/-!
# Chinese-remainder factorization of Kloosterman sums

This is the first recursive dependency of DFI equation (25).  It proves the
exact Bézout-scaled factorization of the standard additive character, moves
units and their inverses through the Chinese remainder equivalence, and then
factors the complete Kloosterman sum at coprime moduli.
-/

open Complex
open scoped BigOperators
open Classical

namespace GuthMaynard.NativeMoment

end GuthMaynard.NativeMoment
