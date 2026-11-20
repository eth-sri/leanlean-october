module

public import ValuedFieldTheory.Valuation.UniqueRing
public import Mathlib.RingTheory.Polynomial.GaussLemma

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# reduction of irreducible factors

This file develops the Galois/residue input in the converse direction.  A
monic polynomial over the base valuation ring whose roots lie in a splitting
field in fact splits over every extension valuation ring: its roots are
integral over the base and hence belong to that ring.
-/

noncomputable section

open Polynomial
open UniqueFactorizationMonoid

namespace AlgebraicNumberTheory
namespace Valuations

open ValuationTheory.Valuations

universe u

end Valuations
end AlgebraicNumberTheory

end
