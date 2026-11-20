/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.IntegralClosure.GoingDown

@[expose] public section

namespace Ideal

/-- A minimal prime of a two-equation intersection has height at most two. -/
theorem height_le_two_of_mem_minimalPrimes_span_pair {R : Type*} [CommRing R]
    [IsNoetherianRing R] {f g : R} {p : Ideal R}
    (hp : p ∈ (Ideal.span ({f, g} : Set R)).minimalPrimes) :
    p.height ≤ 2 := by
  classical
  exact (Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    (s := ({f, g} : Finset R)) (by simpa using hp)).trans
    (by exact_mod_cast (Finset.card_le_two : ({f, g} : Finset R).card ≤ 2))

end Ideal
