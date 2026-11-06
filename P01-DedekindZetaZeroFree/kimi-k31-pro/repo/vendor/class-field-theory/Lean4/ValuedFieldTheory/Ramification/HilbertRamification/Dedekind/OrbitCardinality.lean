module

public import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Hilbert ramification theory: prime-decomposition cardinalities

This file records the parts of the prime-decomposition tower identity that are
already available from the Dedekind-domain Galois action and mathlib's
ramification/inertia API.
-/

noncomputable section

namespace HilbertRamification
namespace Dedekind

open scoped Pointwise
open Algebra Module

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]





















/-- The separable-residue cardinality relation:
when the residue extension is separable, the inertia group has cardinality
equal to the ramification index of the chosen prime. -/
theorem inertia_card_eq_ramificationIdx
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [IsTorsionFree A B]
    (p : Ideal A) (P : Ideal B) [P.LiesOver p] [P.IsPrime] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] (hp : p ≠ ⊥) :
    Nat.card (inertiaGroup P G) =
      P.ramificationIdx A := by
  rw [dedekindRamification_inertia_card_eq_ramificationIdxIn
    (A := A) (B := B) p P G hp]
  exact Ideal.ramificationIdxIn_eq_ramificationIdx p P G



end Dedekind
end HilbertRamification

end
