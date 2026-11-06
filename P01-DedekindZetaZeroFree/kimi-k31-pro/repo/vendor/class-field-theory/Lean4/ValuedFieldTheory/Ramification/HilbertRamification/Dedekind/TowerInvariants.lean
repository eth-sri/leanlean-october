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
# Hilbert ramification theory: ramification and inertia in towers

This file records the tower identities for ramification indices and inertia
degrees used in the prime-decomposition tower identity.
-/

noncomputable section

namespace HilbertRamification
namespace Dedekind

variable {A B C : Type*}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C]
variable [IsScalarTower A B C]

/-- The prime-decomposition tower identity:
ramification indices multiply in a tower. -/
theorem ramificationIdx_tower
    [IsDedekindDomain B] [IsDedekindDomain C]
    {p : Ideal A} {P : Ideal B} {Q : Ideal C}
    [P.IsPrime] [Q.IsPrime]
    (hP : Ideal.map (algebraMap B C) P ≠ ⊥)
    (hp : Ideal.map (algebraMap A C) p ≠ ⊥)
    (hPQ : Ideal.map (algebraMap B C) P ≤ Q) :
    Ideal.ramificationIdx' p Q =
      Ideal.ramificationIdx' p P *
        Ideal.ramificationIdx' P Q := by
  exact Ideal.ramificationIdx'_algebra_tower hP hp hPQ











end Dedekind
end HilbertRamification

end
