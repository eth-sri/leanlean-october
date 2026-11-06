module

public import Mathlib

public import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFields

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Hilbert ramification theory: decomposition and inertia tower

This file contains the group-theoretic fixed-field part of the tower
`Z_P ⊆ T_P ⊆ L` in prime-decomposition theory.
-/

noncomputable section

namespace HilbertRamification
namespace Dedekind

open Algebra Module

variable {A B K L : Type*}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Field K] [Field L] [Algebra K L]
variable (G : Type*) [Group G] [MulSemiringAction G L] [SMulCommClass G K L]

/-- prime-decomposition theory:
the inertia field, viewed as an intermediate field over the decomposition
field. -/
abbrev inertiaFieldOverDecompositionField
    (P : Ideal B) [MulSemiringAction G B]  :=
  IntermediateField.extendScalars
    (decompositionField_le_inertiaField (K := K) (L := L) G P)

variable {G}











variable (G)

section
variable (P : Ideal B) [MulSemiringAction G B]
include P
/-- Restricting the inertia field over the decomposition field back to `K`
recovers the inertia field over `K`. -/
@[simp]
theorem inertiaFieldOverDecompositionField_restrictScalars
      :
    (inertiaFieldOverDecompositionField (K := K) (L := L) G P).restrictScalars K =
      inertiaField (K := K) (L := L) G P :=
  rfl

/-- The prime-decomposition tower identity:
identify the decomposition group with `Gal(L/Z_P)`. -/
def dedekindTower_decompositionGroupEquivGalDecompositionField
     
    [Finite G] [IsGaloisGroup G K L]  :=
  haveI : Finite (decompositionGroup P G) := inferInstance
  IsGaloisGroup.mulEquivAlgEquiv
    (decompositionGroup P G)
    (decompositionField (K := K) (L := L) G P) L

/-- The equivalence `G_P ≃ Gal(L/Z_P)` acts by the original group action on
elements of `L`. -/
@[simp]
theorem dedekindTower_decompositionGroupEquivGalDecompositionField_apply
     
    [Finite G] [IsGaloisGroup G K L]
    (σ : decompositionGroup P G) (x : L) :
    dedekindTower_decompositionGroupEquivGalDecompositionField
        (K := K) (L := L) G P σ x =
      (σ : G) • x :=
  rfl
end




































variable {G}

















variable (G)









































































































































































end Dedekind
end HilbertRamification

end
