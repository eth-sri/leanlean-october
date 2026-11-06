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
# Hilbert ramification theory: decomposition and inertia fields

This file contains the fixed-field layer of prime-decomposition theory.  The
Dedekind-domain file defines the decomposition and inertia groups attached to
a prime ideal; here we view those groups as subgroups of a finite Galois group
acting on the fraction field and use mathlib's Galois correspondence.
-/

noncomputable section

namespace HilbertRamification
namespace Dedekind

open Algebra Module

variable {A B K L : Type*}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Field K] [Field L] [Algebra K L]
variable (G : Type*) [Group G] [MulSemiringAction G L] [SMulCommClass G K L]

/-- The fixed field of a subgroup of a finite Galois group, in the
`IsGaloisGroup` formulation used by the Dedekind ramification API. -/
abbrev fixedFieldOfSubgroup (H : Subgroup G) : IntermediateField K L :=
  FixedPoints.intermediateField H

variable {G}

/-- Elementwise membership in the fixed field of a subgroup. -/
@[simp]
theorem mem_fixedFieldOfSubgroup_iff
    {H : Subgroup G} {x : L} :
    x ∈ fixedFieldOfSubgroup (K := K) (L := L) G H ↔
      ∀ σ : H, (σ : G) • x = x := by
  rfl



variable (G)



variable {G}





variable (G)

/-- The decomposition and inertia definition:
the decomposition field `Z_P`, as the fixed field of the decomposition group.
-/
abbrev decompositionField
    (P : Ideal B) [MulSemiringAction G B] : IntermediateField K L :=
  fixedFieldOfSubgroup (K := K) (L := L) G (decompositionGroup P G)

variable {G}

/-- Elementwise membership in the decomposition field. -/
@[simp]
theorem mem_decompositionField_iff
    {P : Ideal B} [MulSemiringAction G B] {x : L} :
    x ∈ decompositionField (K := K) (L := L) G P ↔
      ∀ σ ∈ decompositionGroup P G, σ • x = x := by
  simp [decompositionField]

variable (G)



variable {G}









variable (G)



/-- The prime-decomposition tower identity:
the decomposition group is the Galois group of `L/Z_P`. -/
instance decompositionGroup_isGaloisGroup
    (P : Ideal B) [MulSemiringAction G B] [IsGaloisGroup G K L] :
    IsGaloisGroup (decompositionGroup P G)
      (decompositionField (K := K) (L := L) G P) L := by
  dsimp [decompositionField, fixedFieldOfSubgroup]
  infer_instance

/-- The inertia-field definition:
the inertia field `T_P`, as the fixed field of the inertia group. -/
abbrev inertiaField
    (P : Ideal B) [MulSemiringAction G B] : IntermediateField K L :=
  fixedFieldOfSubgroup (K := K) (L := L) G (inertiaGroup P G)

variable {G}

/-- Elementwise membership in the inertia field. -/
@[simp]
theorem mem_inertiaField_iff
    {P : Ideal B} [MulSemiringAction G B] {x : L} :
    x ∈ inertiaField (K := K) (L := L) G P ↔
      ∀ σ ∈ inertiaGroup P G, σ • x = x := by
  simp [inertiaField]

variable (G)

/-- Prime-decomposition statement:
the decomposition field is contained in the inertia field. -/
theorem decompositionField_le_inertiaField
    (P : Ideal B) [MulSemiringAction G B] :
    decompositionField (K := K) (L := L) G P ≤
      inertiaField (K := K) (L := L) G P :=
  by
    simpa [decompositionField, inertiaField, fixedFieldOfSubgroup, inertiaGroup, decompositionGroup] using
      (IsGaloisGroup.fixedPoints_le_of_le
        (G := G) (K := K) (L := L)
        (H := inertiaGroup P G) (H' := decompositionGroup P G)
        (by
          simpa [inertiaGroup, decompositionGroup] using
            (Ideal.inertia_le_stabilizer (M := G) P)))



variable {G}





variable (G)



/-- A prime-decomposition consequence:
the inertia group is the Galois group of `L/T_P`. -/
instance inertiaGroup_isGaloisGroup
    (P : Ideal B) [MulSemiringAction G B] [IsGaloisGroup G K L] :
    IsGaloisGroup (inertiaGroup P G)
      (inertiaField (K := K) (L := L) G P) L := by
  dsimp [inertiaField, fixedFieldOfSubgroup]
  infer_instance

end Dedekind
end HilbertRamification

end
