module

public import Mathlib

public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Narrow
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorLattice

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The big Hilbert class field

The big Hilbert class field is the ray class field of modulus one (the
zero finite modulus in the exponent-valued representation).  This file
identifies its defining norm quotient with the narrow class group.  The
maximal-unramified field statement follows from this input together with
the narrow finite conductor/ramification criterion.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The norm subgroup defining the big Hilbert class field. -/
def bigHilbertClassFieldNormSubgroup :
    Subgroup (IdeleClassGroup K) :=
  (RayClass.Modulus.narrowOfFinite
    (0)).congruenceSubgroup

instance bigHilbertClassFieldNormSubgroup_normal :
    (bigHilbertClassFieldNormSubgroup (K := K)).Normal := by
  let : IsMulCommutative (IdeleClassGroup K) :=
    IsMulCommutative.of_comm (fun a b => mul_comm a b)
  exact Subgroup.normal_of_isMulCommutative _

/-- The norm subgroup defining the big Hilbert class field is closed. -/
theorem bigHilbertClassFieldNormSubgroup_isClosed :
    IsClosed
      ((bigHilbertClassFieldNormSubgroup (K := K) :
        Subgroup (IdeleClassGroup K)) :
        Set (IdeleClassGroup K)) :=
  RayClass.isClosed_congruenceSubgroup
    (RayClass.Modulus.narrowOfFinite
      (0))

/-- The reciprocity quotient for the big Hilbert class field is the narrow
ideal class group. -/
alias bigHilbertClassFieldQuotientEquivNarrowClassGroup := _root_.RayClass.rayClassGroupNarrowZeroEquivNarrowClassGroup


















/-- Among conductorial idèle-class subgroups, containing the big-Hilbert
norm subgroup is equivalent to having narrow finite conductor zero. -/
theorem
    bigHilbertClassFieldNormSubgroup_le_iff_narrowFiniteConductor_eq_zero
    (H : ConductorialSubgroup K) :
    bigHilbertClassFieldNormSubgroup (K := K) ≤ H.1 ↔
      H.narrowFiniteConductor = 0 := by
  constructor
  · intro hH
    have hdef :
        IsDefiningModulus H.1
          (RayClass.Modulus.narrowOfFinite
            (0)) := hH
    apply le_antisymm
    · exact H.narrowFiniteConductor_le hdef
    · exact bot_le
  · intro hconductor
    have hdef := H.narrowFiniteConductor_isDefiningModulus
    rw [hconductor] at hdef
    exact hdef













end GlobalClassFields
end GlobalClassFieldTheory

end
