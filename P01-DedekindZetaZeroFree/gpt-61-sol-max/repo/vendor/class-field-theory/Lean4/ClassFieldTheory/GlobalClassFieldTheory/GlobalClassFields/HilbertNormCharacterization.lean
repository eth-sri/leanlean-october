module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassField
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Hilbert norm subgroups and unramified extensions

For a finite Galois extension with no ramified finite prime, the actual
idele-class narrow finite conductor is zero.  Consequently its norm subgroup
contains the big-Hilbert norm subgroup.  This is the norm-subgroup form
of the maximality of the big Hilbert class field.

The inclusion yields a canonical surjection from the narrow class group
onto the actual norm quotient, together with the exact kernel
factorization and the resulting divisibility of orders.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Keep norm-range quotient normality out of exported declaration types. -/
local instance
    hilbertNormCharacterization_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- If no finite prime of the base ramifies in the extension, then the
narrow finite conductor of the actual idele-class norm subgroup is zero. -/
theorem ideleClassNorm_narrowFiniteConductor_eq_zero_of_no_ramifiedFinitePlaces
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    ideleClassNormNarrowFiniteConductor (K := K) (L := L) = 0 := by
  ext v
  rw [Finsupp.zero_apply]
  apply Finsupp.notMem_support_iff.mp
  intro hv
  have hramified :=
    ideleClassNorm_narrowFiniteConductor_support_subset_ramifiedBaseFinitePlaces
      (K := K) (L := L) hv
  rw [hunramified] at hramified
  simp at hramified

/-- The norm subgroup of every finite Galois extension unramified at all
finite primes contains the big-Hilbert norm subgroup. -/
theorem
    bigHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_no_ramifiedFinitePlaces
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    bigHilbertClassFieldNormSubgroup (K := K) ≤
      (_root_.ideleClassNorm K L).range := by
  apply
    (bigHilbertClassFieldNormSubgroup_le_iff_narrowFiniteConductor_eq_zero
      (ideleClassNormConductorialSubgroup (K := K) (L := L))).2
  exact
    ideleClassNorm_narrowFiniteConductor_eq_zero_of_no_ramifiedFinitePlaces
      (K := K) (L := L) hunramified

/-- The canonical transition from the big-Hilbert reciprocity quotient
to the actual norm quotient of an everywhere finite-unramified
extension. -/
def bigHilbertClassFieldQuotientToIdeleClassNormQuotient
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    (IdeleClassGroup K ⧸
        bigHilbertClassFieldNormSubgroup (K := K)) →*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  QuotientGroup.map
    (bigHilbertClassFieldNormSubgroup (K := K))
    ((_root_.ideleClassNorm K L).range)
    (MonoidHom.id _)
    (fun _ hx =>
      bigHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_no_ramifiedFinitePlaces
        (K := K) (L := L) hunramified hx)

/-- The big-Hilbert quotient transition sends an idele class to the
same class modulo the actual norm subgroup. -/
@[simp]
theorem bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (x : IdeleClassGroup K) :
    bigHilbertClassFieldQuotientToIdeleClassNormQuotient
        (K := K) (L := L) hunramified
        (QuotientGroup.mk'
          (bigHilbertClassFieldNormSubgroup (K := K)) x) =
      QuotientGroup.mk'
        ((_root_.ideleClassNorm K L).range) x :=
  rfl








































































































































































































end GlobalClassFields
end GlobalClassFieldTheory

end
